/* Handle Native Client manifest files.

   Copyright (C) 2011 Free Software Foundation, Inc.

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include "nacl-manifest.h"

#include "defs.h"
#include "command.h"
#include "completer.h"
#include "exec.h"
#include "frame.h"
#include "gdbcore.h"
#include "observer.h"
#include "readline/readline.h"
#include "solib.h"
#include "symfile.h"
#include "objfiles.h"

#include <ctype.h>
#include <stdio.h>
#include <string.h>

#define MANIFEST_MAX_NESTING 4

#define MANIFEST_MAX_STRING_SIZE 256

struct file_list
  {
    struct file_list *next;

    char original_name[MANIFEST_MAX_STRING_SIZE];

    char name[MANIFEST_MAX_STRING_SIZE];
  };

/* Mapping of 32-bit *.so libraries.  */
static struct file_list *nacl_file_list_32 = NULL;

/* Mapping of 64-bit *.so libraries.  */
static struct file_list *nacl_file_list_64 = NULL;

/* runnable-ld.so or statically linked 32-bit program name.  */
static char *nacl_program_filename_32 = NULL;

/* runnable-ld.so or statically linked 64-bit program name.  */
static char *nacl_program_filename_64 = NULL;

const char *
nacl_manifest_find (char *original_name)
{
  struct file_list *curr;
  int addr_bit;

  /* HACK: NaCl uses "/lib/" library path to inform service runtime that the
           file should be opened as solib vs. ordinary file. Split that prefix
           here so that GDB can find these files via manifest or as is.  */
  if (strncmp (original_name, "/lib/", 5) == 0)
    original_name += 5;

  addr_bit = gdbarch_addr_bit(target_gdbarch ());

  if (addr_bit == 32)
    curr = nacl_file_list_32;
  else if (addr_bit == 64)
    curr = nacl_file_list_64;
  else
    error(_("Can't map files with manifest due to unknown architecture"));

  for (; curr; curr = curr->next)
    {
      if (strcmp (original_name, curr->original_name) == 0)
        return curr->name;
    }

  if (strcmp(original_name, "NaClMain") == 0)
    {
      if (addr_bit == 32 && nacl_program_filename_32)
	return nacl_program_filename_32;
      if (addr_bit == 64 && nacl_program_filename_64)
	return nacl_program_filename_64;
      error(_("runnable-ld.so not found in manifest"));
    }
  if (strlen(original_name) == 0)
    {
      return nacl_manifest_find("main.nexe");
    }
  /* TODO: Should we complain if we have a manifest but failed to find
     /lib/filename there? */

  return original_name;
}

static void
nacl_manifest_free_list (struct file_list *nacl_file_list)
{
  while (nacl_file_list)
    {
      struct file_list *next = nacl_file_list->next;

      xfree (nacl_file_list);
      nacl_file_list = next;
    }
}

static void
nacl_manifest_free (void)
{
  nacl_manifest_free_list(nacl_file_list_32);
  nacl_file_list_32 = NULL;
  nacl_manifest_free_list(nacl_file_list_64);
  nacl_file_list_64 = NULL;
  xfree (nacl_program_filename_32);
  xfree (nacl_program_filename_64);
  nacl_program_filename_32 = NULL;
  nacl_program_filename_64 = NULL;
}

/* Very dumb parser for JSON subset used in Native Client manifest files.
   This is a SAX-style parser that runs callbacks on JSON events.  */

struct json_manifest_reader
  {
    /* Manifest file.  */
    FILE *file;

    /* Stack of members being parsed.  */
    const char *members[MANIFEST_MAX_NESTING];

    /* Members stack size.  */
    int nesting;

    /* Manifest file directory without slash at the end. */
    char *dirname;
  };

static void
json_on_member (struct json_manifest_reader *r, const char *member)
{
  if (r->nesting == MANIFEST_MAX_NESTING)
    error (_("Invalid manifest file."));

  r->members[r->nesting] = member;
  ++r->nesting;
}

static void
json_on_end_member (struct json_manifest_reader *r, const char *member)
{
  --r->nesting;
}

static void
append_dir_name (struct json_manifest_reader *r,
		 char *full_path,
		 int max_path_size,
		 const char *name)
{
  full_path[0] = '\0';
  if (r->dirname)
    {
      if (strlen (r->dirname) + strlen (SLASH_STRING) >= max_path_size)
	error (_("Mapped file name in manifest is too long."));
      strcpy (full_path, r->dirname);
      strcat (full_path, SLASH_STRING);
    }
  if (strlen (full_path) + strlen (name) >= max_path_size)
    error (_("Mapped file name in manifest is too long."));
  strcat (full_path, name);
}

static struct file_list *
json_append_file_list (struct json_manifest_reader *r,
                       struct file_list **nacl_file_list,
                       const char *original_name,
                       const char *name)
{
  struct file_list *curr = xzalloc (sizeof(struct file_list));

  if (strlen(original_name) >= MANIFEST_MAX_STRING_SIZE)
    error (_("Original file name in manifest is too long."));
  strcpy (curr->original_name, original_name);
  append_dir_name (r, curr->name, MANIFEST_MAX_STRING_SIZE, name);

  curr->next = *nacl_file_list;
  *nacl_file_list = curr;
  return curr;
}

static void
json_on_string_value (struct json_manifest_reader *r, const char *value)
{
  if (r->nesting == 3 &&
      strcmp(r->members[0], "program") == 0 &&
      strcmp(r->members[2], "url") == 0)
    {
      /* We'll xfree nacl_program_filename_* in nacl_manifest_free.  */
      if (strcmp (r->members[1], "x86-32") == 0)
	{
	  nacl_program_filename_32 = malloc (MANIFEST_MAX_STRING_SIZE);
	  append_dir_name (r, nacl_program_filename_32,
			   MANIFEST_MAX_STRING_SIZE, value);
	}
      else if (strcmp (r->members[1], "x86-64") == 0)
	{
	  nacl_program_filename_64 = malloc (MANIFEST_MAX_STRING_SIZE);
	  append_dir_name (r, nacl_program_filename_64,
			   MANIFEST_MAX_STRING_SIZE, value);
	}
    }
  else if (r->nesting == 4 &&
           strcmp (r->members[0], "files") == 0 &&
           strcmp (r->members[3], "url") == 0)
    {
      if (strcmp(r->members[2], "x86-32") == 0)
	json_append_file_list(r, &nacl_file_list_32, r->members[1], value);
      else if (strcmp(r->members[2], "x86-64") == 0)
	json_append_file_list(r, &nacl_file_list_64, r->members[1], value);
    }
}

/* Basic parsing utilities.  */

static int
json_getc (struct json_manifest_reader *r)
{
  return fgetc (r->file);
}

static int
json_getc_nonspace (struct json_manifest_reader *r)
{
  int c;

  while (isspace (c = json_getc (r)));
  return c;
}

/* Parsing routines.

   json_parse_something assumes we are just going to read first character of
   something, probably skipping preceding whitespaces.

   json_finish_parse_something assumes we already read first character of
   something, and checked it was correct.  */


static void json_parse_value (struct json_manifest_reader *r);

static void
json_finish_parse_string (struct json_manifest_reader *r, char *buf, int len)
{
  int c;

  for (; len; --len)
    {
      c = json_getc (r);
      if (c == '"')
        {
          *buf = '\0';
          return;
        }

      if (c == '\n' || c == EOF)
        break;

      *buf++ = (char)c;
    }

  error (_("Invalid manifest file."));
}

/* We only accept non-empty objects.  */

static void
json_finish_parse_object (struct json_manifest_reader *r)
{
  int c;
  char buf[MANIFEST_MAX_STRING_SIZE];

  do
    {
      c = json_getc_nonspace(r);
      if (c == '}')
	break;
      if (c != '\"')
        error (_("Invalid manifest file."));

      json_finish_parse_string (r, buf, MANIFEST_MAX_STRING_SIZE);
      json_on_member (r, buf);

      if (json_getc_nonspace (r) != ':')
        error (_("Invalid manifest file."));

      json_parse_value (r);
      json_on_end_member (r, buf);
    }
  while ((c = json_getc_nonspace (r)) == ',');

  if (c != '}')
    error (_("Invalid manifest file."));
}

/* We only accept objects or strings.  */

static void
json_parse_value (struct json_manifest_reader *r)
{
  int c = json_getc_nonspace (r);

  if (c == '{')
    {
      json_finish_parse_object (r);
    }
  else if (c == '\"')
    {
      char buf[MANIFEST_MAX_STRING_SIZE];

      json_finish_parse_string (r, buf, MANIFEST_MAX_STRING_SIZE);
      json_on_string_value (r, buf);
    }
  else
    {
      error (_("Invalid manifest file."));
    }
}

/* GDB commands for specifying Native Client files.  */

static void
nacl_irt_command (char *args, int from_tty)
{
  if (args)
    {
      char **argv;
      struct cleanup *old_chain;
      char *nacl_irt_filename;

      argv = gdb_buildargv(args);
      old_chain = make_cleanup_freeargv(argv);
      if (*argv == NULL)
	error (_("No IRT file name was specified"));

      nacl_irt_filename = tilde_expand (*argv);
      make_cleanup(xfree, nacl_irt_filename);

      symbol_file_add (nacl_irt_filename, from_tty ? SYMFILE_VERBOSE : 0,
		       NULL, OBJF_USERLOADED);
      /* Recalculate frames.  */
      reinit_frame_cache ();
      do_cleanups(old_chain);
    }
}

static struct observer *about_to_proceed_observer = NULL;

static void
about_to_proceed_hook (void)
{
  if (exec_bfd == NULL)
    {
      const char *filename = nacl_manifest_find ("NaClMain");
      exec_file_attach ((char *) filename, 0);
      symbol_file_add (filename, SYMFILE_MAINLINE, NULL, 0);
    }
}

static void
nacl_manifest_command (char *args, int from_tty)
{
  if (args)
    {
      char **argv;
      struct cleanup *old_chain;
      char *manifest_filename;
      struct json_manifest_reader r = { 0 };

      argv = gdb_buildargv (args);
      old_chain = make_cleanup_freeargv (argv);
      if (*argv == NULL)
	error (_("No manifest file name was specified"));

      manifest_filename = tilde_expand (*argv);
      make_cleanup (xfree, manifest_filename);

      r.file = fopen (manifest_filename, "r");
      if (!r.file)
        perror_with_name (manifest_filename);
      make_cleanup_fclose (r.file);

      r.dirname = ldirname (manifest_filename);
      make_cleanup (xfree, r.dirname);

      /* TODO: Kill existing manifest only if new one parsed OK!  */
      nacl_manifest_free ();
      json_parse_value (&r);

      solib_add (NULL, from_tty, NULL, 1);

      if (about_to_proceed_observer == NULL)
	{
	  about_to_proceed_observer
	    = observer_attach_about_to_proceed (about_to_proceed_hook);
	}

      do_cleanups(old_chain);
    }
}

/* Provide a prototype to silence -Wmissing-prototypes.  */
extern void _initialize_nacl_manifest (void);

void
_initialize_nacl_manifest (void)
{
  struct cmd_list_element *c;

  c = add_com ("nacl-irt", class_files, nacl_irt_command,
	       _("Use FILE as Native Client IRT to be debugged."));
  set_cmd_completer (c, filename_completer);

  c = add_com ("nacl-manifest", class_files, nacl_manifest_command,
	       _("Use FILE as Native Client manifest for the program"
		 " to be debugged."));
  set_cmd_completer (c, filename_completer);
}

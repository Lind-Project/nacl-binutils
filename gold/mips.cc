// mips.cc -- mips target support for gold.

// Copyright 2011, 2012, 2013 Free Software Foundation, Inc.
// Written by Sasa Stankovic <sasa.stankovic@rt-rk.com>
//        and Aleksandar Simeonov <aleksandar.simeonov@rt-rk.com>.
// This file contains borrowed and adapted code from bfd/elfxx-mips.c.

// This file is part of gold.

// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston,
// MA 02110-1301, USA.

#include "gold.h"

#include <algorithm>
#include <set>
#include <sstream>
#include "demangle.h"

#include "elfcpp.h"
#include "parameters.h"
#include "reloc.h"
#include "mips.h"
#include "object.h"
#include "symtab.h"
#include "layout.h"
#include "output.h"
#include "target.h"
#include "target-reloc.h"
#include "target-select.h"
#include "tls.h"
#include "errors.h"
#include "gc.h"
#include "nacl.h"

namespace
{
using namespace gold;

template<int size, bool big_endian>
class Mips_output_data_plt;

template<int size, bool big_endian>
class Mips_output_data_got;

template<int size, bool big_endian>
class Target_mips;

template<int size, bool big_endian>
class Mips_output_section_reginfo;

template<int size, bool big_endian>
class Mips_output_data_la25_stub;

template<int size, bool big_endian>
class Mips_output_data_mips_stubs;

template<int size>
class Mips_symbol;

template<int size, bool big_endian>
class Mips_got_info;

template<int size, bool big_endian>
class Mips_relobj;

// The ""'s around str ensure str is a string literal, so sizeof works.
#define strprefix(var, str)   (strncmp(var, str, sizeof("" str "") - 1) == 0)

// Return true if this symbol should be added to the dynamic symbol
// table.  This function is identical to Symbol::should_add_dynsym_entry.

inline bool
should_add_dynsym_entry(Symbol* sym, Symbol_table* symtab)
{
  // If the symbol is only present on plugin files, the plugin decided we
  // don't need it.
  if (!sym->in_real_elf())
    return false;

  // If the symbol is used by a dynamic relocation, we need to add it.
  if (sym->needs_dynsym_entry())
    return true;

  // If this symbol's section is not added, the symbol need not be added. 
  // The section may have been GCed.  Note that export_dynamic is being 
  // overridden here.  This should not be done for shared objects.
  if (parameters->options().gc_sections() 
      && !parameters->options().shared()
      && sym->source() == Symbol::FROM_OBJECT
      && !sym->object()->is_dynamic())
    {
      Relobj* relobj = static_cast<Relobj*>(sym->object());
      bool is_ordinary;
      unsigned int shndx = sym->shndx(&is_ordinary);
      if (is_ordinary && shndx != elfcpp::SHN_UNDEF
          && !relobj->is_section_included(shndx)
          && !symtab->is_section_folded(relobj, shndx))
        return false;
    }

  // If the symbol was forced dynamic in a --dynamic-list file
  // or an --export-dynamic-symbol option, add it.
  if (!sym->is_from_dynobj()
      && (parameters->options().in_dynamic_list(sym->name())
	  || parameters->options().is_export_dynamic_symbol(sym->name())))
    {
      if (!sym->is_forced_local())
        return true;
      gold_warning(_("Cannot export local symbol '%s'"),
		   sym->demangled_name().c_str());
      return false;
    }

  // If the symbol was forced local in a version script, do not add it.
  if (sym->is_forced_local())
    return false;

  // If dynamic-list-data was specified, add any STT_OBJECT.
  if (parameters->options().dynamic_list_data()
      && !sym->is_from_dynobj()
      && sym->type() == elfcpp::STT_OBJECT)
    return true;

  // If --dynamic-list-cpp-new was specified, add any new/delete symbol.
  // If --dynamic-list-cpp-typeinfo was specified, add any typeinfo symbols.
  if ((parameters->options().dynamic_list_cpp_new()
       || parameters->options().dynamic_list_cpp_typeinfo())
      && !sym->is_from_dynobj())
    {
      // TODO(csilvers): We could probably figure out if we're an operator
      //                 new/delete or typeinfo without the need to demangle.
      char* demangled_name = cplus_demangle(sym->name(),
                                            DMGL_ANSI | DMGL_PARAMS);
      if (demangled_name == NULL)
        {
          // Not a C++ symbol, so it can't satisfy these flags
        }
      else if (parameters->options().dynamic_list_cpp_new()
               && (strprefix(demangled_name, "operator new")
                   || strprefix(demangled_name, "operator delete")))
        {
          free(demangled_name);
          return true;
        }
      else if (parameters->options().dynamic_list_cpp_typeinfo()
               && (strprefix(demangled_name, "typeinfo name for")
                   || strprefix(demangled_name, "typeinfo for")))
        {
          free(demangled_name);
          return true;
        }
      else
        free(demangled_name);
    }

  // If exporting all symbols or building a shared library,
  // and the symbol is defined in a regular object and is
  // externally visible, we need to add it.
  if ((parameters->options().export_dynamic() || parameters->options().shared())
      && !sym->is_from_dynobj()
      && !sym->is_undefined()
      && sym->is_externally_visible())
    return true;

  return false;
}

// The ABI says that every symbol used by dynamic relocations must have
// a global GOT entry.  Among other things, this provides the dynamic
// linker with a free, directly-indexed cache.  The GOT can therefore
// contain symbols that are not referenced by GOT relocations themselves
// (in other words, it may have symbols that are not referenced by things
// like R_MIPS_GOT16 and R_MIPS_GOT_PAGE).

// GOT relocations are less likely to overflow if we put the associated
// GOT entries towards the beginning.  We therefore divide the global
// GOT entries into two areas: "normal" and "reloc-only".  Entries in
// the first area can be used for both dynamic relocations and GP-relative
// accesses, while those in the "reloc-only" area are for dynamic
// relocations only.

// These GGA_* ("Global GOT Area") values are organised so that lower
// values are more general than higher values.  Also, non-GGA_NONE
// values are ordered by the position of the area in the GOT.

enum Global_got_area
{
  GGA_NORMAL = 0,
  GGA_RELOC_ONLY = 1,
  GGA_NONE = 2
};

// The types of GOT entries needed for this platform.
// These values are exposed to the ABI in an incremental link.
// Do not renumber existing values without changing the version
// number of the .gnu_incremental_inputs section.
enum Got_type
{
  GOT_TYPE_STANDARD = 0,      // GOT entry for a regular symbol
  GOT_TYPE_TLS_OFFSET = 1,    // GOT entry for TLS offset
  GOT_TYPE_TLS_PAIR = 2,      // GOT entry for TLS module/offset pair

  // GOT entries for multi-got. We support up to 1024 gots in multi-got links.
  GOT_TYPE_STANDARD_MULTIGOT = 3,
  GOT_TYPE_TLS_OFFSET_MULTIGOT = GOT_TYPE_STANDARD_MULTIGOT + 1024,
  GOT_TYPE_TLS_PAIR_MULTIGOT = GOT_TYPE_TLS_OFFSET_MULTIGOT + 1024
};

// Tls type of got entry.
enum Got_tls_type
{
  GOT_NORMAL = 0,
  GOT_TLS_GD = 1,
  GOT_TLS_LDM = 2,
  GOT_TLS_IE = 4
};

// This class is used to hold information about one GOT entry.
// There are two types of entry:
//
//    (1) SYMBOL + OFFSET addresses, where SYMBOL is local to an input object
//          (object != NULL, symndx >= 0)
//    (2) SYMBOL addresses, where SYMBOL is not local to an input object
//          (object != NULL, symndx == -1)
//
// Type (2) entries are treated differently for different types of GOT.
// In the "master" GOT -- i.e.  the one that describes every GOT
// reference needed in the link -- the Mips_got_entry is keyed on both
// the symbol and the input object that references it.  If it turns out
// that we need multiple GOTs, we can then use this information to
// create separate GOTs for each input object.
//
// However, we want each of these separate GOTs to have at most one
// entry for a given symbol, so their type (2) entries are keyed only
// on the symbol.  The input object given by the "object" field is somewhat
// arbitrary in this case.
//
// This means that when there are multiple GOTs, each GOT has a unique
// Mips_got_entry for every symbol within it.  We can therefore use the
// Mips_got_entry fields to track the symbol's GOT index.
//
// However, if it turns out that we need only a single GOT, we continue
// to use the master GOT to describe it.  There may therefore be several
// Mips_got_entries for the same symbol, each with a different input object.
// We want to make sure that each symbol gets a unique GOT entry, so when
// there's a single GOT, we use the symbol's fields, not the
// Mips_got_entry fields, to track a symbol's GOT index.

template<int size, bool big_endian>
class Mips_got_entry
{
  typedef typename elfcpp::Elf_types<size>::Elf_Addr Mips_address;

public:
  Mips_got_entry(Sized_relobj_file<size, big_endian> *object,
                 unsigned int symndx, Mips_address addend,
                 unsigned char tls_type, unsigned int shndx)
    : object_(object), symndx_(symndx), tls_type_(tls_type), shndx_(shndx)
  { this->d.addend = addend; }

  Mips_got_entry(Sized_relobj_file<size, big_endian> *object,
                 Mips_symbol<size>* sym, unsigned char tls_type)
    : object_(object), symndx_(-1U), tls_type_(tls_type), shndx_(-1U)
  { this->d.sym = sym; }

  bool
  is_for_local_symbol() const
  { return this->object_ != NULL && this->symndx_ != -1U; }

  bool
  is_for_global_symbol() const
  { return this->object_ != NULL && this->symndx_ == -1U; }

  size_t
  hash(bool multi_got) const
  {
    uintptr_t object_id = reinterpret_cast<uintptr_t>(this->object_);
    uintptr_t sym_id = reinterpret_cast<uintptr_t>(this->d.sym);
    if (!multi_got)
      {
        // got_entries only match if they're identical, so use all fields to
        // compute the hash, and compare the appropriate union members.
        return (this->symndx_
                + ((this->tls_type_ & GOT_TLS_LDM) << 17)
                + object_id
                + (this->symndx_ != -1U ? this->d.addend : sym_id));
      }
    else
      {
        // multi_got_entries are still a match in the case of global objects,
        // even if the input object in which they're referenced differs, so the
        // hash computation and compare functions are adjusted
        // accordingly.
        return (this->symndx_
                + (this->symndx_ != -1U
                   ? ((this->tls_type_ & GOT_TLS_LDM)
                      ? (GOT_TLS_LDM << 17)
                      : (object_id + this->d.addend))
                   : sym_id));
      }
  }

  bool
  equals(Mips_got_entry<size, big_endian> *other, bool multi_got) const
  {
    if (!multi_got)
      {
        // An LDM entry can only match another LDM entry.
        if ((this->tls_type_ ^ other->tls_type_) & GOT_TLS_LDM)
          return false;

        return (this->object_ == other->object_
                && this->symndx_ == other->symndx_
                && (this->symndx_ != -1U
                    ? this->d.addend == other->d.addend
                    : this->d.sym == other->d.sym));
      }
    else
      {
        // Any two LDM entries match.
        if (this->tls_type_ & other->tls_type_ & GOT_TLS_LDM)
          return true;

        // Nothing else matches an LDM entry.
        if ((this->tls_type_ ^ other->tls_type_) & GOT_TLS_LDM)
          return false;

        return (this->symndx_ == other->symndx_
                && (this->symndx_ != -1U
                    ? (this->object_ == other->object_
                       && this->d.addend == other->d.addend)
                    : this->d.sym == other->d.sym));
      }
  }

  // The input object in which the symbol is defined.
  Sized_relobj_file<size, big_endian>*
  object() const
  { return this->object_; }

  // The index of the symbol if we have a local symbol; -1 otherwise.
  unsigned int
  symndx() const
  { return this->symndx_; }

  Mips_address
  addend() const
  {
    gold_assert(this->symndx_ != -1U);
    return this->d.addend;
  }

  Mips_symbol<size>*
  sym() const
  {
    gold_assert(this->symndx_ == -1U);
    return this->d.sym;
  }

  bool
  has_tls() const
  { return this->tls_type_ != GOT_NORMAL; }

  void
  add_tls_type(unsigned char tls_flag)
  { this->tls_type_ |= tls_flag; }

  bool
  has_tls_type(unsigned char tls_flag) const
  { return this->tls_type_ & tls_flag; }

  unsigned int
  shndx() const
  { return this->shndx_; }

private:
  // The input object in which the symbol is defined.
  Sized_relobj_file<size, big_endian>* object_;
  // The index of the symbol if we have a local symbol; -1 otherwise.
  unsigned int symndx_;

  union
  {
    // If object != NULL && symndx != -1, the addend of the relocation
    // that should be added to the symbol value.
    Mips_address addend;
    // If object != NULL && symndx == -1, the global symbol
    // corresponding to this GOT entry.  The symbol's entry
    // is in the local area if mips_sym->global_got_area is GGA_NONE,
    // otherwise it is in the global area.
    Mips_symbol<size>* sym;
  } d;

  // The TLS types included in this GOT entry (specifically, GD and
  // IE).  The GD and IE flags can be added as we encounter new
  // relocations.  LDM can also be set; it will always be alone, not
  // combined with any GD or IE flags.  An LDM GOT entry will be
  // a local symbol entry with r_symndx == 0.
  unsigned char tls_type_;

  unsigned int shndx_;
};

// Hash for Mips_got_entry.

template<int size, bool big_endian>
class Mips_got_entry_hash
{
 public:
  Mips_got_entry_hash(bool multi_got)
    : multi_got_(multi_got)
  { }

  size_t
  operator()(Mips_got_entry<size, big_endian> *entry) const
  { return entry->hash(this->multi_got_); }

 private:
  bool multi_got_;
};

// Equality for Mips_got_entry.

template<int size, bool big_endian>
class Mips_got_entry_eq
{
 public:
  Mips_got_entry_eq(bool multi_got)
    : multi_got_(multi_got)
  { }

  bool
  operator()(Mips_got_entry<size, big_endian> *e1,
             Mips_got_entry<size, big_endian> *e2) const
  { return e1->equals(e2, this->multi_got_); }

 private:
  bool multi_got_;
};

// Got_page_range.  This class describes a range of addends: [MIN_ADDEND,
// MAX_ADDEND]. The instances form a non-overlapping list that is sorted by
// increasing MIN_ADDEND.

struct Got_page_range
{
  Got_page_range()
    : next(NULL), min_addend(0), max_addend(0)
  { }

  Got_page_range *next;
  int min_addend;
  int max_addend;

  // Return the maximum number of GOT page entries required.
  int
  get_max_pages()
  { return (this->max_addend - this->min_addend + 0x1ffff) >> 16; }
};

// Got_page_entry.  This class describes the range of addends that are applied
// to page relocations against a given symbol.

struct Got_page_entry
{
  Got_page_entry()
    : object(NULL), symndx(-1U), ranges(NULL), num_pages(0)
  { }

  Got_page_entry(Object *object_, unsigned int symndx_)
    : object(object_), symndx(symndx_), ranges(NULL), num_pages(0)
  { }

  // The input object in which the symbol is defined.
  Object *object;
  // The index of the symbol, as stored in the relocation r_info.
  unsigned int symndx;
  // The ranges for this page entry.
  Got_page_range *ranges;
  // The maximum number of page entries needed for RANGES.
  unsigned int num_pages;
};

// Hash for Got_page_entry.

struct Got_page_entry_hash
{
  size_t
  operator()(Got_page_entry *entry) const
  { return reinterpret_cast<uintptr_t>(entry->object) + entry->symndx; }
};

// Equality for Got_page_entry.

struct Got_page_entry_eq
{
  bool
  operator()(Got_page_entry *entry1, Got_page_entry *entry2) const
  {
    uintptr_t object_id1 = reinterpret_cast<uintptr_t>(entry1->object);
    uintptr_t object_id2 = reinterpret_cast<uintptr_t>(entry2->object);
    return (object_id1 == object_id2 && entry1->symndx == entry2->symndx);
  }
};

// This class maps an input object to a got in a multi-got link.

template<int size, bool big_endian>
struct Object2got_entry
{
  Object2got_entry(const Object *object_)
    : object(object_)
  { }

  const Object *object;
  Mips_got_info<size, big_endian>* g;
};

// Hash for Object2got_entry.

template<int size, bool big_endian>
struct Object2got_entry_hash
{
  size_t
  operator()(Object2got_entry<size, big_endian> *entry) const
  { return reinterpret_cast<uintptr_t>(entry->object); }
};

// Equality for Object2got_entry.

template<int size, bool big_endian>
struct Object2got_entry_eq
{
  bool
  operator()(Object2got_entry<size, big_endian> *entry1,
             Object2got_entry<size, big_endian> *entry2) const
  {
    uintptr_t object_id1 = reinterpret_cast<uintptr_t>(entry1->object);
    uintptr_t object_id2 = reinterpret_cast<uintptr_t>(entry2->object);
    return object_id1 == object_id2;
  }
};

// This class is used to hold .got information when linking.

template<int size, bool big_endian>
class Mips_got_info
{
  typedef Output_data_reloc<elfcpp::SHT_REL, true, size, big_endian>
    Reloc_section;
  typedef Unordered_map<unsigned int, unsigned int> Got_page_offsets;

  // Unordered set of got entries.
  typedef Unordered_set<Mips_got_entry<size, big_endian>*,
      Mips_got_entry_hash<size, big_endian>,
      Mips_got_entry_eq<size, big_endian> > Got_entry_set;

  // Unordered set of got page entries.
  typedef Unordered_set<Got_page_entry*,
      Got_page_entry_hash, Got_page_entry_eq> Got_page_entry_set;

  typedef Unordered_set<Object2got_entry<size, big_endian>*,
      Object2got_entry_hash<size, big_endian>,
      Object2got_entry_eq<size, big_endian> > Object2got_entry_set;

 public:
  Mips_got_info(bool multi_got)
    : global_gotno_(0), reloc_only_gotno_(0), local_gotno_(0),
      page_gotno_(0), tls_gotno_(0), tls_ldm_offset_(-1U),
      got_entries_(256, Mips_got_entry_hash<size, big_endian>(multi_got),
                        Mips_got_entry_eq<size, big_endian>(multi_got)),
      got_page_offset_start_(0), got_page_offset_next_(0),
      next_(NULL), index_(-1U), offset_(0)
  { }

  // Reserve space for a GOT entry containing the value of symbol
  // SYMNDX in input object OBJECT, plus ADDEND.
  void
  record_local_got_symbol(Sized_relobj_file<size, big_endian>* object,
                          unsigned int symndx,
                          typename elfcpp::Elf_types<size>::Elf_Addr addend,
                          unsigned char tls_flag,
                          unsigned int shndx);
  void
  record_global_got_symbol(Mips_symbol<size>* mips_sym,
                           Sized_relobj_file<size, big_endian>* object,
                           unsigned char tls_flag, bool reloc, bool for_call);
  void
  add_local_entries(Target_mips<size, big_endian> *target, Layout* layout);
  void
  add_page_entries(Target_mips<size, big_endian> *target, Layout* layout);
  void
  add_global_entries(Target_mips<size, big_endian> *target, Layout* layout,
                     unsigned int non_reloc_only_global_gotno);
  void
  add_reloc_only_entries(Mips_output_data_got<size, big_endian> *got);
  void
  add_tls_entries(Target_mips<size, big_endian> *target, Layout* layout);
  void
  lay_out_got(Target_mips<size, big_endian> *target, Layout* layout,
              Symbol_table* symtab);
  void
  count_global_got_symbols(Symbol_table* symtab);
  unsigned int
  get_got_page_offset(unsigned int value, unsigned char *got_view);

  // Record that OBJECT has a page relocation against symbol SYMNDX and
  // that ADDEND is the addend for that relocation.
  void
  record_got_page_entry(Sized_relobj_file<size, big_endian> *object,
                        unsigned int symndx, int addend);

  void
  lay_out_multi_got(Target_mips<size, big_endian> *target, Layout* layout);

  // Create one separate got for each object that has got entries, such that
  // we can tell how many local and global entries each object requires.
  void
  make_got_per_object(Got_entry_set &got_entries,
                      Object2got_entry_set &object2got);

  // Use OBJECT2GOT to find OBJECT's got entry, creating one if none exists.
  Mips_got_info<size, big_endian>*
  get_got_for_object(Object2got_entry_set &object2got, Object *object);

  Mips_got_info<size, big_endian>*
  get_got_info(const Object* object);

  // Traverse page entries in GOT_PAGE_ENTRIES and associate each page entry
  // with the object's got.
  void
  make_got_pages_per_object(Got_page_entry_set &got_page_entries,
                            Object2got_entry_set &object2got);

  // Attempt to merge gots of different input objects.
  void
  merge_gots(Object2got_entry_set &object2got);

  // Consider merging the got described by ENTRY with TO, using the
  // information given by ARG.  Returns false if this would lead to overflow,
  // true if they were merged successfully.
  bool
  merge_got_with(Object2got_entry<size, big_endian> *entry,
                  Mips_got_info<size, big_endian> *to,
                  Mips_got_info<size, big_endian> *primary);

  // The number of local .got entries, eventually including page entries.
  unsigned int
  local_gotno() const
  { return this->local_gotno_; }

  // The maximum number of page entries needed.
  unsigned int
  page_gotno() const
  { return this->page_gotno_; }

  Mips_got_info<size, big_endian>*
  next() const
  { return this->next_; }

  unsigned int
  index() const
  { return this->index_; }

  unsigned int
  offset() const
  { return this->offset_; }

  unsigned int
  tls_ldm_offset() const
  { return this->tls_ldm_offset_; }

  void
  set_tls_ldm_offset(unsigned int tls_ldm_offset)
  { this->tls_ldm_offset_ = tls_ldm_offset; }

  Unordered_set<Mips_symbol<size>*>&
  global_got_symbols()
  { return this->global_got_symbols_; }

private:
  // The number of global .got entries.
  unsigned int global_gotno_;
  // The number of global .got entries that are in the GGA_RELOC_ONLY area.
  unsigned int reloc_only_gotno_;
  // The number of local .got entries, eventually including page entries.
  unsigned int local_gotno_;
  // The maximum number of page entries needed.
  unsigned int page_gotno_;
  // The number of .got slots used for TLS.
  unsigned int tls_gotno_;

  // This is the GOT index of the TLS LDM entry for the GOT, -1
  // for none, or -2 for not yet assigned.  This is needed
  // because a single-GOT link may have multiple hash table entries
  // for the LDM.  It does not get initialized in multi-GOT mode.
  unsigned int tls_ldm_offset_;

  Unordered_set<Mips_symbol<size>*> global_got_symbols_;

  // A hash table holding got entries.
  Got_entry_set got_entries_;

  // A hash table of Got_page_entry structures.
  Got_page_entry_set got_page_entries_;

  unsigned int got_page_offset_start_;
  unsigned int got_page_offset_next_;

  Got_page_offsets got_page_offsets_;

  // A hash table mapping input objects to mips_got_info.  Used only for
  // multi-got links.
  Object2got_entry_set object2got;

  // In multi-got links, a pointer to the next got.
  Mips_got_info<size, big_endian> *next_;
  unsigned int index_;
  unsigned int offset_;
};

// This is a helper class used during relocation scan. It records GOT16 addend.

template<int size, bool big_endian>
struct got16_addend
{
  got16_addend(const Sized_relobj_file<size, big_endian>* _object,
               unsigned int _shndx, unsigned int _r_type, unsigned int _r_sym,
               typename elfcpp::Elf_types<size>::Elf_Addr _addend)
    : object(_object), shndx(_shndx), r_type(_r_type), r_sym(_r_sym),
      addend(_addend)
  { }

  const Sized_relobj_file<size, big_endian>* object;
  unsigned int shndx;
  unsigned int r_type;
  unsigned int r_sym;
  typename elfcpp::Elf_types<size>::Elf_Addr addend;
};

// Mips_symbol class.  Holds additional information needed for Mips.

template<int size>
class Mips_symbol : public Sized_symbol<size>
{
 public:
  Mips_symbol()
    : need_fn_stub_(false), has_nonpic_branches_(false), has_la25_stub_(false),
      la25_stub_offset_(0), has_static_relocs_(false), no_lazy_stub_(false),
      lazy_stub_offset_(0), pointer_equality_needed_(false),
      global_got_area_(GGA_NONE), tls_type_(GOT_NORMAL), global_gotoffset_(-1U),
      got_only_for_calls_(true), has_lazy_stub_(false)
  { }

  bool
  is_mips16() const
  { return (this->nonvis() & (elfcpp::STO_MIPS16 >> 2)) == elfcpp::STO_MIPS16 >> 2; }

  bool
  is_micromips() const
  { return (this->nonvis() & (elfcpp::STO_MIPS_ISA >> 2)) == elfcpp::STO_MICROMIPS >> 2; }

  // Return whether we need the fn_stub; this is true if this symbol appears
  // in any relocs other than a 16 bit call.
  bool
  need_fn_stub() const
  { return this->need_fn_stub_; }

  // Set whether we need the fn_stub.
  void
  set_need_fn_stub(bool value)
  { this->need_fn_stub_ = value; }

  bool
  has_nonpic_branches() const
  { return this->has_nonpic_branches_; }

  void
  set_has_nonpic_branches(bool value)
  { this->has_nonpic_branches_ = value; }

  bool
  has_la25_stub() const
  { return this->has_la25_stub_; }

  void
  set_has_la25_stub()
  { this->has_la25_stub_ = true; }

  unsigned int
  la25_stub_offset() const
  { return this->la25_stub_offset_; }

  void
  set_la25_stub_offset(unsigned int offset)
  { this->la25_stub_offset_ = offset; }

  bool
  has_static_relocs() const
  { return this->has_static_relocs_; }

  void
  set_has_static_relocs()
  { this->has_static_relocs_ = true; }

  bool
  no_lazy_stub() const
  { return this->no_lazy_stub_; }

  void
  set_no_lazy_stub()
  { this->no_lazy_stub_ = true; }

  unsigned int
  lazy_stub_offset() const
  { return this->lazy_stub_offset_; }

  void
  set_lazy_stub_offset(unsigned int offset)
  { this->lazy_stub_offset_ = offset; }

  bool
  pointer_equality_needed() const
  { return this->pointer_equality_needed_; }

  void
  set_pointer_equality_needed()
  { this->pointer_equality_needed_ = true; }

  Global_got_area
  global_got_area() const
  { return this->global_got_area_; }

  void
  set_global_got_area(Global_got_area global_got_area)
  { this->global_got_area_ = global_got_area; }

  bool
  has_tls() const
  { return this->tls_type_ != GOT_NORMAL; }

  void
  add_tls_type(unsigned char tls_flag)
  { this->tls_type_ |= tls_flag; }

  bool
  has_tls_type(unsigned char tls_flag) const
  { return this->tls_type_ & tls_flag; }

  unsigned int
  global_gotoffset() const
  { return this->global_gotoffset_; }

  void
  set_global_gotoffset(unsigned int offset)
  {
    if (this->global_gotoffset_ == -1U || offset < this->global_gotoffset_)
      this->global_gotoffset_ = offset;
  }

  bool
  got_only_for_calls() const
  { return this->got_only_for_calls_; }

  void
  set_got_only_for_calls(bool got_only_for_calls)
  { this->got_only_for_calls_ = got_only_for_calls; }

  bool
  is_pic() const
  { return (this->nonvis() & 0xF) == elfcpp::STO_MIPS_PIC >> 2; }

  void
  set_pic()
  { this->set_nonvis((this->nonvis() & ~0xF) | elfcpp::STO_MIPS_PIC >> 2); }

  // Downcast a base pointer to an Mips_symbol pointer.
  static Mips_symbol<size>*
  as_mips_sym(Symbol *sym)
  { return static_cast<Mips_symbol<size>*>(sym); }

  static const Mips_symbol<size>*
  as_mips_sym(const Symbol *sym)
  { return static_cast<const Mips_symbol<size>*>(sym); }

  bool
  has_lazy_stub() const
  { return this->has_lazy_stub_; }

  void
  set_has_lazy_stub(bool has_lazy_stub)
  { this->has_lazy_stub_ = has_lazy_stub; }

 private:
  unsigned char
  st_other() const
  { return (this->nonvis() << 2) | this->visibility(); }

  // Whether we need the fn_stub.
  bool need_fn_stub_ : 1;

  // True if this symbol is referenced by branch relocations from
  // any non-PIC input file.  This is used to determine whether an
  // la25 stub is required.
  bool has_nonpic_branches_ : 1;

  bool has_la25_stub_;

  // The offset of the la25 stub for this symbol from the start of its
  // la25 stab section.
  unsigned int la25_stub_offset_;

  // True if there is a relocation against this symbol that must be
  // resolved by the static linker (in other words, if the relocation
  // cannot possibly be made dynamic).
  bool has_static_relocs_;

  bool no_lazy_stub_;

  unsigned int lazy_stub_offset_;

  bool pointer_equality_needed_;

  Global_got_area global_got_area_;

  unsigned char tls_type_;
  unsigned int global_gotoffset_;
  bool got_only_for_calls_;

  // Whether the symbol has lazy-binding stub.
  bool has_lazy_stub_;
};

// This is a helper class that records relocation found in mips16 stub
// section, and the relocation symbol. It is used to find target symbol
// for mips16 stub.

struct mips16_stub_reloc
{
  mips16_stub_reloc(unsigned int r_type_, unsigned int r_sym_, Symbol* gsym_)
    : r_type(r_type_), r_sym(r_sym_), gsym(gsym_)
  { }

  // Return whether relocation refers to a local symbol.
  bool
  is_local() const
  { return this->gsym == NULL; }

  // Relocation type.
  unsigned int r_type;
  // The symbol index to which relocation refers.
  unsigned int r_sym;
  // The global symbol.
  Symbol* gsym;
};

// Mips16_stub_section class.

class Mips16_stub_section
{
 public:
  Mips16_stub_section(Object* object, unsigned int shndx)
    : object_(object), shndx_(shndx), r_sym_(0), gsym_(NULL),
      is_fn_stub_(false), is_call_stub_(false), is_call_fp_stub_(false)
  {
    const char *section_name = object->section_name(shndx).c_str();
    is_fn_stub_ = is_prefix_of(".mips16.fn", section_name);
    is_call_stub_ = is_prefix_of(".mips16.call.", section_name);
    is_call_fp_stub_ = is_prefix_of(".mips16.call.fp.", section_name);
  }

  Object*
  object() const
  { return this->object_; }

  // Return section index of this stub section.
  unsigned int
  shndx() const
  { return this->shndx_; }

  // Return symbol index, if stub is for a local function.
  unsigned int
  r_sym() const
  { return this->r_sym_; }

  // Return symbol, if stub is for a global function.
  Symbol*
  gsym() const
  { return this->gsym_; }

  // Return whether stub is for a local function.
  bool
  is_for_local_function() const
  { return this->gsym_ == NULL; }

  // Find target symbol for this stub.
  void
  find_target_from_relocs()
  {
    // Trust the first R_MIPS_NONE relocation, if any.
    std::list<mips16_stub_reloc*>::iterator it;
    mips16_stub_reloc* reloc = NULL;
    for (it = this->relocs_.begin(); it != this->relocs_.end(); ++it)
      {
        if ((*it)->r_type == elfcpp::R_MIPS_NONE)
          {
            reloc = *it;
            break;
          }
      }

    // Otherwise trust the first relocation, whatever its kind.
    if (reloc == NULL)
      {
        if (this->relocs_.size() > 0)
          reloc = *this->relocs_.begin();
        else
          gold_error(_("no relocation found in mips16 stub section '%s'"),
                     this->object_->section_name(this->shndx_).c_str());
      }

    if (reloc->is_local())
      this->r_sym_ = reloc->r_sym;
    else
      this->gsym_ = reloc->gsym;
  }

  void
  add_stub_reloc(mips16_stub_reloc* stub_reloc)
  { this->relocs_.push_back(stub_reloc); }

  bool
  is_fn_stub() const
  { return this->is_fn_stub_; }

  bool
  is_call_stub() const
  { return this->is_call_stub_; }

  bool
  is_call_fp_stub() const
  { return this->is_call_fp_stub_; }

  Output_section*
  output_section()
  { return this->object_->output_section(this->shndx_); }

  uint64_t
  output_section_offset()
  { return this->object_->output_section_offset(this->shndx_); }

 private:
  Object* object_;
  unsigned int shndx_;
  unsigned int r_sym_;
  Symbol* gsym_;
  std::list<mips16_stub_reloc*> relocs_;
  bool is_fn_stub_;
  bool is_call_stub_;
  bool is_call_fp_stub_;
};

// Mips_relobj class.

template<int size, bool big_endian>
class Mips_relobj : public Sized_relobj_file<size, big_endian>
{
 public:
  Mips_relobj(const std::string& name, Input_file* input_file, off_t offset,
             const typename elfcpp::Ehdr<size, big_endian>& ehdr)
    : Sized_relobj_file<size, big_endian>(name, input_file, offset, ehdr),
      processor_specific_flags_(0), gp_(0)
  {
    this->is_pic_ = (ehdr.get_e_flags() & elfcpp::EF_MIPS_PIC) != 0;
    this->is_n32_ = elfcpp::abi_n32(ehdr.get_e_flags());
    this->is_n64_ = elfcpp::abi_64(ehdr.get_e_ident()[elfcpp::EI_CLASS]);
  }

  ~Mips_relobj()
  { }

  // Downcast a base pointer to an Mips_relobj pointer.  This is
  // not type-safe but we only use Mips_relobj not the base class.
  static Mips_relobj<size, big_endian>*
  as_mips_relobj(Relobj* relobj)
  { return static_cast<Mips_relobj<size, big_endian>*>(relobj); }

  static const Mips_relobj<size, big_endian>*
  as_mips_relobj(const Relobj* relobj)
  { return static_cast<const Mips_relobj<size, big_endian>*>(relobj); }

  // Processor-specific flags in ELF file header.  This is valid only after
  // reading symbols.
  elfcpp::Elf_Word
  processor_specific_flags() const
  { return this->processor_specific_flags_; }

  // Whether a local symbol is MIPS16 symbol.  R_SYM is the symbol table
  // index.  This is only valid after do_count_local_symbol is called.
  bool
  local_symbol_is_mips16(unsigned int r_sym) const
  {
    gold_assert(r_sym < this->local_symbol_is_mips16_.size());
    return this->local_symbol_is_mips16_[r_sym];
  }

  // Whether a local symbol is microMIPS symbol.  R_SYM is the symbol table
  // index.  This is only valid after do_count_local_symbol is called.
  bool
  local_symbol_is_micromips(unsigned int r_sym) const
  {
    gold_assert(r_sym < this->local_symbol_is_micromips_.size());
    return this->local_symbol_is_micromips_[r_sym];
  }

  std::map<unsigned int, Mips16_stub_section*>&
  get_mips16_stub_sections()
  { return this->mips16_stub_sections_; }

  Mips16_stub_section*
  get_mips16_stub_section(unsigned int shndx) const
  {
    typename std::map<unsigned int, Mips16_stub_section*>::const_iterator it;
    it = this->mips16_stub_sections_.find(shndx);
    if (it != this->mips16_stub_sections_.end())
      return (*it).second;
    return NULL;
  }

  void
  add_mips16_stub_section(Mips16_stub_section* stub_section)
  {
    this->mips16_stub_sections_.insert(
      std::pair<unsigned int, Mips16_stub_section*>(
        stub_section->shndx(), stub_section));
  }

  Mips16_stub_section*
  get_local_mips16_fn_stub(unsigned int r_sym) const
  {
    typename std::map<unsigned int, Mips16_stub_section*>::const_iterator it;
    it = this->local_mips16_fn_stubs_.find(r_sym);
    if (it != this->local_mips16_fn_stubs_.end())
      return (*it).second;
    return NULL;
  }

  void
  set_local_mips16_fn_stub(Mips16_stub_section* stub)
  {
    gold_assert(stub->is_for_local_function());
    unsigned int r_sym = stub->r_sym();
    this->local_mips16_fn_stubs_.insert(
      std::pair<unsigned int, Mips16_stub_section*>(
        r_sym, stub));
  }

  Mips16_stub_section*
  get_local_mips16_call_stub(unsigned int r_sym) const
  {
    typename std::map<unsigned int, Mips16_stub_section*>::const_iterator it;
    it = this->local_mips16_call_stubs_.find(r_sym);
    if (it != this->local_mips16_call_stubs_.end())
      return (*it).second;
    return NULL;
  }

  void
  set_local_mips16_call_stub(Mips16_stub_section* stub)
  {
    gold_assert(stub->is_for_local_function());
    unsigned int r_sym = stub->r_sym();
    this->local_mips16_call_stubs_.insert(
      std::pair<unsigned int, Mips16_stub_section*>(
        r_sym, stub));
  }

  void
  add_local_non_16bit_call(unsigned int r_symindx)
  { this->local_non_16bit_calls_.insert(r_symindx); }

  bool
  has_local_non_16bit_call_relocs(unsigned int symndx)
  {
    return this->local_non_16bit_calls_.find(symndx) != this->local_non_16bit_calls_.end();
  }

  void
  add_local_16bit_call(unsigned int r_symindx)
  { this->local_16bit_calls_.insert(r_symindx); }

  bool
  has_local_16bit_call_relocs(unsigned int symndx)
  { return this->local_16bit_calls_.find(symndx) != this->local_16bit_calls_.end(); }

  // Get gp value that was used to create this object.
  typename elfcpp::Elf_types<size>::Elf_Addr
  gp_value() const
  { return this->gp_; }

  bool
  is_pic() const
  { return this->is_pic_; }

  bool
  is_n32() const
  { return this->is_n32_; }

  bool
  is_n64() const
  { return this->is_n64_; }

  // Whether the object is using NewABI conventions.
  bool
  is_newabi() const
  { return this->is_n32_ || this->is_n64_; }

 protected:
  // Count the local symbols.
  void
  do_count_local_symbols(Stringpool_template<char>*,
                         Stringpool_template<char>*);

  // Read the symbol information.
  void
  do_read_symbols(Read_symbols_data* sd);

 private:

  // processor-specific flags in ELF file header.
  elfcpp::Elf_Word processor_specific_flags_;

  // Bit vector to tell if a local symbol is a MIPS16 symbol or not.
  // This is only valid after do_count_local_symbol is called.
  std::vector<bool> local_symbol_is_mips16_;

  // Bit vector to tell if a local symbol is a microMIPS symbol or not.
  // This is only valid after do_count_local_symbol is called.
  std::vector<bool> local_symbol_is_micromips_;

  std::map<unsigned int, Mips16_stub_section*> mips16_stub_sections_;
  std::set<unsigned int> local_non_16bit_calls_;
  std::set<unsigned int> local_16bit_calls_;

  std::map<unsigned int, Mips16_stub_section*> local_mips16_fn_stubs_;
  std::map<unsigned int, Mips16_stub_section*> local_mips16_call_stubs_;

  typename elfcpp::Elf_types<size>::Elf_Addr gp_;

  // Whether the object is a PIC object.
  bool is_pic_;
  // Whether the object is using the N32 ABI.
  bool is_n32_;
  // Whether the object is using the N64 ABI.
  bool is_n64_;
};

// Mips_output_data_got class.

template<int size, bool big_endian>
class Mips_output_data_got : public Output_data_got<size, big_endian>
{
 public:
  typedef Output_data_reloc<elfcpp::SHT_REL, true, size, big_endian>
    Reloc_section;

  Mips_output_data_got(Target_mips<size, big_endian> *target, Symbol_table* symtab, Layout* layout)
    : Output_data_got<size, big_endian>(), target_(target), symbol_table_(symtab),
      layout_(layout), global_got_index_(0), multi_got_(false)
  {
    this->got_info = new Mips_got_info<size, big_endian>(false);
    this->set_addralign(16);
  }

  // Add a static entry for the GOT entry at OFFSET.  GSYM is a global
  // symbol and R_TYPE is the code of a dynamic relocation that needs to be
  // applied in a static link.
  void
  add_static_reloc(unsigned int got_offset, unsigned int r_type, Symbol* gsym)
  { this->static_relocs_.push_back(Static_reloc(got_offset, r_type, gsym)); }

  // Add a static reloc for the GOT entry at OFFSET.  RELOBJ is an object
  // defining a local symbol with INDEX.  R_TYPE is the code of a dynamic
  // relocation that needs to be applied in a static link.
  void
  add_static_reloc(unsigned int got_offset, unsigned int r_type,
                   Sized_relobj_file<size, big_endian>* relobj,
                   unsigned int index)
  {
    this->static_relocs_.push_back(Static_reloc(got_offset, r_type, relobj,
                                                index));
  }

  // Record that global symbol GSYM has R_TYPE dynamic relocation in the
  // secondary GOT at OFFSET.
  void
  add_secondary_got_reloc(unsigned int got_offset, unsigned int r_type, Symbol* gsym)
  { this->secondary_got_relocs_.push_back(Static_reloc(got_offset, r_type, gsym)); }

  unsigned char*
  got_view()
  {  return this->got_view_;  }

  Symbol_table*
  symbol_table()
  {  return this->symbol_table_;  }

  Layout*
  layout()
  {  return this->layout_;  }

  // Reserve space in G for a GOT entry containing the value of symbol
  // SYMNDX in input object OBJECT, plus ADDEND.
  void
  record_local_got_symbol(Sized_relobj_file<size, big_endian>* object,
                          long symndx,
                          typename elfcpp::Elf_types<size>::Elf_Addr addend,
                          unsigned char tls_flag,
                          unsigned int shndx)
  {
    this->got_info->record_local_got_symbol(object, symndx, addend, tls_flag, shndx);
  }

  void
  record_global_got_symbol(Mips_symbol<size>* mips_sym,
                           Sized_relobj_file<size, big_endian>* object,
                           unsigned char tls_flag, bool reloc, bool for_call)
  {
    this->got_info->record_global_got_symbol(mips_sym, object, tls_flag, reloc, for_call);
  }

  unsigned int
  local_gotno() const
  {
    if (!this->multi_got_)
      return this->got_info->local_gotno();
    else
      {
        Mips_got_info<size, big_endian> *primary = this->got_info->next();
        return 2 + primary->local_gotno() + primary->page_gotno();
      }
  }

  unsigned int
  global_got_index() const
  { return this->global_got_index_; }

  void
  set_global_got_index(unsigned int global_got_index)
  { this->global_got_index_ = global_got_index; }

  void
  lay_out_got(Target_mips<size, big_endian> *target, Layout* layout, Symbol_table *symtab)
  { this->got_info->lay_out_got(target, layout, symtab); }

  unsigned int
  get_got_page_offset(unsigned int value, const Sized_relobj_file<size, big_endian> *object)
  {
    if (!this->multi_got_)
      return this->got_info->get_got_page_offset(value, this->got_view());
    else
      {
        Mips_got_info<size, big_endian> *g = this->got_info->get_got_info(object);
        return g->get_got_page_offset(value, this->got_view());
      }
  }

  // Record that OBJECT has a page relocation against symbol SYMNDX and
  // that ADDEND is the addend for that relocation.
  void
  record_got_page_entry(Sized_relobj_file<size, big_endian> *object,
                        unsigned int symndx, int addend)
  { this->got_info->record_got_page_entry(object, symndx, addend); }

  unsigned int got_offset(const Symbol* gsym, unsigned int got_type,
                          Sized_relobj_file<size, big_endian>* object) const
  {
    if (!this->multi_got_)
      return gsym->got_offset(got_type);
    else
      {
        Mips_got_info<size, big_endian> *g = this->got_info->get_got_info(object);
        return gsym->got_offset(this->multigot_got_type(got_type) + g->index());
      }
  }

  unsigned int
  tls_ldm_offset(Object* object) const
  {
    if (!this->multi_got_)
      return this->got_info->tls_ldm_offset();
    else
      {
        Mips_got_info<size, big_endian> *g = this->got_info->get_got_info(object);
        return g->tls_ldm_offset();
      }
  }

  void
  set_tls_ldm_offset(unsigned int tls_ldm_offset, Object* object)
  {
    if (!this->multi_got_)
      this->got_info->set_tls_ldm_offset(tls_ldm_offset);
    else
      {
        Mips_got_info<size, big_endian> *g = this->got_info->get_got_info(object);
        g->set_tls_ldm_offset(tls_ldm_offset);
      }
  }

  unsigned int
  multigot_got_type(unsigned int got_type) const
  {
    switch (got_type)
      {
      case GOT_TYPE_STANDARD:
        return GOT_TYPE_STANDARD_MULTIGOT;
      case GOT_TYPE_TLS_OFFSET:
        return GOT_TYPE_TLS_OFFSET_MULTIGOT;
      case GOT_TYPE_TLS_PAIR:
        return GOT_TYPE_TLS_PAIR_MULTIGOT;
      default:
        gold_unreachable();
      }
  }

  // Return the GOT offset of type GOT_TYPE of the local symbol
  // SYMNDX.
  unsigned int
  got_offset(unsigned int symndx, unsigned int got_type,
             Sized_relobj_file<size, big_endian>* object) const
  { return object->local_got_offset(symndx, got_type); }

  bool
  multi_got() const
  { return this->multi_got_; }

  void
  set_multi_got()
  { this->multi_got_ = true; }

  unsigned int
  get_got_offset(const Sized_relobj_file<size, big_endian>* object)
  {
    if (!this->multi_got_)
      return 0;

    Mips_got_info<size, big_endian> *g = this->got_info->get_got_info(object);
    return g != NULL ? g->offset() : 0;
  }

  void
  add_reloc_only_entries()
  { this->got_info->add_reloc_only_entries(this); }

 protected:
  // Write out the GOT table.
  void
  do_write(Output_file*);

 private:

  // This class represent dynamic relocations that need to be applied by
  // gold because we are using TLS relocations in a static link.
  class Static_reloc
  {
   public:
    Static_reloc(unsigned int got_offset, unsigned int r_type, Symbol* gsym)
      : got_offset_(got_offset), r_type_(r_type), symbol_is_global_(true)
    { this->u_.global.symbol = gsym; }

    Static_reloc(unsigned int got_offset, unsigned int r_type,
          Sized_relobj_file<size, big_endian>* relobj, unsigned int index)
      : got_offset_(got_offset), r_type_(r_type), symbol_is_global_(false)
    {
      this->u_.local.relobj = relobj;
      this->u_.local.index = index;
    }

    // Return the GOT offset.
    unsigned int
    got_offset() const
    { return this->got_offset_; }

    // Relocation type.
    unsigned int
    r_type() const
    { return this->r_type_; }

    // Whether the symbol is global or not.
    bool
    symbol_is_global() const
    { return this->symbol_is_global_; }

    // For a relocation against a global symbol, the global symbol.
    Symbol*
    symbol() const
    {
      gold_assert(this->symbol_is_global_);
      return this->u_.global.symbol;
    }

    // For a relocation against a local symbol, the defining object.
    Sized_relobj_file<size, big_endian>*
    relobj() const
    {
      gold_assert(!this->symbol_is_global_);
      return this->u_.local.relobj;
    }

    // For a relocation against a local symbol, the local symbol index.
    unsigned int
    index() const
    {
      gold_assert(!this->symbol_is_global_);
      return this->u_.local.index;
    }

   private:
    // GOT offset of the entry to which this relocation is applied.
    unsigned int got_offset_;
    // Type of relocation.
    unsigned int r_type_;
    // Whether this relocation is against a global symbol.
    bool symbol_is_global_;
    // A global or local symbol.
    union
    {
      struct
      {
        // For a global symbol, the symbol itself.
        Symbol* symbol;
      } global;
      struct
      {
        // For a local symbol, the object defining object.
        Sized_relobj_file<size, big_endian>* relobj;
        // For a local symbol, the symbol index.
        unsigned int index;
      } local;
    } u_;
  };

  Target_mips<size, big_endian> *target_;

  // Symbol table of the output object.
  Symbol_table* symbol_table_;
  // Layout of the output object.
  Layout* layout_;

  // Static relocs to be applied to the GOT.
  std::vector<Static_reloc> static_relocs_;

  // .got section view
  unsigned char* got_view_;

  unsigned int global_got_index_;

  // The master GOT information.
  Mips_got_info<size, big_endian> *got_info;

  bool multi_got_;

  // Secondary GOT fixups.
  std::vector<Static_reloc> secondary_got_relocs_;
};

// A class to handle LA25 stubs - non-PIC interface to a PIC function. There are
// two ways of creating these interfaces.  The first is to add:
//
//      lui     $25,%hi(func)
//      j       func
//      addiu   $25,$25,%lo(func)
//
// to a separate trampoline section.  The second is to add:
//
//      lui     $25,%hi(func)
//      addiu   $25,$25,%lo(func)
//
// immediately before a PIC function "func", but only if a function is at the
// beginning of the section, and the section is not too heavily aligned (i.e we
// would need to add no more than 2 nops before the stub.)
//
// We only create stubs of the first type.

template<int size, bool big_endian>
class Mips_output_data_la25_stub : public Output_section_data
{
 public:
  Mips_output_data_la25_stub()
  : Output_section_data(size == 32 ? 4 : 8)
  { }

  // Add LA25 stub for a symbol.
  void
  add_la25_stub(Symbol_table* symtab, Target_mips<size, big_endian>* target,
                Symbol* gsym);

 protected:
  void
  do_adjust_output_section(Output_section* os)
  { os->set_entsize(0); }

 private:
  // Template for LA25 stub.
  static const uint32_t la25_stub_entry[4];

  // Set the final size.
  void
  set_final_data_size()
  { this->set_data_size(this->symbols_.size() * 16); }

  // Creates a symbol for the MIPS_SYM's stub's value and size, to help make
  // the disassembly easier to read.
  Symbol*
  create_stub_symbol(Mips_symbol<size>* mips_sym, Symbol_table* symtab,
                     Target_mips<size, big_endian>* target, uint64_t symsize);

  // Write out the LA25 stub section.
  void
  do_write(Output_file*);

  // Symbols that have stubs.
  Unordered_set<Symbol*> symbols_;
};

// A class to handle the PLT data.

template<int size, bool big_endian>
class Mips_output_data_plt : public Output_section_data
{
 public:
  typedef Output_data_reloc<elfcpp::SHT_REL, true,
                            size, big_endian> Reloc_section;

  Mips_output_data_plt(Layout*, Output_data_space*);

  // Add an entry to the PLT.
  void
  add_entry(Symbol* gsym);

  // Return the .rel.plt section data.
  const Reloc_section*
  rel_plt() const
  { return this->rel_; }

  // Return the number of PLT entries.
  unsigned int
  entry_count() const
  { return this->count_; }

  // Return the offset of the first non-reserved PLT entry.
  static unsigned int
  first_plt_entry_offset()
  { return sizeof(plt0_entry_o32); }

  // Return the size of a PLT entry.
  static unsigned int
  plt_entry_size()
  { return sizeof(plt_entry); }

 protected:
  void
  do_adjust_output_section(Output_section* os);

  // Write to a map file.
  void
  do_print_to_mapfile(Mapfile* mapfile) const
  { mapfile->print_output_data(this, _(".plt")); }

 private:
  // Template for the first PLT entry.
  static const uint32_t plt0_entry_o32[8];
  static const uint32_t plt0_entry_n32[8];
  static const uint32_t plt0_entry_n64[8];

  // Template for subsequent PLT entries.
  static const uint32_t plt_entry[4];

  // Set the final size.
  void
  set_final_data_size()
  {
    unsigned int full_count = this->count_ * 4 + 8;

    this->set_data_size(full_count * 4);
  }

  // Write out the PLT data.
  void
  do_write(Output_file*);

  // The reloc section.
  Reloc_section* rel_;
  // The .got.plt section.
  Output_data_space* got_plt_;
  // The number of PLT entries.
  unsigned int count_;
};

// A class to handle the .MIPS.stubs data.

template<int size, bool big_endian>
class Mips_output_data_mips_stubs : public Output_section_data
{
 public:
   Mips_output_data_mips_stubs()
     : Output_section_data(size == 32 ? 4 : 8), dynsym_count_(-1U),
       stub_offsets_are_set_(false)
   { }

  // Add an entry to the .MIPS.stubs.
  void
  add_entry(Symbol* gsym);

  // Remove entry for a symbol.
  void
  remove_entry(Symbol *sym);

  void
  set_lazy_stub_offsets();

  void
  set_needs_dynsym_value();

  void
  set_dynsym_count(unsigned int dynsym_count)
  { this->dynsym_count_ = dynsym_count; }

 protected:
  void
  do_adjust_output_section(Output_section* os);

  // Write to a map file.
  void
  do_print_to_mapfile(Mapfile* mapfile) const
  { mapfile->print_output_data(this, _(".MIPS.stubs")); }

 private:
  static const uint32_t lazy_stub_normal_1[4];
  static const uint32_t lazy_stub_normal_1_n64[4];
  static const uint32_t lazy_stub_normal_2[4];
  static const uint32_t lazy_stub_normal_2_n64[4];
  static const uint32_t lazy_stub_big[5];
  static const uint32_t lazy_stub_big_n64[5];

  // Set the final size.
  void
  set_final_data_size()
  { this->set_data_size(this->symbols_.size() * 20); }

  // Write out the .MIPS.stubs data.
  void
  do_write(Output_file*);

  // .MIPS.stubs symbols
  Unordered_set<Symbol*> symbols_;
  unsigned int dynsym_count_;
  bool stub_offsets_are_set_;
};

// This class handles Mips .reginfo output section.

template<int size, bool big_endian>
class Mips_output_section_reginfo : public Output_section
{
 public:
  Mips_output_section_reginfo (const char *name, elfcpp::Elf_Word type,
                               elfcpp::Elf_Xword flags,
                               Target_mips<size, big_endian>* target)
    : Output_section(name, type, flags), target_(target)
  {
    this->set_always_keeps_input_sections();
  }

  ~Mips_output_section_reginfo()
  { };

  // Downcast a base pointer to an Mips_output_section_reginfo pointer.
  static Mips_output_section_reginfo<size, big_endian>*
  as_mips_output_section_reginfo(Output_section* os)
  { return static_cast<Mips_output_section_reginfo<size, big_endian>*>(os); }

 protected:
  // Set the final data size.
  void
  set_final_data_size()
  { this->set_data_size(24); }

  // Write out reginfo section.
  void
  do_write(Output_file * of);

 private:
  Target_mips<size, big_endian>* target_;
};

// The MIPS target has relocation types which default handling of relocatable
// relocation cannot process.  So we have to extend the default code.

template<bool big_endian, int sh_type, typename Classify_reloc>
class Mips_scan_relocatable_relocs :
  public Default_scan_relocatable_relocs<sh_type, Classify_reloc>
{
 public:
  // Return the strategy to use for a local symbol which is a section
  // symbol, given the relocation type.
  inline Relocatable_relocs::Reloc_strategy
  local_section_strategy(unsigned int r_type, Relobj *object)
  {
    if (sh_type == elfcpp::SHT_RELA)
      return Relocatable_relocs::RELOC_ADJUST_FOR_SECTION_RELA;
    else
      {
        switch (r_type)
          {
          case elfcpp::R_MIPS_26:
            return Relocatable_relocs::RELOC_SPECIAL;

          default:
            return Default_scan_relocatable_relocs<sh_type, Classify_reloc>::
                local_section_strategy(r_type, object);
          }
      }
  }
};

// Mips_copy_relocs class. This class is almost identical to the class
// Copy_relocs from copy-relocs.h. The only difference is method
// Copy_reloc_entry::emit.

// This class is used to manage COPY relocations.  We try to avoid
// them when possible.  A COPY relocation may be required when an
// executable refers to a variable defined in a shared library.  COPY
// relocations are problematic because they tie the executable to the
// exact size of the variable in the shared library.  We can avoid
// them if all the references to the variable are in a writeable
// section.  In that case we can simply use dynamic relocations.
// However, when scanning relocs, we don't know when we see the
// relocation whether we will be forced to use a COPY relocation or
// not.  So we have to save the relocation during the reloc scanning,
// and then emit it as a dynamic relocation if necessary.  This class
// implements that.  It is used by the target specific code.

// The template parameter SH_TYPE is the type of the reloc section to
// be used for COPY relocs: elfcpp::SHT_REL or elfcpp::SHT_RELA.

template<int sh_type, int size, bool big_endian>
class Mips_copy_relocs
{
 private:
  typedef typename Reloc_types<sh_type, size, big_endian>::Reloc Reloc;

 public:
  Mips_copy_relocs(unsigned int copy_reloc_type)
    : copy_reloc_type_(copy_reloc_type), dynbss_(NULL), entries_()
  { }

  // This is called while scanning relocs if we see a relocation
  // against a symbol which may force us to generate a COPY reloc.
  // SYM is the symbol.  OBJECT is the object whose relocs we are
  // scanning.  The relocation is being applied to section SHNDX in
  // OBJECT.  OUTPUT_SECTION is the output section where section SHNDX
  // will wind up.  REL is the reloc itself.  The Output_data_reloc
  // section is where the dynamic relocs are put.
  void
  copy_reloc(Symbol_table*, Layout*, Sized_symbol<size>* sym,
             Sized_relobj_file<size, big_endian>* object,
             unsigned int shndx, Output_section* output_section,
             const Reloc& rel,
             Output_data_reloc<sh_type, true, size, big_endian>*);

  // Return whether there are any saved relocations.
  bool
  any_saved_relocs() const
  { return !this->entries_.empty(); }

  // Emit any saved relocations which turn out to be needed.  This is
  // called after all the relocs have been scanned.
  void
  emit(Output_data_reloc<sh_type, true, size, big_endian>*,
       Symbol_table*, Layout*, Target_mips<size, big_endian>*);

  // Emit a COPY reloc.
  void
  emit_copy_reloc(Symbol_table*, Sized_symbol<size>*,
                  Output_data*, off_t,
                  Output_data_reloc<sh_type, true, size, big_endian>*);

 private:
  typedef typename elfcpp::Elf_types<size>::Elf_Addr Address;
  typedef typename elfcpp::Elf_types<size>::Elf_Addr Addend;

  // This POD class holds the relocations we are saving.  We will emit
  // these relocations if it turns out that the symbol does not
  // require a COPY relocation.
  class Copy_reloc_entry
  {
   public:
    Copy_reloc_entry(Symbol* sym, unsigned int reloc_type,
                     Sized_relobj_file<size, big_endian>* relobj,
                     unsigned int shndx,
                     Output_section* output_section,
                     Address address, Addend addend)
      : sym_(sym), reloc_type_(reloc_type), relobj_(relobj),
        shndx_(shndx), output_section_(output_section),
        address_(address), addend_(addend)
    { }

    // Emit this reloc if appropriate.  This is called after we have
    // scanned all the relocations, so we know whether we emitted a
    // COPY relocation for SYM_.
    void
    emit(Output_data_reloc<sh_type, true, size, big_endian>*,
         Mips_copy_relocs<sh_type, size, big_endian>* copy_relocs, Symbol_table*,
         Layout*, Target_mips<size, big_endian>*);

   private:
    Symbol* sym_;
    unsigned int reloc_type_;
    Sized_relobj_file<size, big_endian>* relobj_;
    unsigned int shndx_;
    Output_section* output_section_;
    Address address_;
    Addend addend_;
  };

  // A list of relocs to be saved.
  typedef std::vector<Copy_reloc_entry> Copy_reloc_entries;

  // Return whether we need a COPY reloc.
  bool
  need_copy_reloc(Sized_symbol<size>* gsym,
                  Sized_relobj_file<size, big_endian>* object,
                  unsigned int shndx) const;

  // Make a new COPY reloc and emit it.
  void
  make_copy_reloc(Symbol_table*, Layout*, Sized_symbol<size>*,
                  Output_data_reloc<sh_type, true, size, big_endian>*);

  // Save a reloc against SYM for possible emission later.
  void
  save(Symbol*, Sized_relobj_file<size, big_endian>*, unsigned int shndx,
       Output_section*, const Reloc& rel);

  // The target specific relocation type of the COPY relocation.
  const unsigned int copy_reloc_type_;
  // The dynamic BSS data which goes into the .bss section.  This is
  // where variables which require COPY relocations are placed.
  Output_data_space* dynbss_;
  // The list of relocs we are saving.
  Copy_reloc_entries entries_;
};


// Return true if the symbol SYM should be considered to resolve local
// to the current module, and false otherwise. The logic is taken from
// _bfd_elf_symbol_refs_local_p.
bool
symbol_refs_local(const Symbol *sym, bool has_dynsym_entry, bool local_protected)
{
  // If it's a local sym, of course we resolve locally.
  if (sym == NULL)
    return true;

  // STV_HIDDEN or STV_INTERNAL ones must be local.
  if (sym->visibility() == elfcpp::STV_HIDDEN
      || sym->visibility() == elfcpp::STV_INTERNAL)
    return true;

  // If we don't have a definition in a regular file, then we can't
  // resolve locally.  The sym is either undefined or dynamic.
  if (sym->source() != Symbol::FROM_OBJECT || sym->object()->is_dynamic() || sym->is_undefined())
    return false;

  // Forced local symbols resolve locally.
  if (sym->is_forced_local())
    return true;

  // As do non-dynamic symbols.
  if (!has_dynsym_entry)
    return true;

  // At this point, we know the symbol is defined and dynamic.  In an
  // executable it must resolve locally, likewise when building symbolic
  // shared libraries.
  if (parameters->options().output_is_executable() || parameters->options().Bsymbolic())
    return true;

  // Now deal with defined dynamic symbols in shared libraries.  Ones
  // with default visibility might not resolve locally.
  if (sym->visibility() == elfcpp::STV_DEFAULT)
    return false;

  // STV_PROTECTED non-function symbols are local.
  if (sym->type() != elfcpp::STT_FUNC)
    return true;

  // Function pointer equality tests may require that STV_PROTECTED
  // symbols be treated as dynamic symbols.  If the address of a
  // function not defined in an executable is set to that function's
  // plt entry in the executable, then the address of the function in
  // a shared library must also be the plt entry in the executable.
  return local_protected;
}

// Will references to this symbol always reference the symbol in this object?
bool symbol_references_local(const Symbol *sym, bool has_dynsym_entry)
{
  return symbol_refs_local(sym, has_dynsym_entry, false);
}

// Will _calls_ to this symbol always call the version in this object?
bool symbol_calls_local(const Symbol *sym, bool has_dynsym_entry)
{
  return symbol_refs_local(sym, has_dynsym_entry, true);
}

// Compare got offsets of two symbols.

template<int size, bool big_endian>
bool
got_offset_compare(Symbol *sym1, Symbol *sym2)
{
  Mips_symbol<size>* mips_sym1 = Mips_symbol<size>::as_mips_sym(sym1);
  Mips_symbol<size>* mips_sym2 = Mips_symbol<size>::as_mips_sym(sym2);
  unsigned int area1 = mips_sym1->global_got_area();
  unsigned int area2 = mips_sym2->global_got_area();
  gold_assert(area1 != GGA_NONE && area1 != GGA_NONE);

  // GGA_NORMAL entries always come before GGA_RELOC_ONLY.
  if (area1 != area2)
    return area1 < area2;

  return mips_sym1->global_gotoffset() < mips_sym2->global_gotoffset();
}

// Functor class for processing the global symbol table.

template<int size, bool big_endian>
class Symbol_visitor_check_symbols
{
 public:
  Symbol_visitor_check_symbols(Target_mips<size, big_endian>* target,
    Layout* layout, Symbol_table* symtab)
    : target_(target), layout_(layout), symtab_(symtab)
  { }

  void
  operator()(Sized_symbol<size>* sym)
  {
    Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(sym);
    if (target_->local_pic_function(mips_sym))
      {
        // SYM is a function that might need $25 to be valid on entry.
        // If we're creating a non-PIC relocatable object, mark SYM as
        // being PIC.  If we're creating a non-relocatable object with
        // non-PIC branches and jumps to SYM, make sure that SYM has an la25
        // stub.
        if (parameters->options().relocatable())
          {
            if (!parameters->options().output_is_position_independent())
              mips_sym->set_pic();
          }
        else if (mips_sym->has_nonpic_branches())
          {
            target_->create_la25_stub_section(layout_);
            target_->la25_stub_section()->add_la25_stub(symtab_, target_, mips_sym);
          }
      }
  }

 private:
  Target_mips<size, big_endian>* target_;
  Layout* layout_;
  Symbol_table* symtab_;
};

template<int size, bool big_endian>
class Target_mips : public Sized_target<size, big_endian>
{
 public:
  typedef Output_data_reloc<elfcpp::SHT_REL, true, size, big_endian>
    Reloc_section;
  typedef Output_data_reloc<elfcpp::SHT_RELA, true, size, big_endian>
    Reloca_section;
  typedef Unordered_map<const char*, Symbol*> Stub_symbol_info;

  Target_mips(const Target::Target_info* info = &mips_info)
    : Sized_target<size, big_endian>(info),
      got_(NULL), gp_(NULL), plt_(NULL), got_plt_(NULL),
      rel_dyn_(NULL), rela_dyn_(NULL), copy_relocs_(elfcpp::R_MIPS_COPY),
      copy_relocsa_(elfcpp::R_MIPS_COPY), la25_stub_(NULL), mips_stubs_(NULL),
      ei_class_(0), mach_(0), layout_(NULL)
  {
    this->add_machine_extensions();
  }

  // The offset of $gp from the beginning of the .got section.
  static const unsigned int MIPS_GP_OFFSET = 0x7ff0;

  // The maximum size of the GOT for it to be addressable using 16-bit
  // offsets from $gp.
  static const unsigned int MIPS_GOT_MAX_SIZE = MIPS_GP_OFFSET + 0x7fff;

  // Make a new symbol table entry for the Mips target.
  Sized_symbol<size>*
  make_symbol() const
  { return new Mips_symbol<size>(); }

  // Process the relocations to determine unreferenced sections for
  // garbage collection.
  void
  gc_process_relocs(Symbol_table* symtab,
                    Layout* layout,
                    Sized_relobj_file<size, big_endian>* object,
                    unsigned int data_shndx,
                    unsigned int sh_type,
                    const unsigned char* prelocs,
                    size_t reloc_count,
                    Output_section* output_section,
                    bool needs_special_offset_handling,
                    size_t local_symbol_count,
                    const unsigned char* plocal_symbols);

  // Scan the relocations to look for symbol adjustments.
  void
  scan_relocs(Symbol_table* symtab,
              Layout* layout,
              Sized_relobj_file<size, big_endian>* object,
              unsigned int data_shndx,
              unsigned int sh_type,
              const unsigned char* prelocs,
              size_t reloc_count,
              Output_section* output_section,
              bool needs_special_offset_handling,
              size_t local_symbol_count,
              const unsigned char* plocal_symbols);

  // Finalize the sections.
  void
  do_finalize_sections(Layout *, const Input_objects *, Symbol_table *);

  // Relocate a section.
  void
  relocate_section(const Relocate_info<size, big_endian>*,
                   unsigned int sh_type,
                   const unsigned char* prelocs,
                   size_t reloc_count,
                   Output_section* output_section,
                   bool needs_special_offset_handling,
                   unsigned char* view,
                   typename elfcpp::Elf_types<size>::Elf_Addr view_address,
                   section_size_type view_size,
                   const Reloc_symbol_changes*);

  // Scan the relocs during a relocatable link.
  void
  scan_relocatable_relocs(Symbol_table* symtab,
                          Layout* layout,
                          Sized_relobj_file<size, big_endian>* object,
                          unsigned int data_shndx,
                          unsigned int sh_type,
                          const unsigned char* prelocs,
                          size_t reloc_count,
                          Output_section* output_section,
                          bool needs_special_offset_handling,
                          size_t local_symbol_count,
                          const unsigned char* plocal_symbols,
                          Relocatable_relocs*);

  // Relocate a section during a relocatable link.
  void
  relocate_for_relocatable(const Relocate_info<size, big_endian>*,
                           unsigned int sh_type,
                           const unsigned char* prelocs,
                           size_t reloc_count,
                           Output_section* output_section,
                           typename elfcpp::Elf_types<32>::Elf_Off offset_in_output_section,
                           const Relocatable_relocs*,
                           unsigned char* view,
                           typename elfcpp::Elf_types<size>::Elf_Addr view_address,
                           section_size_type view_size,
                           unsigned char* reloc_view,
                           section_size_type reloc_view_size);

  // Perform target-specific processing in a relocatable link.  This is
  // only used if we use the relocation strategy RELOC_SPECIAL.
  void
  relocate_special_relocatable(const Relocate_info<size, big_endian>* relinfo,
                               unsigned int sh_type,
                               const unsigned char* preloc_in,
                               size_t relnum,
                               Output_section* output_section,
                               off_t offset_in_output_section,
                               unsigned char* view,
                               typename elfcpp::Elf_types<32>::Elf_Addr
                                 view_address,
                               section_size_type view_size,
                               unsigned char* preloc_out);

  // Return whether SYM is defined by the ABI.
  bool
  do_is_defined_by_abi(const Symbol* sym) const
  {
    return ((strcmp(sym->name(), "__gnu_local_gp") == 0)
      || (strcmp(sym->name(), "_gp_disp") == 0)
      || (strcmp(sym->name(), "___tls_get_addr") == 0));
  }

  // Return the number of entries in the GOT.
  unsigned int
  got_entry_count() const
  {
    if (!this->has_got_section())
      return 0;
    return this->got_size() / 4;
  }

  // Return the number of entries in the PLT.
  unsigned int
  plt_entry_count() const
  {
    if (this->plt_ == NULL)
      return 0;
    return this->plt_->entry_count();
  }

  // Return the offset of the first non-reserved PLT entry.
  unsigned int
  first_plt_entry_offset() const
  { return Mips_output_data_plt<size, big_endian>::first_plt_entry_offset(); }

  // Return the size of each PLT entry.
  unsigned int
  plt_entry_size() const
  { return Mips_output_data_plt<size, big_endian>::plt_entry_size(); }

  // Returns la25 stub section.
  Mips_output_data_la25_stub<size, big_endian>*
  la25_stub_section()
  { return this->la25_stub_; }

  // Return .MIPS.stubs output section.
  Mips_output_data_mips_stubs<size, big_endian>*
  mips_stubs() const
  { return this->mips_stubs_; }

  // Return TRUE if a relocation of type R_TYPE from MIPS_RELOBJ might
  // require an la25 stub.  See also local_pic_function, which determines
  // whether the destination function ever requires a stub.
  bool
  relocation_needs_la25_stub(Mips_relobj<size, big_endian>* mips_relobj,
                              unsigned int r_type, bool target_is_16_bit_code)
  {
    // We specifically ignore branches and jumps from EF_PIC objects,
    // where the onus is on the compiler or programmer to perform any
    // necessary initialization of $25.  Sometimes such initialization
    // is unnecessary; for example, -mno-shared functions do not use
    // the incoming value of $25, and may therefore be called directly.
    if (mips_relobj->is_pic())
      return false;

    switch (r_type)
      {
      case elfcpp::R_MIPS_26:
      case elfcpp::R_MIPS_PC16:
      case elfcpp::R_MICROMIPS_26_S1:
      case elfcpp::R_MICROMIPS_PC7_S1:
      case elfcpp::R_MICROMIPS_PC10_S1:
      case elfcpp::R_MICROMIPS_PC16_S1:
      case elfcpp::R_MICROMIPS_PC23_S2:
        return true;

      case elfcpp::R_MIPS16_26:
        return !target_is_16_bit_code;

      default:
        return false;
      }
  }

  // Return true if SYM is a locally-defined PIC function, in the sense
  // that it or its fn_stub might need $25 to be valid on entry.
  // Note that MIPS16 functions set up $gp using PC-relative instructions,
  // so they themselves never need $25 to be valid.  Only non-MIPS16
  // entry points are of interest here.
  bool
  local_pic_function(Mips_symbol<size>* sym)
  {
    bool def_regular = sym->source() == Symbol::FROM_OBJECT
      && !sym->object()->is_dynamic() && !sym->is_undefined();

    if (sym->is_defined() && def_regular)
      {
        Mips_relobj<size, big_endian>* mips_relobj =
          static_cast<Mips_relobj<size, big_endian>*>(sym->object());

        if ((mips_relobj->is_pic() || sym->is_pic())
            && (!sym->is_mips16()
             || (this->get_mips16_fn_stub(sym) != NULL && sym->need_fn_stub())))
          return true;
      }
    return false;
  }

  // Create LA25 stub section.
  void
  create_la25_stub_section(Layout*);

  // Get the GOT section, creating it if necessary.
  Mips_output_data_got<size, big_endian>*
  got_section(Symbol_table*, Layout*);

  // Get the GOT section.
  Mips_output_data_got<size, big_endian>*
  got_section() const
  {
    gold_assert(this->got_ != NULL);
    return this->got_;
  }

  // Get value of gp.
  const typename elfcpp::Elf_types<size>::Elf_Addr
  gp_value() const
  {
    if (this->gp_ != NULL)
      return this->gp_->value();
    return 0;
  }

  // Get value of gp. Adjust it for multi-got links.
  typename elfcpp::Elf_types<size>::Elf_Addr
  adjusted_gp_value(const Sized_relobj_file<size, big_endian>* object)
  {
    if (this->gp_ == NULL)
      return 0;

    bool multi_got = false;
    if (this->has_got_section())
      multi_got = this->got_section()->multi_got();
    if (!multi_got)
      return this->gp_->value();
    else
      return this->gp_->value() + this->got_section()->get_got_offset(object);
  }

  // Get the dynamic reloc section, creating it if necessary.
  Reloc_section*
  rel_dyn_section(Layout*);

  Reloca_section*
  rela_dyn_section(Layout*);

  static inline bool
  hi16_reloc(int r_type)
  {
    return (r_type == elfcpp::R_MIPS_HI16
         || r_type == elfcpp::R_MIPS16_HI16
         || r_type == elfcpp::R_MICROMIPS_HI16);
  }

  static inline bool
  lo16_reloc(int r_type)
  {
    return (r_type == elfcpp::R_MIPS_LO16
         || r_type == elfcpp::R_MIPS16_LO16
         || r_type == elfcpp::R_MICROMIPS_LO16);
  }

  static inline bool
  got16_reloc(unsigned int r_type)
  {
    return (r_type == elfcpp::R_MIPS_GOT16
         || r_type == elfcpp::R_MIPS16_GOT16
         || r_type == elfcpp::R_MICROMIPS_GOT16);
  }

  static inline bool
  call_lo16_reloc(unsigned int r_type)
  {
    return r_type == elfcpp::R_MIPS_CALL_LO16
        || r_type == elfcpp::R_MICROMIPS_CALL_LO16;
  }

  static inline bool
  got_lo16_reloc(unsigned int r_type)
  {
    return r_type == elfcpp::R_MIPS_GOT_LO16
        || r_type == elfcpp::R_MICROMIPS_GOT_LO16;
  }

  static inline bool
  got_disp_reloc(unsigned int r_type)
  {
    return r_type == elfcpp::R_MIPS_GOT_DISP
        || r_type == elfcpp::R_MICROMIPS_GOT_DISP;
  }

  static inline bool
  got_page_reloc(unsigned int r_type)
  {
    return r_type == elfcpp::R_MIPS_GOT_PAGE
        || r_type == elfcpp::R_MICROMIPS_GOT_PAGE;
  }

  static inline bool
  tls_gd_reloc(unsigned int r_type)
  {
    return (r_type == elfcpp::R_MIPS_TLS_GD
         || r_type == elfcpp::R_MIPS16_TLS_GD
         || r_type == elfcpp::R_MICROMIPS_TLS_GD);
  }

  static inline bool
  tls_gottprel_reloc(unsigned int r_type)
  {
    return (r_type == elfcpp::R_MIPS_TLS_GOTTPREL
         || r_type == elfcpp::R_MIPS16_TLS_GOTTPREL
         || r_type == elfcpp::R_MICROMIPS_TLS_GOTTPREL);
  }

  static inline bool
  mips16_call_reloc(unsigned int r_type)
  {
    return r_type == elfcpp::R_MIPS16_26 || r_type == elfcpp::R_MIPS16_CALL16;
  }

  // Return TRUE if relocations in section SECTION_NAME can refer directly to a
  // MIPS16 function rather than to a hard-float stub.
  static bool
  section_allows_mips16_refs(const char *section_name)
  {
    return (is_prefix_of(".mips16.fn", section_name)
        || is_prefix_of(".mips16.call", section_name)
        || is_prefix_of(".mips16.call.fp", section_name)
        || strcmp (section_name, ".pdr") == 0);
  }

  bool
  custom_set_dynsym_indexes() const
  { return true; }

  void
  reorder_dyn_symbols(std::vector<Symbol*>* dyn_symbols,
                      std::vector<Symbol*>* symbols1,
                      std::vector<Symbol*>* symbols2) const
  {
    // Mips ABI requires that symbols that have .got entry be at the end of
    // dynamic symbol table, and that order matches order in .got.
    for (std::vector<Symbol *>::iterator p = dyn_symbols->begin();
         p != dyn_symbols->end();
         ++p)
      {
        Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(*p);
        if (mips_sym->global_got_area() == GGA_NORMAL
            || mips_sym->global_got_area() == GGA_RELOC_ONLY)
          symbols2->push_back(mips_sym);
        else
          symbols1->push_back(mips_sym);
      }

    std::sort(symbols2->begin(), symbols2->end(), got_offset_compare<size, big_endian>);
  }

  // Set the dynamic symbol indexes.  INDEX is the index of the first
  // global dynamic symbol.  Pointers to the symbols are stored into the
  // vector SYMS.  The names are added to DYNPOOL.  This returns an
  // updated dynamic symbol index.

  unsigned int
  set_dynsym_indexes(std::vector<Symbol*>* dyn_symbols, unsigned int index,
                     std::vector<Symbol*>* syms, Stringpool* dynpool,
                     Versions* versions, Symbol_table* symtab) const
  {
    std::vector<Symbol *> symbols1;
    std::vector<Symbol *> symbols2;

    reorder_dyn_symbols(dyn_symbols, &symbols1, &symbols2);

    for (std::vector<Symbol *>::iterator p = symbols1.begin();
         p != symbols1.end();
         ++p)
      {
        Symbol* sym = *p;

        // Note that SYM may already have a dynamic symbol index, since
        // some symbols appear more than once in the symbol table, with
        // and without a version.

        if (!sym->has_dynsym_index())
          {
            sym->set_dynsym_index(index);
            ++index;
            syms->push_back(sym);
            dynpool->add(sym->name(), false, NULL);

            // Record any version information.
            if (sym->version() != NULL)
              versions->record_version(symtab, dynpool, sym);

            // If the symbol is defined in a dynamic object and is
            // referenced in a regular object, then mark the dynamic
            // object as needed.  This is used to implement --as-needed.
            if (sym->is_from_dynobj() && sym->in_reg())
              sym->object()->set_is_needed();
          }
      }

    for (std::vector<Symbol *>::iterator p = symbols2.begin();
         p != symbols2.end();
         ++p)
      {
        Symbol* sym = *p;
        if (!sym->has_dynsym_index())
          {
            // Record any version information.
            if (sym->version() != NULL)
              versions->record_version(symtab, dynpool, sym);
          }
      }

    index = versions->finalize(symtab, index, syms);

    int external_count = 0;
    for (std::vector<Symbol *>::iterator p = symbols2.begin();
         p != symbols2.end();
         ++p)
      {
        Symbol* sym = *p;

        if (!sym->has_dynsym_index())
        {
          ++external_count;
          sym->set_dynsym_index(index);
          ++index;
          syms->push_back(sym);
          dynpool->add(sym->name(), false, NULL);

          // If the symbol is defined in a dynamic object and is
          // referenced in a regular object, then mark the dynamic
          // object as needed.  This is used to implement --as-needed.
          if (sym->is_from_dynobj() && sym->in_reg())
            sym->object()->set_is_needed();
        }
      }

    // Set index of the first external symbol that has .got entry.
    this->got_->set_global_got_index(index - external_count);

    if (this->mips_stubs_ != NULL)
      this->mips_stubs_->set_dynsym_count(index);

    // If there are no global symbols with .got entry set value to -1.
    //if (this->global_got_index_ == index)
      //this->global_got_index_ = -1U;

    return index;
  }

  // Remove symbol that should not have lazy stub.
  void
  remove_lazy_stub_entry(Symbol *sym)
  {
    if (this->mips_stubs_ != NULL)
      this->mips_stubs_->remove_entry(sym);
  }

  // The value to write into got[1] for SVR4 targets, to identify it is
  // a GNU object.  The dynamic linker can then use got[1] to store the
  // module pointer.
  uint64_t
  mips_elf_gnu_got1_mask()
  {
    if (elfcpp::abi_64(this->ei_class_))
      return (uint64_t)1 << 63;
    else
      return 1 << 31;
  }

  const char*
  entry_symbol_name() const
  { return "__start"; }

protected:
  // Return the value to use for a dynamic symbol which requires special
  // treatment.  This is how we support equality comparisons of function
  // pointers across shared library boundaries, as described in the
  // processor specific ABI supplement.
  uint64_t
  do_dynsym_value(const Symbol* gsym) const;

  // Make an ELF object.
  Object*
  do_make_elf_object(const std::string&, Input_file*, off_t,
                     const elfcpp::Ehdr<size, big_endian>& ehdr);

  Object*
  do_make_elf_object(const std::string&, Input_file*, off_t,
                     const elfcpp::Ehdr<size, !big_endian>&)
  { gold_unreachable(); }

  // Make an output section.
  Output_section*
  do_make_output_section(const char *name, elfcpp::Elf_Word type,
                          elfcpp::Elf_Xword flags)
    {
      if (type == elfcpp::SHT_MIPS_REGINFO)
        return new Mips_output_section_reginfo<size, big_endian>(name, type, flags, this);
      else
        return new Output_section(name, type, flags);
    }

  void
  do_adjust_elf_header(unsigned char* view, int len) const;

  // Get the custom dynamic tag value.
  unsigned int
  dynamic_tag_custom_value(elfcpp::DT) const;

private:
  // The class which scans relocations.
  class Scan
  {
  public:
    Scan()
    { }

    static inline int
    get_reference_flags(unsigned int r_type);

    inline void
    local(Symbol_table* symtab, Layout* layout, Target_mips* target,
          Sized_relobj_file<size, big_endian>* object,
          unsigned int data_shndx,
          Output_section* output_section,
          const elfcpp::Rel<size, big_endian>& reloc, unsigned int r_type,
          const elfcpp::Sym<size, big_endian>& lsym);

    inline void
    local(Symbol_table* symtab, Layout* layout, Target_mips* target,
          Sized_relobj_file<size, big_endian>* object,
          unsigned int data_shndx,
          Output_section* output_section,
          const elfcpp::Rela<size, big_endian>& reloc, unsigned int r_type,
          const elfcpp::Sym<size, big_endian>& lsym);

    inline void
    local(Symbol_table* symtab, Layout* layout, Target_mips* target,
          Sized_relobj_file<size, big_endian>* object,
          unsigned int data_shndx,
          Output_section* output_section,
          const elfcpp::Rela<size, big_endian>* rela,
          const elfcpp::Rel<size, big_endian>* rel,
          unsigned int rel_type,
          unsigned int r_type,
          const elfcpp::Sym<size, big_endian>& lsym);

    inline void
    global(Symbol_table* symtab, Layout* layout, Target_mips* target,
           Sized_relobj_file<size, big_endian>* object,
           unsigned int data_shndx,
           Output_section* output_section,
           const elfcpp::Rel<size, big_endian>& reloc, unsigned int r_type,
           Symbol* gsym);

    inline void
    global(Symbol_table* symtab, Layout* layout, Target_mips* target,
           Sized_relobj_file<size, big_endian>* object,
           unsigned int data_shndx,
           Output_section* output_section,
           const elfcpp::Rela<size, big_endian>& reloc, unsigned int r_type,
           Symbol* gsym);

    inline void
    global(Symbol_table* symtab, Layout* layout, Target_mips* target,
           Sized_relobj_file<size, big_endian>* object,
           unsigned int data_shndx,
           Output_section* output_section,
           const elfcpp::Rela<size, big_endian>* rela,
           const elfcpp::Rel<size, big_endian>* rel,
           unsigned int rel_type,
           unsigned int r_type,
           Symbol* gsym);

    inline bool
    local_reloc_may_be_function_pointer(Symbol_table* , Layout* ,
                                        Target_mips* ,
                                        Sized_relobj_file<size, big_endian>* ,
                                        unsigned int ,
                                        Output_section* ,
                                        const elfcpp::Rel<size, big_endian>& ,
                                        unsigned int ,
                                        const elfcpp::Sym<size, big_endian>&)
    { return false; }

    inline bool
    global_reloc_may_be_function_pointer(Symbol_table* , Layout* ,
                                         Target_mips* ,
                                         Sized_relobj_file<size, big_endian>* ,
                                         unsigned int ,
                                         Output_section* ,
                                         const elfcpp::Rel<size, big_endian>& ,
                                         unsigned int , Symbol*)
    { return false; }

    inline bool
    local_reloc_may_be_function_pointer(Symbol_table* , Layout* ,
                                        Target_mips* ,
                                        Sized_relobj_file<size, big_endian>* ,
                                        unsigned int ,
                                        Output_section* ,
                                        const elfcpp::Rela<size, big_endian>& ,
                                        unsigned int ,
                                        const elfcpp::Sym<size, big_endian>&)
    { return false; }

    inline bool
    global_reloc_may_be_function_pointer(Symbol_table* , Layout* ,
                                         Target_mips* ,
                                         Sized_relobj_file<size, big_endian>* ,
                                         unsigned int ,
                                         Output_section* ,
                                         const elfcpp::Rela<size, big_endian>& ,
                                         unsigned int , Symbol*)
    { return false; }
  private:
    static void
    unsupported_reloc_local(Sized_relobj_file<size, big_endian>*,
                            unsigned int r_type);

    static void
    unsupported_reloc_global(Sized_relobj_file<size, big_endian>*,
                             unsigned int r_type, Symbol*);
  };

  // The class which implements relocation.
  class Relocate
  {
   public:
    Relocate()
    { }

    ~Relocate()
    { }

    // Return whether the R_MIPS_32 relocation needs to be applied.
    inline bool
    should_apply_r_mips_32_reloc(const Mips_symbol<size>* gsym,
                                 unsigned int r_type,
                                 Output_section* output_section, Target_mips* target);

    // Do a relocation.  Return false if the caller should not issue
    // any warnings about this relocation.
    inline bool
    relocate(const Relocate_info<size, big_endian>*, Target_mips*,
             Output_section*, size_t relnum,
             const elfcpp::Rela<size, big_endian>*,
             const elfcpp::Rel<size, big_endian>*,
             unsigned int,
             unsigned int,  const Sized_symbol<size>*,
             const Symbol_value<size>*,
             unsigned char*,
             typename elfcpp::Elf_types<size>::Elf_Addr,
             section_size_type);

    inline bool
    relocate(const Relocate_info<size, big_endian>*, Target_mips*,
             Output_section*, size_t relnum,
             const elfcpp::Rel<size, big_endian>&,
             unsigned int, const Sized_symbol<size>*,
             const Symbol_value<size>*,
             unsigned char*,
             typename elfcpp::Elf_types<size>::Elf_Addr,
             section_size_type);

    inline bool
    relocate(const Relocate_info<size, big_endian>*, Target_mips*,
             Output_section*, size_t relnum,
             const elfcpp::Rela<size, big_endian>&,
             unsigned int, const Sized_symbol<size>*,
             const Symbol_value<size>*,
             unsigned char*,
             typename elfcpp::Elf_types<size>::Elf_Addr,
             section_size_type);
  };

  // A class which returns the size required for a relocation type,
  // used while scanning relocs during a relocatable link.
  class Relocatable_size_for_reloc
  {
   public:
    unsigned int
    get_size_for_reloc(unsigned int, Relobj*);
  };

  // This POD class holds the dynamic relocations that should be emitted instead
  // of R_MIPS_32, R_MIPS_REL32 and R_MIPS_64 relocations.  We will emit these
  // relocations if it turns out that the symbol does not have static
  // relocations.
  class Dyn_reloc
  {
   public:
    Dyn_reloc(Mips_symbol<size>* sym, unsigned int r_type,
              Sized_relobj_file<size, big_endian>* relobj,
              unsigned int shndx,
              Output_section* output_section,
              typename elfcpp::Elf_types<size>::Elf_Addr r_offset)
      : sym_(sym), r_type_(r_type), relobj_(relobj),
        shndx_(shndx), output_section_(output_section),
        r_offset_(r_offset)
    { }

    // Emit this reloc if appropriate.  This is called after we have
    // scanned all the relocations, so we know whether the symbol has
    // static relocations.
    void
    emit(Reloc_section* rel_dyn, Mips_output_data_got<size, big_endian>* got, Symbol_table *symtab)
    {
      if (!this->sym_->has_static_relocs())
        {
          got->record_global_got_symbol(this->sym_, this->relobj_, 0, true, false);
          if (!symbol_references_local (this->sym_, should_add_dynsym_entry(this->sym_, symtab)))
            rel_dyn->add_global(this->sym_, this->r_type_, this->output_section_, this->relobj_,
                                this->shndx_, this->r_offset_);
          else
            rel_dyn->add_symbolless_global_addend(this->sym_, this->r_type_, this->output_section_, this->relobj_,
                                this->shndx_, this->r_offset_);
        }
    }

   private:
    Mips_symbol<size>* sym_;
    unsigned int r_type_;
    Sized_relobj_file<size, big_endian>* relobj_;
    unsigned int shndx_;
    Output_section* output_section_;
    typename elfcpp::Elf_types<size>::Elf_Addr r_offset_;
  };

  // Adjust TLS relocation type based on the options and whether this
  // is a local symbol.
  static tls::Tls_optimization
  optimize_tls_reloc(bool is_final, int r_type);

  // Return whether there is a GOT section.
  bool
  has_got_section() const
  { return this->got_ != NULL; }

  // Check whether the given ELF header flags describe a 32-bit binary.
  bool
  mips_32bit_flags(elfcpp::Elf_Word);

  enum Mips_mach {
    mach_mips3000             = 3000,
    mach_mips3900             = 3900,
    mach_mips4000             = 4000,
    mach_mips4010             = 4010,
    mach_mips4100             = 4100,
    mach_mips4111             = 4111,
    mach_mips4120             = 4120,
    mach_mips4300             = 4300,
    mach_mips4400             = 4400,
    mach_mips4600             = 4600,
    mach_mips4650             = 4650,
    mach_mips5000             = 5000,
    mach_mips5400             = 5400,
    mach_mips5500             = 5500,
    mach_mips6000             = 6000,
    mach_mips7000             = 7000,
    mach_mips8000             = 8000,
    mach_mips9000             = 9000,
    mach_mips10000            = 10000,
    mach_mips12000            = 12000,
    mach_mips14000            = 14000,
    mach_mips16000            = 16000,
    mach_mips16               = 16,
    mach_mips5                = 5,
    mach_mips_loongson_2e     = 3001,
    mach_mips_loongson_2f     = 3002,
    mach_mips_loongson_3a     = 3003,
    mach_mips_sb1             = 12310201, /* octal 'SB', 01 */
    mach_mips_octeon          = 6501,
    mach_mips_octeonp         = 6601,
    mach_mips_octeon2         = 6502,
    mach_mips_xlr             = 887682,   /* decimal 'XLR'  */
    mach_mipsisa32            = 32,
    mach_mipsisa32r2          = 33,
    mach_mipsisa64            = 64,
    mach_mipsisa64r2          = 65,
    mach_mips_micromips       = 96
  };

  // Return the MACH for a MIPS e_flags value.
  unsigned int
  elf_mips_mach(elfcpp::Elf_Word);

  // Check whether machine EXTENSION is an extension of machine BASE.
  bool
  mips_mach_extends(unsigned int, unsigned int);

  // Merge processor specific flags.
  void
  merge_processor_specific_flags(const std::string&, elfcpp::Elf_Word, unsigned char, bool);

  // True if we are linking for CPUs that are faster if JAL is converted to BAL.
  bool
  jal_to_bal() const
  { return false; }

  // True if we are linking for CPUs that are faster if JALR is converted to BAL.
  // This should be safe for all architectures.  We enable this predicate for
  // all CPUs.
  bool
  jalr_to_bal() const
  { return true; }

  // True if we are linking for CPUs that are faster if JR is converted to B.
  // This should be safe for all architectures.  We enable this predicate for
  // all CPUs.
  bool
  jr_to_b() const
  { return true; }

  // Return the size of the GOT section.
  section_size_type
  got_size() const
  {
    gold_assert(this->got_ != NULL);
    return this->got_->data_size();
  }

  // Create a PLT entry for a global symbol.
  void
  make_plt_entry(Symbol_table*, Layout*, Symbol*);

  // Create a .MIPS.stubs entry for a global symbol.
  void
  make_lazy_stub_entry(Layout*, Symbol*);

  // Get the PLT section.
  const Mips_output_data_plt<size, big_endian>*
  plt_section() const
  {
    gold_assert(this->plt_ != NULL);
    return this->plt_;
  }

  // Get the GOT PLT section.
  const Mips_output_data_plt<size, big_endian>*
  got_plt_section() const
  {
    gold_assert(this->got_plt_ != NULL);
    return this->got_plt_;
  }

  // Copy a relocation against a global symbol.
  void
  copy_reloc(Symbol_table* symtab, Layout* layout,
             Sized_relobj_file<size, big_endian>* object,
             unsigned int shndx, Output_section* output_section,
             Symbol* sym, const elfcpp::Rel<size, big_endian>& reloc)
  {
    this->copy_relocs_.copy_reloc(symtab, layout,
                                  symtab->get_sized_symbol<size>(sym),
                                  object, shndx, output_section,
                                  reloc, this->rel_dyn_section(layout));
  }

  // Copy a relocation against a global symbol.
  void
  copy_reloc(Symbol_table* symtab, Layout* layout,
             Sized_relobj_file<size, big_endian>* object,
             unsigned int shndx, Output_section* output_section,
             Symbol* sym, const elfcpp::Rela<size, big_endian>& reloc)
  {
    this->copy_relocsa_.copy_reloc(symtab, layout,
                                   symtab->get_sized_symbol<size>(sym),
                                   object, shndx, output_section,
                                   reloc, this->rela_dyn_section(layout));
  }

  void
  dynamic_reloc(Mips_symbol<size>* sym, unsigned int r_type,
                Sized_relobj_file<size, big_endian>* relobj,
                unsigned int shndx,
                Output_section* output_section,
                typename elfcpp::Elf_types<size>::Elf_Addr r_offset)
  {
    this->dyn_relocs_.push_back(Dyn_reloc(sym, r_type, relobj, shndx,
                                          output_section, r_offset));
  }

  // Calculate value of _gp symbol.
  void
  set_gp(Layout*, Symbol_table*);

  const char*
  elf_mips_abi_name(elfcpp::Elf_Word e_flags, unsigned char ei_class);
  const char*
  elf_mips_mach_name (elfcpp::Elf_Word e_flags);

  // Adds entries that describe how machines relate to one another.  The entries
  // are ordered topologically with MIPS I extensions listed last.  First element
  // is extension, second element is base.
  void
  add_machine_extensions()
  {
    // MIPS64r2 extensions.
    this->add_extension(mach_mips_octeon2, mach_mips_octeonp);
    this->add_extension(mach_mips_octeonp, mach_mips_octeon);
    this->add_extension(mach_mips_octeon, mach_mipsisa64r2);

    // MIPS64 extensions.
    this->add_extension(mach_mipsisa64r2, mach_mipsisa64);
    this->add_extension(mach_mips_sb1, mach_mipsisa64);
    this->add_extension(mach_mips_xlr, mach_mipsisa64);
    this->add_extension(mach_mips_loongson_3a, mach_mipsisa64);

    // MIPS V extensions.
    this->add_extension(mach_mipsisa64, mach_mips5);

    // R10000 extensions.
    this->add_extension(mach_mips12000, mach_mips10000);
    this->add_extension(mach_mips14000, mach_mips10000);
    this->add_extension(mach_mips16000, mach_mips10000);

    // R5000 extensions.  Note: the vr5500 ISA is an extension of the core
    // vr5400 ISA, but doesn't include the multimedia stuff.  It seems
    // better to allow vr5400 and vr5500 code to be merged anyway, since
    // many libraries will just use the core ISA.  Perhaps we could add
    // some sort of ASE flag if this ever proves a problem.
    this->add_extension(mach_mips5500, mach_mips5400);
    this->add_extension(mach_mips5400, mach_mips5000);

    // MIPS IV extensions.
    this->add_extension(mach_mips5, mach_mips8000);
    this->add_extension(mach_mips10000, mach_mips8000);
    this->add_extension(mach_mips5000, mach_mips8000);
    this->add_extension(mach_mips7000, mach_mips8000);
    this->add_extension(mach_mips9000, mach_mips8000);

    // VR4100 extensions.
    this->add_extension(mach_mips4120, mach_mips4100);
    this->add_extension(mach_mips4111, mach_mips4100);

    // MIPS III extensions.
    this->add_extension(mach_mips_loongson_2e, mach_mips4000);
    this->add_extension(mach_mips_loongson_2f, mach_mips4000);
    this->add_extension(mach_mips8000, mach_mips4000);
    this->add_extension(mach_mips4650, mach_mips4000);
    this->add_extension(mach_mips4600, mach_mips4000);
    this->add_extension(mach_mips4400, mach_mips4000);
    this->add_extension(mach_mips4300, mach_mips4000);
    this->add_extension(mach_mips4100, mach_mips4000);
    this->add_extension(mach_mips4010, mach_mips4000);

    // MIPS32 extensions.
    this->add_extension(mach_mipsisa32r2, mach_mipsisa32);

    // MIPS II extensions.
    this->add_extension(mach_mips4000, mach_mips6000);
    this->add_extension(mach_mipsisa32, mach_mips6000);

    // MIPS I extensions.
    this->add_extension(mach_mips6000, mach_mips3000);
    this->add_extension(mach_mips3900, mach_mips3000);
  }

  // Add value to MIPS extenstions.
  void
  add_extension(unsigned int base, unsigned int extension)
  {
    std::pair<unsigned int, unsigned int> ext(base, extension);
    this->mips_mach_extensions_.push_back(ext);
  }

  // Return mips16 fn stub section for SYM, or NULL if there isn't any.
  Mips16_stub_section*
  get_mips16_fn_stub(const Symbol* sym) const
  {
    typename Mips16_stubs_map::const_iterator it = this->mips16_fn_stubs_.find(sym);
    if (it != this->mips16_fn_stubs_.end())
      return it->second;
    return NULL;
  }

  // Set mips16 fn stub section for symbol SYM.
  bool
  add_mips16_fn_stub(const Symbol *sym, Mips16_stub_section *stub)
  {
    std::pair<typename Mips16_stubs_map::iterator, bool> result =
      this->mips16_fn_stubs_.insert(
        std::pair<const Symbol*, Mips16_stub_section*>(sym, stub));
    return result.second;
  }

  // Return mips16 call stub section for SYM, or NULL if there isn't any.
  Mips16_stub_section*
  get_mips16_call_stub(const Symbol* sym) const
  {
    typename Mips16_stubs_map::const_iterator it = this->mips16_call_stubs_.find(sym);
    if (it != this->mips16_call_stubs_.end())
      return it->second;
    return NULL;
  }

  // Set mips16 call stub section for symbol SYM.
  bool
  add_mips16_call_stub(const Symbol *sym, Mips16_stub_section *stub)
  {
    std::pair<typename Mips16_stubs_map::iterator, bool> result =
      this->mips16_call_stubs_.insert(
        std::pair<const Symbol*, Mips16_stub_section*>(sym, stub));
    return result.second;
  }

  // Return mips16 call.fp stub section for SYM, or NULL if there isn't any.
  Mips16_stub_section*
  get_mips16_call_fp_stub(const Symbol* sym) const
  {
    typename Mips16_stubs_map::const_iterator it = this->mips16_call_fp_stubs_.find(sym);
    if (it != this->mips16_call_fp_stubs_.end())
      return it->second;
    return NULL;
  }

  // Set mips16 call.fp stub section for symbol SYM.
  bool
  add_mips16_call_fp_stub(const Symbol *sym, Mips16_stub_section *stub)
  {
    std::pair<typename Mips16_stubs_map::iterator, bool> result =
      this->mips16_call_fp_stubs_.insert(
        std::pair<const Symbol*, Mips16_stub_section*>(sym, stub));
    return result.second;
  }

  // Information about this specific target which we pass to the
  // general Target structure.
  static Target::Target_info mips_info;
  // The GOT section.
  Mips_output_data_got<size, big_endian>* got_;
  // gp symbol
  Sized_symbol<size>* gp_;
  // The PLT section.
  Mips_output_data_plt<size, big_endian>* plt_;
  // The GOT PLT section.
  Output_data_space* got_plt_;
  // The dynamic reloc section.
  Reloc_section* rel_dyn_;
  Reloca_section* rela_dyn_;
  // Relocs saved to avoid a COPY reloc.
  Mips_copy_relocs<elfcpp::SHT_REL, size, big_endian> copy_relocs_;
  Mips_copy_relocs<elfcpp::SHT_RELA, size, big_endian> copy_relocsa_;

  // A list of dyn relocs to be saved.
  std::vector<Dyn_reloc> dyn_relocs_;

  // The LA25 stub section.
  Mips_output_data_la25_stub<size, big_endian>* la25_stub_;
  // Architecture extensions.
  std::vector<std::pair<unsigned int, unsigned int> > mips_mach_extensions_;
  // .MIPS.stubs
  Mips_output_data_mips_stubs<size, big_endian>* mips_stubs_;

  unsigned char ei_class_;
  unsigned int mach_;
  Layout* layout_;

  typedef Unordered_map<const Symbol*, Mips16_stub_section*> Mips16_stubs_map;

  typename std::list<got16_addend<size, big_endian> > got16_addends;

  // Map of mips16 fn stubs for global 16bit functions. 32 bit functions
  // should use this stubs to call 16 bit functions.
  Mips16_stubs_map mips16_fn_stubs_;

  Mips16_stubs_map mips16_call_stubs_;
  Mips16_stubs_map mips16_call_fp_stubs_;
};


// Mips_copy_relocs::Copy_reloc_entry methods.

// Emit the reloc if appropriate.

template<int sh_type, int size, bool big_endian>
void
Mips_copy_relocs<sh_type, size, big_endian>::Copy_reloc_entry::emit(
    Output_data_reloc<sh_type, true, size, big_endian>* reloc_section,
    Mips_copy_relocs<sh_type, size, big_endian>* copy_relocs,
    Symbol_table* symtab, Layout* layout, Target_mips<size, big_endian> *target)
{
  // If the symbol is no longer defined in a dynamic object, then we
  // emitted a COPY relocation, and we do not want to emit this
  // dynamic relocation.
  if (!this->sym_->is_from_dynobj())
    return;

  bool can_make_dynamic = this->reloc_type_ == elfcpp::R_MIPS_32
                       || this->reloc_type_ == elfcpp::R_MIPS_REL32
                       || this->reloc_type_ == elfcpp::R_MIPS_64;

  Mips_symbol<size>* sym = Mips_symbol<size>::as_mips_sym(this->sym_);
  if (can_make_dynamic && !sym->has_static_relocs())
    {
      target->got_section(symtab, layout)->record_global_got_symbol(sym, this->relobj_, 0, true, false);
      if (!symbol_references_local (sym, should_add_dynsym_entry(sym, symtab)))
        target->rel_dyn_section(layout)->add_global(sym, elfcpp::R_MIPS_REL32,
            this->output_section_, this->relobj_, this->shndx_, this->address_);
      else
        target->rel_dyn_section(layout)->add_symbolless_global_addend(
            sym, elfcpp::R_MIPS_REL32, this->output_section_, this->relobj_,
            this->shndx_, this->address_);
    }
  else
    copy_relocs->make_copy_reloc(symtab, layout,
        static_cast<Sized_symbol<size>*>(this->sym_), reloc_section);
}

// Mips_copy_relocs methods.

// Handle a relocation against a symbol which may force us to generate
// a COPY reloc.

template<int sh_type, int size, bool big_endian>
void
Mips_copy_relocs<sh_type, size, big_endian>::copy_reloc(
    Symbol_table* symtab,
    Layout* layout,
    Sized_symbol<size>* sym,
    Sized_relobj_file<size, big_endian>* object,
    unsigned int shndx,
    Output_section* output_section,
    const Reloc& rel,
    Output_data_reloc<sh_type, true, size, big_endian>* reloc_section)
{
  if (this->need_copy_reloc(sym, object, shndx))
    this->make_copy_reloc(symtab, layout, sym, reloc_section);
  else
    {
      // We may not need a COPY relocation.  Save this relocation to
      // possibly be emitted later.
      this->save(sym, object, shndx, output_section, rel);
    }
}

// Return whether we need a COPY reloc for a relocation against SYM.
// The relocation is begin applied to section SHNDX in OBJECT.

template<int sh_type, int size, bool big_endian>
bool
Mips_copy_relocs<sh_type, size, big_endian>::need_copy_reloc(
    Sized_symbol<size>* sym,
    Sized_relobj_file<size, big_endian>* object,
    unsigned int shndx) const
{
  if (!parameters->options().copyreloc())
    return false;

  if (sym->symsize() == 0)
    return false;

  // If this is a readonly section, then we need a COPY reloc.
  // Otherwise we can use a dynamic reloc.  Note that calling
  // section_flags here can be slow, as the information is not cached;
  // fortunately we shouldn't see too many potential COPY relocs.
  if ((object->section_flags(shndx) & elfcpp::SHF_WRITE) == 0)
    return true;

  return false;
}

// Emit a COPY relocation for SYM.

template<int sh_type, int size, bool big_endian>
void
Mips_copy_relocs<sh_type, size, big_endian>::emit_copy_reloc(
    Symbol_table* symtab,
    Sized_symbol<size>* sym,
    Output_data* posd,
    off_t offset,
    Output_data_reloc<sh_type, true, size, big_endian>* reloc_section)
{
  // Define the symbol as being copied.
  symtab->define_with_copy_reloc(sym, posd, offset);

  // Add the COPY relocation to the dynamic reloc section.
  reloc_section->add_global_generic(sym, this->copy_reloc_type_, posd,
                                    offset, 0);
}

// Make a COPY relocation for SYM and emit it.

template<int sh_type, int size, bool big_endian>
void
Mips_copy_relocs<sh_type, size, big_endian>::make_copy_reloc(
    Symbol_table* symtab,
    Layout* layout,
    Sized_symbol<size>* sym,
    Output_data_reloc<sh_type, true, size, big_endian>* reloc_section)
{
  // We should not be here if -z nocopyreloc is given.
  gold_assert(parameters->options().copyreloc());

  typename elfcpp::Elf_types<size>::Elf_WXword symsize = sym->symsize();

  // There is no defined way to determine the required alignment of
  // the symbol.  We know that the symbol is defined in a dynamic
  // object.  We start with the alignment of the section in which it
  // is defined; presumably we do not require an alignment larger than
  // that.  Then we reduce that alignment if the symbol is not aligned
  // within the section.
  gold_assert(sym->is_from_dynobj());
  bool is_ordinary;
  unsigned int shndx = sym->shndx(&is_ordinary);
  gold_assert(is_ordinary);
  typename elfcpp::Elf_types<size>::Elf_WXword addralign;

  {
    // Lock the object so we can read from it.  This is only called
    // single-threaded from scan_relocs, so it is OK to lock.
    // Unfortunately we have no way to pass in a Task token.
    const Task* dummy_task = reinterpret_cast<const Task*>(-1);
    Object* obj = sym->object();
    Task_lock_obj<Object> tl(dummy_task, obj);
    addralign = obj->section_addralign(shndx);
  }

  typename Sized_symbol<size>::Value_type value = sym->value();
  while ((value & (addralign - 1)) != 0)
    addralign >>= 1;

  // Mark the dynamic object as needed for the --as-needed option.
  sym->object()->set_is_needed();

  if (this->dynbss_ == NULL)
    {
      this->dynbss_ = new Output_data_space(addralign, "** dynbss");
      layout->add_output_section_data(".bss",
                                      elfcpp::SHT_NOBITS,
                                      elfcpp::SHF_ALLOC | elfcpp::SHF_WRITE,
                                      this->dynbss_, ORDER_BSS, false);
    }

  Output_data_space* dynbss = this->dynbss_;

  if (addralign > dynbss->addralign())
    dynbss->set_space_alignment(addralign);

  section_size_type dynbss_size =
    convert_to_section_size_type(dynbss->current_data_size());
  dynbss_size = align_address(dynbss_size, addralign);
  section_size_type offset = dynbss_size;
  dynbss->set_current_data_size(dynbss_size + symsize);

  this->emit_copy_reloc(symtab, sym, dynbss, offset, reloc_section);
}

// Save a relocation to possibly be emitted later.

template<int sh_type, int size, bool big_endian>
void
Mips_copy_relocs<sh_type, size, big_endian>::save(
    Symbol* sym,
    Sized_relobj_file<size, big_endian>* object,
    unsigned int shndx,
    Output_section* output_section,
    const Reloc& rel)
{
  unsigned int reloc_type = elfcpp::elf_r_type<size>(rel.get_r_info());
  typename elfcpp::Elf_types<size>::Elf_Addr addend =
    Reloc_types<sh_type, size, big_endian>::get_reloc_addend_noerror(&rel);
  this->entries_.push_back(Copy_reloc_entry(sym, reloc_type, object, shndx,
                                            output_section, rel.get_r_offset(),
                                            addend));
}

// Emit any saved relocs.

template<int sh_type, int size, bool big_endian>
void
Mips_copy_relocs<sh_type, size, big_endian>::emit(
    Output_data_reloc<sh_type, true, size, big_endian>* reloc_section,
    Symbol_table* symtab, Layout* layout, Target_mips<size, big_endian> *target)
{
  for (typename Copy_reloc_entries::iterator p = this->entries_.begin();
       p != this->entries_.end();
       ++p)
    p->emit(reloc_section, this, symtab, layout, target);

  // We no longer need the saved information.
  this->entries_.clear();
}

// Instantiate the templates we need.

#ifdef HAVE_TARGET_32_LITTLE
template
class Mips_copy_relocs<elfcpp::SHT_REL, 32, false>;

template
class Mips_copy_relocs<elfcpp::SHT_RELA, 32, false>;
#endif

#ifdef HAVE_TARGET_32_BIG
template
class Mips_copy_relocs<elfcpp::SHT_REL, 32, true>;

template
class Mips_copy_relocs<elfcpp::SHT_RELA, 32, true>;
#endif

#ifdef HAVE_TARGET_64_LITTLE
template
class Mips_copy_relocs<elfcpp::SHT_REL, 64, false>;

template
class Mips_copy_relocs<elfcpp::SHT_RELA, 64, false>;
#endif

#ifdef HAVE_TARGET_64_BIG
template
class Mips_copy_relocs<elfcpp::SHT_REL, 64, true>;

template
class Mips_copy_relocs<elfcpp::SHT_RELA, 64, true>;
#endif


//   R_MIPS16_26 is used for the mips16 jal and jalx instructions.
//   Most mips16 instructions are 16 bits, but these instructions
//   are 32 bits.
//
//   The format of these instructions is:
//
//   +--------------+--------------------------------+
//   |     JALX     | X|   Imm 20:16  |   Imm 25:21  |
//   +--------------+--------------------------------+
//   |                Immediate  15:0                |
//   +-----------------------------------------------+
//
//   JALX is the 5-bit value 00011.  X is 0 for jal, 1 for jalx.
//   Note that the immediate value in the first word is swapped.
//
//   When producing a relocatable object file, R_MIPS16_26 is
//   handled mostly like R_MIPS_26.  In particular, the addend is
//   stored as a straight 26-bit value in a 32-bit instruction.
//   (gas makes life simpler for itself by never adjusting a
//   R_MIPS16_26 reloc to be against a section, so the addend is
//   always zero).  However, the 32 bit instruction is stored as 2
//   16-bit values, rather than a single 32-bit value.  In a
//   big-endian file, the result is the same; in a little-endian
//   file, the two 16-bit halves of the 32 bit value are swapped.
//   This is so that a disassembler can recognize the jal
//   instruction.
//
//   When doing a final link, R_MIPS16_26 is treated as a 32 bit
//   instruction stored as two 16-bit values.  The addend A is the
//   contents of the targ26 field.  The calculation is the same as
//   R_MIPS_26.  When storing the calculated value, reorder the
//   immediate value as shown above, and don't forget to store the
//   value as two 16-bit values.
//
//   To put it in MIPS ABI terms, the relocation field is T-targ26-16,
//   defined as
//
//   big-endian:
//   +--------+----------------------+
//   |        |                      |
//   |        |    targ26-16         |
//   |31    26|25                   0|
//   +--------+----------------------+
//
//   little-endian:
//   +----------+------+-------------+
//   |          |      |             |
//   |  sub1    |      |     sub2    |
//   |0        9|10  15|16         31|
//   +----------+--------------------+
//   where targ26-16 is sub1 followed by sub2 (i.e., the addend field A is
//   ((sub1 << 16) | sub2)).
//
//   When producing a relocatable object file, the calculation is
//   (((A < 2) | ((P + 4) & 0xf0000000) + S) >> 2)
//   When producing a fully linked file, the calculation is
//   let R = (((A < 2) | ((P + 4) & 0xf0000000) + S) >> 2)
//   ((R & 0x1f0000) << 5) | ((R & 0x3e00000) >> 5) | (R & 0xffff)
//
//   The table below lists the other MIPS16 instruction relocations.
//   Each one is calculated in the same way as the non-MIPS16 relocation
//   given on the right, but using the extended MIPS16 layout of 16-bit
//   immediate fields:
//
//      R_MIPS16_GPREL          R_MIPS_GPREL16
//      R_MIPS16_GOT16          R_MIPS_GOT16
//      R_MIPS16_CALL16         R_MIPS_CALL16
//      R_MIPS16_HI16           R_MIPS_HI16
//      R_MIPS16_LO16           R_MIPS_LO16
//
//   A typical instruction will have a format like this:
//
//   +--------------+--------------------------------+
//   |    EXTEND    |     Imm 10:5    |   Imm 15:11  |
//   +--------------+--------------------------------+
//   |    Major     |   rx   |   ry   |   Imm  4:0   |
//   +--------------+--------------------------------+
//
//   EXTEND is the five bit value 11110.  Major is the instruction
//   opcode.
//
//   All we need to do here is shuffle the bits appropriately.
//   As above, the two 16-bit halves must be swapped on a
//   little-endian system.

static inline bool
mips16_reloc (unsigned int r_type)
{
  switch (r_type)
    {
    case elfcpp::R_MIPS16_26:
    case elfcpp::R_MIPS16_GPREL:
    case elfcpp::R_MIPS16_GOT16:
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MIPS16_HI16:
    case elfcpp::R_MIPS16_LO16:
    case elfcpp::R_MIPS16_TLS_GD:
    case elfcpp::R_MIPS16_TLS_LDM:
    case elfcpp::R_MIPS16_TLS_DTPREL_HI16:
    case elfcpp::R_MIPS16_TLS_DTPREL_LO16:
    case elfcpp::R_MIPS16_TLS_GOTTPREL:
    case elfcpp::R_MIPS16_TLS_TPREL_HI16:
    case elfcpp::R_MIPS16_TLS_TPREL_LO16:
      return true;

    default:
      return false;
    }
}

// Check if a microMIPS reloc.

static inline bool
micromips_reloc(unsigned int r_type)
{
  switch (r_type)
    {
    case elfcpp::R_MICROMIPS_26_S1:
    case elfcpp::R_MICROMIPS_HI16:
    case elfcpp::R_MICROMIPS_LO16:
    case elfcpp::R_MICROMIPS_GPREL16:
    case elfcpp::R_MICROMIPS_LITERAL:
    case elfcpp::R_MICROMIPS_GOT16:
    case elfcpp::R_MICROMIPS_PC7_S1:
    case elfcpp::R_MICROMIPS_PC10_S1:
    case elfcpp::R_MICROMIPS_PC16_S1:
    case elfcpp::R_MICROMIPS_CALL16:
    case elfcpp::R_MICROMIPS_GOT_DISP:
    case elfcpp::R_MICROMIPS_GOT_PAGE:
    case elfcpp::R_MICROMIPS_GOT_OFST:
    case elfcpp::R_MICROMIPS_GOT_HI16:
    case elfcpp::R_MICROMIPS_GOT_LO16:
    case elfcpp::R_MICROMIPS_SUB:
    case elfcpp::R_MICROMIPS_HIGHER:
    case elfcpp::R_MICROMIPS_HIGHEST:
    case elfcpp::R_MICROMIPS_CALL_HI16:
    case elfcpp::R_MICROMIPS_CALL_LO16:
    case elfcpp::R_MICROMIPS_SCN_DISP:
    case elfcpp::R_MICROMIPS_JALR:
    case elfcpp::R_MICROMIPS_HI0_LO16:
    case elfcpp::R_MICROMIPS_TLS_GD:
    case elfcpp::R_MICROMIPS_TLS_LDM:
    case elfcpp::R_MICROMIPS_TLS_DTPREL_HI16:
    case elfcpp::R_MICROMIPS_TLS_DTPREL_LO16:
    case elfcpp::R_MICROMIPS_TLS_GOTTPREL:
    case elfcpp::R_MICROMIPS_TLS_TPREL_HI16:
    case elfcpp::R_MICROMIPS_TLS_TPREL_LO16:
    case elfcpp::R_MICROMIPS_GPREL7_S2:
    case elfcpp::R_MICROMIPS_PC23_S2:
      return true;

    default:
      return false;
    }
}

// Similar to MIPS16, the two 16-bit halves in microMIPS must be swapped
// on a little-endian system.  This does not apply to R_MICROMIPS_PC7_S1
// and R_MICROMIPS_PC10_S1 relocs that apply to 16-bit instructions.

static inline bool
micromips_reloc_shuffle(unsigned int r_type)
{
  return (micromips_reloc(r_type)
          && r_type != elfcpp::R_MICROMIPS_PC7_S1
          && r_type != elfcpp::R_MICROMIPS_PC10_S1);
}

template<bool big_endian>
void
mips_reloc_unshuffle(unsigned char* view, unsigned int r_type, bool jal_shuffle)
{
  typedef typename elfcpp::Swap<16, big_endian>::Valtype Valtype16;
  typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype32;

  if (!mips16_reloc(r_type) && !micromips_reloc_shuffle(r_type))
    return;

  // Pick up the first and second halfwords of the instruction.
  Valtype16 first = elfcpp::Swap<16, big_endian>::readval(view);
  Valtype16 second = elfcpp::Swap<16, big_endian>::readval(view + 2);
  Valtype32 val;

  if (micromips_reloc(r_type) || (r_type == elfcpp::R_MIPS16_26 && !jal_shuffle))
    val = first << 16 | second;
  else if (r_type != elfcpp::R_MIPS16_26)
    val = (((first & 0xf800) << 16) | ((second & 0xffe0) << 11)
           | ((first & 0x1f) << 11) | (first & 0x7e0) | (second & 0x1f));
  else
    val = (((first & 0xfc00) << 16) | ((first & 0x3e0) << 11)
           | ((first & 0x1f) << 21) | second);

  elfcpp::Swap<32, big_endian>::writeval(view, val);
}

template<bool big_endian>
void
mips_reloc_shuffle(unsigned char* view, unsigned int r_type, bool jal_shuffle)
{
  typedef typename elfcpp::Swap<16, big_endian>::Valtype Valtype16;
  typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype32;

  if (!mips16_reloc(r_type) && !micromips_reloc_shuffle(r_type))
    return;

  Valtype32 val = elfcpp::Swap<32, big_endian>::readval(view);
  Valtype16 first, second;

  if (micromips_reloc(r_type) || (r_type == elfcpp::R_MIPS16_26 && !jal_shuffle))
    {
      second = val & 0xffff;
      first = val >> 16;
    }
  else if (r_type != elfcpp::R_MIPS16_26)
    {
      second = ((val >> 11) & 0xffe0) | (val & 0x1f);
      first = ((val >> 16) & 0xf800) | ((val >> 11) & 0x1f) | (val & 0x7e0);
    }
  else
    {
      second = val & 0xffff;
      first = ((val >> 16) & 0xfc00) | ((val >> 11) & 0x3e0)
               | ((val >> 21) & 0x1f);
    }

  elfcpp::Swap<16, big_endian>::writeval(view + 2, second);
  elfcpp::Swap<16, big_endian>::writeval(view, first);
}


// Helper structure for R_MIPS*_HI16/LO16 and R_MIPS*_GOT16/LO16 relocations. It
// records high part of the relocation pair.

template<int size, bool big_endian>
struct reloc_high
{
  reloc_high(unsigned char* _view, const Sized_relobj_file<size, big_endian>* _object,
    const Symbol_value<size>* _psymval,
    typename elfcpp::Elf_types<size>::Elf_Addr _addend,
    unsigned int _r_type, unsigned int _rel_type,
    typename elfcpp::Elf_types<size>::Elf_Addr _address = 0, bool _gp_disp = false)
    : view(_view), object(_object), psymval(_psymval), addend(_addend),
      r_type(_r_type), rel_type(_rel_type), address(_address), gp_disp(_gp_disp)
  { }

  unsigned char* view;
  const Sized_relobj_file<size, big_endian>* object;
  const Symbol_value<size>* psymval;
  typename elfcpp::Elf_types<size>::Elf_Addr addend;
  unsigned int r_type;
  unsigned int rel_type;
  typename elfcpp::Elf_types<size>::Elf_Addr address;
  bool gp_disp;
};

template<int size, bool big_endian>
class Mips_relocate_functions : public Relocate_functions<size, big_endian>
{
public:
  typedef enum
  {
    STATUS_OKAY,        // No error during relocation.
    STATUS_OVERFLOW,    // Relocation overflow.
    STATUS_BAD_RELOC    // Relocation cannot be applied.
  } Status;

private:
  typedef Relocate_functions<size, big_endian> Base;
  typedef Mips_relocate_functions<size, big_endian> This;

  static typename std::list<reloc_high<size, big_endian> > hi16_relocs;
  static typename std::list<reloc_high<size, big_endian> > got16_relocs;

public:
  // R_MIPS_16: S + sign-extend(A)
  static inline typename This::Status
  rel16(unsigned char* view,
        const Sized_relobj_file<size, big_endian>* object,
        const Symbol_value<size>* psymval,
        typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
        unsigned int rel_type)
  {
    typedef typename elfcpp::Swap<16, big_endian>::Valtype Valtype;
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Reltype;
    Valtype* wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<16, big_endian>::readval(wv);
    Reltype addend;

    if (rel_type == elfcpp::SHT_RELA)
      addend = Bits<16>::sign_extend32(addend_o);
    else
      addend = Bits<16>::sign_extend32(val);

    Reltype x = psymval->value(object, addend);
    val = Bits<16>::bit_select32(val, x, 0xffffU);
    elfcpp::Swap<16, big_endian>::writeval(wv, val);
    return (Bits<16>::has_overflow32(x)
            ? This::STATUS_OVERFLOW
            : This::STATUS_OKAY);
  }

  // R_MIPS_32: S + A
  static inline typename This::Status
  rel32(unsigned char* view,
        const Sized_relobj_file<size, big_endian>* object,
        const Symbol_value<size>* psymval,
        typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
        unsigned int rel_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype* wv = reinterpret_cast<Valtype*>(view);
    Valtype addend;

    if (rel_type == elfcpp::SHT_RELA)
      addend = Bits<32>::sign_extend32(addend_o);
    else
      addend = elfcpp::Swap<32, big_endian>::readval(wv);

    Valtype x = psymval->value(object, addend);
    elfcpp::Swap<32, big_endian>::writeval(wv, x);
    return This::STATUS_OKAY;
  }

  // R_MIPS_JALR, R_MICROMIPS_JALR
  static inline typename This::Status
  reljalr(unsigned char* view,
          const Sized_relobj_file<size, big_endian>* object,
          const Symbol_value<size>* psymval,
          typename elfcpp::Elf_types<size>::Elf_Addr address,
          bool cross_mode_jump, unsigned int r_type,
          bool jalr_to_bal, bool jr_to_b)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype* wv = reinterpret_cast<Valtype*>(view);
    mips_reloc_unshuffle<big_endian>(view, r_type, false);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);

    // Try converting J(AL)R to B(AL), if the target is in range.
    if (!parameters->options().relocatable()
        && r_type == elfcpp::R_MIPS_JALR
        && !cross_mode_jump
        && ((jalr_to_bal && val == 0x0320f809)    // jalr t9
            || (jr_to_b && val == 0x03200008)))   // jr t9
      {
        int offset = psymval->value(object, 0) - (address + 4);
        if (!Bits<18>::has_overflow32(offset))
          {
            if (val == 0x03200008)   // jr t9
              val = 0x10000000 | (((Valtype)offset >> 2) & 0xffff);   // b addr
            else
              val = 0x04110000 | (((Valtype)offset >> 2) & 0xffff);   // bal addr
          }
      }

    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    mips_reloc_shuffle<big_endian>(view, r_type, false);
    return This::STATUS_OKAY;
  }

  // R_MIPS_PC32: S + A - P
  static inline typename This::Status
  relpc32(unsigned char* view,
          const Sized_relobj_file<size, big_endian>* object,
          const Symbol_value<size>* psymval,
          typename elfcpp::Elf_types<size>::Elf_Addr address,
          typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
          unsigned int rel_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype* wv = reinterpret_cast<Valtype*>(view);
    Valtype addend;
    if (rel_type == elfcpp::SHT_RELA)
      addend = Bits<32>::sign_extend32(addend_o);
    else
      addend = elfcpp::Swap<32, big_endian>::readval(wv);

    Valtype x = psymval->value(object, addend) - address;
    elfcpp::Swap<32, big_endian>::writeval(wv, x);
    return This::STATUS_OKAY;
  }

  // R_MIPS_26, R_MIPS16_26, R_MICROMIPS_26_S1
  static inline typename This::Status
  rel26(unsigned char* view,
        const Sized_relobj_file<size, big_endian>* object,
        const Symbol_value<size>* psymval,
        typename elfcpp::Elf_types<size>::Elf_Addr address,
        bool local,
        typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
        unsigned int rel_type, const Symbol* gsym,
        bool cross_mode_jump, unsigned int r_type, bool jal_to_bal)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;

    mips_reloc_unshuffle<big_endian>(view, r_type, false);
    Valtype* wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);

    Valtype addend;
    if (rel_type == elfcpp::SHT_REL)
      {
        if (r_type == elfcpp::R_MICROMIPS_26_S1)
          addend = (val & 0x03ffffff) << 1;
        else
          addend = (val & 0x03ffffff) << 2;
      }
    else
      addend = addend_o;

    // Make sure the target of JALX is word-aligned.  Bit 0 must be
    // the correct ISA mode selector and bit 1 must be 0.
    if (cross_mode_jump
        && (psymval->value(object, 0) & 3) != (r_type == elfcpp::R_MIPS_26))
      {
        gold_warning(_("JALX to a non-word-aligned address"));
        return This::STATUS_BAD_RELOC;
      }

    // Shift is 2, unusually, for microMIPS JALX.
    unsigned int shift =
        (!cross_mode_jump && r_type == elfcpp::R_MICROMIPS_26_S1) ? 1 : 2;

    Valtype x;
    if (local)
      x = addend | ((address + 4) & (0xfc000000 << shift));
    else
      {
        if (shift == 1)
          x = Bits<27>::sign_extend32(addend);
        else
          x = Bits<28>::sign_extend32(addend);
      }
    x = psymval->value(object, x) >> shift;

    if (!local && !gsym->is_weak_undefined())
      {
        if ((x >> 26) != ((address + 4) >> (26 + shift)))
        {
          gold_error(_("relocation truncated to fit: %u against '%s'"), r_type, gsym->name());
          return This::STATUS_OVERFLOW;
        }
      }

    val = Bits<32>::bit_select32(val, x, 0x03ffffff);

    // If required, turn JAL into JALX.
    if (cross_mode_jump)
    {
      bool ok;
      Valtype opcode = val >> 26;
      Valtype jalx_opcode;

      // Check to see if the opcode is already JAL or JALX.
      if (r_type == elfcpp::R_MIPS16_26)
        {
          ok = (opcode == 0x6) || (opcode == 0x7);
          jalx_opcode = 0x7;
        }
      else if (r_type == elfcpp::R_MICROMIPS_26_S1)
        {
          ok = (opcode == 0x3d) || (opcode == 0x3c);
          jalx_opcode = 0x3c;
        }
      else
        {
          ok = (opcode == 0x3) || (opcode == 0x1d);
          jalx_opcode = 0x1d;
        }

      // If the opcode is not JAL or JALX, there's a problem.
      if (!ok)
        {
          gold_error(_("Direct jumps between ISA modes are not allowed; consider recompiling with interlinking enabled."));
          return This::STATUS_BAD_RELOC;
        }

      // Make this the JALX opcode.
      val = (val & ~(0x3f << 26)) | (jalx_opcode << 26);
    }

    // Try converting JAL to BAL, if the target is in range.
    if (!parameters->options().relocatable()
        && !cross_mode_jump
        && ((jal_to_bal
              && r_type == elfcpp::R_MIPS_26
              && (val >> 26) == 0x3)))    // jal addr
      {
        Valtype dest = (x << 2) | (((address + 4) >> 28) << 28);
        int offset = dest - (address + 4);
        if (!Bits<18>::has_overflow32(offset))
          {
            if (val == 0x03200008)   // jr t9
              val = 0x10000000 | (((Valtype)offset >> 2) & 0xffff);   // b addr
            else
              val = 0x04110000 | (((Valtype)offset >> 2) & 0xffff);   // bal addr
          }
      }

    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    mips_reloc_shuffle<big_endian>(view, r_type, !parameters->options().relocatable());
    return This::STATUS_OKAY;
  }

  // R_MIPS_PC16
  static inline typename This::Status
  relpc16(unsigned char* view,
          const Sized_relobj_file<size, big_endian>* object,
          const Symbol_value<size>* psymval,
          typename elfcpp::Elf_types<size>::Elf_Addr address,
          typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
          unsigned int rel_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype* wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);

    Valtype addend;
    if (rel_type == elfcpp::SHT_REL)
      addend = (val & 0xffff) << 2;
    else
      addend = addend_o;
    addend = Bits<18>::sign_extend32(addend);

    Valtype x = psymval->value(object, addend) - address;
    val = Bits<16>::bit_select32(val, x >> 2, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    return (Bits<18>::has_overflow32(x)
            ? This::STATUS_OVERFLOW
            : This::STATUS_OKAY);
  }

  // R_MIPS_HI16, R_MIPS16_HI16, R_MICROMIPS_HI16,
  static inline typename This::Status
  relhi16(unsigned char* view,
          const Sized_relobj_file<size, big_endian>* object,
          const Symbol_value<size>* psymval,
          typename elfcpp::Elf_types<size>::Elf_Addr addend,
          typename elfcpp::Elf_types<size>::Elf_Addr address,
          bool gp_disp, unsigned int r_type, unsigned int rel_type)
  {
    // Record the relocation. It will be resolved when we find lo16 part.
    hi16_relocs.push_back(reloc_high<size, big_endian>(view, object, psymval,
                          addend, r_type, rel_type, address, gp_disp));
    return This::STATUS_OKAY;
  }

  // R_MIPS_HI16, R_MIPS16_HI16, R_MICROMIPS_HI16,
  static inline typename This::Status
  do_relhi16(unsigned char* view,
             const Sized_relobj_file<size, big_endian>* object,
             const Symbol_value<size>* psymval,
             typename elfcpp::Elf_types<size>::Elf_Addr addend_hi,
             typename elfcpp::Elf_types<size>::Elf_Addr address,
             bool gp_disp, unsigned int r_type,
             unsigned int rel_type,
             typename elfcpp::Swap<32, big_endian>::Valtype addend_lo,
             Target_mips<size, big_endian> *target)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    mips_reloc_unshuffle<big_endian>(view, r_type, false);
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);

    Valtype addend;
    if (rel_type == elfcpp::SHT_REL)
      addend = ((val & 0xffff) << 16) + addend_lo;
    else
      addend = addend_hi;

    Valtype value;
    if (!gp_disp)
      value = psymval->value(object, addend);
    else
      {
        // For MIPS16 ABI code we generate this sequence
        //    0: li      $v0,%hi(_gp_disp)
        //    4: addiupc $v1,%lo(_gp_disp)
        //    8: sll     $v0,16
        //   12: addu    $v0,$v1
        //   14: move    $gp,$v0
        // So the offsets of hi and lo relocs are the same, but the
        // base $pc is that used by the ADDIUPC instruction at $t9 + 4.
        // ADDIUPC clears the low two bits of the instruction address,
        // so the base is ($t9 + 4) & ~3.
        Valtype gp_offset;
        if (r_type == elfcpp::R_MIPS16_HI16)
          gp_offset = target->adjusted_gp_value(object) - ((address + 4) & ~0x3);
        // The microMIPS .cpload sequence uses the same assembly
        // instructions as the traditional psABI version, but the
        // incoming $t9 has the low bit set.
        else if (r_type == elfcpp::R_MICROMIPS_HI16)
          gp_offset = target->adjusted_gp_value(object) - address - 1;
        else
          gp_offset = target->adjusted_gp_value(object) - address;
        value = gp_offset + addend;
      }
    Valtype x = ((value + 0x8000) >> 16) & 0xffff;
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    mips_reloc_shuffle<big_endian>(view, r_type, false);
    return (gp_disp && (target->gp_value() != 0) && Bits<16>::has_overflow32(x)
            ? This::STATUS_OVERFLOW
            : This::STATUS_OKAY);
  }

  // R_MIPS_GOT16, R_MIPS16_GOT16, R_MICROMIPS_GOT16
  static inline typename This::Status
  relgot16_local(unsigned char* view,
                 const Sized_relobj_file<size, big_endian>* object,
                 const Symbol_value<size>* psymval,
                 typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
                 unsigned int rel_type, unsigned int r_type)
  {
    // Record the relocation. It will be resolved when we find lo16 part.
    got16_relocs.push_back(reloc_high<size, big_endian>(view, object, psymval,
                           addend_o, r_type, rel_type));
    return This::STATUS_OKAY;
  }

  // R_MIPS_GOT16, R_MIPS16_GOT16, R_MICROMIPS_GOT16
  static inline typename This::Status
  do_relgot16_local(unsigned char* view,
                    const Sized_relobj_file<size, big_endian>* object,
                    const Symbol_value<size>* psymval,
                    typename elfcpp::Elf_types<size>::Elf_Addr addend_hi,
                    unsigned int r_type, unsigned int rel_type,
                    typename elfcpp::Swap<32, big_endian>::Valtype addend_lo,
                    Target_mips<size, big_endian> *target)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    mips_reloc_unshuffle<big_endian>(view, r_type, false);
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);

    Valtype addend;
    if (rel_type == elfcpp::SHT_REL)
      addend = ((val & 0xffff) << 16) + addend_lo;
    else
      addend = addend_hi;

    // Find got page entry.
    Valtype value = ((psymval->value(object, addend) + 0x8000) >> 16) & 0xffff;
    value <<= 16;
    unsigned int got_offset = target->got_section()->get_got_page_offset(value, object);

    // Resolve the relocation.
    Valtype x = target->got_section()->address() + got_offset - target->adjusted_gp_value(object);
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    mips_reloc_shuffle<big_endian>(view, r_type, false);
    return (Bits<16>::has_overflow32(x)
            ? This::STATUS_OVERFLOW
            : This::STATUS_OKAY);
  }

  // R_MIPS_LO16, R_MIPS16_LO16, R_MICROMIPS_LO16, R_MICROMIPS_HI0_LO16
  static inline typename This::Status
  rello16(Target_mips<size, big_endian> *target, unsigned char* view,
          const Sized_relobj_file<size, big_endian>* object,
          const Symbol_value<size>* psymval,
          typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
          unsigned int rel_type,
          typename elfcpp::Elf_types<size>::Elf_Addr address,
          bool gp_disp, unsigned int r_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    mips_reloc_unshuffle<big_endian>(view, r_type, false);
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);

    Valtype addend;
    if (rel_type == elfcpp::SHT_REL)
      addend = Bits<16>::sign_extend32(val & 0xffff);
    else
      addend = addend_o;

    // Resolve pending R_MIPS_HI16 relocations.
    typename std::list<reloc_high<size, big_endian> >::iterator it = hi16_relocs.begin();
    while (it != hi16_relocs.end())
      {
        reloc_high<size, big_endian> hi16 = *it;
        if (hi16.psymval->value(hi16.object, 0) == psymval->value(object, 0))
          {
            if (do_relhi16(hi16.view, hi16.object, hi16.psymval, hi16.addend,
                           hi16.address, hi16.gp_disp, hi16.r_type,
                           hi16.rel_type, addend, target)
                == This::STATUS_OVERFLOW)
              return This::STATUS_OVERFLOW;
            it = hi16_relocs.erase(it);
          }
        else
          ++it;
      }

    // Resolve pending local R_MIPS_GOT16 relocations.
    typename std::list<reloc_high<size, big_endian> >::iterator it2 = got16_relocs.begin();
    while (it2 != got16_relocs.end())
      {
        reloc_high<size, big_endian> got16 = *it2;
        if (got16.psymval->value(got16.object, 0) == psymval->value(object, 0))
          {
            if (do_relgot16_local(got16.view, got16.object, got16.psymval,
                                  got16.addend, got16.r_type, got16.rel_type,
                                  addend, target)
                == This::STATUS_OVERFLOW)
              return This::STATUS_OVERFLOW;
            it2 = got16_relocs.erase(it2);
          }
        else
          ++it2;
      }

    // Resolve R_MIPS_LO16 relocation.
    Valtype x;
    if (!gp_disp)
      x = psymval->value(object, addend);
    else
      {
        // See the comment for R_MIPS16_HI16 above for the reason
        // for this conditional.
        Valtype gp_offset;
        if (r_type == elfcpp::R_MIPS16_LO16)
          gp_offset = target->adjusted_gp_value(object) - (address & ~0x3);
        else if (r_type == elfcpp::R_MICROMIPS_LO16
              || r_type == elfcpp::R_MICROMIPS_HI0_LO16)
          gp_offset = target->adjusted_gp_value(object) - address + 3;
        else
          gp_offset = target->adjusted_gp_value(object) - address + 4;
        // The MIPS ABI requires checking the R_MIPS_LO16 relocation
        // for overflow.  Relocations against _gp_disp are normally
        // generated from the .cpload pseudo-op.  It generates code
        // that normally looks like this:

        //   lui    $gp,%hi(_gp_disp)
        //   addiu  $gp,$gp,%lo(_gp_disp)
        //   addu   $gp,$gp,$t9

        // Here $t9 holds the address of the function being called,
        // as required by the MIPS ELF ABI.  The R_MIPS_LO16
        // relocation can easily overflow in this situation, but the
        // R_MIPS_HI16 relocation will handle the overflow.
        // Therefore, we consider this a bug in the MIPS ABI, and do
        // not check for overflow here.
        x = gp_offset + addend;
      }
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    mips_reloc_shuffle<big_endian>(view, r_type, false);
    return This::STATUS_OKAY;
  }

  // R_MIPS_CALL16, R_MIPS16_CALL16, R_MICROMIPS_CALL16
  // R_MIPS_GOT16, R_MIPS16_GOT16, R_MICROMIPS_GOT16
  // R_MIPS_TLS_GD, R_MIPS16_TLS_GD, R_MICROMIPS_TLS_GD
  // R_MIPS_TLS_GOTTPREL, R_MIPS16_TLS_GOTTPREL, R_MICROMIPS_TLS_GOTTPREL
  // R_MIPS_TLS_LDM, R_MIPS16_TLS_LDM, R_MICROMIPS_TLS_LDM
  // R_MIPS_GOT_DISP, R_MICROMIPS_GOT_DISP
  static inline typename This::Status
  relgot(Target_mips<size, big_endian> *target, unsigned char* view,
         const Sized_relobj_file<size, big_endian>* object,
         unsigned int got_offset, unsigned int r_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    mips_reloc_unshuffle<big_endian>(view, r_type, false);
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);
    Valtype x = target->got_section()->address() + got_offset
              - target->adjusted_gp_value(object);
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    mips_reloc_shuffle<big_endian>(view, r_type, false);
    return (Bits<16>::has_overflow32(x)
            ? This::STATUS_OVERFLOW
            : This::STATUS_OKAY);
  }

  // R_MIPS_GOT_PAGE, R_MICROMIPS_GOT_PAGE
  static inline typename This::Status
  relgotpage(Target_mips<size, big_endian> *target, unsigned char* view,
             const Sized_relobj_file<size, big_endian>* object,
             const Symbol_value<size>* psymval,
             typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
             unsigned int rel_type)
  {
    // Find a GOT page entry that points to within 32KB of symbol + addend.
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(view);
    Valtype addend = rel_type == elfcpp::SHT_REL ? val & 0xffff : addend_o;

    // Find got page entry.
    typename elfcpp::Elf_types<size>::Elf_Addr value;
    value = (psymval->value(object, addend) + 0x8000) & ~0xffff;
    unsigned int  got_offset = target->got_section()->get_got_page_offset(value, object);

    Valtype x = target->got_section()->address() + got_offset
              - target->adjusted_gp_value(object);
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    return (Bits<16>::has_overflow32(x)
            ? This::STATUS_OVERFLOW
            : This::STATUS_OKAY);
  }

  // R_MIPS_GOT_OFST, R_MICROMIPS_GOT_OFST
  static inline typename This::Status
  relgotofst(Target_mips<size, big_endian> *target, unsigned char* view,
             const Sized_relobj_file<size, big_endian>* object,
             const Symbol_value<size>* psymval,
             typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
             unsigned int rel_type, bool local)
  {
    // For a local symbol, find a GOT page entry that points to within 32KB of
    // symbol + addend. Relocation value is the offset of the got page entry's
    // value from symbol + addend.
    // For a global symbol, relocation value is addend.
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(view);
    Valtype addend = rel_type == elfcpp::SHT_REL ? val & 0xffff : addend_o;
    Valtype x;
    if (local)
      {
        // Find got page entry.
        typename elfcpp::Elf_types<size>::Elf_Addr value;
        value = (psymval->value(object, addend) + 0x8000) & ~0xffff;
        target->got_section()->get_got_page_offset(value, object);

        x = psymval->value(object, addend) - value;
      }
    else
      x = addend;
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    return (Bits<16>::has_overflow32(x)
            ? This::STATUS_OVERFLOW
            : This::STATUS_OKAY);
  }

  // R_MIPS_GOT_HI16, R_MIPS_CALL_HI16,
  // R_MICROMIPS_GOT_HI16, R_MICROMIPS_CALL_HI16
  static inline typename This::Status
  relgot_hi16(Target_mips<size, big_endian> *target, unsigned char* view,
              const Sized_relobj_file<size, big_endian>* object,
              unsigned int got_offset)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);
    Valtype x = target->got_section()->address() + got_offset
              - target->adjusted_gp_value(object);
    x = ((x + 0x8000) >> 16) & 0xffff;
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    return This::STATUS_OKAY;
  }

  // R_MIPS_GOT_LO16, R_MIPS_CALL_LO16,
  // R_MICROMIPS_GOT_LO16, R_MICROMIPS_CALL_LO16
  static inline typename This::Status
  relgot_lo16(Target_mips<size, big_endian> *target, unsigned char* view,
              const Sized_relobj_file<size, big_endian>* object,
              unsigned int got_offset)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);
    Valtype x = target->got_section()->address() + got_offset
              - target->adjusted_gp_value(object);
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    return This::STATUS_OKAY;
  }

  // R_MIPS_GPREL16, R_MIPS16_GPREL, R_MIPS_LITERAL, R_MICROMIPS_LITERAL
  // R_MICROMIPS_GPREL7_S2, R_MICROMIPS_GPREL16
  static inline typename This::Status
  relgprel(unsigned char* view,
           const Sized_relobj_file<size, big_endian>* object,
           const Symbol_value<size>* psymval,
           const typename elfcpp::Swap<size, big_endian>::Valtype gp,
           typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
           unsigned int rel_type,
           bool local, unsigned int r_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;

    const Mips_relobj<size, big_endian>* mips_relobj =
      Mips_relobj<size, big_endian>::as_mips_relobj(object);

    mips_reloc_unshuffle<big_endian>(view, r_type, false);
    Valtype* wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);

    Valtype addend;
    if (rel_type == elfcpp::SHT_RELA)
      addend = addend_o;
    else
      {
        if (r_type == elfcpp::R_MICROMIPS_GPREL7_S2)
          addend = (val & 0x7f) << 2;
        else
          addend = val & 0xffff;
        // Only sign-extend the addend if it was extracted from the
        // instruction.  If the addend was separate, leave it alone,
        // otherwise we may lose significant bits.
        addend = Bits<16>::sign_extend32(addend);
      }

    Valtype x = psymval->value(object, addend) - gp;

    // If the symbol was local, any earlier relocatable links will
    // have adjusted its addend with the gp offset, so compensate
    // for that now.  Don't do it for symbols forced local in this
    // link, though, since they won't have had the gp offset applied
    // to them before.
    if (local)
      x += mips_relobj->gp_value();

    if (r_type == elfcpp::R_MICROMIPS_GPREL7_S2)
      val = Bits<32>::bit_select32(val, x, 0x7f);
    else
      val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    mips_reloc_shuffle<big_endian>(view, r_type, false);
    if (Bits<16>::has_overflow32(x))
      {
        gold_error(_("small-data section exceeds 64KB; lower small-data size limit (see option -G)"));
        return This::STATUS_OVERFLOW;
      }
    return This::STATUS_OKAY;
  }

  // R_MIPS_GPREL32
  static inline typename This::Status
  relgprel32(unsigned char* view,
             const Sized_relobj_file<size, big_endian>* object,
             const Symbol_value<size>* psymval,
             const typename elfcpp::Swap<size, big_endian>::Valtype gp,
             typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
             unsigned int rel_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;

    const Mips_relobj<size, big_endian>* mips_relobj =
      Mips_relobj<size, big_endian>::as_mips_relobj(object);

    Valtype* wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);
    Valtype addend = (rel_type == elfcpp::SHT_REL) ? val : addend_o;

    // R_MIPS_GPREL32 relocations are defined for local symbols only.
    Valtype x = psymval->value(object, addend) + mips_relobj->gp_value() - gp;
    elfcpp::Swap<32, big_endian>::writeval(wv, x);
    return This::STATUS_OKAY;
 }

  // R_MIPS_TLS_TPREL_HI16, R_MIPS16_TLS_TPREL_HI16, R_MICROMIPS_TLS_TPREL_HI16
  // R_MIPS_TLS_DTPREL_HI16, R_MIPS16_TLS_DTPREL_HI16,
  // R_MICROMIPS_TLS_DTPREL_HI16
  static inline typename This::Status
  tlsrelhi16(unsigned char* view,
             const Sized_relobj_file<size, big_endian>* object,
             const Symbol_value<size>* psymval,
             const typename elfcpp::Swap<32, big_endian>::Valtype tp_offset,
             typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
             unsigned int rel_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype* wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);
    Valtype addend = rel_type == elfcpp::SHT_REL ? val & 0xffff : addend_o;

    // tls symbol values are relative to tls_segment()->vaddr()
    Valtype x = ((psymval->value(object, addend) - tp_offset) + 0x8000) >> 16;
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    return This::STATUS_OKAY;
  }

  // R_MIPS_TLS_TPREL_LO16, R_MIPS16_TLS_TPREL_LO16, R_MICROMIPS_TLS_TPREL_LO16,
  // R_MIPS_TLS_DTPREL_LO16, R_MIPS16_TLS_DTPREL_LO16,
  // R_MICROMIPS_TLS_DTPREL_LO16,
  // R_MIPS_TLS_TPREL32, R_MIPS_TLS_TPREL64,
  // R_MIPS_TLS_DTPREL32, R_MIPS_TLS_DTPREL64
  static inline typename This::Status
  tlsrello16(unsigned char* view,
             const Sized_relobj_file<size, big_endian>* object,
             const Symbol_value<size>* psymval,
             const typename elfcpp::Swap<32, big_endian>::Valtype tp_offset,
             typename elfcpp::Elf_types<size>::Elf_Addr addend_o,
             unsigned int rel_type)
  {
    typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;
    Valtype *wv = reinterpret_cast<Valtype*>(view);
    Valtype val = elfcpp::Swap<32, big_endian>::readval(wv);
    Valtype addend = rel_type == elfcpp::SHT_REL ? val & 0xffff : addend_o;

    // tls symbol values are relative to tls_segment()->vaddr()
    Valtype x = psymval->value(object, addend) - tp_offset;
    val = Bits<32>::bit_select32(val, x, 0xffff);
    elfcpp::Swap<32, big_endian>::writeval(wv, val);
    return This::STATUS_OKAY;
  }
};

template<int size, bool big_endian>
typename std::list<reloc_high<size, big_endian> >
    Mips_relocate_functions<size, big_endian>::hi16_relocs;

template<int size, bool big_endian>
typename std::list<reloc_high<size, big_endian> >
    Mips_relocate_functions<size, big_endian>::got16_relocs;

// Mips_got_info methods.

// Reserve space for a GOT entry containing the value of symbol
// SYMNDX in input object OBJECT, plus ADDEND.
template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::record_local_got_symbol(
    Sized_relobj_file<size, big_endian>* object,
    unsigned int symndx,
    typename elfcpp::Elf_types<size>::Elf_Addr addend,
    unsigned char tls_flag,
    unsigned int shndx)
{
  Mips_got_entry<size, big_endian> *entry =
    new Mips_got_entry<size, big_endian>(object, symndx, addend, tls_flag,
                                         shndx);

  typename Got_entry_set::iterator it = this->got_entries_.find(entry);
  if (it != this->got_entries_.end())
    {
      Mips_got_entry<size, big_endian> *e = *it;
      if (tls_flag == GOT_TLS_GD && !e->has_tls_type(GOT_TLS_GD))
        {
          this->tls_gotno_ += 2;
          e->add_tls_type(tls_flag);
        }
      else if (tls_flag == GOT_TLS_IE && !e->has_tls_type(GOT_TLS_IE))
        {
          this->tls_gotno_ += 1;
          e->add_tls_type(tls_flag);
        }
      return;
    }

  if (tls_flag != 0)
    {
      entry->add_tls_type(tls_flag);
      if (tls_flag == GOT_TLS_IE)
        this->tls_gotno_ += 1;
      else if (tls_flag == GOT_TLS_GD)
        this->tls_gotno_ += 2;
      else if (this->tls_ldm_offset_ == -1U)
        {
          this->tls_ldm_offset_ = -2U;
          this->tls_gotno_ += 2;
        }
    }
  //else
    //entry->tls_type = 0;

  this->got_entries_.insert(entry);
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::record_global_got_symbol(
    Mips_symbol<size>* mips_sym,
    Sized_relobj_file<size, big_endian>* object,
    unsigned char tls_flag, bool reloc, bool for_call)
{
  if (!for_call)
    mips_sym->set_got_only_for_calls(false);

  // A global symbol in the GOT must also be in the dynamic symbol table.
  if (!mips_sym->needs_dynsym_entry())
    {
      switch (mips_sym->visibility())
        {
        case elfcpp::STV_INTERNAL:
        case elfcpp::STV_HIDDEN:
          mips_sym->set_is_forced_local();
          break;
        default:
          mips_sym->set_needs_dynsym_entry();
        }
    }

  if (tls_flag == 0)
    this->global_got_symbols_.insert(mips_sym);
  else if (tls_flag == GOT_TLS_GD && !mips_sym->has_tls_type(GOT_TLS_GD))
    this->tls_gotno_ += 2;
  else if (tls_flag == GOT_TLS_IE && !mips_sym->has_tls_type(GOT_TLS_IE))
    this->tls_gotno_ += 1;
  mips_sym->add_tls_type(tls_flag);

  if (reloc)
    {
      if (mips_sym->global_got_area() == GGA_NONE)
        mips_sym->set_global_got_area(GGA_RELOC_ONLY);
      return;
    }

  Mips_got_entry<size, big_endian> *entry = new Mips_got_entry<size, big_endian>(object, mips_sym, 0);

  typename Got_entry_set::iterator it = this->got_entries_.find(entry);
  if (it != this->got_entries_.end())
    {
      // If we've already marked this entry as needing GOT space, we don't
      // need to do it again.
      (*it)->add_tls_type(tls_flag);
      return;
    }

  entry->add_tls_type(tls_flag);

  this->got_entries_.insert(entry);

  //if (tls_flag == 0)
    //mips_sym->set_global_got_area(GGA_NORMAL);
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::add_local_entries(
    Target_mips<size, big_endian> *target, Layout* layout)
{
  Mips_output_data_got<size, big_endian> *got = target->got_section();
  // First two GOT entries are reserved. The first entry will be filled at
  // runtime. The second entry will be used by some runtime loaders.
  got->add_constant(0);
  got->add_constant(target->mips_elf_gnu_got1_mask());

  for (typename Got_entry_set::iterator
       p = this->got_entries_.begin();
       p != this->got_entries_.end();
       ++p)
    {
      Mips_got_entry<size, big_endian> *entry = *p;
      if (entry->is_for_local_symbol() && !entry->has_tls())
        {
          got->add_local(entry->object(), entry->symndx(),
                         GOT_TYPE_STANDARD);
          unsigned int got_offset = entry->object()->local_got_offset(
              entry->symndx(), GOT_TYPE_STANDARD);
          if (got->multi_got() && this->index_ > 0
              && parameters->options().output_is_position_independent())
            target->rel_dyn_section(layout)->add_local(entry->object(),
                entry->symndx(), elfcpp::R_MIPS_REL32, got, got_offset);
        }
    }

  this->add_page_entries(target, layout);

  // Add global entries which should be in the local area.
  for (typename Got_entry_set::iterator
       p = this->got_entries_.begin();
       p != this->got_entries_.end();
       ++p)
    {
      Mips_got_entry<size, big_endian> *entry = *p;
      if (!entry->is_for_global_symbol())
        continue;

      Mips_symbol<size>* mips_sym = entry->sym();
      if (mips_sym->global_got_area() == GGA_NONE && !mips_sym->has_tls())
        {
          unsigned int got_type;
          if (!got->multi_got())
            got_type = GOT_TYPE_STANDARD;
          else
            got_type = GOT_TYPE_STANDARD_MULTIGOT
                     + this->index_;
          if (got->add_global(mips_sym, got_type))
            {
              mips_sym->set_global_gotoffset(mips_sym->got_offset(got_type));
              if (got->multi_got() && this->index_ > 0
                  && parameters->options().output_is_position_independent())
                target->rel_dyn_section(layout)->add_symbolless_global_addend(
                    mips_sym, elfcpp::R_MIPS_REL32, got,
                    mips_sym->got_offset(got_type));
            }
        }
    }
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::add_page_entries(
    Target_mips<size, big_endian> *target, Layout* layout)
{
  if (this->page_gotno_ == 0)
    return;

  Mips_output_data_got<size, big_endian> *got = target->got_section();
  this->got_page_offset_start_ = got->add_constant(0);
  if (got->multi_got() && this->index_ > 0
      && parameters->options().output_is_position_independent())
    target->rel_dyn_section(layout)->add_absolute(elfcpp::R_MIPS_REL32, got,
                                                  this->got_page_offset_start_);
  int num_entries = this->page_gotno_;
  unsigned int prev_offset = this->got_page_offset_start_;
  while (--num_entries > 0)
    {
      unsigned int next_offset = got->add_constant(0);
      if (got->multi_got() && this->index_ > 0
          && parameters->options().output_is_position_independent())
        target->rel_dyn_section(layout)->add_absolute(elfcpp::R_MIPS_REL32, got,
                                                      next_offset);
      gold_assert(next_offset == prev_offset + size/8);
      prev_offset = next_offset;
    }
  this->got_page_offset_next_ = this->got_page_offset_start_;
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::add_global_entries(
    Target_mips<size, big_endian> *target, Layout* layout,
    unsigned int non_reloc_only_global_gotno)
{
  Mips_output_data_got<size, big_endian> *got = target->got_section();
  // Add GGA_NORMAL entries.
  unsigned int count = 0;
  for (typename Got_entry_set::iterator
       p = this->got_entries_.begin();
       p != this->got_entries_.end();
       ++p)
    {
      Mips_got_entry<size, big_endian> *entry = *p;
      if (!entry->is_for_global_symbol())
        continue;

      Mips_symbol<size>* mips_sym = entry->sym();
      if (mips_sym->global_got_area() != GGA_NORMAL)
        continue;

      unsigned int got_type;
      if (!got->multi_got())
        got_type = GOT_TYPE_STANDARD;
      else
        // For multi-got links, global symbol can be in both primary and
        // secondary got(s), so we need to define custom got type
        // (GOT_TYPE_STANDARD_MULTIGOT + got-index) to ensure that symbol
        // is added to secondary got(s).
        got_type = GOT_TYPE_STANDARD_MULTIGOT
                 + this->index_;
      if (!got->add_global(mips_sym, got_type))
        continue;

      mips_sym->set_global_gotoffset(mips_sym->got_offset(got_type));
      if (got->multi_got() && this->index_ == 0)
        count++;
      if (got->multi_got() && this->index_ > 0)
        {
          if (parameters->options().output_is_position_independent()
              || (!parameters->doing_static_link()
                  && mips_sym->is_from_dynobj() && !mips_sym->is_undefined()))
            {
              target->rel_dyn_section(layout)->add_global(
                  mips_sym, elfcpp::R_MIPS_REL32, got,
                  mips_sym->got_offset(got_type));
              got->add_secondary_got_reloc(mips_sym->got_offset(got_type),
                                           elfcpp::R_MIPS_REL32, mips_sym);
            }
        }
    }

  if (!got->multi_got() || this->index_ == 0)
    {
      if (got->multi_got())
        {
          // We need to allocate space in the primary got for GGA_NORMAL entries
          // of secondary gots, to ensure that got offsets of GGA_RELOC_ONLY entries
          // correspond to dynamic symbol indexes.
          while (count < non_reloc_only_global_gotno)
            {
              got->add_constant(0);
              ++count;
            }
        }

      // Add GGA_RELOC_ONLY entries.
      got->add_reloc_only_entries();
    }
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::add_reloc_only_entries(
    Mips_output_data_got<size, big_endian> *got)
{
  for (typename Unordered_set<Mips_symbol<size>*>::iterator
       p = this->global_got_symbols_.begin();
       p != this->global_got_symbols_.end();
       ++p)
    {
      Mips_symbol<size>* mips_sym = *p;
      if (mips_sym->global_got_area() == GGA_RELOC_ONLY)
        {
          unsigned int got_type;
          if (!got->multi_got())
            got_type = GOT_TYPE_STANDARD;
          else
            got_type = GOT_TYPE_STANDARD_MULTIGOT;
          if (got->add_global(mips_sym, got_type))
            mips_sym->set_global_gotoffset(mips_sym->got_offset(got_type));
        }
    }
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::add_tls_entries(
    Target_mips<size, big_endian> *target, Layout* layout)
{
  Mips_output_data_got<size, big_endian> *got = target->got_section();
  // Add local tls entries.
  for (typename Got_entry_set::iterator
       p = this->got_entries_.begin();
       p != this->got_entries_.end();
       ++p)
    {
      Mips_got_entry<size, big_endian> *entry = *p;
      if (!entry->is_for_local_symbol())
        continue;

      if (entry->has_tls_type(GOT_TLS_GD))
        {
          unsigned int got_type = GOT_TYPE_TLS_PAIR;
          unsigned int r_type1 = size == 32 ? elfcpp::R_MIPS_TLS_DTPMOD32 :
                                              elfcpp::R_MIPS_TLS_DTPMOD64;
          unsigned int r_type2 = size == 32 ? elfcpp::R_MIPS_TLS_DTPREL32 :
                                              elfcpp::R_MIPS_TLS_DTPREL64;

          if (!parameters->doing_static_link())
            {
              got->add_local_pair_with_rel(entry->object(), entry->symndx(),
                                           entry->shndx(), got_type,
                                           target->rel_dyn_section(layout), r_type1, 0);
              unsigned int got_offset = entry->object()->local_got_offset(entry->symndx(),
                                         got_type);
              got->add_static_reloc(got_offset + size/8, r_type2,
                                    entry->object(), entry->symndx());
            }
          else
            {
              // We are doing a static link.  Mark it as belong to module 1,
              // the executable.
              unsigned int got_offset = got->add_constant(1);
              entry->object()->set_local_got_offset(entry->symndx(), got_type,
                                                  got_offset);
              got->add_constant(0);
              got->add_static_reloc(got_offset + size/8, r_type2,
                                    entry->object(), entry->symndx());
            }
        }
      if (entry->has_tls_type(GOT_TLS_IE))
        {
          unsigned int got_type = GOT_TYPE_TLS_OFFSET;
          unsigned int r_type = size == 32 ? elfcpp::R_MIPS_TLS_TPREL32 :
                                             elfcpp::R_MIPS_TLS_TPREL64;
          if (!parameters->doing_static_link())
            got->add_local_with_rel(entry->object(), entry->symndx(), got_type,
                                    target->rel_dyn_section(layout), r_type);
          else
            {
              got->add_local(entry->object(), entry->symndx(), got_type);
              unsigned int got_offset =
                  entry->object()->local_got_offset(entry->symndx(), got_type);
              got->add_static_reloc(got_offset, r_type, entry->object(),
                                    entry->symndx());
            }
        }
      if (entry->has_tls_type(GOT_TLS_LDM))
        {
          if (got->tls_ldm_offset(entry->object()) != -1U
              && got->tls_ldm_offset(entry->object()) != -2U)
            continue;

          unsigned int r_type = size == 32 ?
                                  elfcpp::R_MIPS_TLS_DTPMOD32 :
                                  elfcpp::R_MIPS_TLS_DTPMOD64;
          unsigned int got_offset;
          if (!parameters->doing_static_link())
            {
              got_offset = got->add_constant(0);
              target->rel_dyn_section(layout)->add_local(
                  entry->object(), 0, r_type, got, got_offset);
            }
          else
            // We are doing a static link.  Just mark it as belong to module 1,
            // the executable.
            got_offset = got->add_constant(1);

          got->add_constant(0);
          got->set_tls_ldm_offset(got_offset, entry->object());
        }
    }

  // Add global tls entries.
  for (typename Got_entry_set::iterator
       p = this->got_entries_.begin();
       p != this->got_entries_.end();
       ++p)
    {
      Mips_got_entry<size, big_endian> *entry = *p;
      if (!entry->is_for_global_symbol())
        continue;

      Mips_symbol<size>* mips_sym = entry->sym();
      if (entry->has_tls_type(GOT_TLS_GD))
        {
          unsigned int got_type;
          if (!got->multi_got())
            got_type = GOT_TYPE_TLS_PAIR;
          else
            got_type = GOT_TYPE_TLS_PAIR_MULTIGOT
                     + this->index_;
          unsigned int r_type1 = size == 32 ? elfcpp::R_MIPS_TLS_DTPMOD32 :
                                              elfcpp::R_MIPS_TLS_DTPMOD64;
          unsigned int r_type2 = size == 32 ? elfcpp::R_MIPS_TLS_DTPREL32 :
                                              elfcpp::R_MIPS_TLS_DTPREL64;
          if (!parameters->doing_static_link())
            got->add_global_pair_with_rel(mips_sym, got_type,
                             target->rel_dyn_section(layout), r_type1, r_type2);
          else
            {
              // Add a GOT pair for for R_MIPS_TLS_GD.  The creates a pair of
              // GOT entries. The first one is initialized to be 1, which is the
              // module index for the main executable and the second one 0.  A
              // reloc of the type R_MIPS_TLS_DTPREL32/64 will be created for
              // the second GOT entry and will be applied by gold.
              unsigned int got_offset = got->add_constant(1);
              mips_sym->set_got_offset(got_type, got_offset);
              got->add_constant(0);
              got->add_static_reloc(got_offset + size/8, r_type2, mips_sym);
            }
        }
      if (entry->has_tls_type(GOT_TLS_IE))
        {
          unsigned int got_type;
          if (!got->multi_got())
            got_type = GOT_TYPE_TLS_OFFSET;
          else
            got_type = GOT_TYPE_TLS_OFFSET_MULTIGOT
                     + this->index_;
          unsigned int r_type = size == 32 ? elfcpp::R_MIPS_TLS_TPREL32 :
                                             elfcpp::R_MIPS_TLS_TPREL64;
          if (!parameters->doing_static_link())
            got->add_global_with_rel(mips_sym, got_type,
                                     target->rel_dyn_section(layout), r_type);
          else
            {
              got->add_global(mips_sym, got_type);
              unsigned int got_offset = mips_sym->got_offset(got_type);
              got->add_static_reloc(got_offset, r_type, mips_sym);
            }
        }
    }
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::lay_out_got(
    Target_mips<size, big_endian> *target, Layout* layout, Symbol_table* symtab)
{
  this->local_gotno_ += 2;
  this->local_gotno_ += this->page_gotno_;
  this->count_global_got_symbols(symtab);

  unsigned int got_size = (this->local_gotno_ + this->global_gotno_ + this->tls_gotno_) * size/8;
  if (got_size > Target_mips<size, big_endian>::MIPS_GOT_MAX_SIZE)
    this->lay_out_multi_got(target, layout);
  else
    {
      this->add_local_entries(target, layout);
      this->add_global_entries(target, layout, /*not used*/-1U);
      this->add_tls_entries(target, layout);
    }
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::count_global_got_symbols(Symbol_table* symtab)
{
  for (typename Unordered_set<Mips_symbol<size>*>::iterator
       p = this->global_got_symbols_.begin();
       p != this->global_got_symbols_.end();
       ++p)
    {
      Mips_symbol<size>* sym = *p;
      // Make a final decision about whether the symbol belongs in the
      // local or global GOT.  Symbols that bind locally can (and in the
      // case of forced-local symbols, must) live in the local GOT.
      // Those that are aren't in the dynamic symbol table must also
      // live in the local GOT.

      if (!should_add_dynsym_entry(sym, symtab)
          || (sym->got_only_for_calls()
            ? symbol_calls_local(sym, should_add_dynsym_entry(sym, symtab))
            : symbol_references_local(sym, should_add_dynsym_entry(sym, symtab))))
        {
          // The symbol belongs in the local GOT.  We no longer need this
          // entry if it was only used for relocations; those relocations
          // will be against the null or section symbol instead.
          if (sym->global_got_area() != GGA_RELOC_ONLY)
            this->local_gotno_ += 1;
          sym->set_global_got_area(GGA_NONE);
        }
      else
        {
          if (sym->global_got_area() == GGA_RELOC_ONLY)
            this->reloc_only_gotno_++;
          this->global_gotno_ += 1;
        }
    }
}

template<int size, bool big_endian>
unsigned int
Mips_got_info<size, big_endian>::get_got_page_offset(unsigned int value,
                                                     unsigned char *got_view)
{
  typename Got_page_offsets::iterator it = this->got_page_offsets_.find(value);
  if (it != this->got_page_offsets_.end())
    return it->second;

  gold_assert(this->got_page_offset_next_ < this->got_page_offset_start_ + (size/8) * this->page_gotno_);

  unsigned int got_offset = this->got_page_offset_next_;
  elfcpp::Swap<size, big_endian>::writeval(got_view + got_offset, value);
  this->got_page_offsets_[value] = got_offset;
  this->got_page_offset_next_ += size/8;
  return got_offset;
}

// Record that OBJECT has a page relocation against symbol SYMNDX and
// that ADDEND is the addend for that relocation.
// This function creates an upper bound on the number of GOT slots
// required; no attempt is made to combine references to non-overridable
// global symbols across multiple input files.
template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::record_got_page_entry(
    Sized_relobj_file<size, big_endian> *object,
    unsigned int symndx, int addend)
{
  struct Got_page_range **range_ptr, *range;
  int old_pages, new_pages;

  // Find the Got_page_entry for this symbol.
  Got_page_entry *entry = new Got_page_entry(object, symndx);
  typename Got_page_entry_set::iterator it = this->got_page_entries_.find(entry);
  if (it != this->got_page_entries_.end())
    entry = *it;
  else
    this->got_page_entries_.insert(entry);

  // Skip over ranges whose maximum extent cannot share a page entry
  // with ADDEND.
  range_ptr = &entry->ranges;
  while (*range_ptr && addend > (*range_ptr)->max_addend + 0xffff)
    range_ptr = &(*range_ptr)->next;

  // If we scanned to the end of the list, or found a range whose
  // minimum extent cannot share a page entry with ADDEND, create
  // a new singleton range.
  range = *range_ptr;
  if (!range || addend < range->min_addend - 0xffff)
    {
      range = new Got_page_range();
      range->next = *range_ptr;
      range->min_addend = addend;
      range->max_addend = addend;

      *range_ptr = range;
      ++entry->num_pages;
      ++this->page_gotno_;
      return;
    }

  // Remember how many pages the old range contributed.
  old_pages = range->get_max_pages();

  // Update the ranges.
  if (addend < range->min_addend)
    range->min_addend = addend;
  else if (addend > range->max_addend)
    {
      if (range->next && addend >= range->next->min_addend - 0xffff)
        {
          old_pages += range->next->get_max_pages();
          range->max_addend = range->next->max_addend;
          range->next = range->next->next;
        }
      else
        range->max_addend = addend;
    }

  // Record any change in the total estimate.
  new_pages = range->get_max_pages();
  if (old_pages != new_pages)
    {
      entry->num_pages += new_pages - old_pages;
      this->page_gotno_ += new_pages - old_pages;
    }
}

template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::lay_out_multi_got(
    Target_mips<size, big_endian> *target, Layout* layout)
{
  target->got_section()->set_multi_got();

  // Count how many GOT entries each input object requires, creating a
  // map from object to got info while at that.
  this->make_got_per_object(this->got_entries_, this->object2got);

  // Also count how many page entries each input object requires.
  this->make_got_pages_per_object(this->got_page_entries_, this->object2got);

  // Try to merge the GOTs of input objects together, as long as they
  // don't seem to exceed the maximum GOT size, choosing one of them
  // to be the primary GOT.
  this->merge_gots(this->object2got);

  // G is the primary GOT.
  Mips_got_info<size, big_endian> *g = this->next_;

  // Every symbol that is referenced in a dynamic relocation must be
  // present in the primary GOT.
  g->global_gotno_ = this->global_gotno_;

  // Add got entries.
  unsigned int i = 0;
  unsigned int offset = 0;
  do
    {
      g->index_ = i;
      g->add_local_entries(target, layout);
      if (i == 0)
        g->add_global_entries(target, layout,
                              this->global_gotno_ - this->reloc_only_gotno_);
      else
        g->add_global_entries(target, layout,
                              /*not used*/-1U);
      g->add_tls_entries(target, layout);
      g->offset_ = offset;
      offset += (2 + g->local_gotno_ + g->page_gotno_ + g->global_gotno_ + g->tls_gotno_) * size/8;

      if (i > 0)
        {
          // Forbid global symbols in every non-primary GOT from having
          // lazy-binding stubs.
          for (typename Got_entry_set::iterator
               p = g->got_entries_.begin();
               p != g->got_entries_.end();
               ++p)
            {
              Mips_got_entry<size, big_endian> *entry = *p;
              if (entry->is_for_global_symbol())
                target->remove_lazy_stub_entry(entry->sym());
            }
        }

      g = g->next_;
      ++i;
    }
  while (g);

}

// Create one separate got for each object that has got entries, such that
// we can tell how many local and global entries each object requires.
template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::make_got_per_object(Got_entry_set &got_entries,
    Object2got_entry_set &object2got)
{
  for (typename Got_entry_set::iterator
       p = got_entries.begin();
       p != got_entries.end();
       ++p)
    {
      Mips_got_entry<size, big_endian> *entry = *p;
      Mips_got_info<size, big_endian> *g
        = this->get_got_for_object(object2got, entry->object());
      gold_assert(g != NULL);

      // Insert the GOT entry in the object's got entry hash table.
      typename Got_entry_set::iterator it = g->got_entries_.find(entry);
      if (it != g->got_entries_.end())
        continue;

      Mips_got_entry<size, big_endian> *entry2 = new Mips_got_entry<size, big_endian>(*entry);
      g->got_entries_.insert(entry2);

      if (entry->has_tls())
        {
          if (entry->has_tls_type(GOT_TLS_GD | GOT_TLS_LDM))
            g->tls_gotno_ += 2;
          if (entry->has_tls_type(GOT_TLS_IE))
            g->tls_gotno_ += 1;
        }
      else if (entry->is_for_local_symbol()
            || entry->sym()->global_got_area() == GGA_NONE)
        ++g->local_gotno_;
      else
        ++g->global_gotno_;
    }
}

// Use OBJECT2GOT to find OBJECT's got entry, creating one if none exists.
template<int size, bool big_endian>
Mips_got_info<size, big_endian>*
Mips_got_info<size, big_endian>::get_got_for_object(
    Object2got_entry_set &object2got, Object *object)
{
  Object2got_entry<size, big_endian> *entry = new Object2got_entry<size, big_endian>(object);

  typename Object2got_entry_set::iterator it = object2got.find(entry);
  if (it != object2got.end())
    return (*it)->g;

  entry->g = new Mips_got_info<size, big_endian>(true);
  object2got.insert(entry);
  return entry->g;
}

template<int size, bool big_endian>
Mips_got_info<size, big_endian>*
Mips_got_info<size, big_endian>::get_got_info(const Object* object)
{
  Object2got_entry<size, big_endian> *entry = new Object2got_entry<size, big_endian>(object);

  typename Object2got_entry_set::iterator it = object2got.find(entry);
  if (it != object2got.end())
    return (*it)->g;
  return NULL;
}

// Traverse page entries in GOT_PAGE_ENTRIES and associate each page entry
// with the object's got.
template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::make_got_pages_per_object(
    Got_page_entry_set &got_page_entries, Object2got_entry_set &object2got)
{
  for (typename Got_page_entry_set::iterator
       p = got_page_entries.begin();
       p != got_page_entries.end();
       ++p)
    {
      Got_page_entry *entry = *p;
      Mips_got_info<size, big_endian> *g
        = this->get_got_for_object(object2got, entry->object);
      gold_assert(g != NULL);

      // Insert the GOT entry in the object's got entry hash table.
      typename Got_page_entry_set::iterator it = g->got_page_entries_.find(entry);
      if (it != g->got_page_entries_.end())
        continue;

      Got_page_entry *entry2 = new Got_page_entry();
      *entry2 = *entry;
      g->got_page_entries_.insert(entry2);
      g->page_gotno_ += entry->num_pages;
    }
}

// Attempt to merge gots of different input objects.  Try to use as much
// as possible of the primary got, since it doesn't require explicit
// dynamic relocations, but don't use objects that would reference global
// symbols out of the addressable range.  Failing the primary got,
// attempt to merge with the current got, or finish the current got
// and then make make the new got current.
template<int size, bool big_endian>
void
Mips_got_info<size, big_endian>::merge_gots(Object2got_entry_set &object2got)
{
  Mips_got_info<size, big_endian> *primary = NULL;
  Mips_got_info<size, big_endian> *current = NULL;

  for (typename Object2got_entry_set::iterator
       p = object2got.begin();
       p != object2got.end();
       ++p)
    {
      Object2got_entry<size, big_endian> *entry = *p;
      Mips_got_info<size, big_endian> *g = entry->g;

      // Work out the number of page, local and TLS entries.
      unsigned int estimate = this->page_gotno_;
      if (estimate > g->page_gotno_)
        estimate = g->page_gotno_;
      estimate += g->local_gotno_ + g->tls_gotno_;

      // We place TLS GOT entries after both locals and globals.  The globals
      // for the primary GOT may overflow the normal GOT size limit, so be
      // sure not to merge a GOT which requires TLS with the primary GOT in that
      // case.  This doesn't affect non-primary GOTs.
      estimate += (g->tls_gotno_ > 0 ? this->global_gotno_ : g->global_gotno_);

      unsigned int max_count = Target_mips<size, big_endian>::MIPS_GOT_MAX_SIZE / (size/8) - 2;
      if (estimate <= max_count)
        {
          // If we don't have a primary GOT, use it as
          // a starting point for the primary GOT.
          if (!primary)
            {
              primary = g;
              continue;
            }

          // Try merging with the primary GOT.
          if (this->merge_got_with (entry, primary, primary))
            continue;
        }

      // If we can merge with the last-created got, do it.
      if (current && this->merge_got_with (entry, current, primary))
        continue;

      // Well, we couldn't merge, so create a new GOT.  Don't check if it
      // fits; if it turns out that it doesn't, we'll get relocation
      // overflows anyway.
      g->next_ = current;
      current = g;
    }

  // If we do not find any suitable primary GOT, create an empty one.
  if (primary == NULL)
    this->next_ = new Mips_got_info<size, big_endian>(true);
  else
    this->next_ = primary;
  this->next_->next_ = current;
}

// Consider merging the got described by ENTRY with TO, using the
// information given by ARG.  Returns false if this would lead to overflow,
// true if they were merged successfully.
template<int size, bool big_endian>
bool
Mips_got_info<size, big_endian>::merge_got_with(
    Object2got_entry<size, big_endian> *entry,
    Mips_got_info<size, big_endian> *to,
    Mips_got_info<size, big_endian> *primary)
{
  Mips_got_info<size, big_endian> *from = entry->g;
  unsigned int estimate;

  // Work out how many page entries we would need for the combined GOT.
  estimate = this->page_gotno_;
  if (estimate >= from->page_gotno_ + to->page_gotno_)
    estimate = from->page_gotno_ + to->page_gotno_;

  // And conservatively estimate how many local and TLS entries
  // would be needed.
  estimate += from->local_gotno_ + to->local_gotno_;
  estimate += from->tls_gotno_ + to->tls_gotno_;

  // If we're merging with the primary got, we will always have
  // the full set of global entries.  Otherwise estimate those
  // conservatively as well.
  if (to == primary)
    estimate += this->global_gotno_;
  else
    estimate += from->global_gotno_ + to->global_gotno_;

  // Bail out if the combined GOT might be too big.
  unsigned int max_count = Target_mips<size, big_endian>::MIPS_GOT_MAX_SIZE / (size/8) - 2;
  if (estimate > max_count)
    return false;

  // Commit to the merge.  Record that TO is now the got for this object.
  entry->g = to;

  // Transfer the object's got information from FROM to TO.
  this->make_got_per_object(from->got_entries_, this->object2got);
  this->make_got_pages_per_object(from->got_page_entries_, this->object2got);

  // We don't have to worry about releasing memory of the actual
  // got entries, since they're all in the master got_entries hash
  // table anyway.
  //delete from->got_entries;
  //delete from->got_page_entries;
  return true;
}

// Mips_output_data_got methods.

template<int size, bool big_endian>
void
Mips_output_data_got<size, big_endian>::do_write(Output_file* of)
{
  typedef typename elfcpp::Elf_types<size>::Elf_Addr Mips_address;

  // Call parent to write out GOT.
  Output_data_got<size, big_endian>::do_write(of);

  const off_t offset = this->offset();
  const section_size_type oview_size =
    convert_to_section_size_type(this->data_size());
  unsigned char* const oview = of->get_output_view(offset, oview_size);

  // Needed for fixing values of .got section.
  this->got_view_ = oview;

  // Write lazy stub addresses.
  for (typename Unordered_set<Mips_symbol<size>*>::iterator
       p = got_info->global_got_symbols().begin();
       p != got_info->global_got_symbols().end();
       ++p)
    {
      Mips_symbol<size>* mips_sym = *p;
      if (mips_sym->has_lazy_stub())
        {
          //if (mips_sym->is_forwarder())
            //mips_sym = this->symbol_table_->resolve_forwards(mips_sym);

          typedef typename elfcpp::Swap<size, big_endian>::Valtype Valtype;
          Valtype* wv = reinterpret_cast<Valtype*>(
            oview + (this->local_gotno() + mips_sym->dynsym_index() - this->global_got_index()) * size/8);
          Valtype value = target_->mips_stubs()->address() + mips_sym->lazy_stub_offset();
          elfcpp::Swap<size, big_endian>::writeval(wv, value);
        }
    }

  if (!this->secondary_got_relocs_.empty())
    {
      // Fixup for the secondary got R_MIPS_REL32 relocs.  Since glibc's ld.so
      // when resolving R_MIPS_REL32 relocs just adds the final primary got
      // entry value to the relocation field, we need to copy initial value of
      // secondary got entry to corresponding primary got entry so that primary
      // entry is correctly resolved, and we need to initialize secondary got
      // entry to 0.
      for (size_t i = 0; i < this->secondary_got_relocs_.size(); ++i)
        {
          Static_reloc& reloc(this->secondary_got_relocs_[i]);
          if (reloc.symbol_is_global())
            {
              const Symbol* gsym = reloc.symbol();
              gold_assert(gsym != NULL);
              if (gsym->is_forwarder())
                gsym = this->symbol_table_->resolve_forwards(gsym);

              unsigned got_offset = reloc.got_offset();
              gold_assert(got_offset < oview_size);

              typedef typename elfcpp::Swap<size, big_endian>::Valtype Valtype;
              Valtype* wv_prim = reinterpret_cast<Valtype*>(
                oview + (this->local_gotno() + gsym->dynsym_index() - this->global_got_index()) * size/8);
              Valtype* wv_sec = reinterpret_cast<Valtype*>(oview + got_offset);
              Valtype value = elfcpp::Swap<size, big_endian>::readval(wv_sec);
              elfcpp::Swap<size, big_endian>::writeval(wv_prim, value);
              elfcpp::Swap<size, big_endian>::writeval(wv_sec, 0);
            }
        }

      of->write_output_view(offset, oview_size, oview);
    }

  // We are done if there is no fix up.
  if (this->static_relocs_.empty())
    return;

  Output_segment* tls_segment = this->layout_->tls_segment();
  gold_assert(tls_segment != NULL);

  for (size_t i = 0; i < this->static_relocs_.size(); ++i)
    {
      Static_reloc& reloc(this->static_relocs_[i]);

      Mips_address value;
      if (!reloc.symbol_is_global())
        {
          Sized_relobj_file<size, big_endian>* object = reloc.relobj();
          const Symbol_value<size>* psymval =
            object->local_symbol(reloc.index());

          // We are doing static linking.  Issue an error and skip this
          // relocation if the symbol is undefined or in a discarded_section.
          bool is_ordinary;
          unsigned int shndx = psymval->input_shndx(&is_ordinary);
          if ((shndx == elfcpp::SHN_UNDEF)
              || (is_ordinary
                  && shndx != elfcpp::SHN_UNDEF
                  && !object->is_section_included(shndx)
                  && !this->symbol_table_->is_section_folded(object, shndx)))
            {
              gold_error(_("undefined or discarded local symbol %u from "
                           " object %s in GOT"),
                         reloc.index(), reloc.relobj()->name().c_str());
              continue;
            }

          value = psymval->value(object, 0);
        }
      else
        {
          const Symbol* gsym = reloc.symbol();
          gold_assert(gsym != NULL);
          if (gsym->is_forwarder())
            gsym = this->symbol_table_->resolve_forwards(gsym);

          // We are doing static linking.  Issue an error and skip this
          // relocation if the symbol is undefined or in a discarded_section
          // unless it is a weakly_undefined symbol.
          if ((gsym->is_defined_in_discarded_section()
                || gsym->is_undefined())
              && !gsym->is_weak_undefined())
            {
              gold_error(_("undefined or discarded symbol %s in GOT"),
                         gsym->name());
              continue;
            }

          if (!gsym->is_weak_undefined())
            value = Mips_symbol<size>::as_mips_sym(gsym)->value();
          else
            value = 0;
        }

      unsigned got_offset = reloc.got_offset();
      gold_assert(got_offset < oview_size);

      typedef typename elfcpp::Swap<size, big_endian>::Valtype Valtype;
      Valtype* wv = reinterpret_cast<Valtype*>(oview + got_offset);
      Valtype x;

      switch (reloc.r_type())
        {
        case elfcpp::R_MIPS_TLS_DTPMOD32:
          x = value;
          break;
        case elfcpp::R_MIPS_TLS_TPREL32:
          x = value - elfcpp::TP_OFFSET;
          break;
        case elfcpp::R_MIPS_TLS_DTPREL32:
          x = value - elfcpp::DTP_OFFSET;
          break;
        default:
          gold_unreachable();
          break;
        }

      elfcpp::Swap<size, big_endian>::writeval(wv, x);
    }

  of->write_output_view(offset, oview_size, oview);
}

// Mips_relobj methods.

// Count the local symbols.  The Mips backend needs to know if a symbol
// is a MIPS16 or microMIPS function or not.  For global symbols, it is easy
// because the Symbol object keeps the ELF symbol type and st_other field.
// For local symbol it is harder because we cannot access this information.
// So we override the do_count_local_symbol in parent and scan local symbols to
// mark MIPS16 and microMIPS functions.  This is not the most efficient way but
// I do not want to slow down other ports by calling a per symbol target hook
// inside Sized_relobj_file<size, big_endian>::do_count_local_symbols.

template<int size, bool big_endian>
void
Mips_relobj<size, big_endian>::do_count_local_symbols(
    Stringpool_template<char>* pool,
    Stringpool_template<char>* dynpool)
{
  // Ask parent to count the local symbols.
  Sized_relobj_file<size, big_endian>::do_count_local_symbols(pool, dynpool);
  const unsigned int loccount = this->local_symbol_count();
  if (loccount == 0)
    return;

  // Initialize the mips16 and micromips function bit-vector.
  std::vector<bool> empty_vector(loccount, false);
  std::vector<bool> empty_vector2(loccount, false);
  this->local_symbol_is_mips16_.swap(empty_vector);
  this->local_symbol_is_micromips_.swap(empty_vector2);

  // Read the symbol table section header.
  const unsigned int symtab_shndx = this->symtab_shndx();
  elfcpp::Shdr<size, big_endian>
      symtabshdr(this, this->elf_file()->section_header(symtab_shndx));
  gold_assert(symtabshdr.get_sh_type() == elfcpp::SHT_SYMTAB);

  // Read the local symbols.
  const int sym_size = elfcpp::Elf_sizes<size>::sym_size;
  gold_assert(loccount == symtabshdr.get_sh_info());
  off_t locsize = loccount * sym_size;
  const unsigned char* psyms = this->get_view(symtabshdr.get_sh_offset(),
                                              locsize, true, true);

  // Loop over the local symbols and mark any MIPS16 or microMIPS local symbols.

  // Skip the first dummy symbol.
  psyms += sym_size;
  for (unsigned int i = 1; i < loccount; ++i, psyms += sym_size)
    {
      elfcpp::Sym<size, big_endian> sym(psyms);
      unsigned char st_other = sym.get_st_other();
      this->local_symbol_is_mips16_[i] = elfcpp::elf_st_is_mips16(st_other);
      this->local_symbol_is_micromips_[i] = elfcpp::elf_st_is_micromips(st_other);
    }
}

// Read the symbol information.

template<int size, bool big_endian>
void
Mips_relobj<size, big_endian>::do_read_symbols(Read_symbols_data* sd)
{
  // Call parent class to read symbol information.
  Sized_relobj_file<size, big_endian>::do_read_symbols(sd);

  // Read processor-specific flags in ELF file header.
  const unsigned char* pehdr = this->get_view(elfcpp::file_header_offset,
                                              elfcpp::Elf_sizes<size>::ehdr_size,
                                              true, false);
  elfcpp::Ehdr<size, big_endian> ehdr(pehdr);
  this->processor_specific_flags_ = ehdr.get_e_flags();

  if (size == 32)
    {
      // Go over the section headers and look for .reginfo section.
      // The .reginfo section is not used in the 64-bit MIPS ELF ABI.
      const size_t shdr_size = elfcpp::Elf_sizes<size>::shdr_size;
      const unsigned char* pshdrs = sd->section_headers->data();
      const unsigned char* ps = pshdrs + shdr_size;
      for (unsigned int i = 1; i < this->shnum(); ++i, ps += shdr_size)
        {
          elfcpp::Shdr<size, big_endian> shdr(ps);

          if (shdr.get_sh_type() == elfcpp::SHT_MIPS_REGINFO)
            {
              section_offset_type section_offset = shdr.get_sh_offset();
              section_size_type section_size =
                convert_to_section_size_type(shdr.get_sh_size());
              const unsigned char* view =
                 this->get_view(section_offset, section_size, true, false);

              // Read gp value that was used to create this object.
              this->gp_ = elfcpp::Swap<size, big_endian>::readval(view + 20);
            }
        }
    }
  else if (size == 64)
    {
      // TODO(sasa): In the 64 bit ABI, the .MIPS.options section holds register
      // information.
    }
}

// Mips_output_data_la25_stub methods.

// TODO(sasa): Micromips has different la25 stubs.
template<int size, bool big_endian>
const uint32_t Mips_output_data_la25_stub<size, big_endian>::la25_stub_entry[4] =
{
  0x3c190000,           // lui $25,%hi(func)
  0x08000000,           // j func
  0x27390000,           // add $25,$25,%lo(func)
  0x00000000            // nop
};

// Add la25 stub for a symbol.

template<int size, bool big_endian>
void
Mips_output_data_la25_stub<size, big_endian>::add_la25_stub(Symbol_table* symtab,
                                        Target_mips<size, big_endian>* target,
                                        Symbol* gsym)
{
  Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(gsym);
  if (!mips_sym->has_la25_stub())
    {
      mips_sym->set_has_la25_stub();
      mips_sym->set_la25_stub_offset(this->symbols_.size() * 16);
      this->symbols_.insert(gsym);
      this->create_stub_symbol(mips_sym, symtab, target, 16);
    }
}

// We're going to create a stub for MIPS_SYM.  Create a symbol for the stub's
// value and size, to help make the disassembly easier to read.

template<int size, bool big_endian>
Symbol*
Mips_output_data_la25_stub<size, big_endian>::create_stub_symbol(
    Mips_symbol<size>* mips_sym, Symbol_table* symtab,
    Target_mips<size, big_endian>* target, uint64_t symsize)
{
  Symbol* sym;
  char* buffer = new char[strlen(mips_sym->name()) + 6];
  sprintf(buffer, ".pic.%s", mips_sym->name());

  unsigned int offset = mips_sym->la25_stub_offset();
  if (mips_sym->is_micromips())
    offset |= 1;

  // Make it a local function.
  sym = symtab->define_in_output_data(buffer, NULL,
                                      Symbol_table::PREDEFINED,
                                      target->la25_stub_section(),
                                      offset, symsize, elfcpp::STT_FUNC,
                                      elfcpp::STB_LOCAL,
                                      elfcpp::STV_DEFAULT, 0,
                                      false, false);
  sym->set_is_forced_local();
  return sym;
}

// Write out the STUB.  This uses the hand-coded instructions above,
// and adjusts them as needed.

template<int size, bool big_endian>
void
Mips_output_data_la25_stub<size, big_endian>::do_write(Output_file* of)
{
  const off_t offset = this->offset();
  const section_size_type oview_size =
    convert_to_section_size_type(this->data_size());
  unsigned char* const oview = of->get_output_view(offset, oview_size);

  for (typename Unordered_set<Symbol*>::iterator
       p = this->symbols_.begin();
       p != this->symbols_.end();
       ++p)
    {
      Mips_symbol<size> *sym = Mips_symbol<size>::as_mips_sym(*p);
      unsigned char* pov = oview + sym->la25_stub_offset();

      unsigned int value = (unsigned int)sym->value();
      gold_assert(offset >= 0 && offset < 0x0fffffff);
      uint32_t stub_insn0 = la25_stub_entry[0] | (((value + 0x8000) >> 16) & 0xffff);
      elfcpp::Swap<32, big_endian>::writeval(pov, stub_insn0);
      uint32_t stub_insn1 = la25_stub_entry[1] | (((value >> 2) & 0x03ffffff));
      elfcpp::Swap<32, big_endian>::writeval(pov + 4, stub_insn1);
      uint32_t stub_insn2 = la25_stub_entry[2] | ((value & 0x0000ffff));
      elfcpp::Swap<32, big_endian>::writeval(pov + 8, stub_insn2);
      uint32_t stub_insn3 = la25_stub_entry[3];
      elfcpp::Swap<32, big_endian>::writeval(pov + 12, stub_insn3);
    }

  of->write_output_view(offset, oview_size, oview);
}

// Mips_output_data_plt methods.

// The format of the first PLT entry in an O32 executable.
template<int size, bool big_endian>
const uint32_t Mips_output_data_plt<size, big_endian>::plt0_entry_o32[8] =
{
  0x3c1c0000,         // lui $28, %hi(&GOTPLT[0])
  0x8f990000,         // lw $25, %lo(&GOTPLT[0])($28)
  0x279c0000,         // addiu $28, $28, %lo(&GOTPLT[0])
  0x031cc023,         // subu $24, $24, $28
  0x03e07821,         // move $15, $31        # 32-bit move (addu)
  0x0018c082,         // srl $24, $24, 2
  0x0320f809,         // jalr $25
  0x2718fffe          // subu $24, $24, 2
};

// The format of the first PLT entry in an N32 executable.  Different
// because gp ($28) is not available; we use t2 ($14) instead.
template<int size, bool big_endian>
const uint32_t Mips_output_data_plt<size, big_endian>::plt0_entry_n32[8] =
{
  0x3c0e0000,         // lui $14, %hi(&GOTPLT[0])
  0x8dd90000,         // lw $25, %lo(&GOTPLT[0])($14)
  0x25ce0000,         // addiu $14, $14, %lo(&GOTPLT[0])
  0x030ec023,         // subu $24, $24, $14
  0x03e07821,         // move $15, $31        # 32-bit move (addu)
  0x0018c082,         // srl $24, $24, 2
  0x0320f809,         // jalr $25
  0x2718fffe          // subu $24, $24, 2
};

// The format of the first PLT entry in an N64 executable.  Different
// from N32 because of the increased size of GOT entries.
template<int size, bool big_endian>
const uint32_t Mips_output_data_plt<size, big_endian>::plt0_entry_n64[8] =
{
  0x3c0e0000,         // lui $14, %hi(&GOTPLT[0])
  0xddd90000,         // ld $25, %lo(&GOTPLT[0])($14)
  0x25ce0000,         // addiu $14, $14, %lo(&GOTPLT[0])
  0x030ec023,         // subu $24, $24, $14
  0x03e07821,         // move $15, $31        # 64-bit move (daddu)
  0x0018c0c2,         // srl $24, $24, 3
  0x0320f809,         // jalr $25
  0x2718fffe          // subu $24, $24, 2
};

// Subsequent entries in the PLT.

template<int size, bool big_endian>
const uint32_t Mips_output_data_plt<size, big_endian>::plt_entry[4] =
{
  0x3c0f0000,           // lui $15, %hi(.got.plt entry)
  0x8df90000,           // l[wd] $25, %lo(.got.plt entry)($15)
  0x03200008,           // jr $25
  0x25f80000            // addiu $24, $15, %lo(.got.plt entry)
};

// Create the PLT section.  The ordinary .got section is an argument,
// since we need to refer to the start.

template<int size, bool big_endian>
Mips_output_data_plt<size, big_endian>::Mips_output_data_plt(Layout* layout,
                                                     Output_data_space* got_plt)
  : Output_section_data(size == 32 ? 4 : 8), got_plt_(got_plt), count_(0)
{
  this->rel_ = new Reloc_section(false);
  layout->add_output_section_data(".rel.plt", elfcpp::SHT_REL,
                                  elfcpp::SHF_ALLOC, this->rel_,
                                  ORDER_DYNAMIC_PLT_RELOCS, false);
}

template<int size, bool big_endian>
void
Mips_output_data_plt<size, big_endian>::do_adjust_output_section(
    Output_section* os)
{ os->set_entsize(0); }

// Add an entry to the PLT.

template<int size, bool big_endian>
void
Mips_output_data_plt<size, big_endian>::add_entry(Symbol* gsym)
{
  gold_assert(!gsym->has_plt_offset());

  gsym->set_plt_offset(this->count_ * sizeof(plt_entry)
                       + sizeof(plt0_entry_o32));

  ++this->count_;

  section_offset_type got_offset = this->got_plt_->current_data_size();

  // Every PLT entry needs a GOT entry which points back to the PLT
  // entry (this will be changed by the dynamic linker, normally
  // lazily when the function is called).
  this->got_plt_->set_current_data_size(got_offset + 4);

  gsym->set_needs_dynsym_entry();
  this->rel_->add_global(gsym, elfcpp::R_MIPS_JUMP_SLOT, this->got_plt_,
                         got_offset);
}

// Write out the PLT.  This uses the hand-coded instructions above,
// and adjusts them as needed.

template<int size, bool big_endian>
void
Mips_output_data_plt<size, big_endian>::do_write(Output_file* of)
{
  typedef typename elfcpp::Elf_types<size>::Elf_Addr Mips_address;

  // Read processor-specific flags in ELF file header.
  const unsigned char* pehdr = of->get_output_view(elfcpp::file_header_offset,
                                   elfcpp::Elf_sizes<size>::ehdr_size);
  elfcpp::Ehdr<size, big_endian> ehdr(pehdr);
  bool n32 = elfcpp::abi_n32(ehdr.get_e_flags());
  bool n64 = elfcpp::abi_64(ehdr.get_e_ident()[elfcpp::EI_CLASS]);

  const off_t offset = this->offset();
  const section_size_type oview_size =
    convert_to_section_size_type(this->data_size());
  unsigned char* const oview = of->get_output_view(offset, oview_size);

  const off_t got_file_offset = this->got_plt_->offset();
  const section_size_type got_size =
    convert_to_section_size_type(this->got_plt_->data_size());
  unsigned char* const got_view = of->get_output_view(got_file_offset,
                                                      got_size);
  unsigned char* pov = oview;

  Mips_address plt_address = this->address();
  Mips_address got_address = this->got_plt_->address();

  const uint32_t *plt0_entry;
  if (n64)
    plt0_entry = plt0_entry_n64;
  else if (n32)
    plt0_entry = plt0_entry_n32;
  else
    plt0_entry = plt0_entry_o32;

  uint32_t plt_insn0 = plt0_entry[0] | (((got_address + 0x8000) >> 16) & 0xffff);
  elfcpp::Swap<32, big_endian>::writeval(pov, plt_insn0);
  uint32_t plt_insn1 = plt0_entry[1] | (got_address & 0xffff);
  elfcpp::Swap<32, big_endian>::writeval(pov + 4, plt_insn1);
  uint32_t plt_insn2 = plt0_entry[2] | (got_address & 0xffff);
  elfcpp::Swap<32, big_endian>::writeval(pov + 8, plt_insn2);

  for (size_t i = 3; i < 8; i++)
    elfcpp::Swap<32, big_endian>::writeval(pov + i * 4, plt0_entry[i]);

  pov += sizeof(plt0_entry_o32);

  unsigned char* got_pov = got_view;

  memset(got_pov, 0, 8);
  got_pov += 8;

  const int rel_size = elfcpp::Elf_sizes<32>::rel_size;
  unsigned int plt_offset = sizeof(plt0_entry_o32);
  unsigned int plt_rel_offset = 0;
  unsigned int got_offset = 8;
  const unsigned int count = this->count_;
  for (unsigned int i = 0;
       i < count;
       ++i,
         pov += sizeof(plt_entry),
         got_pov += 4,
         plt_offset += sizeof(plt_entry),
         plt_rel_offset += rel_size,
         got_offset += 4)
    {
      // Set and adjust the PLT entry itself.
      int32_t offset = (got_address + got_offset);

      uint32_t plt_insn0 = plt_entry[0] | (((offset + 0x8000) >> 16) & 0xffff);
      elfcpp::Swap<32, big_endian>::writeval(pov, plt_insn0);
      uint32_t plt_insn1 = plt_entry[1] | (offset & 0xffff);
      elfcpp::Swap<32, big_endian>::writeval(pov + 4, plt_insn1);
      uint32_t plt_insn2 = plt_entry[2];
      elfcpp::Swap<32, big_endian>::writeval(pov + 8, plt_insn2);
      uint32_t plt_insn3 = plt_entry[3] | (offset & 0xffff);
      elfcpp::Swap<32, big_endian>::writeval(pov + 12, plt_insn3);

      // Set the entry in the GOT.
      elfcpp::Swap<32, big_endian>::writeval(got_pov, plt_address);
    }

  gold_assert(static_cast<section_size_type>(pov - oview) == oview_size);
  gold_assert(static_cast<section_size_type>(got_pov - got_view) == got_size);

  of->write_output_view(offset, oview_size, oview);
  of->write_output_view(got_file_offset, got_size, got_view);
}

// Mips_output_data_mips_stubs methods.

// The format of the lazy binding stub when dynamic symbol count is less than
// 64K, dynamic symbol index is less than 32K, and ABI is not N64.
template<int size, bool big_endian>
const uint32_t Mips_output_data_mips_stubs<size, big_endian>::lazy_stub_normal_1[4] =
{
  0x8f998010,         // lw t9,0x8010(gp)
  0x03e07821,         // addu t7,ra,zero
  0x0320f809,         // jalr t9,ra
  0x24180000          // addiu t8,zero,DYN_INDEX sign extended
};

// Same as above, except that ABI is N64.
template<int size, bool big_endian>
const uint32_t Mips_output_data_mips_stubs<size, big_endian>::lazy_stub_normal_1_n64[4] =
{
  0xdf998010,         // ld t9,0x8010(gp)
  0x03e0782d,         // daddu t7,ra,zero
  0x0320f809,         // jalr t9,ra
  0x64180000          // daddiu t8,zero,DYN_INDEX sign extended
};

// The format of the lazy binding stub when dynamic symbol count is less than
// 64K, dynamic symbol index is between 32K and 64K, and ABI is not N64.
template<int size, bool big_endian>
const uint32_t Mips_output_data_mips_stubs<size, big_endian>::lazy_stub_normal_2[4] =
{
  0x8f998010,         // lw t9,0x8010(gp)
  0x03e07821,         // addu t7,ra,zero
  0x0320f809,         // jalr t9,ra
  0x34180000          // ori t8,zero,DYN_INDEX unsigned
};

// Same as above, except that ABI is N64.
template<int size, bool big_endian>
const uint32_t Mips_output_data_mips_stubs<size, big_endian>::lazy_stub_normal_2_n64[4] =
{
  0xdf998010,         // ld t9,0x8010(gp)
  0x03e0782d,         // daddu t7,ra,zero
  0x0320f809,         // jalr t9,ra
  0x34180000          // ori t8,zero,DYN_INDEX unsigned
};

// The format of the lazy binding stub when dynamic symbol count is greater than
// 64K, and ABI is not N64.
template<int size, bool big_endian>
const uint32_t Mips_output_data_mips_stubs<size, big_endian>::lazy_stub_big[5] =
{
  0x8f998010,         // lw t9,0x8010(gp)
  0x03e07821,         // addu t7,ra,zero
  0x3c180000,         // lui t8,DYN_INDEX
  0x0320f809,         // jalr t9,ra
  0x37180000          // ori t8,t8,DYN_INDEX
};

// Same as above, except that ABI is N64.
template<int size, bool big_endian>
const uint32_t Mips_output_data_mips_stubs<size, big_endian>::lazy_stub_big_n64[5] =
{
  0xdf998010,         // ld t9,0x8010(gp)
  0x03e0782d,         // daddu t7,ra,zero
  0x3c180000,         // lui t8,DYN_INDEX
  0x0320f809,         // jalr t9,ra
  0x37180000          // ori t8,t8,DYN_INDEX
};

template<int size, bool big_endian>
void
Mips_output_data_mips_stubs<size, big_endian>::do_adjust_output_section(
    Output_section* os)
{ os->set_entsize(0); }

// Add an entry to the .MIPS.stubs.

template<int size, bool big_endian>
void
Mips_output_data_mips_stubs<size, big_endian>::add_entry(Symbol* sym)
{
  Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(sym);
  gold_assert(!mips_sym->has_plt_offset());
  if (!mips_sym->has_lazy_stub())
    {
      mips_sym->set_has_lazy_stub(true);
      this->symbols_.insert(mips_sym);
    }
}

// Remove entry for a symbol.
template<int size, bool big_endian>
void
Mips_output_data_mips_stubs<size, big_endian>::remove_entry(Symbol *sym)
{
  Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(sym);
  if (mips_sym->has_lazy_stub())
    {
      mips_sym->set_has_lazy_stub(false);
      this->symbols_.erase(mips_sym);
    }
}

template<int size, bool big_endian>
void
Mips_output_data_mips_stubs<size, big_endian>::set_lazy_stub_offsets()
{
  if (this->stub_offsets_are_set_)
    return;

  gold_assert(this->dynsym_count_ != -1U);

  int i = 0;
  for (Unordered_set<Symbol*>::const_iterator p = this->symbols_.begin();
       p != this->symbols_.end(); ++p, ++i)
    {
      Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(*p);
      if (this->dynsym_count_ > 0x10000)
        mips_sym->set_lazy_stub_offset(20 * i);
      else
        mips_sym->set_lazy_stub_offset(16 * i);

      this->stub_offsets_are_set_ = true;
    }
}

template<int size, bool big_endian>
void
Mips_output_data_mips_stubs<size, big_endian>::set_needs_dynsym_value()
{
  for (Unordered_set<Symbol*>::const_iterator p = this->symbols_.begin();
       p != this->symbols_.end(); ++p)
    {
      Symbol *sym = *p;
      if (sym->is_from_dynobj())
        sym->set_needs_dynsym_value();
    }
}

// Write out the .MIPS.stubs.  This uses the hand-coded instructions and
// adjusts them as needed.

template<int size, bool big_endian>
void
Mips_output_data_mips_stubs<size, big_endian>::do_write(Output_file* of)
{
  // Read processor-specific flags in ELF file header.
  const unsigned char* pehdr = of->get_output_view(elfcpp::file_header_offset,
                                   elfcpp::Elf_sizes<size>::ehdr_size);
  elfcpp::Ehdr<size, big_endian> ehdr(pehdr);
  bool n64 = elfcpp::abi_64(ehdr.get_e_ident()[elfcpp::EI_CLASS]);

  const off_t offset = this->offset();
  const section_size_type oview_size =
    convert_to_section_size_type(this->data_size());
  unsigned char* const oview = of->get_output_view(offset, oview_size);

  bool big_stub = this->dynsym_count_ > 0x10000;
  for (Unordered_set<Symbol*>::const_iterator p = this->symbols_.begin();
       p != this->symbols_.end(); ++p)
    {
      Mips_symbol<size> *sym = Mips_symbol<size>::as_mips_sym(*p);
      const uint32_t *lazy_stub;
      if (!big_stub)
        {
          if (sym->dynsym_index() & ~0x7fff)
            // Dynsym index is between 32K and 64K.
            lazy_stub = n64 ? lazy_stub_normal_2_n64 : lazy_stub_normal_2;
          else
            // Dynsym index is less than 32K.
            lazy_stub = n64 ? lazy_stub_normal_1_n64 : lazy_stub_normal_1;
        }
      else
        lazy_stub = n64 ? lazy_stub_big_n64 : lazy_stub_big;

      unsigned char *pov = oview + sym->lazy_stub_offset();
      unsigned int off = 0;
      elfcpp::Swap<32, big_endian>::writeval(pov + off, lazy_stub[off/4]);
      off += 4;
      elfcpp::Swap<32, big_endian>::writeval(pov + off, lazy_stub[off/4]);
      off += 4;
      uint32_t inst;
      if (big_stub)
        {
          // LUI instruction of the big stub. Paste high 16 bits of the
          // dynsym index.
          inst = lazy_stub[off/4] | ((sym->dynsym_index() >> 16) & 0x7fff);
          elfcpp::Swap<32, big_endian>::writeval(pov + off, inst);
          off += 4;
        }
      elfcpp::Swap<32, big_endian>::writeval(pov + off, lazy_stub[off/4]);
      off += 4;
      // Last stub instruction. Paste low 16 bits of the dynsym index.
      inst = lazy_stub[off/4] | (sym->dynsym_index() & 0xffff);
      elfcpp::Swap<32, big_endian>::writeval(pov + off, inst);
    }

  // We always allocate 20 bytes for every stub, because final dynsym count is
  // not known in method do_finalize_sections. There are 4 unused bytes per stub
  // if final dynsym count is less than 0x10000.
  // TODO(sasa): Can we strip unused bytes during the relaxation?
  unsigned int used = this->symbols_.size() * (big_stub ? 20 : 16);
  unsigned int unused = big_stub ? 0 : this->symbols_.size() * 4;
  gold_assert(static_cast<section_size_type>(used + unused) == oview_size);

  of->write_output_view(offset, oview_size, oview);
}

// Mips_output_section_reginfo methods.

template<int size, bool big_endian>
void
Mips_output_section_reginfo<size, big_endian>::do_write(Output_file* of)
{
  typedef typename elfcpp::Swap<size, big_endian>::Valtype Valtype;
  Valtype gprmask = 0, cprmask1 = 0, cprmask2 = 0, cprmask3 = 0, cprmask4 = 0;

  for (Input_section_list::const_iterator p = this->input_sections().begin();
       p != this->input_sections().end();
       ++p)
    {
      Relobj* relobj = p->relobj();
      unsigned int shndx = p->shndx();

      section_size_type section_size;
      const unsigned char* section_contents =
        relobj->section_contents(shndx, &section_size, false);

      gprmask |= elfcpp::Swap<size, big_endian>::readval(section_contents);
      cprmask1 |= elfcpp::Swap<size, big_endian>::readval(section_contents + 4);
      cprmask2 |= elfcpp::Swap<size, big_endian>::readval(section_contents + 8);
      cprmask3 |= elfcpp::Swap<size, big_endian>::readval(section_contents + 12);
      cprmask4 |= elfcpp::Swap<size, big_endian>::readval(section_contents + 16);
    }

  off_t offset = this->offset();
  off_t data_size = this->data_size();

  unsigned char* view = of->get_output_view(offset, data_size);
  elfcpp::Swap<size, big_endian>::writeval(view, gprmask);
  elfcpp::Swap<size, big_endian>::writeval(view + 4, cprmask1);
  elfcpp::Swap<size, big_endian>::writeval(view + 8, cprmask2);
  elfcpp::Swap<size, big_endian>::writeval(view + 12, cprmask3);
  elfcpp::Swap<size, big_endian>::writeval(view + 16, cprmask4);
  // Write the gp value.
  elfcpp::Swap<size, big_endian>::writeval(view + 20, target_->gp_value());

  of->write_output_view(offset, data_size, view);
}

// Target_mips methods.

// Return the value to use for a dynamic symbol which requires special
// treatment.  This is how we support equality comparisons of function
// pointers across shared library boundaries, as described in the
// processor specific ABI supplement.

template<int size, bool big_endian>
uint64_t
Target_mips<size, big_endian>::do_dynsym_value(const Symbol* gsym) const
{
  uint64_t value = 0;
  const Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(gsym);

  if (!mips_sym->has_lazy_stub())
    {
      if (mips_sym->has_plt_offset())
        {
          // We distinguish between PLT entries and lazy-binding stubs by
          // giving the former an st_other value of STO_MIPS_PLT.  Set the
          // value to the stub address if there are any relocations in the
          // binary where pointer equality matters.
          if (mips_sym->pointer_equality_needed())
            value = this->plt_section()->address() + mips_sym->plt_offset();
          else
            value = 0;
        }
    }
  else
    {
      this->mips_stubs()->set_lazy_stub_offsets();
      // The run-time linker uses the st_value field of the symbol
      // to reset the global offset table entry for this external
      // to its stub address when unlinking a shared object.
      value = this->mips_stubs()->address() + mips_sym->lazy_stub_offset();
    }

  Mips16_stub_section *fn_stub_section = this->get_mips16_fn_stub(mips_sym);
  if (fn_stub_section != NULL)
    // If we have a MIPS16 function with a stub, the dynamic symbol must
    // refer to the stub, since only the stub uses the standard calling
    // conventions.
    value = fn_stub_section->output_section()->address() + fn_stub_section->output_section_offset();

  return value;
}

// Get the dynamic reloc section, creating it if necessary.

template<int size, bool big_endian>
typename Target_mips<size, big_endian>::Reloc_section*
Target_mips<size, big_endian>::rel_dyn_section(Layout* layout)
{
  if (this->rel_dyn_ == NULL)
    {
      gold_assert(layout != NULL);
      this->rel_dyn_ = new Reloc_section(true/*parameters->options().combreloc()*/);
      layout->add_output_section_data(".rel.dyn", elfcpp::SHT_REL,
                                      elfcpp::SHF_ALLOC, this->rel_dyn_,
                                      ORDER_DYNAMIC_RELOCS, false);

      // First entry in .rel.dyn has to be null.
      // This is hack - we define dummy output data and set its address to 0,
      // and define absolute R_MIPS_NONE relocation with offset 0 against it.
      // This ensures that the entry is null.
      Output_data *od = new Output_data_zero_fill(0, 0);
      od->set_address(0);
      this->rel_dyn_->add_absolute(elfcpp::R_MIPS_NONE, od, 0);
    }
  return this->rel_dyn_;
}

template<int size, bool big_endian>
typename Target_mips<size, big_endian>::Reloca_section*
Target_mips<size, big_endian>::rela_dyn_section(Layout* layout)
{
  if (this->rela_dyn_ == NULL)
    {
      gold_assert(layout != NULL);
      this->rela_dyn_ = new Reloca_section(true/*parameters->options().combreloc()*/);
      layout->add_output_section_data(".rela.dyn", elfcpp::SHT_RELA,
                                      elfcpp::SHF_ALLOC, this->rela_dyn_,
                                      ORDER_DYNAMIC_RELOCS, false);
    }
  return this->rela_dyn_;
}

// Get the GOT section, creating it if necessary.

template<int size, bool big_endian>
Mips_output_data_got<size, big_endian>*
Target_mips<size, big_endian>::got_section(Symbol_table* symtab,
                                           Layout* layout)
{
  if (this->got_ == NULL)
    {
      gold_assert(symtab != NULL && layout != NULL);

      this->got_ = new Mips_output_data_got<size, big_endian>(this, symtab, layout);
      layout->add_output_section_data(".got", elfcpp::SHT_PROGBITS,
                                      elfcpp::SHF_ALLOC | elfcpp::SHF_WRITE |
                                      elfcpp::SHF_MIPS_GPREL,
                                      this->got_, ORDER_DATA, false);

      // Define _GLOBAL_OFFSET_TABLE_ at the start of the .got section.
      symtab->define_in_output_data("_GLOBAL_OFFSET_TABLE_", NULL,
                                    Symbol_table::PREDEFINED,
                                    this->got_,
                                    0, 0, elfcpp::STT_OBJECT,
                                    elfcpp::STB_GLOBAL,
                                    elfcpp::STV_DEFAULT, 0,
                                    false, false);
    }

  return this->got_;
}

// Calculate value of _gp symbol.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::set_gp(Layout* layout, Symbol_table* symtab)
{
  if (this->gp_ != NULL)
    return;

  Output_data *section = layout->find_output_section(".got");
  if (section == NULL)
    {
      // If there is no .got section, gp should be based on .sdata.
      // TODO(sasa): If there are both .got and .sdata sections, they must be together, with .got comming first.
      for (Layout::Section_list::const_iterator p = layout->section_list().begin();
           p != layout->section_list().end();
           ++p)
        {
          if (strcmp((*p)->name(), ".sdata") == 0)
            {
              section = *p;
              break;
            }
        }
    }

  Sized_symbol<size>* gp =
      static_cast<Sized_symbol<size>*>(symtab->lookup("_gp"));
  if (gp != NULL)
    {
      if (gp->source() != Symbol::IS_CONSTANT && section != NULL)
        gp->init_output_data(gp->name(), NULL, section, MIPS_GP_OFFSET, 0,
                             elfcpp::STT_OBJECT,
                             elfcpp::STB_GLOBAL,
                             elfcpp::STV_DEFAULT, 0,
                             false, false);
      this->gp_ = gp;
    }
  else if (section != NULL)
    {
      gp = static_cast<Sized_symbol<size>*>(symtab->define_in_output_data(
                                      "_gp", NULL, Symbol_table::PREDEFINED,
                                      section, MIPS_GP_OFFSET, 0,
                                      elfcpp::STT_OBJECT,
                                      elfcpp::STB_GLOBAL,
                                      elfcpp::STV_DEFAULT,
                                      0, false, false));
      this->gp_ = gp;
    }
}

// Create a PLT entry for a global symbol.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::make_plt_entry(Symbol_table* symtab,
                                              Layout* layout,
                                              Symbol* gsym)
{
  Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(gsym);
  if (mips_sym->has_lazy_stub() || gsym->has_plt_offset())
    return;

  if (this->plt_ == NULL)
    {
      // Create the GOT section first.
      this->got_section(symtab, layout);

      this->got_plt_ = new Output_data_space(4, "** GOT PLT");
      layout->add_output_section_data(".got.plt", elfcpp::SHT_PROGBITS,
                                      (elfcpp::SHF_ALLOC | elfcpp::SHF_WRITE),
                                      this->got_plt_, ORDER_DATA, false);

      // The first two entries are reserved.
      this->got_plt_->set_current_data_size(2 * 4);

      this->plt_ = new Mips_output_data_plt<size, big_endian>(layout,
                                                              this->got_plt_);
      layout->add_output_section_data(".plt", elfcpp::SHT_PROGBITS,
                                      (elfcpp::SHF_ALLOC
                                       | elfcpp::SHF_EXECINSTR),
                                      this->plt_, ORDER_PLT, false);

      // Define _PROCEDURE_LINKAGE_TABLE_ at the start of the .plt section.
      symtab->define_in_output_data("_PROCEDURE_LINKAGE_TABLE_", NULL,
                                    Symbol_table::PREDEFINED,
                                    this->plt_,
                                    0, 0, elfcpp::STT_FUNC,
                                    elfcpp::STB_LOCAL,
                                    elfcpp::STV_DEFAULT, 0,
                                    false, false);
    }

  this->plt_->add_entry(gsym);
}


// Create a .MIPS.stubs entry for a global symbol.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::make_lazy_stub_entry(Layout* layout,
                                                    Symbol* gsym)
{
  Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(gsym);
  if (mips_sym->has_lazy_stub())
    return;
  if (mips_sym->has_plt_offset())
    return;

  if (this->mips_stubs_ == NULL)
    {
      // Create the .MIPS.stubs section first.
      this->mips_stubs_ =
        new Mips_output_data_mips_stubs<size, big_endian>();

      layout->add_output_section_data(".MIPS.stubs", elfcpp::SHT_PROGBITS,
                                      (elfcpp::SHF_ALLOC
                                       | elfcpp::SHF_EXECINSTR),
                                      this->mips_stubs_, ORDER_PLT, false);
    }
  this->mips_stubs_->add_entry(mips_sym);
}

// Create LA25 stub section.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::create_la25_stub_section(Layout* layout)
{
  if (this->la25_stub_ == NULL)
    {
      this->la25_stub_ = new Mips_output_data_la25_stub<size, big_endian>();
      layout->add_output_section_data(".text", elfcpp::SHT_PROGBITS,
                                      (elfcpp::SHF_ALLOC
                                       | elfcpp::SHF_EXECINSTR
                                       | elfcpp::SHF_WRITE),
                                      this->la25_stub_, ORDER_TEXT, false);
    }
}

// Process the relocations to determine unreferenced sections for
// garbage collection.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::gc_process_relocs(
                        Symbol_table* symtab,
                        Layout* layout,
                        Sized_relobj_file<size, big_endian>* object,
                        unsigned int data_shndx,
                        unsigned int,
                        const unsigned char* prelocs,
                        size_t reloc_count,
                        Output_section* output_section,
                        bool needs_special_offset_handling,
                        size_t local_symbol_count,
                        const unsigned char* plocal_symbols)
{
  typedef Target_mips<size, big_endian> Mips;
  typedef typename Target_mips<size, big_endian>::Scan Scan;

  gold::gc_process_relocs<size, big_endian, Mips, elfcpp::SHT_REL, Scan,
                          typename Target_mips::Relocatable_size_for_reloc>(
    symtab,
    layout,
    this,
    object,
    data_shndx,
    prelocs,
    reloc_count,
    output_section,
    needs_special_offset_handling,
    local_symbol_count,
    plocal_symbols);
}

// Scan the relocations to look for symbol adjustments.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::scan_relocs(
                        Symbol_table* symtab,
                        Layout* layout,
                        Sized_relobj_file<size, big_endian>* object,
                        unsigned int data_shndx,
                        unsigned int sh_type,
                        const unsigned char* prelocs,
                        size_t reloc_count,
                        Output_section* output_section,
                        bool needs_special_offset_handling,
                        size_t local_symbol_count,
                        const unsigned char* plocal_symbols)
{
  typedef Target_mips<size, big_endian> Mips;
  typedef typename Target_mips<size, big_endian>::Scan Scan;

  if (sh_type == elfcpp::SHT_REL)
    gold::scan_relocs<size, big_endian, Mips, elfcpp::SHT_REL, Scan>(
      symtab,
      layout,
      this,
      object,
      data_shndx,
      prelocs,
      reloc_count,
      output_section,
      needs_special_offset_handling,
      local_symbol_count,
      plocal_symbols);
  else if (sh_type == elfcpp::SHT_RELA)
    gold::scan_relocs<size, big_endian, Mips, elfcpp::SHT_RELA, Scan>(
      symtab,
      layout,
      this,
      object,
      data_shndx,
      prelocs,
      reloc_count,
      output_section,
      needs_special_offset_handling,
      local_symbol_count,
      plocal_symbols);
}

template<int size, bool big_endian>
bool
Target_mips<size, big_endian>::mips_32bit_flags(elfcpp::Elf_Word flags)
{
  return ((flags & elfcpp::EF_MIPS_32BITMODE) != 0
          || (flags & elfcpp::EF_MIPS_ABI) == elfcpp::E_MIPS_ABI_O32
          || (flags & elfcpp::EF_MIPS_ABI) == elfcpp::E_MIPS_ABI_EABI32
          || (flags & elfcpp::EF_MIPS_ARCH) == elfcpp::E_MIPS_ARCH_1
          || (flags & elfcpp::EF_MIPS_ARCH) == elfcpp::E_MIPS_ARCH_2
          || (flags & elfcpp::EF_MIPS_ARCH) == elfcpp::E_MIPS_ARCH_32
          || (flags & elfcpp::EF_MIPS_ARCH) == elfcpp::E_MIPS_ARCH_32R2);
}

// Return the MACH for a MIPS e_flags value.
template<int size, bool big_endian>
unsigned int
Target_mips<size, big_endian>::elf_mips_mach(elfcpp::Elf_Word flags)
{
  switch (flags & elfcpp::EF_MIPS_MACH)
    {
    case elfcpp::E_MIPS_MACH_3900:
      return mach_mips3900;

    case elfcpp::E_MIPS_MACH_4010:
      return mach_mips4010;

    case elfcpp::E_MIPS_MACH_4100:
      return mach_mips4100;

    case elfcpp::E_MIPS_MACH_4111:
      return mach_mips4111;

    case elfcpp::E_MIPS_MACH_4120:
      return mach_mips4120;

    case elfcpp::E_MIPS_MACH_4650:
      return mach_mips4650;

    case elfcpp::E_MIPS_MACH_5400:
      return mach_mips5400;

    case elfcpp::E_MIPS_MACH_5500:
      return mach_mips5500;

    case elfcpp::E_MIPS_MACH_9000:
      return mach_mips9000;

    case elfcpp::E_MIPS_MACH_SB1:
      return mach_mips_sb1;

    case elfcpp::E_MIPS_MACH_LS2E:
      return mach_mips_loongson_2e;

    case elfcpp::E_MIPS_MACH_LS2F:
      return mach_mips_loongson_2f;

    case elfcpp::E_MIPS_MACH_LS3A:
      return mach_mips_loongson_3a;

    case elfcpp::E_MIPS_MACH_OCTEON2:
      return mach_mips_octeon2;

    case elfcpp::E_MIPS_MACH_OCTEON:
      return mach_mips_octeon;

    case elfcpp::E_MIPS_MACH_XLR:
      return mach_mips_xlr;

    default:
      switch (flags & elfcpp::EF_MIPS_ARCH)
        {
        default:
        case elfcpp::E_MIPS_ARCH_1:
          return mach_mips3000;

        case elfcpp::E_MIPS_ARCH_2:
          return mach_mips6000;

        case elfcpp::E_MIPS_ARCH_3:
          return mach_mips4000;

        case elfcpp::E_MIPS_ARCH_4:
          return mach_mips8000;

        case elfcpp::E_MIPS_ARCH_5:
          return mach_mips5;

        case elfcpp::E_MIPS_ARCH_32:
          return mach_mipsisa32;

        case elfcpp::E_MIPS_ARCH_64:
          return mach_mipsisa64;

        case elfcpp::E_MIPS_ARCH_32R2:
          return mach_mipsisa32r2;

        case elfcpp::E_MIPS_ARCH_64R2:
          return mach_mipsisa64r2;
        }
    }

  return 0;
}

// Check whether machine EXTENSION is an extension of machine BASE.
template<int size, bool big_endian>
bool
Target_mips<size, big_endian>::mips_mach_extends(unsigned int base,
                                                 unsigned int extension)
{
  if (extension == base)
    return true;

  if ((base == mach_mipsisa32)
      && this->mips_mach_extends(mach_mipsisa64, extension))
    return true;

  if ((base == mach_mipsisa32r2)
      && this->mips_mach_extends(mach_mipsisa64r2, extension))
    return true;

  for (unsigned int i = 0; i < this->mips_mach_extensions_.size(); ++i)
    if (extension == this->mips_mach_extensions_[i].first)
      {
        extension = this->mips_mach_extensions_[i].second;
        if (extension == base)
          return true;
      }

  return false;
}

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::merge_processor_specific_flags(
    const std::string& name, elfcpp::Elf_Word in_flags, unsigned char in_ei_class,
    bool dyn_obj)
{
  // If flags are not set yet, just copy them.
  if (!this->are_processor_specific_flags_set())
    {
      this->set_processor_specific_flags(in_flags);
      this->ei_class_ = in_ei_class;
      this->mach_ = this->elf_mips_mach(in_flags);
      return;
    }

  elfcpp::Elf_Word new_flags = in_flags;
  elfcpp::Elf_Word old_flags = this->processor_specific_flags();
  elfcpp::Elf_Word merged_flags = this->processor_specific_flags();
  merged_flags |= new_flags & elfcpp::EF_MIPS_NOREORDER;

  // Check flag compatibility.
  new_flags &= ~elfcpp::EF_MIPS_NOREORDER;
  old_flags &= ~elfcpp::EF_MIPS_NOREORDER;

  // Some IRIX 6 BSD-compatibility objects have this bit set.  It
  // doesn't seem to matter.
  new_flags &= ~elfcpp::EF_MIPS_XGOT;
  old_flags &= ~elfcpp::EF_MIPS_XGOT;

  // MIPSpro generates ucode info in n64 objects.  Again, we should
  // just be able to ignore this.
  new_flags &= ~elfcpp::EF_MIPS_UCODE;
  old_flags &= ~elfcpp::EF_MIPS_UCODE;

  // DSOs should only be linked with CPIC code.
  if (dyn_obj)
    new_flags |= elfcpp::EF_MIPS_PIC | elfcpp::EF_MIPS_CPIC;

  if (new_flags == old_flags)
    {
      this->set_processor_specific_flags(merged_flags);
      return;
    }

  if (((new_flags & (elfcpp::EF_MIPS_PIC | elfcpp::EF_MIPS_CPIC)) != 0)
      != ((old_flags & (elfcpp::EF_MIPS_PIC | elfcpp::EF_MIPS_CPIC)) != 0))
    gold_warning(_("%s: linking abicalls files with non-abicalls files"), name.c_str());

  if (new_flags & (elfcpp::EF_MIPS_PIC | elfcpp::EF_MIPS_CPIC))
    merged_flags |= elfcpp::EF_MIPS_CPIC;
  if (!(new_flags & elfcpp::EF_MIPS_PIC))
    merged_flags &= ~elfcpp::EF_MIPS_PIC;

  new_flags &= ~(elfcpp::EF_MIPS_PIC | elfcpp::EF_MIPS_CPIC);
  old_flags &= ~(elfcpp::EF_MIPS_PIC | elfcpp::EF_MIPS_CPIC);

  // Compare the ISAs.
  if (mips_32bit_flags(old_flags) != mips_32bit_flags(new_flags))
    gold_error(_("%s: linking 32-bit code with 64-bit code"), name.c_str());
  else if (!this->mips_mach_extends(this->elf_mips_mach(in_flags), this->mach_))
    {
      // Output ISA isn't the same as, or an extension of, input ISA.
      if (this->mips_mach_extends(this->mach_, this->elf_mips_mach(in_flags)))
        {
          // Copy the architecture info from input object to output.  Also copy
          // the 32-bit flag (if set) so that we continue to recognise
          // output as a 32-bit binary.
          this->mach_ = this->elf_mips_mach(in_flags);
          merged_flags &= ~(elfcpp::EF_MIPS_ARCH | elfcpp::EF_MIPS_MACH);
          merged_flags |=
              new_flags & (elfcpp::EF_MIPS_ARCH | elfcpp::EF_MIPS_MACH | elfcpp::EF_MIPS_32BITMODE);

          // Copy across the ABI flags if output doesn't use them
          // and if that was what caused us to treat input object as 32-bit.
          if ((old_flags & elfcpp::EF_MIPS_ABI) == 0
              && this->mips_32bit_flags(new_flags)
              && !this->mips_32bit_flags(new_flags & ~elfcpp::EF_MIPS_ABI))
            merged_flags |= new_flags & elfcpp::EF_MIPS_ABI;
        }
      else
        // The ISAs aren't compatible.
        gold_error(_("%s: linking %s module with previous %s modules"),
                     name.c_str(), this->elf_mips_mach_name(in_flags),
                     this->elf_mips_mach_name(merged_flags));
    }

  new_flags &= ~(elfcpp::EF_MIPS_ARCH | elfcpp::EF_MIPS_MACH | elfcpp::EF_MIPS_32BITMODE);
  old_flags &= ~(elfcpp::EF_MIPS_ARCH | elfcpp::EF_MIPS_MACH | elfcpp::EF_MIPS_32BITMODE);

  // Compare ABIs.  The 64-bit ABI does not use EF_MIPS_ABI. But, it does set
  // EI_CLASS differently from any 32-bit ABI.
  if ((new_flags & elfcpp::EF_MIPS_ABI) != (old_flags & elfcpp::EF_MIPS_ABI)
      || (in_ei_class != this->ei_class_))
    {
      // Only error if both are set (to different values).
      if (((new_flags & elfcpp::EF_MIPS_ABI) && (old_flags & elfcpp::EF_MIPS_ABI))
          || (in_ei_class != this->ei_class_))
        gold_error(_("%s: ABI mismatch: linking %s module with previous %s modules"),
                      name.c_str(), this->elf_mips_abi_name(in_flags, in_ei_class),
                      this->elf_mips_abi_name(merged_flags, this->ei_class_));

      new_flags &= ~elfcpp::EF_MIPS_ABI;
      old_flags &= ~elfcpp::EF_MIPS_ABI;
    }

  // Compare ASEs.  Forbid linking MIPS16 and microMIPS ASE modules together
  // and allow arbitrary mixing of the remaining ASEs (retain the union).
  if ((new_flags & elfcpp::EF_MIPS_ARCH_ASE) != (old_flags & elfcpp::EF_MIPS_ARCH_ASE))
    {
      int old_micro = old_flags & elfcpp::EF_MIPS_ARCH_ASE_MICROMIPS;
      int new_micro = new_flags & elfcpp::EF_MIPS_ARCH_ASE_MICROMIPS;
      int old_m16 = old_flags & elfcpp::EF_MIPS_ARCH_ASE_M16;
      int new_m16 = new_flags & elfcpp::EF_MIPS_ARCH_ASE_M16;
      int micro_mis = old_m16 && new_micro;
      int m16_mis = old_micro && new_m16;

      if (m16_mis || micro_mis)
        gold_error(_("%s: ASE mismatch: linking %s module with previous %s modules"),
                     name.c_str(), m16_mis ? "MIPS16" : "microMIPS",
                     m16_mis ? "microMIPS" : "MIPS16");

      merged_flags |= new_flags & elfcpp::EF_MIPS_ARCH_ASE;

      new_flags &= ~ elfcpp::EF_MIPS_ARCH_ASE;
      old_flags &= ~ elfcpp::EF_MIPS_ARCH_ASE;
    }

  // Warn about any other mismatches.
  if (new_flags != old_flags)
    gold_error(_("%s: uses different e_flags (0x%x) fields than previous modules (0x%x)"),
                 name.c_str(), new_flags, old_flags);

  this->set_processor_specific_flags(merged_flags);
}

// Adjust ELF file header.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::do_adjust_elf_header(
    unsigned char* view,
    int len) const
{
  gold_assert(len == elfcpp::Elf_sizes<size>::ehdr_size);

  elfcpp::Ehdr<size, big_endian> ehdr(view);
  unsigned char e_ident[elfcpp::EI_NIDENT];
  memcpy(e_ident, ehdr.get_e_ident(), elfcpp::EI_NIDENT);

  e_ident[elfcpp::EI_CLASS] = this->ei_class_;

  elfcpp::Ehdr_write<size, big_endian> oehdr(view);
  oehdr.put_e_ident(e_ident);
}

// do_make_elf_object to override the same function in the base class.
// We need to use a target-specific sub-class of
// Sized_relobj_file<size, big_endian> to store Mips specific information.
// Hence we need to have our own ELF object creation.

template<int size, bool big_endian>
Object*
Target_mips<size, big_endian>::do_make_elf_object(
    const std::string& name,
    Input_file* input_file,
    off_t offset, const elfcpp::Ehdr<size, big_endian>& ehdr)
{
  int et = ehdr.get_e_type();
  // ET_EXEC files are valid input for --just-symbols/-R,
  // and we treat them as relocatable objects.
  if (et == elfcpp::ET_REL
      || (et == elfcpp::ET_EXEC && input_file->just_symbols()))
    {
      Mips_relobj<size, big_endian>* obj =
        new Mips_relobj<size, big_endian>(name, input_file, offset, ehdr);
      obj->setup();
      return obj;
    }
  else if (et == elfcpp::ET_DYN)
    {
      /*Sized_dynobj<size, big_endian>* obj =
        new Arm_dynobj<big_endian>(name, input_file, offset, ehdr);
      obj->setup();
      return obj;*/
      return Target::do_make_elf_object(name, input_file, offset, ehdr);
    }
  else
    {
      gold_error(_("%s: unsupported ELF file type %d"),
                 name.c_str(), et);
      return NULL;
    }
}

// Finalize the sections.

template <int size, bool big_endian>
void
Target_mips<size, big_endian>::do_finalize_sections(Layout* layout,
                                        const Input_objects* input_objects,
                                        Symbol_table* symtab)
{
  if (!parameters->doing_static_link()
      && (strcmp(parameters->options().hash_style(), "gnu") == 0
          || strcmp(parameters->options().hash_style(), "both") == 0))
    {
      // .gnu.hash and the MIPS ABI require .dynsym to be sorted in different
      // ways.  .gnu.hash needs symbols to be grouped by hash code whereas the
      // MIPS ABI requires a mapping between the GOT and the symbol table.
      gold_error(".gnu.hash is incompatible with the MIPS ABI");
    }

  // Set _gp value.
  this->set_gp(layout, symtab);

  for (Input_objects::Relobj_iterator p = input_objects->relobj_begin();
       p != input_objects->relobj_end();
       ++p)
    {
      Mips_relobj<size, big_endian>* mips_relobj =
          Mips_relobj<size, big_endian>::as_mips_relobj(*p);
      for (unsigned int i = 1; i < mips_relobj->shnum(); ++i)
        {
          const char *section_name = mips_relobj->section_name(i).c_str();
          if (strcmp(section_name, ".reginfo") == 0)
            {
              mips_relobj->set_output_section(i, NULL);
              break;
            }
        }
    }

  // Check for any mips16 stub sections that we can discard.
  if (!parameters->options().relocatable())
    {
      for (Input_objects::Relobj_iterator p = input_objects->relobj_begin();
          p != input_objects->relobj_end();
          ++p)
        {
          Mips_relobj<size, big_endian>* mips_relobj =
              Mips_relobj<size, big_endian>::as_mips_relobj(*p);
          std::map<unsigned int, Mips16_stub_section*>&
              mips16_stub_sections = mips_relobj->get_mips16_stub_sections();
          typename std::map<unsigned int, Mips16_stub_section*>
              ::const_iterator it;
          for (it = mips16_stub_sections.begin();
               it != mips16_stub_sections.end(); ++it)
            {
              Mips16_stub_section* stub_section = it->second;
              stub_section->find_target_from_relocs();
              bool discard = false;
              if (stub_section->is_for_local_function())
                {
                  if (stub_section->is_fn_stub())
                    {
                      // This stub is for a local symbol.  This stub will only be
                      // needed if there is some relocation in this object, other
                      // than a 16 bit function call, which refers to this symbol.
                      if (!mips_relobj->has_local_non_16bit_call_relocs(
                          stub_section->r_sym()))
                        discard = true;
                      else
                        mips_relobj->set_local_mips16_fn_stub(stub_section);
                    }
                  else
                    {
                      // This stub is for a local symbol.  This stub will only be
                      // needed if there is some relocation (R_MIPS16_26) in this object
                      // that refers to this symbol.
                      gold_assert(stub_section->is_call_stub() || stub_section->is_call_fp_stub());
                      if (!mips_relobj->has_local_16bit_call_relocs(
                          stub_section->r_sym()))
                        discard = true;
                      else
                        mips_relobj->set_local_mips16_call_stub(stub_section);
                    }
                }
              else
                {
                  Mips_symbol<size>* gsym =
                      Mips_symbol<size>::as_mips_sym(stub_section->gsym());
                  if (stub_section->is_fn_stub())
                    {
                      if (!this->add_mips16_fn_stub(gsym, stub_section))
                        // We already have a stub for this function.
                        discard = true;
                      else if (should_add_dynsym_entry(gsym, symtab))
                        {
                          // If we have a MIPS16 function with a stub, the dynamic symbol must
                          // refer to the stub, since only the stub uses the standard calling
                          // conventions.
                          gsym->set_need_fn_stub(true);
                          if (gsym->is_from_dynobj())
                            gsym->set_needs_dynsym_value();

                          gsym->set_symsize(mips_relobj->section_size(stub_section->shndx()));
                          gsym->set_nonvis(0); // clears MIPS16 flag from st_other.

                        }
                      if (!gsym->need_fn_stub())
                        discard = true;
                    }
                  else if (stub_section->is_call_stub())
                    {
                      if (gsym->is_mips16())
                        // We don't need the call_stub; this is a 16 bit function, so
                        // calls from other 16 bit functions are OK.
                        discard = true;
                      else if (!this->add_mips16_call_stub(gsym, stub_section))
                        // We already have a stub for this function.
                        discard = true;
                    }
                  else
                    {
                      gold_assert(stub_section->is_call_fp_stub());
                      if (gsym->is_mips16())
                        // We don't need the call_stub; this is a 16 bit function, so
                        // calls from other 16 bit functions are OK.
                        discard = true;
                      else if (!this->add_mips16_call_fp_stub(gsym, stub_section))
                        // We already have a stub for this function.
                        discard = true;
                    }
                }
              if (discard)
                mips_relobj->set_output_section(stub_section->shndx(), NULL);
            }
        }
    }

  // Merge processor-specific flags.
  for (Input_objects::Relobj_iterator p = input_objects->relobj_begin();
       p != input_objects->relobj_end();
       ++p)
    {
      Mips_relobj<size, big_endian>* relobj =
        Mips_relobj<size, big_endian>::as_mips_relobj(*p);

      Input_file::Format format = relobj->input_file()->format();
      if (format == Input_file::FORMAT_ELF)
        {
          // Read processor-specific flags in ELF file header.
          const unsigned char* pehdr = relobj->get_view(
                                            elfcpp::file_header_offset,
                                            elfcpp::Elf_sizes<size>::ehdr_size,
                                            true, false);

          elfcpp::Ehdr<size, big_endian> ehdr(pehdr);
          elfcpp::Elf_Word in_flags = ehdr.get_e_flags();
          unsigned char ei_class = ehdr.get_e_ident()[elfcpp::EI_CLASS];

          this->merge_processor_specific_flags(relobj->name(), in_flags, ei_class, false);
        }
    }

  for (Input_objects::Dynobj_iterator p = input_objects->dynobj_begin();
       p != input_objects->dynobj_end();
       ++p)
    {
      Sized_dynobj<size, big_endian>* dynobj =
                static_cast<Sized_dynobj<size, big_endian>*>(*p);

      // Read processor-specific flags.
      const unsigned char* pehdr = dynobj->get_view(elfcpp::file_header_offset,
                                           elfcpp::Elf_sizes<size>::ehdr_size,
                                           true, false);

      elfcpp::Ehdr<size, big_endian> ehdr(pehdr);
      elfcpp::Elf_Word in_flags = ehdr.get_e_flags();
      unsigned char ei_class = ehdr.get_e_ident()[elfcpp::EI_CLASS];

      this->merge_processor_specific_flags(dynobj->name(), in_flags, ei_class, true);
    }

  if (!parameters->options().relocatable() && !parameters->doing_static_link())
    // In case there is no .got section, create one.
    this->got_section(symtab, layout);

  // Emit any relocs we saved in an attempt to avoid generating COPY
  // relocs.
  if (this->copy_relocs_.any_saved_relocs())
    this->copy_relocs_.emit(this->rel_dyn_section(layout), symtab, layout, this);

  if (this->copy_relocsa_.any_saved_relocs())
    this->copy_relocsa_.emit(this->rela_dyn_section(layout), symtab, layout, this);

  // Emit dynamic relocs.
  for (typename std::vector<Dyn_reloc>::iterator p = this->dyn_relocs_.begin();
       p != this->dyn_relocs_.end();
       ++p)
    p->emit(this->rel_dyn_section(layout), this->got_section(), symtab);

  if (this->has_got_section())
    this->got_section()->lay_out_got(this, layout, symtab);

  if (this->mips_stubs() != NULL)
    this->mips_stubs()->set_needs_dynsym_value();

  // Check for functions that might need $25 to be valid on entry.
  // TODO(sasa): Can we do this without iterating over all symbols?
  typedef Symbol_visitor_check_symbols<size, big_endian> Symbol_visitor;
  symtab->for_all_symbols<size, Symbol_visitor>(Symbol_visitor(this, layout, symtab));

  // Add NULL segment.
  if (!parameters->options().relocatable())
    layout->make_output_segment(elfcpp::PT_NULL, 0);

  for (Layout::Section_list::const_iterator p = layout->section_list().begin();
       p != layout->section_list().end();
       ++p)
    {
      if ((*p)->type() == elfcpp::SHT_MIPS_REGINFO)
        {
          Mips_output_section_reginfo<size, big_endian>* reginfo =
            Mips_output_section_reginfo<size, big_endian>::as_mips_output_section_reginfo(*p);

          if (!parameters->options().relocatable())
            {
              Output_segment *reginfo_segment =
                layout->make_output_segment(elfcpp::PT_MIPS_REGINFO, elfcpp::PF_R);
              reginfo_segment->add_output_section_to_nonload(reginfo, elfcpp::PF_R);
            }
        }
    }

  // Fill in some more dynamic tags.
  // TODO(sasa): Add more dynamic tags.
  const Reloc_section* rel_plt = (this->plt_ == NULL
                                  ? NULL
                                  : this->plt_->rel_plt());
  layout->add_target_dynamic_tags(true, this->got_, rel_plt,
                                  this->rel_dyn_, true, false);

  Output_data_dynamic* const odyn = layout->dynamic_data();
  if ((odyn) &&
    (!parameters->options().relocatable() && !parameters->doing_static_link()))
  {
    unsigned int d_val;
    // This element holds a 32-bit version id for the Runtime
    // Linker Interface.  This will start at integer value 1.
    d_val = 0x01;
    odyn->add_constant(elfcpp::DT_MIPS_RLD_VERSION, d_val);

    // Dynamic flags
    d_val = elfcpp::RHF_NOTPOT;
    odyn->add_constant(elfcpp::DT_MIPS_FLAGS, d_val);

    // Save layout for using when emiting custom dynamic tags.
    this->layout_ = layout;

    // This member holds the base address of the segment.
    odyn->add_custom(elfcpp::DT_MIPS_BASE_ADDRESS);

    // This member holds the number of entries in the .dynsym section.
    odyn->add_custom(elfcpp::DT_MIPS_SYMTABNO);

    // This member holds the index of the first dynamic symbol
    // table entry that corresponds to an entry in the global offset table.
    odyn->add_custom(elfcpp::DT_MIPS_GOTSYM);

    // This member holds the number of local got entries.
    odyn->add_constant(elfcpp::DT_MIPS_LOCAL_GOTNO, this->got_->local_gotno());

    if (this->plt_ != NULL)
      // DT_MIPS_PLTGOT dynamic tag
      odyn->add_section_address(elfcpp::DT_MIPS_PLTGOT, this->got_plt_);
  }

  // @LOCALMOD-BEGIN
  // Ensure that the size of the text section is a multiple of bundle size,
  // otherwise NaClTextDyncodeCreate will reject it in case it is not.
  const int kInstructionBundleSize = 16;
  Output_section *text = layout->find_output_section(".text");
  text->set_current_data_size(align_address(text->current_data_size(),
                                            kInstructionBundleSize));
  // @LOCALMOD-END

  Target::do_finalize_sections (layout, input_objects, symtab);
 }

// Get the custom dynamic tag value.
template<int size, bool big_endian>
unsigned int
Target_mips<size, big_endian>::dynamic_tag_custom_value(elfcpp::DT tag) const
{
  Output_section *dynsym = this->layout_->find_output_section(".dynsym");
  gold_assert(dynsym != NULL);

  switch (tag)
    {
    case elfcpp::DT_MIPS_BASE_ADDRESS:
      {
        // The base address of the segment.
        typedef std::vector<Output_segment*> Segment_list;
        Segment_list segment_list;

        // Find all readable PT_LOAD segments.
        segment_list.push_back(this->layout_->find_output_segment(
            elfcpp::PT_LOAD, elfcpp::PF_R, elfcpp::PF_W | elfcpp::PF_X));
        segment_list.push_back(this->layout_->find_output_segment(
            elfcpp::PT_LOAD, elfcpp::PF_R | elfcpp::PF_X, elfcpp::PF_W));
        segment_list.push_back(this->layout_->find_output_segment(
            elfcpp::PT_LOAD, elfcpp::PF_R | elfcpp::PF_W, elfcpp::PF_X));
        segment_list.push_back(this->layout_->find_output_segment(
            elfcpp::PT_LOAD, elfcpp::PF_R | elfcpp::PF_W | elfcpp::PF_X, 0));

        unsigned int base_addr = -1U;
        for (Segment_list::const_iterator p = segment_list.begin();
             p != segment_list.end();
             ++p)
          {
            if (*p != NULL && (*p)->vaddr() < base_addr)
              base_addr = (*p)->vaddr();
          }

        return base_addr;
      }

    case elfcpp::DT_MIPS_SYMTABNO:
      // The number of entries in the .dynsym section.
      return (unsigned int)dynsym->data_size()/16;

    case elfcpp::DT_MIPS_GOTSYM:
      {
        // The index of the first dynamic symbol table entry that corresponds
        // to an entry in the global offset table.
        unsigned int min_index = this->got_->global_got_index();
        if (min_index == -1U)
          min_index = (unsigned int)dynsym->data_size()/16;
        return min_index;
      }

    default:
      gold_error(_("Unknown dynamic tag 0x%x"), (unsigned int)tag);
    }

  return (unsigned int)-1;
}

// Relocate a section.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::relocate_section(
                        const Relocate_info<size, big_endian>* relinfo,
                        unsigned int sh_type,
                        const unsigned char* prelocs,
                        size_t reloc_count,
                        Output_section* output_section,
                        bool needs_special_offset_handling,
                        unsigned char* view,
                        typename elfcpp::Elf_types<size>::Elf_Addr address,
                        section_size_type view_size,
                        const Reloc_symbol_changes* reloc_symbol_changes)
{
  typedef Target_mips<size, big_endian> Mips;
  typedef typename Target_mips<size, big_endian>::Relocate Mips_relocate;

  if (sh_type == elfcpp::SHT_REL)
    gold::relocate_section<size, big_endian, Mips, elfcpp::SHT_REL,
      Mips_relocate>(
      relinfo,
      this,
      prelocs,
      reloc_count,
      output_section,
      needs_special_offset_handling,
      view,
      address,
      view_size,
      reloc_symbol_changes);
  else if (sh_type == elfcpp::SHT_RELA)
    gold::relocate_section<size, big_endian, Mips, elfcpp::SHT_RELA,
      Mips_relocate>(
      relinfo,
      this,
      prelocs,
      reloc_count,
      output_section,
      needs_special_offset_handling,
      view,
      address,
      view_size,
     reloc_symbol_changes);
}

// Return the size of a relocation while scanning during a relocatable
// link.

template<int size, bool big_endian>
unsigned int
Target_mips<size, big_endian>::Relocatable_size_for_reloc::get_size_for_reloc(
    unsigned int r_type,
    Relobj* object)
{
  switch (r_type)
    {
    case elfcpp::R_MIPS_NONE:
    case elfcpp::R_MIPS_TLS_DTPMOD64:
    case elfcpp::R_MIPS_TLS_DTPREL64:
    case elfcpp::R_MIPS_TLS_TPREL64:
      return 0;

    case elfcpp::R_MIPS_32:
    case elfcpp::R_MIPS_TLS_DTPMOD32:
    case elfcpp::R_MIPS_TLS_DTPREL32:
    case elfcpp::R_MIPS_TLS_TPREL32:
    case elfcpp::R_MIPS_REL32:
    case elfcpp::R_MIPS_PC32:
    case elfcpp::R_MIPS_GPREL32:
    case elfcpp::R_MIPS_JALR:
      return 4;

    case elfcpp::R_MIPS_16:
    case elfcpp::R_MIPS_HI16:
    case elfcpp::R_MIPS_LO16:
    case elfcpp::R_MIPS_GPREL16:
    case elfcpp::R_MIPS16_HI16:
    case elfcpp::R_MIPS16_LO16:
    case elfcpp::R_MIPS_PC16:
    case elfcpp::R_MIPS_GOT16:
    case elfcpp::R_MIPS16_GOT16:
    case elfcpp::R_MIPS_CALL16:
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MIPS_GOT_HI16:
    case elfcpp::R_MIPS_CALL_HI16:
    case elfcpp::R_MIPS_GOT_LO16:
    case elfcpp::R_MIPS_CALL_LO16:
    case elfcpp::R_MIPS_TLS_DTPREL_HI16:
    case elfcpp::R_MIPS_TLS_DTPREL_LO16:
    case elfcpp::R_MIPS_TLS_TPREL_HI16:
    case elfcpp::R_MIPS_TLS_TPREL_LO16:
    case elfcpp::R_MIPS16_GPREL:
    case elfcpp::R_MIPS_GOT_DISP:
    case elfcpp::R_MIPS_LITERAL:
    case elfcpp::R_MIPS_GOT_PAGE:
    case elfcpp::R_MIPS_GOT_OFST:
    case elfcpp::R_MIPS_TLS_GD:
    case elfcpp::R_MIPS_TLS_LDM:
    case elfcpp::R_MIPS_TLS_GOTTPREL:
      return 2;

    // These relocations are not byte sized
    case elfcpp::R_MIPS_26:
    case elfcpp::R_MIPS16_26:
      return 4;

    case elfcpp::R_MIPS_COPY:
    case elfcpp::R_MIPS_JUMP_SLOT:
      object->error(_("unexpected reloc %u in object file"), r_type);
      return 0;

    default:
      object->error(_("unsupported reloc %u in object file"), r_type);
      return 0;
  }
}

// Scan the relocs during a relocatable link.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::scan_relocatable_relocs(
                        Symbol_table* symtab,
                        Layout* layout,
                        Sized_relobj_file<size, big_endian>* object,
                        unsigned int data_shndx,
                        unsigned int sh_type,
                        const unsigned char* prelocs,
                        size_t reloc_count,
                        Output_section* output_section,
                        bool needs_special_offset_handling,
                        size_t local_symbol_count,
                        const unsigned char* plocal_symbols,
                        Relocatable_relocs* rr)
{
  gold_assert(sh_type == elfcpp::SHT_REL);

  typedef Mips_scan_relocatable_relocs<big_endian, elfcpp::SHT_REL,
    Relocatable_size_for_reloc> Scan_relocatable_relocs;

  gold::scan_relocatable_relocs<size, big_endian, elfcpp::SHT_REL,
    Scan_relocatable_relocs>(
    symtab,
    layout,
    object,
    data_shndx,
    prelocs,
    reloc_count,
    output_section,
    needs_special_offset_handling,
    local_symbol_count,
    plocal_symbols,
    rr);
}

// Relocate a section during a relocatable link.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::relocate_for_relocatable(
                        const Relocate_info<size, big_endian>* relinfo,
                        unsigned int sh_type,
                        const unsigned char* prelocs,
                        size_t reloc_count,
                        Output_section* output_section,
                        typename elfcpp::Elf_types<32>::Elf_Off offset_in_output_section,
                        const Relocatable_relocs* rr,
                        unsigned char* view,
                        typename elfcpp::Elf_types<size>::Elf_Addr view_address,
                        section_size_type view_size,
                        unsigned char* reloc_view,
                        section_size_type reloc_view_size)
{
  gold_assert(sh_type == elfcpp::SHT_REL);

  gold::relocate_for_relocatable<size, big_endian, elfcpp::SHT_REL>(
    relinfo,
    prelocs,
    reloc_count,
    output_section,
    offset_in_output_section,
    rr,
    view,
    view_address,
    view_size,
    reloc_view,
    reloc_view_size);
}

// Perform target-specific processing in a relocatable link.  This is
// only used if we use the relocation strategy RELOC_SPECIAL.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::relocate_special_relocatable(
    const Relocate_info<size, big_endian>* relinfo,
    unsigned int sh_type,
    const unsigned char* preloc_in,
    size_t relnum,
    Output_section* output_section,
    off_t offset_in_output_section,
    unsigned char* view,
    elfcpp::Elf_types<32>::Elf_Addr view_address,
    section_size_type,
    unsigned char* preloc_out)
{
  // We can only handle REL type relocation sections.
  gold_assert(sh_type == elfcpp::SHT_REL);

  typedef typename Reloc_types<elfcpp::SHT_REL, size, big_endian>::Reloc Reltype;
  typedef typename Reloc_types<elfcpp::SHT_REL, size, big_endian>::Reloc_write
    Reltype_write;

  typedef typename elfcpp::Elf_types<32>::Elf_Addr Mips_address;
  typedef Mips_relocate_functions<size, big_endian> Reloc_funcs;

  const Mips_address invalid_address = static_cast<Mips_address>(0) - 1;

  Sized_relobj_file<size, big_endian>* object = relinfo->object;
  const unsigned int local_count = object->local_symbol_count();

  Reltype reloc(preloc_in);
  Reltype_write reloc_write(preloc_out);

  elfcpp::Elf_types<32>::Elf_WXword r_info = reloc.get_r_info();
  const unsigned int r_sym = elfcpp::elf_r_sym<size>(r_info);
  const unsigned int r_type = elfcpp::elf_r_type<size>(r_info);

  // Get the new symbol index.
  // We only use RELOC_SPECIAL strategy in local relocations.
  gold_assert(r_sym < local_count);

  // We are adjusting a section symbol.  We need to find
  // the symbol table index of the section symbol for
  // the output section corresponding to input section
  // in which this symbol is defined.
  bool is_ordinary;
  unsigned int shndx = object->local_symbol_input_shndx(r_sym, &is_ordinary);
  gold_assert(is_ordinary);
  Output_section* os = object->output_section(shndx);
  gold_assert(os != NULL);
  gold_assert(os->needs_symtab_index());
  unsigned int new_symndx = os->symtab_index();

  // Get the new offset--the location in the output section where
  // this relocation should be applied.

  Mips_address offset = reloc.get_r_offset();
  Mips_address new_offset;
  if (offset_in_output_section != invalid_address)
    new_offset = offset + offset_in_output_section;
  else
    {
      section_offset_type sot_offset =
          convert_types<section_offset_type, Mips_address>(offset);
      section_offset_type new_sot_offset =
          output_section->output_offset(object, relinfo->data_shndx,
                                        sot_offset);
      gold_assert(new_sot_offset != -1);
      new_offset = new_sot_offset;
    }

  // In an object file, r_offset is an offset within the section.
  // In an executable or dynamic object, generated by
  // --emit-relocs, r_offset is an absolute address.
  if (!parameters->options().relocatable())
    {
      new_offset += view_address;
      if (offset_in_output_section != invalid_address)
        new_offset -= offset_in_output_section;
    }

  reloc_write.put_r_offset(new_offset);
  reloc_write.put_r_info(elfcpp::elf_r_info<32>(new_symndx, r_type));

  // Handle the reloc addend.
  // The relocation uses a section symbol in the input file.
  // We are adjusting it to use a section symbol in the output
  // file.  The input section symbol refers to some address in
  // the input section.  We need the relocation in the output
  // file to refer to that same address.  This adjustment to
  // the addend is the same calculation we use for a simple
  // absolute relocation for the input section symbol.

  const Symbol_value<size>* psymval = object->local_symbol(r_sym);

  unsigned char* paddend = view + offset;
  typename Reloc_funcs::Status reloc_status = Reloc_funcs::STATUS_OKAY;
  switch (r_type)
    {
    case elfcpp::R_MIPS_26:
      reloc_status = Reloc_funcs::rel26(paddend, object, psymval,
          offset_in_output_section, true, 0, sh_type, NULL,
          false /*TODO(sasa): cross mode jump*/, r_type, this->jal_to_bal());
      break;

    default:
      gold_unreachable();
    }

  // Report any errors.
  switch (reloc_status)
    {
    case Reloc_funcs::STATUS_OKAY:
      break;
    case Reloc_funcs::STATUS_OVERFLOW:
      gold_error_at_location(relinfo, relnum, reloc.get_r_offset(),
                             _("relocation overflow"));
      break;
    case Reloc_funcs::STATUS_BAD_RELOC:
      gold_error_at_location(relinfo, relnum, reloc.get_r_offset(),
        _("unexpected opcode while processing relocation"));
      break;
    default:
      gold_unreachable();
    }
}

// Optimize the TLS relocation type based on what we know about the
// symbol.  IS_FINAL is true if the final address of this symbol is
// known at link time.

template<int size, bool big_endian>
tls::Tls_optimization
Target_mips<size, big_endian>::optimize_tls_reloc(bool, int)
{
  // FIXME: Currently we do not do any TLS optimization.
  return tls::TLSOPT_NONE;
}

// Scan a relocation for a local symbol.

template<int size, bool big_endian>
inline void
Target_mips<size, big_endian>::Scan::local(
                        Symbol_table* symtab,
                        Layout* layout,
                        Target_mips<size, big_endian>* target,
                        Sized_relobj_file<size, big_endian>* object,
                        unsigned int data_shndx,
                        Output_section* output_section,
                        const elfcpp::Rela<size, big_endian>* rela,
                        const elfcpp::Rel<size, big_endian>* rel,
                        unsigned int rel_type,
                        unsigned int r_type,
                        const elfcpp::Sym<size, big_endian>& lsym)
{
  typename elfcpp::Elf_types<size>::Elf_Addr r_offset;
  typename elfcpp::Elf_types<size>::Elf_WXword r_info;
  typename elfcpp::Elf_types<size>::Elf_Swxword r_addend;

  if (rel_type == elfcpp::SHT_RELA)
    {
      r_offset = rela->get_r_offset();
      r_info = rela->get_r_info();
      r_addend = rela->get_r_addend();
    }
  else
    {
      r_offset = rel->get_r_offset();
      r_info = rel->get_r_info();
      r_addend = 0;
    }

  unsigned int r_sym = elfcpp::elf_r_sym<size>(r_info);
  Mips_relobj<size, big_endian>* mips_object =
      Mips_relobj<size, big_endian>::as_mips_relobj(object);

  const char *section_name = object->section_name(data_shndx).c_str();
  if (is_prefix_of(".mips16.fn", section_name)
      || is_prefix_of(".mips16.call.", section_name)
      || is_prefix_of(".mips16.call.fp.", section_name))
    {
      Mips16_stub_section *stub_section =
          mips_object->get_mips16_stub_section(data_shndx);
      if (stub_section == NULL)
        {
          stub_section = new Mips16_stub_section(mips_object, data_shndx);
          mips_object->add_mips16_stub_section(stub_section);
        }

      mips16_stub_reloc* reloc = new mips16_stub_reloc(r_type, r_sym, NULL);
      stub_section->add_stub_reloc(reloc);
    }

  if (r_type == elfcpp::R_MIPS_NONE)
    // R_MIPS_NONE is used in mips16 stub sections, to define the target of the
    // mips16 stub.
    return;

  if (!mips16_call_reloc(r_type) && !section_allows_mips16_refs(section_name))
    // This reloc would need to refer to a MIPS16 hard-float stub, if
    // there is one. We ignore MIPS16 stub sections and .pdr section when
    // looking for relocs that would need to refer to MIPS16 stubs.
    mips_object->add_local_non_16bit_call(r_sym);

  if (r_type == elfcpp::R_MIPS16_26 && !section_allows_mips16_refs(section_name))
    mips_object->add_local_16bit_call(r_sym);

  switch (r_type)
    {
    case elfcpp::R_MIPS_GOT16:
    case elfcpp::R_MIPS_CALL16:
    case elfcpp::R_MIPS_CALL_HI16:
    case elfcpp::R_MIPS_CALL_LO16:
    case elfcpp::R_MIPS_GOT_HI16:
    case elfcpp::R_MIPS_GOT_LO16:
    case elfcpp::R_MIPS_GOT_PAGE:
    case elfcpp::R_MIPS_GOT_OFST:
    case elfcpp::R_MIPS_GOT_DISP:
    case elfcpp::R_MIPS_TLS_GOTTPREL:
    case elfcpp::R_MIPS_TLS_GD:
    case elfcpp::R_MIPS_TLS_LDM:
    case elfcpp::R_MIPS16_GOT16:
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MIPS16_TLS_GOTTPREL:
    case elfcpp::R_MIPS16_TLS_GD:
    case elfcpp::R_MIPS16_TLS_LDM:
    case elfcpp::R_MICROMIPS_GOT16:
    case elfcpp::R_MICROMIPS_CALL16:
    case elfcpp::R_MICROMIPS_CALL_HI16:
    case elfcpp::R_MICROMIPS_CALL_LO16:
    case elfcpp::R_MICROMIPS_GOT_HI16:
    case elfcpp::R_MICROMIPS_GOT_LO16:
    case elfcpp::R_MICROMIPS_GOT_PAGE:
    case elfcpp::R_MICROMIPS_GOT_OFST:
    case elfcpp::R_MICROMIPS_GOT_DISP:
    case elfcpp::R_MICROMIPS_TLS_GOTTPREL:
    case elfcpp::R_MICROMIPS_TLS_GD:
    case elfcpp::R_MICROMIPS_TLS_LDM:
      // We need a GOT section.
      target->got_section(symtab, layout);
      break;

    default:
      break;
    }

    if (target->call_lo16_reloc(r_type)
               || target->got_lo16_reloc(r_type)
               || target->got_disp_reloc(r_type))
      {
        // We may need a local GOT entry for this relocation.  We
        // don't count R_MIPS_GOT_PAGE because we can estimate the
        // maximum number of pages needed by looking at the size of
        // the segment.  Similar comments apply to R_MIPS*_GOT16 and
        // R_MIPS*_CALL16.  We don't count R_MIPS_GOT_HI16, or
        // R_MIPS_CALL_HI16 because these are always followed by an
        // R_MIPS_GOT_LO16 or R_MIPS_CALL_LO16.
        Mips_output_data_got<size, big_endian>* got =
          target->got_section(symtab, layout);
        unsigned int r_sym = elfcpp::elf_r_sym<size>(r_info);
        got->record_local_got_symbol(object, r_sym, r_addend, 0, -1U);
      }

  switch (r_type)
    {
    case elfcpp::R_MIPS_CALL16:
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MICROMIPS_CALL16:
      gold_error(_("CALL16 reloc at 0x%lx not against global symbol "), (unsigned long)r_offset);
      return;

    case elfcpp::R_MIPS_GOT_PAGE:
    case elfcpp::R_MICROMIPS_GOT_PAGE:
    case elfcpp::R_MIPS16_GOT16:
    case elfcpp::R_MIPS_GOT16:
    case elfcpp::R_MIPS_GOT_HI16:
    case elfcpp::R_MIPS_GOT_LO16:
    case elfcpp::R_MICROMIPS_GOT16:
    case elfcpp::R_MICROMIPS_GOT_HI16:
    case elfcpp::R_MICROMIPS_GOT_LO16:
      {
        // This relocation needs a page entry in the GOT.
        typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;

        // Get the section contents.
        section_size_type view_size = 0;
        const unsigned char *view =
          object->section_contents(data_shndx, &view_size, false);
        view += r_offset;

        Valtype val = elfcpp::Swap<32, big_endian>::readval(view);
        Valtype addend = (rel_type == elfcpp::SHT_REL) ? val & 0xffff : r_addend;

        if (rel_type == elfcpp::SHT_REL && target->got16_reloc(r_type))
          target->got16_addends.push_back(
            got16_addend<size, big_endian>(object, data_shndx, r_type, r_sym, addend));

        else
          target->got_section()->record_got_page_entry(object, r_sym, addend);
        break;
      }

    case elfcpp::R_MIPS_LO16:
    case elfcpp::R_MIPS16_LO16:
    case elfcpp::R_MICROMIPS_LO16:
      {
        if (rel_type != elfcpp::SHT_REL)
          break;

        // Find corresponding R_MIPS_GOT16 relocation, calculate combined addend
        // and record got page entry.
        typename std::list<got16_addend<size, big_endian> >::iterator it = target->got16_addends.begin();
        while (it != target->got16_addends.end())
          {
            got16_addend<size, big_endian> _got16_addend = *it;
            if (_got16_addend.object != object || _got16_addend.shndx != data_shndx)
              {
                gold_error("Can't find matching LO16 reloc");
                break;
              }

            unsigned int got16_type;
            if (r_type == elfcpp::R_MIPS16_LO16)
              got16_type = elfcpp::R_MIPS16_GOT16;
            else if (r_type == elfcpp::R_MICROMIPS_LO16)
              got16_type = elfcpp::R_MICROMIPS_GOT16;
            else
              got16_type = elfcpp::R_MIPS_GOT16;

            if (_got16_addend.r_sym != r_sym || _got16_addend.r_type != got16_type)
              {
                ++it;
                continue;
              }

            // The combined value is the sum of the HI16 addend, left-shifted by
            // sixteen bits, and the LO16 addend, sign extended.  (Usually, the
            // code does a `lui' of the HI16 value, and then an `addiu' of the
            // LO16 value.)

            // According to the MIPS ELF ABI, the R_MIPS_LO16 relocation must
            // be immediately following.  However, for the IRIX6 ABI, the next
            // relocation may be a composed relocation consisting of several
            // relocations for the same address.  In that case, the R_MIPS_LO16
            // relocation may occur as one of these.  We permit a similar
            // extension in general, as that is useful for GCC.

            // In some cases GCC dead code elimination removes the LO16 but keeps
            // the corresponding HI16.  This is strictly speaking a violation of
            // the ABI but not immediately harmful.
            typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;

            // Get the section contents.
            section_size_type view_size = 0;
            const unsigned char *view =
              object->section_contents(data_shndx, &view_size, false);
            view += r_offset;

            Valtype val = elfcpp::Swap<32, big_endian>::readval(view);
            int32_t addend = Bits<16>::sign_extend32(val & 0xffff);

            addend = (_got16_addend.addend << 16) + addend;
            target->got_section()->record_got_page_entry(object, r_sym, addend);

            it = target->got16_addends.erase(it);
          }
        break;
      }
    }

  switch (r_type)
    {
    case elfcpp::R_MIPS_32:
    case elfcpp::R_MIPS_REL32:
    case elfcpp::R_MIPS_64:
      {
        if (parameters->options().output_is_position_independent())
          {
            // If building a shared library (or a position-independent
            // executable), we need to create a dynamic relocation for
            // this location.
            Reloc_section* rel_dyn = target->rel_dyn_section(layout);
            unsigned int r_sym = elfcpp::elf_r_sym<32>(r_info);
            if (lsym.get_st_type() != elfcpp::STT_SECTION)
              rel_dyn->add_local(object, r_sym, elfcpp::R_MIPS_REL32, output_section,
                                 data_shndx, r_offset);
            else
              {
                gold_assert(lsym.get_st_value() == 0);
                rel_dyn->add_symbolless_local_addend(object, r_sym, elfcpp::R_MIPS_REL32,
                                                     output_section,
                                                     data_shndx,
                                                     r_offset);
              }
          }
        break;
      }

    case elfcpp::R_MIPS_TLS_GOTTPREL:
    case elfcpp::R_MIPS16_TLS_GOTTPREL:
    case elfcpp::R_MICROMIPS_TLS_GOTTPREL:
    case elfcpp::R_MIPS_TLS_LDM:
    case elfcpp::R_MIPS16_TLS_LDM:
    case elfcpp::R_MICROMIPS_TLS_LDM:
    case elfcpp::R_MIPS_TLS_GD:
    case elfcpp::R_MIPS16_TLS_GD:
    case elfcpp::R_MICROMIPS_TLS_GD:
      {
        unsigned int r_sym = elfcpp::elf_r_sym<size>(r_info);
        bool output_is_shared = parameters->options().shared();
        const tls::Tls_optimization optimized_type
            = Target_mips<size, big_endian>::optimize_tls_reloc(
                                             !output_is_shared, r_type);
        switch (r_type)
          {
          case elfcpp::R_MIPS_TLS_GD:
          case elfcpp::R_MIPS16_TLS_GD:
          case elfcpp::R_MICROMIPS_TLS_GD:
            if (optimized_type == tls::TLSOPT_NONE)
              {
                // Create a pair of GOT entries for the module index and
                // dtv-relative offset.
                Mips_output_data_got<size, big_endian>* got
                    = target->got_section(symtab, layout);
                unsigned int shndx = lsym.get_st_shndx();
                bool is_ordinary;
                shndx = object->adjust_sym_shndx(r_sym, shndx, &is_ordinary);
                if (!is_ordinary)
                  {
                    object->error(_("local symbol %u has bad shndx %u"),
                                  r_sym, shndx);
                    break;
                  }
                got->record_local_got_symbol(object, r_sym, r_addend, GOT_TLS_GD, shndx);
              }
            else
              // FIXME: TLS optimization not supported yet.
              gold_unreachable();
            break;

          case elfcpp::R_MIPS_TLS_LDM:
          case elfcpp::R_MIPS16_TLS_LDM:
          case elfcpp::R_MICROMIPS_TLS_LDM:
            if (optimized_type == tls::TLSOPT_NONE)
              // We always record LDM symbols as local with index 0.
              target->got_section()->record_local_got_symbol(object, 0, r_addend, GOT_TLS_LDM, -1U);
            else
              // FIXME: TLS optimization not supported yet.
              gold_unreachable();
            break;
          case elfcpp::R_MIPS_TLS_GOTTPREL:
          case elfcpp::R_MIPS16_TLS_GOTTPREL:
          case elfcpp::R_MICROMIPS_TLS_GOTTPREL:
            layout->set_has_static_tls();
            if (optimized_type == tls::TLSOPT_NONE)
              {
                // Create a GOT entry for the tp-relative offset.
                Mips_output_data_got<size, big_endian>* got
                  = target->got_section(symtab, layout);
                got->record_local_got_symbol(object, r_sym, r_addend, GOT_TLS_IE, -1U);
              }
            else
              // FIXME: TLS optimization not supported yet.
              gold_unreachable();
            break;

          default:
            gold_unreachable();
        }
      }
      break;

    default:
      //unsupported_reloc_local(object, r_type);
      break;
    }

  // Refuse some position-dependent relocations when creating a
  // shared library.  Do not refuse R_MIPS_32 / R_MIPS_64; they're
  // not PIC, but we can create dynamic relocations and the result
  // will be fine.  Also do not refuse R_MIPS_LO16, which can be
  // combined with R_MIPS_GOT16.
  if (parameters->options().shared())
    {
      switch (r_type)
        {
        case elfcpp::R_MIPS16_HI16:
        case elfcpp::R_MIPS_HI16:
        case elfcpp::R_MICROMIPS_HI16:
          // Don't refuse a high part relocation if it's against
          // no symbol (e.g. part of a compound relocation).
          if (r_sym == 0)
            break;

          // FALLTHROUGH

        case elfcpp::R_MIPS16_26:
        case elfcpp::R_MIPS_26:
        case elfcpp::R_MICROMIPS_26_S1:
          gold_error(_("%s: relocation %u against `%s' can not be used when making a shared object; recompile with -fPIC"),
              object->name().c_str(), r_type, "a local symbol");
        default:
          break;
        }
    }
}

template<int size, bool big_endian>
inline void
Target_mips<size, big_endian>::Scan::local(
                        Symbol_table* symtab,
                        Layout* layout,
                        Target_mips<size, big_endian>* target,
                        Sized_relobj_file<size, big_endian>* object,
                        unsigned int data_shndx,
                        Output_section* output_section,
                        const elfcpp::Rel<size, big_endian>& reloc,
                        unsigned int r_type,
                        const elfcpp::Sym<size, big_endian>& lsym)
{
  local(
    symtab,
    layout,
    target,
    object,
    data_shndx,
    output_section,
    (const elfcpp::Rela<size, big_endian>*) NULL,
    &reloc,
    elfcpp::SHT_REL,
    r_type,
    lsym);
}


template<int size, bool big_endian>
inline void
Target_mips<size, big_endian>::Scan::local(
                        Symbol_table* symtab,
                        Layout* layout,
                        Target_mips<size, big_endian>* target,
                        Sized_relobj_file<size, big_endian>* object,
                        unsigned int data_shndx,
                        Output_section* output_section,
                        const elfcpp::Rela<size, big_endian>& reloc,
                        unsigned int r_type,
                        const elfcpp::Sym<size, big_endian>& lsym)
{
  local(
    symtab,
    layout,
    target,
    object,
    data_shndx,
    output_section,
    &reloc,
    (const elfcpp::Rel<size, big_endian>*) NULL,
    elfcpp::SHT_RELA,
    r_type,
    lsym);
}

// Scan a relocation for a global symbol.

template<int size, bool big_endian>
inline void
Target_mips<size, big_endian>::Scan::global(
                                Symbol_table* symtab,
                                Layout* layout,
                                Target_mips<size, big_endian>* target,
                                Sized_relobj_file<size, big_endian>* object,
                                unsigned int data_shndx,
                                Output_section* output_section,
                                const elfcpp::Rela<size, big_endian>* rela,
                                const elfcpp::Rel<size, big_endian>* rel,
                                unsigned int rel_type,
                                unsigned int r_type,
                                Symbol* gsym)
{
  typename elfcpp::Elf_types<size>::Elf_Addr r_offset;
  typename elfcpp::Elf_types<size>::Elf_WXword r_info;
  typename elfcpp::Elf_types<size>::Elf_Swxword r_addend;

  if (rel_type == elfcpp::SHT_RELA)
    {
      r_offset = rela->get_r_offset();
      r_info = rela->get_r_info();
      r_addend = rela->get_r_addend();
    }
  else
    {
      r_offset = rel->get_r_offset();
      r_info = rel->get_r_info();
      r_addend = 0;
    }

  unsigned int r_sym = elfcpp::elf_r_sym<size>(r_info);
  Mips_relobj<size, big_endian>* mips_object =
      Mips_relobj<size, big_endian>::as_mips_relobj(object);
  Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(gsym);

  const char *section_name = object->section_name(data_shndx).c_str();
  if (is_prefix_of(".mips16.fn", section_name)
      || is_prefix_of(".mips16.call.", section_name)
      || is_prefix_of(".mips16.call.fp.", section_name))
    {
      Mips16_stub_section *stub_section =
          mips_object->get_mips16_stub_section(data_shndx);
      if (stub_section == NULL)
        {
          stub_section = new Mips16_stub_section(mips_object, data_shndx);
          mips_object->add_mips16_stub_section(stub_section);
        }

      mips16_stub_reloc* reloc = new mips16_stub_reloc(r_type, r_sym, gsym);
      stub_section->add_stub_reloc(reloc);
    }

  if (r_type == elfcpp::R_MIPS_NONE)
    // R_MIPS_NONE is used in mips16 stub sections, to define the target of the
    // mips16 stub.
    return;

  if (!mips16_call_reloc(r_type) && !section_allows_mips16_refs(section_name))
    // This reloc would need to refer to a MIPS16 hard-float stub, if
    // there is one. We ignore MIPS16 stub sections and .pdr section when
    // looking for relocs that would need to refer to MIPS16 stubs.
    mips_sym->set_need_fn_stub(true);

  // A reference to _GLOBAL_OFFSET_TABLE_ implies that we need a got
  // section.  We check here to avoid creating a dynamic reloc against
  // _GLOBAL_OFFSET_TABLE_.
  if (!target->has_got_section()
      && strcmp(gsym->name(), "_GLOBAL_OFFSET_TABLE_") == 0)
    target->got_section(symtab, layout);

  // We need PLT entries if there
  // are static-only relocations against an externally-defined function.
  // This can technically occur for shared libraries if there are
  // branches to the symbol, although it is unlikely that this will be
  // used in practice due to the short ranges involved.  It can occur
  // for any relative or absolute relocation in executables; in that
  // case, the PLT entry becomes the function's canonical address.
  bool static_reloc = false;

  // Set CAN_MAKE_DYNAMIC to true if we can convert this
  // relocation into a dynamic one.
  bool can_make_dynamic = false;
  switch (r_type)
    {
    case elfcpp::R_MIPS_GOT16:
    case elfcpp::R_MIPS_CALL16:
    case elfcpp::R_MIPS_CALL_HI16:
    case elfcpp::R_MIPS_CALL_LO16:
    case elfcpp::R_MIPS_GOT_HI16:
    case elfcpp::R_MIPS_GOT_LO16:
    case elfcpp::R_MIPS_GOT_PAGE:
    case elfcpp::R_MIPS_GOT_OFST:
    case elfcpp::R_MIPS_GOT_DISP:
    case elfcpp::R_MIPS_TLS_GOTTPREL:
    case elfcpp::R_MIPS_TLS_GD:
    case elfcpp::R_MIPS_TLS_LDM:
    case elfcpp::R_MIPS16_GOT16:
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MIPS16_TLS_GOTTPREL:
    case elfcpp::R_MIPS16_TLS_GD:
    case elfcpp::R_MIPS16_TLS_LDM:
    case elfcpp::R_MICROMIPS_GOT16:
    case elfcpp::R_MICROMIPS_CALL16:
    case elfcpp::R_MICROMIPS_CALL_HI16:
    case elfcpp::R_MICROMIPS_CALL_LO16:
    case elfcpp::R_MICROMIPS_GOT_HI16:
    case elfcpp::R_MICROMIPS_GOT_LO16:
    case elfcpp::R_MICROMIPS_GOT_PAGE:
    case elfcpp::R_MICROMIPS_GOT_OFST:
    case elfcpp::R_MICROMIPS_GOT_DISP:
    case elfcpp::R_MICROMIPS_TLS_GOTTPREL:
    case elfcpp::R_MICROMIPS_TLS_GD:
    case elfcpp::R_MICROMIPS_TLS_LDM:
      // We need a GOT section.
      target->got_section(symtab, layout);
      break;

    // This is just a hint; it can safely be ignored.  Don't set
    // has_static_relocs for the corresponding symbol.
    case elfcpp::R_MIPS_JALR:
    case elfcpp::R_MICROMIPS_JALR:
      break;

    case elfcpp::R_MIPS_32:
    case elfcpp::R_MIPS_REL32:
    case elfcpp::R_MIPS_64:
      if (parameters->options().shared()
          || strcmp(gsym->name(), "__gnu_local_gp") != 0)
        {
          can_make_dynamic = true;
          break;
        }
      // Fall through.

    default:
      // Most static relocations require pointer equality, except
      // for branches.
      mips_sym->set_pointer_equality_needed();

      // Fall through.

    case elfcpp::R_MIPS_26:
    case elfcpp::R_MIPS_PC16:
    case elfcpp::R_MIPS16_26:
    case elfcpp::R_MICROMIPS_26_S1:
    case elfcpp::R_MICROMIPS_PC7_S1:
    case elfcpp::R_MICROMIPS_PC10_S1:
    case elfcpp::R_MICROMIPS_PC16_S1:
    case elfcpp::R_MICROMIPS_PC23_S2:
      static_reloc = true;
      mips_sym->set_has_static_relocs();
      break;
    }

  // If there are call relocations against an externally-defined symbol,
  // see whether we can create a MIPS lazy-binding stub for it.  We can
  // only do this if all references to the function are through call
  // relocations, and in that case, the traditional lazy-binding stubs
  // are much more efficient than PLT entries.
  switch (r_type)
    {
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MIPS_CALL16:
    case elfcpp::R_MIPS_CALL_HI16:
    case elfcpp::R_MIPS_CALL_LO16:
    case elfcpp::R_MIPS_JALR:
    case elfcpp::R_MICROMIPS_CALL16:
    case elfcpp::R_MICROMIPS_CALL_HI16:
    case elfcpp::R_MICROMIPS_CALL_LO16:
    case elfcpp::R_MICROMIPS_JALR:
      if (!mips_sym->no_lazy_stub())
        {
          if ((gsym->needs_plt_entry() && gsym->is_from_dynobj())
              // Calls from shared objects to undefined symbols of type
              // STT_NOTYPE need lazy-binding stub.
              || (gsym->is_undefined() && parameters->options().shared()))
            target->make_lazy_stub_entry(layout, gsym);
        }
      break;
    default:
      {
        // We must not create a stub for a symbol that has relocations
        // related to taking the function's address.
        mips_sym->set_no_lazy_stub();
        target->remove_lazy_stub_entry(mips_sym);
        break;
      }
  }

  if (target->relocation_needs_la25_stub (mips_object, r_type,
      mips_sym->is_mips16()))
    mips_sym->set_has_nonpic_branches(true);

  // R_MIPS_HI16 against _gp_disp is used for $gp setup,
  // and has a special meaning.
  bool gp_disp_against_hi16 = !mips_object->is_newabi()
      && strcmp(gsym->name(), "_gp_disp") == 0
      && (hi16_reloc(r_type) || lo16_reloc(r_type));
  if (static_reloc && gsym->needs_plt_entry())
    {
      target->make_plt_entry(symtab, layout, gsym);

      // Since this is not a PC-relative relocation, we may be
      // taking the address of a function.  In that case we need to
      // set the entry in the dynamic symbol table to the address of
      // the PLT entry.
      if (gsym->is_from_dynobj() && !parameters->options().shared())
        {
          gsym->set_needs_dynsym_value();
          // We distinguish between PLT entries and lazy-binding stubs by
          // giving the former an st_other value of STO_MIPS_PLT.  Set the
          // flag if there are any relocations in the binary where pointer
          // equality matters.
          if (mips_sym->pointer_equality_needed())
            gsym->set_nonvis(elfcpp::STO_MIPS_PLT>>2);
        }
    }
  if ((static_reloc || can_make_dynamic) && !gp_disp_against_hi16)
    {
      // Absolute addressing relocations.
      // Make a dynamic relocation if necessary.
      if (gsym->needs_dynamic_reloc(Scan::get_reference_flags(r_type)))
        {
          if (gsym->may_need_copy_reloc())
            {
              if (rel_type == elfcpp::SHT_RELA)
                target->copy_reloc(symtab, layout, object,
                                   data_shndx, output_section, gsym, *rela);
              else
                target->copy_reloc(symtab, layout, object,
                                   data_shndx, output_section, gsym, *rel);
            }
          else if (can_make_dynamic)
            {
              // Create .rel.dyn section.
              target->rel_dyn_section(layout);
              target->dynamic_reloc(mips_sym, elfcpp::R_MIPS_REL32,
                                    object, data_shndx, output_section,
                                    r_offset);
            }
          else
            gold_error(_("non-dynamic relocations refer to dynamic symbol %s"), gsym->name());
        }
    }

  bool for_call = false;
  switch (r_type)
    {
    case elfcpp::R_MIPS_CALL16:
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MICROMIPS_CALL16:
    case elfcpp::R_MIPS_CALL_HI16:
    case elfcpp::R_MIPS_CALL_LO16:
    case elfcpp::R_MICROMIPS_CALL_HI16:
    case elfcpp::R_MICROMIPS_CALL_LO16:
      for_call = true;
      // Fall through.

    case elfcpp::R_MIPS16_GOT16:
    case elfcpp::R_MIPS_GOT16:
    case elfcpp::R_MIPS_GOT_HI16:
    case elfcpp::R_MIPS_GOT_LO16:
    case elfcpp::R_MICROMIPS_GOT16:
    case elfcpp::R_MICROMIPS_GOT_HI16:
    case elfcpp::R_MICROMIPS_GOT_LO16:
    case elfcpp::R_MIPS_GOT_DISP:
    case elfcpp::R_MICROMIPS_GOT_DISP:
      {
        // The symbol requires a GOT entry.
        Mips_output_data_got<size, big_endian> *got =
          target->got_section(symtab, layout);
        got->record_global_got_symbol(mips_sym, object, 0, false, for_call);
        mips_sym->set_global_got_area(GGA_NORMAL);
      }
      break;

    case elfcpp::R_MIPS_GOT_PAGE:
    case elfcpp::R_MICROMIPS_GOT_PAGE:
      {
        // This relocation needs a page entry in the GOT.
        typedef typename elfcpp::Swap<32, big_endian>::Valtype Valtype;

        // Get the section contents.
        section_size_type view_size = 0;
        const unsigned char *view =
          object->section_contents(data_shndx, &view_size, false);
        view += r_offset;

        Valtype val = elfcpp::Swap<32, big_endian>::readval(view);
        Valtype addend = (rel_type == elfcpp::SHT_REL) ? val & 0xffff : r_addend;
        Mips_output_data_got<size, big_endian> *got =
          target->got_section(symtab, layout);
        got->record_got_page_entry(object, r_sym, addend);

        // If this is a global, overridable symbol, GOT_PAGE will
        // decay to GOT_DISP, so we'll need a GOT entry for it.
        bool def_regular = mips_sym->source() == Symbol::FROM_OBJECT
            && !mips_sym->object()->is_dynamic() && !mips_sym->is_undefined();
        if (!def_regular
            || (parameters->options().output_is_position_independent()
                && !parameters->options().Bsymbolic()
                && !mips_sym->is_forced_local()))
          {
            got->record_global_got_symbol(mips_sym, object, 0, false, for_call);
            mips_sym->set_global_got_area(GGA_NORMAL);
          }
      }
      break;

    case elfcpp::R_MIPS_TLS_GOTTPREL:
    case elfcpp::R_MIPS16_TLS_GOTTPREL:
    case elfcpp::R_MICROMIPS_TLS_GOTTPREL:
    case elfcpp::R_MIPS_TLS_LDM:
    case elfcpp::R_MIPS16_TLS_LDM:
    case elfcpp::R_MICROMIPS_TLS_LDM:
    case elfcpp::R_MIPS_TLS_GD:
    case elfcpp::R_MIPS16_TLS_GD:
    case elfcpp::R_MICROMIPS_TLS_GD:
      {
        const bool is_final = gsym->final_value_is_known();
        const tls::Tls_optimization optimized_type =
            Target_mips<size, big_endian>::optimize_tls_reloc(is_final, r_type);

        switch (r_type)
          {
          case elfcpp::R_MIPS_TLS_GD:
          case elfcpp::R_MIPS16_TLS_GD:
          case elfcpp::R_MICROMIPS_TLS_GD:
            if (optimized_type == tls::TLSOPT_NONE)
              {
                // Create a pair of GOT entries for the module index and
                // dtv-relative offset.
                Mips_output_data_got<size, big_endian>* got
                    = target->got_section(symtab, layout);
                got->record_global_got_symbol(mips_sym, object, GOT_TLS_GD, false, false);
              }
            else
              // FIXME: TLS optimization not supported yet.
              gold_unreachable();
            break;

          case elfcpp::R_MIPS_TLS_LDM:
          case elfcpp::R_MIPS16_TLS_LDM:
          case elfcpp::R_MICROMIPS_TLS_LDM:
            if (optimized_type == tls::TLSOPT_NONE)
              // We always record LDM symbols as local with index 0.
              target->got_section()->record_local_got_symbol(object, 0, r_addend, GOT_TLS_LDM, -1U);
            else
              // FIXME: TLS optimization not supported yet.
              gold_unreachable();
            break;
          case elfcpp::R_MIPS_TLS_GOTTPREL:
          case elfcpp::R_MIPS16_TLS_GOTTPREL:
          case elfcpp::R_MICROMIPS_TLS_GOTTPREL:
            layout->set_has_static_tls();
            if (optimized_type == tls::TLSOPT_NONE)
              {
                // Create a GOT entry for the tp-relative offset.
                Mips_output_data_got<size, big_endian>* got
                  = target->got_section(symtab, layout);
                got->record_global_got_symbol(mips_sym, object, GOT_TLS_IE, false, false);
              }
            else
              // FIXME: TLS optimization not supported yet.
              gold_unreachable();
            break;

          default:
            gold_unreachable();
        }
      }
      break;
    case elfcpp::R_MIPS_COPY:
    case elfcpp::R_MIPS_JUMP_SLOT:
      // These are relocations which should only be seen by the
      // dynamic linker, and should never be seen here.
      gold_error(_("%s: unexpected reloc %u in object file"),
                 object->name().c_str(), r_type);
      break;

    default:
      //unsupported_reloc_global(object, r_type, gsym);
      break;
    }

  // Refuse some position-dependent relocations when creating a
  // shared library.  Do not refuse R_MIPS_32 / R_MIPS_64; they're
  // not PIC, but we can create dynamic relocations and the result
  // will be fine.  Also do not refuse R_MIPS_LO16, which can be
  // combined with R_MIPS_GOT16.
  if (parameters->options().shared())
    {
      switch (r_type)
        {
        case elfcpp::R_MIPS16_HI16:
        case elfcpp::R_MIPS_HI16:
        case elfcpp::R_MICROMIPS_HI16:
          // Don't refuse a high part relocation if it's against
          // no symbol (e.g. part of a compound relocation).
          if (r_sym == 0)
            break;

          // R_MIPS_HI16 against _gp_disp is used for $gp setup,
          // and has a special meaning.
          if (!mips_object->is_newabi()
              && strcmp(gsym->name(), "_gp_disp") == 0)
            break;

          // FALLTHROUGH

        case elfcpp::R_MIPS16_26:
        case elfcpp::R_MIPS_26:
        case elfcpp::R_MICROMIPS_26_S1:
          gold_error(_("%s: relocation %u against `%s' can not be used when making a shared object; recompile with -fPIC"),
              object->name().c_str(), r_type, gsym->name());
        default:
          break;
        }
    }
}

template<int size, bool big_endian>
inline void
Target_mips<size, big_endian>::Scan::global(
                                Symbol_table* symtab,
                                Layout* layout,
                                Target_mips<size, big_endian>* target,
                                Sized_relobj_file<size, big_endian>* object,
                                unsigned int data_shndx,
                                Output_section* output_section,
                                const elfcpp::Rela<size, big_endian>& reloc,
                                unsigned int r_type,
                                Symbol* gsym)
{
  global(
    symtab,
    layout,
    target,
    object,
    data_shndx,
    output_section,
    &reloc,
    (const elfcpp::Rel<size, big_endian>*) NULL,
    elfcpp::SHT_RELA,
    r_type,
    gsym);
}

template<int size, bool big_endian>
inline void
Target_mips<size, big_endian>::Scan::global(
                                Symbol_table* symtab,
                                Layout* layout,
                                Target_mips<size, big_endian>* target,
                                Sized_relobj_file<size, big_endian>* object,
                                unsigned int data_shndx,
                                Output_section* output_section,
                                const elfcpp::Rel<size, big_endian>& reloc,
                                unsigned int r_type,
                                Symbol* gsym)
{
  global(
    symtab,
    layout,
    target,
    object,
    data_shndx,
    output_section,
    (const elfcpp::Rela<size, big_endian>*) NULL,
    &reloc,
    elfcpp::SHT_REL,
    r_type,
    gsym);
}

// Return whether a R_MIPS_32 relocation needs to be applied.

template<int size, bool big_endian>
inline bool
Target_mips<size, big_endian>::Relocate::should_apply_r_mips_32_reloc(
    const Mips_symbol<size>* gsym,
    unsigned int r_type,
    Output_section* output_section,
    Target_mips* target)
{
  // If the output section is not allocated, then we didn't call
  // scan_relocs, we didn't create a dynamic reloc, and we must apply
  // the reloc here.
  if ((output_section->flags() & elfcpp::SHF_ALLOC) == 0)
      return true;

  if (gsym == NULL)
    {
      // For local symbols, we will have created a R_MIPS_REL32 dynamic
      // relocation only if the output is position independent.
      if (parameters->options().output_is_position_independent())
        // We have generated dynamic reloc (R_MIPS_REL32).
        return true;
      else
        // We have not generated dynamic reloc.
        return true;
    }
  else
    {
      // For global symbols, we use the same helper routines used in the
      // scan pass.
      if (gsym->needs_dynamic_reloc(Scan::get_reference_flags(r_type))
          && !gsym->may_need_copy_reloc())
        {
          // We have generated dynamic reloc (R_MIPS_REL32).

          bool multi_got = false;
          if (target->has_got_section())
            multi_got = target->got_section()->multi_got();
          bool has_got_offset;
          if (!multi_got)
            has_got_offset = gsym->has_got_offset(GOT_TYPE_STANDARD);
          else
            has_got_offset = gsym->global_gotoffset() != -1U;
          if (!has_got_offset)
            return true;
          else
            // Apply the relocation only if the symbol is in the local got.
            // Do not apply the relocation if the symbol is in the global
            // got.
            return symbol_references_local(gsym, gsym->has_dynsym_index());
        }
      else
        // We have not generated dynamic reloc.
        return true;
    }
}

// Perform a relocation.

template<int size, bool big_endian>
inline bool
Target_mips<size, big_endian>::Relocate::relocate(
                        const Relocate_info<size, big_endian>* relinfo,
                        Target_mips* target,
                        Output_section* output_section,
                        size_t relnum,
                        const elfcpp::Rela<size, big_endian>* rela,
                        const elfcpp::Rel<size, big_endian>* rel,
                        unsigned int rel_type,
                        unsigned int r_type,
                        const Sized_symbol<size>* gsym,
                        const Symbol_value<size>* psymval,
                        unsigned char* view,
                        typename elfcpp::Elf_types<size>::Elf_Addr address,
                        section_size_type)
{
  typename elfcpp::Elf_types<size>::Elf_Addr r_offset;
  typename elfcpp::Elf_types<size>::Elf_WXword r_info;
  typename elfcpp::Elf_types<size>::Elf_Swxword r_addend;

  if (rel_type == elfcpp::SHT_RELA)
    {
      r_offset = rela->get_r_offset();
      r_info = rela->get_r_info();
      r_addend = rela->get_r_addend();
    }
  else
    {
      r_offset = rel->get_r_offset();
      r_info = rel->get_r_info();
      r_addend = 0;
    }

  typedef Mips_relocate_functions<size, big_endian> Reloc_funcs;
  typename Reloc_funcs::Status reloc_status = Reloc_funcs::STATUS_OKAY;

  unsigned int got_offset = 0;
  Sized_relobj_file<size, big_endian>* object = relinfo->object;

  unsigned int r_sym = elfcpp::elf_r_sym<size>(r_info);
  bool target_is_16_bit_code = false;
  bool target_is_micromips_code = false;
  bool cross_mode_jump;

  Symbol_value<size> symval;

  Mips_relobj<size, big_endian>* mips_object =
      Mips_relobj<size, big_endian>::as_mips_relobj(object);
  const Mips_symbol<size>* mips_sym = Mips_symbol<size>::as_mips_sym(gsym);

  bool changed_mips16_value = false;
  if (gsym == NULL)
    {
      target_is_16_bit_code = mips_object->local_symbol_is_mips16(r_sym);
      target_is_micromips_code = mips_object->local_symbol_is_micromips(r_sym);
      if (target_is_16_bit_code || target_is_micromips_code)
        {
          // MIPS16/microMIPS text labels should be treated as odd.
          symval.set_output_value(psymval->value(object, 1));
          psymval = &symval;
          changed_mips16_value = true;
        }
    }
  else
    {
      target_is_16_bit_code = mips_sym->is_mips16();
      // If the output section is the PLT section, then the target is not
      // microMIPS.
      target_is_micromips_code = mips_sym->is_micromips()
          && !gsym->use_plt_offset(Scan::get_reference_flags(r_type));

      // If this is a mips16/microMIPS text symbol, add 1 to the value to make
      // it odd.  This will cause something like .word SYM to come up with
      // the right value when it is loaded into the PC.

      if (mips_sym->is_mips16() || mips_sym->is_micromips())
        {
          symval.set_output_value(psymval->value(object, 1));
          psymval = &symval;
          changed_mips16_value = true;
        }

      // Pick the value to use for symbols defined in shared objects.
      if (mips_sym->use_plt_offset(Scan::get_reference_flags(r_type))
          || mips_sym->has_lazy_stub()  )
        {
          elfcpp::Elf_Xword value;

          if (!mips_sym->has_lazy_stub())
            value = target->plt_section()->address() + mips_sym->plt_offset();
          else
            value = target->mips_stubs()->address() + mips_sym->lazy_stub_offset();

          symval.set_output_value(value);
          psymval = &symval;
        }
    }

  // TRUE if the symbol referred to by this relocation is "_gp_disp".
  // Note that such a symbol must always be a global symbol.
  bool gp_disp = gsym && (strcmp(gsym->name(), "_gp_disp") == 0)
                      && !mips_object->is_newabi();

  // TRUE if the symbol referred to by this relocation is "__gnu_local_gp".
  // Note that such a symbol must always be a global symbol.
  bool gnu_local_gp = gsym && (strcmp(gsym->name(), "__gnu_local_gp") == 0);


  if (gp_disp)
    {
      if (!target->hi16_reloc(r_type) && !target->lo16_reloc(r_type))
        gold_error_at_location(relinfo, relnum, r_offset,
          _("relocations against _gp_disp are permitted only"
            " with R_MIPS_HI16 and R_MIPS_LO16 relocations."));
    }
  else if (gnu_local_gp)
    {
      // __gnu_local_gp is _gp symbol.
      symval.set_output_value(target->adjusted_gp_value(object));
      psymval = &symval;
    }

  // If this is a reference to a 16-bit function with a stub, we need
  // to redirect the relocation to the stub unless:
  //
  // (a) the relocation is for a MIPS16 JAL;
  //
  // (b) the relocation is for a MIPS16 PIC call, and there are no
  //     non-MIPS16 uses of the GOT slot; or
  //
  // (c) the section allows direct references to MIPS16 functions.
  if (r_type != elfcpp::R_MIPS16_26
      && !parameters->options().relocatable()
      && ((mips_sym != NULL
           && target->get_mips16_fn_stub(mips_sym) != NULL
           && (r_type != elfcpp::R_MIPS16_CALL16 || mips_sym->need_fn_stub()))
          || (mips_sym == NULL
              && mips_object->get_local_mips16_fn_stub(r_sym) != NULL))
      && !section_allows_mips16_refs(object->section_name(relinfo->data_shndx).c_str()))
    {
      // This is a 32- or 64-bit call to a 16-bit function.  We should
      // have already noticed that we were going to need the
      // stub.
      elfcpp::Elf_Xword value;
      if (mips_sym == NULL)
        {
          Mips16_stub_section *fn_stub_section = mips_object->get_local_mips16_fn_stub(r_sym);
          value = fn_stub_section->output_section()->address() + fn_stub_section->output_section_offset();
        }
      else
        {
          gold_assert(mips_sym->need_fn_stub());
          if (mips_sym->has_la25_stub())
            {
              // If a LA25 header for the stub itself exists, point to the
              // prepended LUI/ADDIU sequence.
              value = target->la25_stub_section()->address() + mips_sym->la25_stub_offset();
            }
          else
            {
              Mips16_stub_section *fn_stub_section = target->get_mips16_fn_stub(mips_sym);
              value = fn_stub_section->output_section()->address() + fn_stub_section->output_section_offset();
            }
          }
      symval.set_output_value(value);
      psymval = &symval;
      changed_mips16_value = true;

      // The target is 16-bit, but the stub isn't.
      target_is_16_bit_code = false;
    }
  // If this is a 16-bit call to a 32- or 64-bit function with a stub, we
  // need to redirect the call to the stub.  Note that we specifically
  // exclude R_MIPS16_CALL16 from this behavior; indirect calls should
  // use an indirect stub instead.
  else if (r_type == elfcpp::R_MIPS16_26 && !parameters->options().relocatable()
           && ((mips_sym != NULL
                && (target->get_mips16_call_stub(mips_sym) != NULL || target->get_mips16_call_fp_stub(mips_sym) != NULL))
               || (mips_sym == NULL
                   && mips_object->get_local_mips16_call_stub(r_sym) != NULL))
           && !target_is_16_bit_code)
    {
      elfcpp::Elf_Xword value;
      Mips16_stub_section *call_stub_section;
      if (mips_sym == NULL)
        call_stub_section = mips_object->get_local_mips16_call_stub(r_sym);
      else
        {
          // If both call_stub and call_fp_stub are defined, we can figure
          // out which one to use by checking which one appears in the input
          // file.
          if (target->get_mips16_call_stub(mips_sym) != NULL
              && target->get_mips16_call_fp_stub(mips_sym) != NULL)
            {
              call_stub_section = NULL;
              for (unsigned int i = 1; i < mips_object->shnum(); ++i)
                {
                  const char *section_name = mips_object->section_name(i).c_str();
                  if (is_prefix_of(".mips16.call.fp.", section_name))
                    {
                      call_stub_section = target->get_mips16_call_fp_stub(mips_sym);
                      break;
                    }

                }
              if (call_stub_section == NULL)
                call_stub_section = target->get_mips16_call_stub(mips_sym);
            }
          else if (target->get_mips16_call_stub(mips_sym) != NULL)
            call_stub_section = target->get_mips16_call_stub(mips_sym);
          else
            call_stub_section = target->get_mips16_call_fp_stub(mips_sym);
        }

      value = call_stub_section->output_section()->address()
            + call_stub_section->output_section_offset();
      symval.set_output_value(value);
      psymval = &symval;
      changed_mips16_value = true;
    }
  // If this is a direct call to a PIC function, redirect to the
  // non-PIC stub.
  else if (mips_sym != NULL
           && mips_sym->has_la25_stub()
           && target->relocation_needs_la25_stub (mips_object, r_type,
                                                  target_is_16_bit_code))
    {
      elfcpp::Elf_Xword value;
      value = target->la25_stub_section()->address() + mips_sym->la25_stub_offset();
      symval.set_output_value(value);
      psymval = &symval;
    }

  // Calls from 16-bit code to 32-bit code and vice versa require the
  // mode change.  However, we can ignore calls to undefined weak symbols,
  // which should never be executed at runtime.  This exception is important
  // because the assembly writer may have "known" that any definition of the
  // symbol would be 16-bit code, and that direct jumps were therefore
  // acceptable.
  cross_mode_jump = (!parameters->options().relocatable()
                     && !(gsym != NULL && gsym->is_weak_undefined())
                     && ((r_type == elfcpp::R_MIPS16_26 && !target_is_16_bit_code)
                         || (r_type == elfcpp::R_MICROMIPS_26_S1
                             && !target_is_micromips_code)
                         || ((r_type == elfcpp::R_MIPS_26 || r_type == elfcpp::R_MIPS_JALR)
                              && (target_is_16_bit_code
                                  || target_is_micromips_code))));

  bool local = gsym == NULL || symbol_references_local(gsym, gsym->has_dynsym_index());

  // Global R_MIPS_GOT_PAGE/R_MICROMIPS_GOT_PAGE relocations are equivalent
  // to R_MIPS_GOT_DISP/R_MICROMIPS_GOT_DISP.  The addend is applied by the
  // corresponding R_MIPS_GOT_OFST/R_MICROMIPS_GOT_OFST.
  if (got_page_reloc(r_type) && !local)
    r_type = (micromips_reloc(r_type)
              ? elfcpp::R_MICROMIPS_GOT_DISP : elfcpp::R_MIPS_GOT_DISP);

  bool update_got_entry = false;
  switch (r_type)
    {
    case elfcpp::R_MIPS_NONE:
      break;
    case elfcpp::R_MIPS_16:
      reloc_status = Reloc_funcs::rel16(view, object, psymval, r_addend, rel_type);
      break;

    case elfcpp::R_MIPS_32:
      if (should_apply_r_mips_32_reloc(mips_sym, r_type, output_section, target))
        reloc_status = Reloc_funcs::rel32(view, object, psymval, r_addend, rel_type);
      if (mips_sym != NULL && (mips_sym->is_mips16() || mips_sym->is_micromips())
          && mips_sym->global_got_area() == GGA_RELOC_ONLY)
        {
          // If target->get_mips16_fn_stub(mips_sym) is NULL, symbol value is
          // already updated by adding +1.
          if (target->get_mips16_fn_stub(mips_sym) != NULL)
            {
              gold_assert(mips_sym->need_fn_stub());
              Mips16_stub_section *fn_stub_section = target->get_mips16_fn_stub(mips_sym);
              elfcpp::Elf_Xword value =
                fn_stub_section->output_section()->address() + fn_stub_section->output_section_offset();
              symval.set_output_value(value);
              psymval = &symval;
            }
          got_offset = mips_sym->global_gotoffset();
          update_got_entry = true;
        }
      break;

    case elfcpp::R_MIPS_REL32:
      gold_unreachable();

    case elfcpp::R_MIPS_PC32:
      reloc_status = Reloc_funcs::relpc32(view, object, psymval, address, r_addend, rel_type);
      break;

    case elfcpp::R_MIPS16_26:
      // The calculation for R_MIPS16_26 is just the same as for an
      // R_MIPS_26.  It's only the storage of the relocated field into
      // the output file that's different.  So, we just fall through to the
      // R_MIPS_26 case here.
    case elfcpp::R_MIPS_26:
    case elfcpp::R_MICROMIPS_26_S1:
      reloc_status = Reloc_funcs::rel26(view, object, psymval, address,
          gsym == NULL, r_addend, rel_type, gsym, cross_mode_jump, r_type, target->jal_to_bal());
      break;

    case elfcpp::R_MIPS_HI16:
    case elfcpp::R_MIPS16_HI16:
    case elfcpp::R_MICROMIPS_HI16:
      reloc_status = Reloc_funcs::relhi16(view, object, psymval, r_addend,
                                          address, gp_disp, r_type, rel_type);
      break;

    case elfcpp::R_MIPS_LO16:
    case elfcpp::R_MIPS16_LO16:
    case elfcpp::R_MICROMIPS_LO16:
    case elfcpp::R_MICROMIPS_HI0_LO16:
      reloc_status = Reloc_funcs::rello16(target, view, object, psymval,
                                          r_addend, rel_type, address,
                                          gp_disp, r_type);
      break;

    case elfcpp::R_MIPS_LITERAL:
    case elfcpp::R_MICROMIPS_LITERAL:
      // Because we don't merge literal sections, we can handle this
      // just like R_MIPS_GPREL16.  In the long run, we should merge
      // shared literals, and then we will need to additional work
      // here.

      // Fall through.

    case elfcpp::R_MIPS_GPREL16:
    case elfcpp::R_MIPS16_GPREL:
    case elfcpp::R_MICROMIPS_GPREL7_S2:
    case elfcpp::R_MICROMIPS_GPREL16:

      reloc_status = Reloc_funcs::relgprel(view, object, psymval,
                                           target->adjusted_gp_value(object), r_addend,
                                           rel_type, gsym == NULL, r_type);
      break;

    case elfcpp::R_MIPS_PC16:
      reloc_status = Reloc_funcs::relpc16(view, object, psymval, address,
                                          r_addend, rel_type);
      break;
    case elfcpp::R_MIPS_GPREL32:
      reloc_status = Reloc_funcs::relgprel32(view, object, psymval,
                                             target->adjusted_gp_value(object), r_addend, rel_type);
      break;
    case elfcpp::R_MIPS_GOT_HI16:
    case elfcpp::R_MIPS_CALL_HI16:
    case elfcpp::R_MICROMIPS_GOT_HI16:
    case elfcpp::R_MICROMIPS_CALL_HI16:
      if (gsym != NULL)
        got_offset = target->got_section()->got_offset(gsym, GOT_TYPE_STANDARD, object);
      else
        got_offset = target->got_section()->got_offset(r_sym, GOT_TYPE_STANDARD, object);
      reloc_status = Reloc_funcs::relgot_hi16(target, view, object, got_offset);
      break;

    case elfcpp::R_MIPS_GOT_LO16:
    case elfcpp::R_MIPS_CALL_LO16:
    case elfcpp::R_MICROMIPS_GOT_LO16:
    case elfcpp::R_MICROMIPS_CALL_LO16:
      if (gsym != NULL)
        got_offset = target->got_section()->got_offset(gsym, GOT_TYPE_STANDARD, object);
      else
        got_offset = target->got_section()->got_offset(r_sym, GOT_TYPE_STANDARD, object);
      reloc_status = Reloc_funcs::relgot_lo16(target, view, object, got_offset);
      break;

    case elfcpp::R_MIPS_GOT_DISP:
    case elfcpp::R_MICROMIPS_GOT_DISP:
      gold_assert(gsym != NULL);
      got_offset = target->got_section()->got_offset(gsym, GOT_TYPE_STANDARD, object);
      reloc_status = Reloc_funcs::relgot(target, view, object, got_offset, r_type);
      break;

    case elfcpp::R_MIPS_CALL16:
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MICROMIPS_CALL16:
      gold_assert(gsym != NULL);
      got_offset = target->got_section()->got_offset(gsym, GOT_TYPE_STANDARD, object);
      reloc_status = Reloc_funcs::relgot(target, view, object, got_offset, r_type);
      // TODO(sasa): We should also initialize update_got_entry in other places where relgot is called.
      update_got_entry = changed_mips16_value;
      break;

    case elfcpp::R_MIPS_GOT16:
    case elfcpp::R_MIPS16_GOT16:
    case elfcpp::R_MICROMIPS_GOT16:
      if (gsym != NULL)
        {
          got_offset = target->got_section()->got_offset(gsym, GOT_TYPE_STANDARD, object);
          reloc_status = Reloc_funcs::relgot(target, view, object, got_offset, r_type);
        }
      else
        reloc_status = Reloc_funcs::relgot16_local(view, object, psymval,
                                                   r_addend, rel_type, r_type);
      break;

    case elfcpp::R_MIPS_TLS_GD:
    case elfcpp::R_MIPS16_TLS_GD:
    case elfcpp::R_MICROMIPS_TLS_GD:
      if (gsym != NULL)
        got_offset = target->got_section()->got_offset(gsym, GOT_TYPE_TLS_PAIR, object);
      else
        got_offset = target->got_section()->got_offset(r_sym, GOT_TYPE_TLS_PAIR, object);
      reloc_status = Reloc_funcs::relgot(target, view, object, got_offset, r_type);
      break;

    case elfcpp::R_MIPS_TLS_GOTTPREL:
    case elfcpp::R_MIPS16_TLS_GOTTPREL:
    case elfcpp::R_MICROMIPS_TLS_GOTTPREL:
      if (gsym != NULL)
        got_offset = target->got_section()->got_offset(gsym, GOT_TYPE_TLS_OFFSET, object);
      else
        got_offset = target->got_section()->got_offset(r_sym, GOT_TYPE_TLS_OFFSET, object);
      reloc_status = Reloc_funcs::relgot(target, view, object, got_offset, r_type);
      break;

    case elfcpp::R_MIPS_TLS_LDM:
    case elfcpp::R_MIPS16_TLS_LDM:
    case elfcpp::R_MICROMIPS_TLS_LDM:
      // Relocate the field with the offset of the GOT entry for
      // the module index.
      got_offset = target->got_section()->tls_ldm_offset(object);
      reloc_status = Reloc_funcs::relgot(target, view, object, got_offset, r_type);
      break;

    case elfcpp::R_MIPS_GOT_PAGE:
    case elfcpp::R_MICROMIPS_GOT_PAGE:
      reloc_status = Reloc_funcs::relgotpage(target, view, object, psymval,
                                             r_addend, rel_type);
      break;

    case elfcpp::R_MIPS_GOT_OFST:
    case elfcpp::R_MICROMIPS_GOT_OFST:
      reloc_status = Reloc_funcs::relgotofst(target, view, object, psymval,
                                             r_addend, rel_type, local);
      break;

    case elfcpp::R_MIPS_JALR:
    case elfcpp::R_MICROMIPS_JALR:
      // This relocation is only a hint.  In some cases, we optimize
      // it into a bal instruction.  But we don't try to optimize
      // when the symbol does not resolve locally.
      if (gsym == NULL || symbol_calls_local(gsym, gsym->has_dynsym_index()))
        reloc_status = Reloc_funcs::reljalr(view, object, psymval, address,
                                            cross_mode_jump, r_type,
                                            target->jalr_to_bal(), target->jr_to_b());
      break;

    case elfcpp::R_MIPS_TLS_DTPREL_HI16:
    case elfcpp::R_MIPS16_TLS_DTPREL_HI16:
    case elfcpp::R_MICROMIPS_TLS_DTPREL_HI16:
      reloc_status = Reloc_funcs::tlsrelhi16(view, object, psymval,
                                             elfcpp::DTP_OFFSET, r_addend,
                                             rel_type);
      break;
    case elfcpp::R_MIPS_TLS_DTPREL_LO16:
    case elfcpp::R_MIPS16_TLS_DTPREL_LO16:
    case elfcpp::R_MICROMIPS_TLS_DTPREL_LO16:
    case elfcpp::R_MIPS_TLS_DTPREL32:
    case elfcpp::R_MIPS_TLS_DTPREL64:
      reloc_status = Reloc_funcs::tlsrello16(view, object, psymval,
                                             elfcpp::DTP_OFFSET, r_addend,
                                             rel_type);
      break;
    case elfcpp::R_MIPS_TLS_TPREL_HI16:
    case elfcpp::R_MIPS16_TLS_TPREL_HI16:
    case elfcpp::R_MICROMIPS_TLS_TPREL_HI16:
      reloc_status = Reloc_funcs::tlsrelhi16(view, object, psymval,
                                             elfcpp::TP_OFFSET, r_addend,
                                             rel_type);
      break;
    case elfcpp::R_MIPS_TLS_TPREL_LO16:
    case elfcpp::R_MIPS16_TLS_TPREL_LO16:
    case elfcpp::R_MICROMIPS_TLS_TPREL_LO16:
    case elfcpp::R_MIPS_TLS_TPREL32:
    case elfcpp::R_MIPS_TLS_TPREL64:
      reloc_status = Reloc_funcs::tlsrello16(view, object, psymval,
                                             elfcpp::TP_OFFSET, r_addend,
                                             rel_type);
      break;
    default:
      gold_error_at_location(relinfo, relnum, r_offset,
                             _("unsupported reloc %u"), r_type);
      break;
    }

  if (update_got_entry)
    elfcpp::Swap<32, big_endian>::writeval(target->got_section()->got_view()
      + got_offset, psymval->value(object, 0));

  // Report any errors.
  switch (reloc_status)
    {
    case Reloc_funcs::STATUS_OKAY:
      break;
    case Reloc_funcs::STATUS_OVERFLOW:
      gold_error_at_location(relinfo, relnum, r_offset,
                             _("relocation overflow"));
      break;
    case Reloc_funcs::STATUS_BAD_RELOC:
      gold_error_at_location(
        relinfo,
        relnum,
        r_offset,
        _("unexpected opcode while processing relocation"));
      break;
    default:
      gold_unreachable();
    }

  return true;
}

template<int size, bool big_endian>
inline bool
Target_mips<size, big_endian>::Relocate::relocate(
                        const Relocate_info<size, big_endian>* relinfo,
                        Target_mips* target,
                        Output_section* output_section,
                        size_t relnum,
                        const elfcpp::Rela<size, big_endian>& reloc,
                        unsigned int r_type,
                        const Sized_symbol<size>* gsym,
                        const Symbol_value<size>* psymval,
                        unsigned char* view,
                        typename elfcpp::Elf_types<size>::Elf_Addr address,
                        section_size_type view_size)
{
  return relocate(
    relinfo,
    target,
    output_section,
    relnum,
    &reloc,
    (const elfcpp::Rel<size, big_endian>*) NULL,
    elfcpp::SHT_RELA,
    r_type,
    gsym,
    psymval,
    view,
    address,
    view_size);
}

template<int size, bool big_endian>
inline bool
Target_mips<size, big_endian>::Relocate::relocate(
                        const Relocate_info<size, big_endian>* relinfo,
                        Target_mips* target,
                        Output_section* output_section,
                        size_t relnum,
                        const elfcpp::Rel<size, big_endian>& reloc,
                        unsigned int r_type,
                        const Sized_symbol<size>* gsym,
                        const Symbol_value<size>* psymval,
                        unsigned char* view,
                        typename elfcpp::Elf_types<size>::Elf_Addr address,
                        section_size_type view_size)
{
  return relocate(
    relinfo,
    target,
    output_section,
    relnum,
    (const elfcpp::Rela<size, big_endian>*) NULL,
    &reloc,
    elfcpp::SHT_REL,
    r_type,
    gsym,
    psymval,
    view,
    address,
    view_size);
}

// Get the Reference_flags for a particular relocation.

template<int size, bool big_endian>
int
Target_mips<size, big_endian>::Scan::get_reference_flags(
                       unsigned int r_type)
{
  switch (r_type)
    {
    case elfcpp::R_MIPS_NONE:
      // No symbol reference.
      return 0;

    case elfcpp::R_MIPS_16:
    case elfcpp::R_MIPS_32:
    case elfcpp::R_MIPS_64:
    case elfcpp::R_MIPS_HI16:
    case elfcpp::R_MIPS_LO16:
    case elfcpp::R_MIPS16_HI16:
    case elfcpp::R_MIPS16_LO16:
      return Symbol::ABSOLUTE_REF;

    case elfcpp::R_MIPS_26:
    case elfcpp::R_MIPS16_26:
      return Symbol::FUNCTION_CALL | Symbol::ABSOLUTE_REF;

    case elfcpp::R_MIPS_GPREL32:
    case elfcpp::R_MIPS_GPREL16:
    case elfcpp::R_MIPS16_GPREL:
    case elfcpp::R_MIPS_REL32:
      return Symbol::RELATIVE_REF;

    case elfcpp::R_MIPS_PC16:
    case elfcpp::R_MIPS_PC32:
    case elfcpp::R_MIPS_JALR:
      return Symbol::FUNCTION_CALL | Symbol::RELATIVE_REF;

    case elfcpp::R_MIPS_GOT16:
    case elfcpp::R_MIPS16_GOT16:
    case elfcpp::R_MIPS_CALL16:
    case elfcpp::R_MIPS16_CALL16:
    case elfcpp::R_MIPS_GOT_DISP:
    case elfcpp::R_MIPS_GOT_HI16:
    case elfcpp::R_MIPS_CALL_HI16:
    case elfcpp::R_MIPS_GOT_LO16:
    case elfcpp::R_MIPS_CALL_LO16:
    case elfcpp::R_MIPS_LITERAL:
    case elfcpp::R_MIPS_GOT_PAGE:
    case elfcpp::R_MIPS_GOT_OFST:
      // Absolute in GOT.
      return Symbol::RELATIVE_REF;

    case elfcpp::R_MIPS_TLS_DTPMOD32:
    case elfcpp::R_MIPS_TLS_DTPREL32:
    case elfcpp::R_MIPS_TLS_DTPMOD64:
    case elfcpp::R_MIPS_TLS_DTPREL64:
    case elfcpp::R_MIPS_TLS_GD:
    case elfcpp::R_MIPS_TLS_LDM:
    case elfcpp::R_MIPS_TLS_DTPREL_HI16:
    case elfcpp::R_MIPS_TLS_DTPREL_LO16:
    case elfcpp::R_MIPS_TLS_GOTTPREL:
    case elfcpp::R_MIPS_TLS_TPREL32:
    case elfcpp::R_MIPS_TLS_TPREL64:
    case elfcpp::R_MIPS_TLS_TPREL_HI16:
    case elfcpp::R_MIPS_TLS_TPREL_LO16:
      return Symbol::TLS_REF;

    case elfcpp::R_MIPS_COPY:
    case elfcpp::R_MIPS_JUMP_SLOT:
    default:
      // Not expected.  We will give an error later.
      return 0;
    }
}

// Report an unsupported relocation against a local symbol.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::Scan::unsupported_reloc_local(
                        Sized_relobj_file<size, big_endian>* object,
                        unsigned int r_type)
{
  gold_error(_("%s: unsupported reloc %u against local symbol"),
             object->name().c_str(), r_type);
}

// Report an unsupported relocation against a global symbol.

template<int size, bool big_endian>
void
Target_mips<size, big_endian>::Scan::unsupported_reloc_global(
                        Sized_relobj_file<size, big_endian>* object,
                        unsigned int r_type,
                        Symbol* gsym)
{
  gold_error(_("%s: unsupported reloc %u against global symbol %s"),
             object->name().c_str(), r_type, gsym->demangled_name().c_str());
}

// Return printable name for ABI.
template<int size, bool big_endian>
const char *
Target_mips<size, big_endian>::elf_mips_abi_name(elfcpp::Elf_Word e_flags, unsigned char ei_class)
{
  switch (e_flags & elfcpp::EF_MIPS_ABI)
    {
    case 0:
      if ((e_flags & elfcpp::EF_MIPS_ABI2) != 0)
        return "N32";
      else if (elfcpp::abi_64(ei_class))
        return "64";
      else
        return "none";
    case elfcpp::E_MIPS_ABI_O32:
      return "O32";
    case elfcpp::E_MIPS_ABI_O64:
      return "O64";
    case elfcpp::E_MIPS_ABI_EABI32:
      return "EABI32";
    case elfcpp::E_MIPS_ABI_EABI64:
      return "EABI64";
    default:
      return "unknown abi";
    }
}

template<int size, bool big_endian>
const char *
Target_mips<size, big_endian>::elf_mips_mach_name(elfcpp::Elf_Word e_flags)
{
  switch (e_flags & elfcpp::EF_MIPS_MACH)
    {
    case elfcpp::E_MIPS_MACH_3900:
      return "mips:3900";
    case elfcpp::E_MIPS_MACH_4010:
      return "mips:4010";
    case elfcpp::E_MIPS_MACH_4100:
      return "mips:4100";
    case elfcpp::E_MIPS_MACH_4111:
      return "mips:4111";
    case elfcpp::E_MIPS_MACH_4120:
      return "mips:4120";
    case elfcpp::E_MIPS_MACH_4650:
      return "mips:4650";
    case elfcpp::E_MIPS_MACH_5400:
      return "mips:5400";
    case elfcpp::E_MIPS_MACH_5500:
      return "mips:5500";
    case elfcpp::E_MIPS_MACH_SB1:
      return "mips:sb1";
    case elfcpp::E_MIPS_MACH_9000:
      return "mips:9000";
    case elfcpp::E_MIPS_MACH_LS2E:
      return "mips:loongson-2e";
    case elfcpp::E_MIPS_MACH_LS2F:
      return "mips:loongson-2f";
    case elfcpp::E_MIPS_MACH_LS3A:
      return "mips:loongson-3a";
    case elfcpp::E_MIPS_MACH_OCTEON:
      return "mips:octeon";
    case elfcpp::E_MIPS_MACH_OCTEON2:
      return "mips:octeon2";
    case elfcpp::E_MIPS_MACH_XLR:
      return "mips:xlr";
    default:
      switch (e_flags & elfcpp::EF_MIPS_ARCH)
        {
        default:
        case elfcpp::E_MIPS_ARCH_1:
          return "mips:3000";

        case elfcpp::E_MIPS_ARCH_2:
          return "mips:6000";

        case elfcpp::E_MIPS_ARCH_3:
          return "mips:4000";

        case elfcpp::E_MIPS_ARCH_4:
          return "mips:8000";

        case elfcpp::E_MIPS_ARCH_5:
          return "mips:mips5";

        case elfcpp::E_MIPS_ARCH_32:
          return "mips:isa32";

        case elfcpp::E_MIPS_ARCH_64:
          return "mips:isa64";

        case elfcpp::E_MIPS_ARCH_32R2:
          return "mips:isa32r2";

        case elfcpp::E_MIPS_ARCH_64R2:
          return "mips:isa64r2";
        }
    }
    return "unknown CPU";
}

template<int size, bool big_endian>
Target::Target_info Target_mips<size, big_endian>::mips_info =
{
  size,                 // size
  big_endian,           // is_big_endian
  elfcpp::EM_MIPS,      // machine_code
  true,                 // has_make_symbol
  false,                // has_resolve
  false,                // has_code_fill
  true,                 // is_default_stack_executable
  false,                // can_icf_inline_merge_sections
  '\0',                 // wrap_char
  "/lib/ld.so.1",       // dynamic_linker
  0x20000,              // default_text_segment_address
  0x10000,		// abi_pagesize (overridable by -z max-page-size)
  0x10000,		// common_pagesize (overridable by -z common-page-size)
  true,                 // isolate_execinstr
  0x10000000,           // rosegment_gap
  elfcpp::SHN_UNDEF,    // small_common_shndx
  elfcpp::SHN_UNDEF,    // large_common_shndx
  0,                    // small_common_section_flags
  0,                    // large_common_section_flags
  NULL,                 // attributes_section
  NULL                  // attributes_vendor
};

// Target selector for Mips.  Note this is never instantiated directly.
// It's only used in Target_selector_mips_nacl, below.

template<int size, bool big_endian>
class Target_selector_mips : public Target_selector
{
public:
  Target_selector_mips()
    : Target_selector(elfcpp::EM_MIPS, size, big_endian,
                size == 64 ?
                  (big_endian ? "elf64-tradbigmips" : "elf64-tradlittlemips") :
                  (big_endian ? "elf32-tradbigmips" : "elf32-tradlittlemips"),
                (size == 64 ?
                  (big_endian ? "elf64-tradbigmips" : "elf64-tradlittlemips") :
                  (big_endian ? "elf32-tradbigmips" : "elf32-tradlittlemips")))
  { }

  Target* do_instantiate_target()
  { return new Target_mips<size, big_endian>(); }
};

// Target selectors.

template<int size, bool big_endian>
class Target_selector_mips_nacl
  : public Target_selector_nacl<Target_selector_mips<size, big_endian>,
                                Target_mips<size, big_endian> >
{
 public:
  Target_selector_mips_nacl()
    : Target_selector_nacl<Target_selector_mips<size, big_endian>,
                           Target_mips<size, big_endian> >(
          "mips",
          big_endian ? "elf32-tradbigmips-nacl" : "elf32-tradlittlemips-nacl",
          big_endian ? "elf32-tradbigmips-nacl" : "elf32-tradlittlemips-nacl")
  { }
};

Target_selector_mips_nacl<32, false> target_selector_mips32;

} // End anonymous namespace.

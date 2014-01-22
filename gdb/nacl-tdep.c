/* Target-dependent code for NaCl.

   Copyright (C) 2001, 2003-2012 Free Software Foundation, Inc.

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

#include "defs.h"
#include "amd64-linux-tdep.h"
#include "i386-linux-tdep.h"
#include "linux-tdep.h"
#include "amd64-tdep.h"
#include "nacl-manifest.h"
#include "symtab.h"
#include "solib-svr4.h"
#include "frame.h"
#include "osabi.h"
#include "disasm.h"
#include "breakpoint.h"
#include "target.h"
#include "elf-bfd.h"
#include "inferior.h"

static enum gdb_osabi
nacl_osabi_sniffer (bfd *abfd)
{
  /* We removed Linux remote debugging support from NaCl debugger, so we must
     handle all ELF files ourselves now.

     If we want to support both Linux and NaCl remote debugging simultaneously,
     we would have to find some way to distinguish NaCl and Linux binaries here.
     Currently there is no way to distinguish PNaCl-produced binaries from
     Linux binaries.

     See issues https://code.google.com/p/nativeclient/issues/detail?id=2971 and
     https://code.google.com/p/nativeclient/issues/detail?id=3313
     for details.  */
  if (bfd_get_flavour (abfd) == bfd_target_elf_flavour)
    return GDB_OSABI_NACL;

  return GDB_OSABI_UNKNOWN;
}

static void
nacl_init_abi (struct gdbarch_info info, struct gdbarch *gdbarch)
{
  /* NaCl uses SVR4-style shared libraries.  */
  set_gdbarch_skip_trampoline_code (gdbarch, find_solib_trampoline_target);
  set_solib_svr4_map_so_name (gdbarch, nacl_manifest_find);
  set_gdbarch_process_record (gdbarch, i386_process_record);
  set_gdbarch_call_dummy_location(gdbarch, AT_ENTRY_POINT);
}

static void
i386_nacl_init_abi (struct gdbarch_info info, struct gdbarch *gdbarch)
{
  struct gdbarch_tdep *tdep = gdbarch_tdep (gdbarch);
  linux_init_abi (info, gdbarch);
  i386_elf_init_abi (info, gdbarch);
  i386_linux_init_gregset (tdep);
  tdep->tdesc = tdesc_i386_linux;
  set_solib_svr4_fetch_link_map_offsets (gdbarch,
					 svr4_ilp32_fetch_link_map_offsets);
  nacl_init_abi (info, gdbarch);
}

static CORE_ADDR
amd64_nacl_addr_bits_remove (struct gdbarch *gdbarch, CORE_ADDR val)
{
  return val & 0xffffffffUL;
}

static CORE_ADDR
amd64_nacl_unwind_pc (struct gdbarch *gdbarch, struct frame_info *this_frame)
{
  CORE_ADDR pc;
  pc = frame_unwind_register_unsigned (this_frame, gdbarch_pc_regnum (gdbarch));
  return amd64_nacl_addr_bits_remove (gdbarch, pc);
}

static CORE_ADDR
amd64_nacl_unwind_sp (struct gdbarch *gdbarch, struct frame_info *this_frame)
{
  CORE_ADDR sp;
  sp = frame_unwind_register_unsigned (this_frame, gdbarch_sp_regnum (gdbarch));
  return amd64_nacl_addr_bits_remove (gdbarch, sp);
}

static struct link_map_offsets *
amd64_nacl_fetch_link_map_offsets (void)
{
  static struct link_map_offsets lmo;
  static struct link_map_offsets *lmp = NULL;

  if (lmp == NULL)
    {
      lmp = &lmo;

      lmo.r_version_offset = 0;
      lmo.r_version_size = 4;
      lmo.r_map_offset = 4;
      lmo.r_brk_offset = 8;
      /* Dynamic linker is in the normal list of shared objects.  */
      lmo.r_ldsomap_offset = -1;

      lmo.link_map_size = 24;
      lmo.l_addr_offset = 0;
      lmo.l_name_offset = 8;
      lmo.l_ld_offset = 12;
      lmo.l_next_offset = 16;
      lmo.l_prev_offset = 20;
    }

  return lmp;
}

static CORE_ADDR
amd64_nacl_skip_rsp_sandboxing (CORE_ADDR addr)
{
  gdb_byte buf[3];
  if (target_read_memory (addr, buf, sizeof(buf)) == 0)
    {
      /* 4c 01 fc    add  %r15,%rsp  */
      if (buf[0] == 0x4c && buf[1] == 0x01 && buf[2] == 0xfc)
        {
          return addr + 3;
        }
    }
  return addr;
}

static CORE_ADDR
amd64_nacl_adjust_breakpoint_address (struct gdbarch *gdbarch, CORE_ADDR addr)
{
  return amd64_nacl_skip_rsp_sandboxing (addr);
}

static int
amd64_nacl_software_single_step (struct frame_info *frame)
{
  struct gdbarch *gdbarch;
  CORE_ADDR pc;
  CORE_ADDR bp_pc;

  gdbarch = get_frame_arch (frame);
  pc = get_frame_register_unsigned (frame, gdbarch_pc_regnum (gdbarch));
  pc = amd64_nacl_addr_bits_remove (gdbarch, pc);

  /* Check if next instruction is rsp sandboxing.  If yes, assume current
     instruction is rsp modification.  */
  pc += gdb_insn_length (gdbarch, pc);
  bp_pc = amd64_nacl_skip_rsp_sandboxing (pc);
  if (bp_pc != pc)
    {
      insert_single_step_breakpoint (gdbarch,
                                     get_frame_address_space (frame),
                                     bp_pc);
      return 1;
    }

  return 0;
}

static struct frame_id
amd64_nacl_dummy_id (struct gdbarch *gdbarch, struct frame_info *this_frame)
{
  CORE_ADDR fp;

  fp = get_frame_register_unsigned (this_frame, AMD64_RBP_REGNUM) + 16;
  fp = amd64_nacl_addr_bits_remove(gdbarch, fp);

  return frame_id_build (fp, get_frame_pc (this_frame));
}

static int
amd64_nacl_inner_than (CORE_ADDR lhs, CORE_ADDR rhs)
{
  return (uint32_t)lhs < (uint32_t)rhs;
}

static void
amd64_nacl_init_abi (struct gdbarch_info info, struct gdbarch *gdbarch)
{
  struct gdbarch_tdep *tdep = gdbarch_tdep (gdbarch);

  linux_init_abi (info, gdbarch);
  amd64_init_abi (info, gdbarch);
  amd64_linux_init_gregset (tdep);
  tdep->tdesc = tdesc_amd64_linux;
  set_solib_svr4_fetch_link_map_offsets (gdbarch,
					 amd64_nacl_fetch_link_map_offsets);
  nacl_init_abi (info, gdbarch);

  /* NaCl data model.

     WARNING! This might confuse a lot of code, as it uses
       if (set_gdbarch_ptr_bit (gdbarch) == <bits>)
     to distinguish between i386 and x86_64 (lame!).  Luckily, most of that
     code is about native debugging and syscalls, so it is not used for NaCl.

     TODO(eaeltsin): find better way to distinguish between i386 and x86_64!  */
  set_gdbarch_long_bit (gdbarch, 32);
  set_gdbarch_ptr_bit (gdbarch, 32);

  /* TODO(eaeltsin): we might use address size instead of pointer size to
     distinguish between i386 and x86_64...  At least address size is not
     a property of the data model.  */
  set_gdbarch_addr_bit (gdbarch, 64);

  /* How to extract addresses from registers.  */
  set_gdbarch_addr_bits_remove (gdbarch, amd64_nacl_addr_bits_remove);
  set_gdbarch_unwind_pc (gdbarch, amd64_nacl_unwind_pc);
  set_gdbarch_unwind_sp (gdbarch, amd64_nacl_unwind_sp);
  set_gdbarch_inner_than (gdbarch, amd64_nacl_inner_than);

  /* Where to set breakpoints.  */
  set_gdbarch_adjust_breakpoint_address (gdbarch,
                                         amd64_nacl_adjust_breakpoint_address);
  set_gdbarch_software_single_step (gdbarch, amd64_nacl_software_single_step);
  /* Recognizing dummy frames.  */
  set_gdbarch_dummy_id(gdbarch, amd64_nacl_dummy_id);
}

/* Provide a prototype to silence -Wmissing-prototypes.  */
extern void _initialize_nacl_tdep (void);

void
_initialize_nacl_tdep (void)
{
  gdbarch_register_osabi_sniffer (bfd_arch_i386, bfd_target_elf_flavour,
				  nacl_osabi_sniffer);

  gdbarch_register_osabi (bfd_arch_i386, bfd_mach_x86_64,
			  GDB_OSABI_NACL, amd64_nacl_init_abi);

  gdbarch_register_osabi (bfd_arch_i386, 0,
			  GDB_OSABI_NACL, i386_nacl_init_abi);
}

// nacl_file.cc -- handle file lookups for NaCl version of gold  -*- C++ -*-

// Copyright 2012 Free Software Foundation, Inc.
// Written by the Native Client authors.

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


#include "nacl_file.h"

#if !defined(__native_client__)
#error "Cannot build nacl_file.cc without __native_client__"
#endif

#include <fcntl.h>
#include <map>
#include <string>
#include <unistd.h>
#include <vector>

#include <irt.h>
#include "native_client/src/shared/srpc/nacl_srpc.h"

#include "gold.h"

using namespace gold;

extern int gold_main(int argc, char** argv);

#define FILENAME_OUTPUT   "a.out"
#define FILENAME_OBJ      "__PNACL_GENERATED"

const int kMaxArgc = 256;
// This value cannot change without also changing the signature of the
// RunWithSplit RPC
const int kMaxObjectFiles = 16;

namespace
{
std::map<std::string, int> g_preopened_files;
struct nacl_irt_resource_open g_irt_resource_open;

// Register some filename -> fd mappings that correspond to pre-opened fds.
// Otherwise files are opened via the IRT open_resource() function.
void RegisterPreopenedFd(const char* filename, int fd) {
  std::string key(filename);
  std::map<std::string, int>::iterator it = g_preopened_files.find(key);

  if (it != g_preopened_files.end()) {
    gold_fatal(_("nacl_file::set_preopened_fd already set %s to %d."),
               filename, it->second);
  } else {
    g_preopened_files[key] = fd;
  }
}

// Set up interfaces for IRT open_resource.
void GetIRTInterface() {
  size_t query_result = nacl_interface_query(
      NACL_IRT_RESOURCE_OPEN_v0_1,
      &g_irt_resource_open, sizeof(g_irt_resource_open));
  if (query_result != sizeof(g_irt_resource_open)) {
    gold_fatal(_("nacl_file::GetIRTInterface failed"));
  }
}

int IrtOpenFile(const char* filename) {
  int fd = -1;
  if (int res = g_irt_resource_open.open_resource(filename, &fd)) {
    gold_fatal(_("IrtOpenFile (%s) failed: %d\n"), filename, res);
  }
  return fd;
}

void RunCommon(const std::vector<std::string>& arg_vec,
               NaClSrpcRpc* rpc,
               NaClSrpcClosure* done) {
  // repackage the commandline to what main() expects
  const char* argv[kMaxArgc];
  if (arg_vec.size() >  kMaxArgc) {
    gold_fatal(_("commandline too long"));
  }
  for (size_t i = 0; i < arg_vec.size(); ++i) argv[i] = arg_vec[i].c_str();

  // call hijacked main()
  int ret = gold_main(arg_vec.size(), const_cast<char**>(&argv[0]));
  rpc->result = ret > 0 ? NACL_SRPC_RESULT_APP_ERROR : NACL_SRPC_RESULT_OK;
  done->Run(done);
}

// c.f.: pnacl/driver/nativeld.py
const char* kDefaultCommandCommon[] = {
  "gold",
  "--eh-frame-hdr",
  "-nostdlib",
  // ARM only but added to everything for convenience
  "--no-fix-cortex-a8",
  "-o",
  FILENAME_OUTPUT,
  0
};

const char* kDefaultCommandStatic[] = {
  "-static",
  "crtbegin.o",
  FILENAME_OBJ,
  "@shim",
  "--start-group",
  "libgcc.a",            // TODO(robertm): use -l here?
  "libcrt_platform.a",   // TODO(robertm): use -l here?
  "--end-group",
  "crtend.o",
  0,  // sentinel
};


void ProcessCommandline(const char** src,
                        std::vector<std::string>* result) {
  for (int i = 0; src[i] != 0; ++i) {
    if (src[i][0] != '@') {
      result->push_back(src[i]);
      continue;
    }

    if (src[i] == std::string("@shim")) {
      result->push_back("--entry=__pnacl_start");
      result->push_back("libpnacl_irt_shim.a");
    } else {
      gold_fatal(_("unknown meta command line flag"));
    }
  }
}


// SRPC signature: :ihhhhhhhhhhhhhhhhh:
// i:   number N of object files to use
// h{16}: handles of objfiles. N of them are valid.
// h:  handle of nexe file
void
SrpcRunWithSplit(NaClSrpcRpc* rpc,
                 NaClSrpcArg** in_args,
                 NaClSrpcArg** /* out_args */,
                 NaClSrpcClosure* done) {
  int object_count = in_args[0]->u.ival;
  if (object_count > kMaxObjectFiles || object_count < 1) {
    gold_fatal(_("Invalid object count"));
  }
  std::vector<char *> filenames(object_count);
  for (int i = 0; i < object_count; i++) {
    const int len = sizeof(FILENAME_OBJ) + 2;
    filenames[i] = new char[len];
    snprintf(filenames[i], len, "%s%d", FILENAME_OBJ, i);
    RegisterPreopenedFd(filenames[i], in_args[i + 1]->u.hval);
  }
  int nexe_fd = in_args[kMaxObjectFiles + 1]->u.hval;
  RegisterPreopenedFd(FILENAME_OUTPUT, nexe_fd);

  std::vector<std::string> result_arg_vec;

  ProcessCommandline(kDefaultCommandCommon, &result_arg_vec);
  // Construct the rest of the command line, replacing FILENAME_OBJ with a list
  // of input files from the descriptors.
  const int cmdline_len = ((sizeof(kDefaultCommandStatic) /
                            sizeof(kDefaultCommandStatic[0])) +
                           object_count - 1);
  const char *command_line[cmdline_len];

  int arg = 0;
  for (int i = 0; kDefaultCommandStatic[i] != 0; i++) {
    if (!strcmp(kDefaultCommandStatic[i], FILENAME_OBJ)) {
      for (int k = 0; k < object_count; k++) {
        command_line[arg++] = filenames[k];
      }
    } else {
      command_line[arg++] = kDefaultCommandStatic[i];
    }
  }
  command_line[arg] = 0;

  ProcessCommandline(command_line, &result_arg_vec);
  for (int i = 0; i < object_count; i++) {
    delete [] filenames[i];
  }
  RunCommon(result_arg_vec, rpc, done);
}

} // End anonymous namespace.

namespace nacl_file
{

int NaClOpenFileDescriptor(const char *filename) {
  std::string key(filename);
  std::map<std::string, int>::iterator it = g_preopened_files.find(key);
  int fd;
  // First check if it is a pre-opened file.
  if (it != g_preopened_files.end()) {
    fd = it->second;
  } else {
    // Otherwise, open the file through the IRT.
    fd = IrtOpenFile(filename);
  }
  // In case the file was re-opened, seek back to the beginning.
  // This might be the case for the --start/end-group implementation.
  lseek(fd, 0, SEEK_SET);
  return fd;
}

void NaClReleaseFileDescriptor(int fd) {
  // Note: we do not close the fd as it maybe opened again.
  // For now we are getting lucky:
  // gold is not closing any of the libraries. And it IS closing
  // the nexe for us in Output_file::close
}

} // End namespace nacl_file.


int main() {
  if (!NaClSrpcModuleInit()) {
    gold_fatal(_("NaClSrpcModuleInit failed\n"));
  }
  GetIRTInterface();

  // Start the message loop to process SRPCs.
  // It usually never terminates unless killed.
  const struct NaClSrpcHandlerDesc srpc_methods[] = {
    { "RunWithSplit:ihhhhhhhhhhhhhhhhh:", SrpcRunWithSplit },
    { NULL, NULL },
  };

  if (!NaClSrpcAcceptClientConnection(srpc_methods)) {
    gold_fatal(_("NaClSrpcAcceptClientConnection failed\n"));
  }

  NaClSrpcModuleFini();
  return 0;
}

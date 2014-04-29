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

#include "native_client/src/public/imc_syscalls.h"
#include "native_client/src/public/name_service.h"
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

// Register some filename -> fd mappings so that we do not
// need to use the ManifestNameService  (aka directory) service.
// Note, there seems to be the following convention:
// the directory service knows about files like  "files/<filename>".
// Locally, we refer to the files as <filename>.
// For object files passed in via Srpc, we register the incoming .o
// descriptor as FILENAME_OBJ WITHOUT the "files/" prefix.
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

// Look up additional resource files through the nacl manifest service
// which essentially maps a (file)name to a (file)descriptor
NaClSrpcChannel g_nacl_manifest_channel;

// Make ManifestNameService service available for lookups.
void ManifestLookupInit() {
  int nameservice_address = -1;
  int nameservice_fd = -1;
  int manifest_address = -1;
  int manifest_fd = -1;
  int status;
  NaClSrpcChannel nameservice_channel;

  /* Attach to the reverse service for doing manifest file queries. */
  nacl_nameservice(&nameservice_address);
  if (nameservice_address == -1) {
    gold_fatal(_("nacl_nameservice failed\n"));
  }
  nameservice_fd = imc_connect(nameservice_address);
  close(nameservice_address);
  if (nameservice_fd == -1) {
    gold_fatal(_("name service connect failed\n"));
  }
  if (!NaClSrpcClientCtor(&nameservice_channel, nameservice_fd)) {
    gold_fatal(_("name service channel ctor failed\n"));
  }
  if (NACL_SRPC_RESULT_OK !=
      NaClSrpcInvokeBySignature(&nameservice_channel, NACL_NAME_SERVICE_LOOKUP,
                                "ManifestNameService", O_RDWR,
                                &status, &manifest_address)) {
    gold_fatal(_("ManifestNameService SRPC failed, status %d\n"), status);
  }
  NaClSrpcDtor(&nameservice_channel);
  if (manifest_address == -1) {
    gold_fatal(_("manifest name service address is -1\n"));
  }
  manifest_fd = imc_connect(manifest_address);
  close(manifest_address);
  if (manifest_fd == -1) {
    gold_fatal(_("manifest name service connect failed\n"));
  }
  if (!NaClSrpcClientCtor(&g_nacl_manifest_channel, manifest_fd)) {
    gold_fatal(_("manifest channel ctor failed\n"));
  }
}

void ManifestLookupFini() {
  NaClSrpcDtor(&g_nacl_manifest_channel);
}

const int kUnknownFd = -1;

int LookupFileByName(const char* filename) {
  int fd = kUnknownFd;
  int status;
  // Files looked up via the nameservice are assumed to have a "files/" prefix.
  std::string prefix("files/");
  std::string full_filename = prefix + std::string(filename);
  NaClSrpcError error =
      NaClSrpcInvokeBySignature(&g_nacl_manifest_channel,
                                NACL_NAME_SERVICE_LOOKUP,
                                full_filename.c_str(),
                                O_RDONLY,
                                &status,
                                &fd);
  if (error != NACL_SRPC_RESULT_OK) {
    gold_fatal(_("Lookup (%s) failed.\n"), filename);
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


// c.f.: pnacl/driver/pnacl-nativeld.py
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

} // End namespace gold.

namespace nacl_file
{

// This is the only exported API from this file
int NaClOpenFileDescriptor(const char *filename) {
  std::string key(filename);
  std::map<std::string, int>::iterator it = g_preopened_files.find(key);
  int fd;
  if (it != g_preopened_files.end()) {
    fd = it->second;
  } else {
    // Otherwise, ask the nameservice.
    fd = LookupFileByName(filename);
  }
  // in case the file was re-opened, say to do --start/end-group
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


int
main()
{
  if (!NaClSrpcModuleInit()) {
    gold_fatal(_("NaClSrpcModuleInit failed\n"));
  }
  ManifestLookupInit();

  // Start the message loop to process SRPCs.
  // It usually never terminates unless killed.
  const struct NaClSrpcHandlerDesc srpc_methods[] = {
    { "RunWithSplit:ihhhhhhhhhhhhhhhhh:", SrpcRunWithSplit },
    { NULL, NULL },
  };

  if (!NaClSrpcAcceptClientConnection(srpc_methods)) {
    gold_fatal(_("NaClSrpcAcceptClientConnection failed\n"));
  }

  ManifestLookupFini();
  NaClSrpcModuleFini();
  return 0;
}

// nacl_file.h -- handle file lookups for NaCl version of gold  -*- C++ -*-

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


#ifndef NACL_FILE_H
#define NACL_FILE_H

namespace nacl_file
{
// Look up an input file (possibly via the reverse-service channel).
extern int NaClOpenFileDescriptor(const char *filename);

// Tell the subsystem that the descriptor is no longer uused.
// Note: this is currently little more than a dummy.
extern void NaClReleaseFileDescriptor(int fd);

} // End namespace nacl_file.


#endif  // NACL_FILE_H

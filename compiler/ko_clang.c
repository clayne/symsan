/*
  The code is modified from AFL's LLVM mode and Angora.

   ------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

 */

#define KO_MAIN

#include "alloc_inl.h"
#include "defs.h"
#include "debug.h"
#include "version.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

static char *obj_path;       /* Path to runtime libraries         */
static char *taint_path;     /* Path to the taint pass            */
static char **cc_params;     /* Parameters passed to the real CC  */
static u32 cc_par_cnt = 1;   /* Param count, including argv0      */
static u8 is_cxx = 0;
static u8 use_native_cxx = 0;
static u8 use_native_zlib = 1; /* Use system zlib by default */

/* Try to find the executable from PATH */
static char *find_executable_in_path(const char *filename) {
  char *path = getenv("PATH");
  if (path == NULL) {
    FATAL("Cannot get PATH env");
    return NULL;
  }

  char *prev = path;
  char full_path[PATH_MAX];
  size_t filename_len = strlen(filename);
  while (1) {
    char *colon = strstr(prev, ":");
    size_t len = colon ? colon - prev : strlen(prev);
    if (len + 1 + filename_len + 1 >= PATH_MAX) {
      WARNF("Path too long: %s", prev);
      continue;
    }

    // Construct the full path
    memcpy(full_path, prev, len);
    full_path[len] = '/';
    memcpy(full_path + len + 1, filename, filename_len + 1);

    // Check if the file exists and is executable
    if (access(full_path, X_OK) == 0) {
      return ck_strdup(full_path);
    }

    if (colon == NULL || *(colon + 1) == '\0') {
      break;
    }
    prev = colon + 1;
  }

  return NULL;
}

/* Try to find the runtime libraries. If that fails, abort. */
static void find_obj(const char *argv0) {

  char *slash;
  char path[PATH_MAX];

  if (strchr(argv0, '/') == NULL) {
    char *exec_path = find_executable_in_path(argv0);
    if (exec_path == NULL) {
      FATAL("Cannot find the compiler (%s) in PATH", argv0);
    }
    if (!realpath(exec_path, path)) {
      FATAL("Cannot get real path of the compiler (%s): %s", exec_path, strerror(errno));
    }
    ck_free(exec_path);
  } else {
    if (!realpath(argv0, path)) {
      FATAL("Cannot get real path of the compiler (%s): %s", argv0, strerror(errno));
    }
  }

  slash = strrchr(path, '/');

  if (slash) {
    char *dir;
    *slash = 0;
    dir = ck_strdup(path);
    *slash = '/';

    taint_path = alloc_printf("%s/../lib/symsan/TaintPass.so", dir);
    if (!access(taint_path, R_OK)) {
      obj_path = alloc_printf("%s/../lib/symsan", dir);
    } else {
      FATAL("Unable to find 'TaintPass.so' at %s", path);
    }

    ck_free(dir);
  }
}

static void check_type(char *name) {
  if (!strcmp(name, "ko-clang++")) {
    is_cxx = 1;
  }
}

static u8 check_if_assembler(u32 argc, char **argv) {
  /* Check if a file with an assembler extension ("s" or "S") appears in argv */

  while (--argc) {
    const char *cur = *(++argv);

    const char *ext = strrchr(cur, '.');
    if (ext && (!strcmp(ext + 1, "s") || !strcmp(ext + 1, "S"))) {
      return 1;
    }
  }

  return 0;
}

static void add_runtime() {
  if (getenv("KO_LIBRARY_PATH")) {
    cc_params[cc_par_cnt++] = alloc_printf("-L%s", getenv("KO_LIBRARY_PATH"));
  }

  cc_params[cc_par_cnt++] = "-Wl,--whole-archive";
  cc_params[cc_par_cnt++] = alloc_printf("%s/libdfsan_rt-x86_64.a", obj_path);
  cc_params[cc_par_cnt++] = "-Wl,--no-whole-archive";
  cc_params[cc_par_cnt++] =
      alloc_printf("-Wl,--dynamic-list=%s/libdfsan_rt-x86_64.a.syms", obj_path);

  cc_params[cc_par_cnt++] = alloc_printf("-Wl,-T%s/taint.ld", obj_path);

  if (is_cxx && !use_native_cxx) {
    // cc_params[cc_par_cnt++] = "-Wl,--whole-archive";
    cc_params[cc_par_cnt++] = alloc_printf("%s/libc++.a", obj_path);
    cc_params[cc_par_cnt++] = alloc_printf("%s/libc++abi.a", obj_path);
    cc_params[cc_par_cnt++] = alloc_printf("%s/libunwind.a", obj_path);
    // cc_params[cc_par_cnt++] = "-Wl,--no-whole-archive";
  } else {
    cc_params[cc_par_cnt++] = "-lc++";
    cc_params[cc_par_cnt++] = "-lc++abi";
    cc_params[cc_par_cnt++] = "-l:libunwind.so";
  }
  cc_params[cc_par_cnt++] = "-lrt";

  cc_params[cc_par_cnt++] = "-Wl,--no-as-needed";
  cc_params[cc_par_cnt++] = "-Wl,--gc-sections"; // if darwin -Wl, -dead_strip
  cc_params[cc_par_cnt++] = "-ldl";
  cc_params[cc_par_cnt++] = "-lpthread";
  cc_params[cc_par_cnt++] = "-lm";

  if (use_native_zlib) {
    cc_params[cc_par_cnt++] = "-lz";
  }

  if (getenv("KO_USE_Z3")) {
    cc_params[cc_par_cnt++] = "-Wl,--whole-archive";
    cc_params[cc_par_cnt++] = alloc_printf("%s/libZ3Solver.a", obj_path);
    cc_params[cc_par_cnt++] = "-Wl,--no-whole-archive";
    cc_params[cc_par_cnt++] = "-lz3";
  }

  if (getenv("KO_USE_FASTGEN")) {
    cc_params[cc_par_cnt++] = "-Wl,--whole-archive";
    cc_params[cc_par_cnt++] = alloc_printf("%s/libFastgen.a", obj_path);
    cc_params[cc_par_cnt++] = "-Wl,--no-whole-archive";
  }
}

static void add_taint_pass() {
  cc_params[cc_par_cnt++] = "-fexperimental-new-pass-manager";
  cc_params[cc_par_cnt++] = alloc_printf("-fplugin=%s", taint_path); // to enable options
  cc_params[cc_par_cnt++] = alloc_printf("-fpass-plugin=%s", taint_path);
  cc_params[cc_par_cnt++] = "-mllvm";
  cc_params[cc_par_cnt++] =
      alloc_printf("-taint-abilist=%s/dfsan_abilist.txt", obj_path);

  if (use_native_zlib) {
    cc_params[cc_par_cnt++] = "-mllvm";
    cc_params[cc_par_cnt++] =
        alloc_printf("-taint-abilist=%s/zlib_abilist.txt", obj_path);
  }

  if (getenv("KO_TRACE_FP")) {
    cc_params[cc_par_cnt++] = "-mllvm";
    cc_params[cc_par_cnt++] = "-taint-trace-float-pointer";
  }

  if (getenv("KO_NO_TRACE_BOUND")) {
    cc_params[cc_par_cnt++] = "-mllvm";
    cc_params[cc_par_cnt++] = "-taint-trace-bound=false";
  }

  if (getenv("KO_SOLVE_UB")) {
    cc_params[cc_par_cnt++] = "-mllvm";
    cc_params[cc_par_cnt++] = "-taint-solve-ub=true";
  }

  if (is_cxx && use_native_cxx) {
    cc_params[cc_par_cnt++] = "-mllvm";
    cc_params[cc_par_cnt++] =
        alloc_printf("-taint-abilist=%s/libc++_abilist.txt", obj_path);
  }
}

static void edit_params(u32 argc, char **argv) {

  u8 fortify_set = 0, asan_set = 0, x_set = 0, maybe_linking = 1, bit_mode = 0;
  u8 maybe_assembler = 0;
  char *name;

  cc_params = ck_alloc((argc + 128) * sizeof(char *));

  name = strrchr(argv[0], '/');
  if (!name)
    name = argv[0];
  else
    name++;
  check_type(name);

  if (is_cxx) {
    char *alt_cxx = getenv("KO_CXX");
    cc_params[0] = alt_cxx ? alt_cxx : "clang++";
  } else {
    char *alt_cc = getenv("KO_CC");
    cc_params[0] = alt_cc ? alt_cc : "clang";
  }

  maybe_assembler = check_if_assembler(argc, argv);

  use_native_cxx = getenv("KO_USE_NATIVE_LIBCXX") ? 1 : 0;

  use_native_zlib = getenv("KO_NO_NATIVE_ZLIB") ? 0 : 1;

  /* Detect stray -v calls from ./configure scripts. */
  if (argc == 1 && !strcmp(argv[1], "-v"))
    maybe_linking = 0;

  while (--argc) {
    char *cur = *(++argv);
    // FIXME
    if (!strcmp(cur, "-O1") || !strcmp(cur, "-O2") || !strcmp(cur, "-O3")) {
      //continue;
    }
    if (!strcmp(cur, "-m32"))
      bit_mode = 32;
    if (!strcmp(cur, "-m64"))
      bit_mode = 64;

    if (!strcmp(cur, "-x"))
      x_set = 1;

    if (!strcmp(cur, "-c") || !strcmp(cur, "-S") || !strcmp(cur, "-E"))
      maybe_linking = 0;

    if (!strncmp(cur, "-fsanitize=", strlen("-fsanitize="))) {
      continue; // doesn't work together
    }

    if (!use_native_zlib && !strcmp(cur, "-lz"))
      continue; // ignore -lz if we are using our own zlib

    if (strstr(cur, "FORTIFY_SOURCE"))
      fortify_set = 1;

    if (!strcmp(cur, "-shared"))
      maybe_linking = 0;

    if (!strcmp(cur, "-Wl,-z,defs") || !strcmp(cur, "-Wl,--no-undefined"))
      continue;

    if (strstr(cur, "-stdlib=") == cur) {
      // XXX: use native if the target prefers stdlibc++?
      continue;
    }

    if (!strcmp(cur, "-lc++") || !strcmp(cur, "-lc++abi") || !strcmp(cur, "-lunwind") ||
        strstr(cur, "-l:libc++.so") == cur ||
        strstr(cur, "-l:libc++abi.so") == cur ||
        strstr(cur, "-l:libunwind.so") == cur) {
      // skip libc++, libc++abi, and libunwind
      continue;
    }

    if (strstr(cur, "libSymsanProxy.o")) {
      char* last = *(argv - 1);
      if (last) {
        if (!strcmp(last, "-I")) { // remove the -I
          cc_params[cc_par_cnt - 1] = cur;
          continue;
        }
        if (!strcmp(last, "-L")) { // remove the -L
          cc_params[cc_par_cnt - 1] = cur;
          continue;
        }
      }
    }

    cc_params[cc_par_cnt++] = cur;
  }

  if (getenv("KO_CONFIG")) {
    cc_params[cc_par_cnt] = NULL;
    return;
  }

  if (!maybe_assembler) {
    add_taint_pass();
  }

  cc_params[cc_par_cnt++] = "-pie";
  cc_params[cc_par_cnt++] = "-fpic";
  cc_params[cc_par_cnt++] = "-Qunused-arguments";
  cc_params[cc_par_cnt++] = "-fno-vectorize";
  cc_params[cc_par_cnt++] = "-fno-slp-vectorize";
#if 0
  cc_params[cc_par_cnt++] = "-mno-mmx";
  cc_params[cc_par_cnt++] = "-mno-sse";
  cc_params[cc_par_cnt++] = "-mno-sse2";
  cc_params[cc_par_cnt++] = "-mno-avx";
  cc_params[cc_par_cnt++] = "-mno-sse3";
  cc_params[cc_par_cnt++] = "-mno-sse4.1";
  cc_params[cc_par_cnt++] = "-mno-sse4.2";
  cc_params[cc_par_cnt++] = "-mno-ssse3";
  cc_params[cc_par_cnt++] = "-mno-avx2";
  cc_params[cc_par_cnt++] = "-mno-avx512f";
  cc_params[cc_par_cnt++] = "-mno-avx512bw";
  cc_params[cc_par_cnt++] = "-mno-avx512dq";
  cc_params[cc_par_cnt++] = "-mno-avx512vl";
#endif

  if (getenv("KO_HARDEN")) {
    cc_params[cc_par_cnt++] = "-fstack-protector-all";

    if (!fortify_set)
      cc_params[cc_par_cnt++] = "-D_FORTIFY_SOURCE=2";
  }

  if (!getenv("KO_DONT_OPTIMIZE")) {
    cc_params[cc_par_cnt++] = "-g";
    cc_params[cc_par_cnt++] = "-O3";
    cc_params[cc_par_cnt++] = "-funroll-loops";
  }

  if (is_cxx && !use_native_cxx) {
    // FIXME: or use the same header
    // cc_params[cc_par_cnt++] = alloc_printf("-I%s/../include/c++/v1", obj_path);
    cc_params[cc_par_cnt++] = "-stdlib=libc++";
  }

  if (maybe_linking) {

    if (x_set) {
      cc_params[cc_par_cnt++] = "-x";
      cc_params[cc_par_cnt++] = "none";
    }

    add_runtime();

    switch (bit_mode) {
    case 0:
      break;
    case 32:
      /* if (access(cc_params[cc_par_cnt - 1], R_OK)) */
      FATAL("-m32 is not supported by your compiler");
      break;

    case 64:
      /* if (access(cc_params[cc_par_cnt - 1], R_OK)) */
      // FATAL("-m64 is not supported by your compiler");
      break;
    }
  }

  cc_params[cc_par_cnt] = NULL;
}

/* Main entry point */

int main(int argc, char **argv) {

  if (argc < 2) {

    SAYF("\n"
         "This is a helper application for Kirenenko. It serves as a drop-in "
         "replacement\n"
         "for clang, letting you recompile third-party code with the required "
         "runtime\n"
         "instrumentation. A common use pattern would be one of the "
         "following:\n\n"

         "  CC=%s/ko-clang ./configure\n"
         "  CXX=%s/ko-clang++ ./configure\n\n"

         "You can specify custom next-stage toolchain via KO_CC and KO_CXX."
         "You can set (e.g., export) KO_CONFIG=1 to avoid problems during "
         "configure.\n"
         "Setting\n"
         "KO_HARDEN enables hardening optimizations in the compiled "
         "code.\n\n",
         "xx", "xx");

    exit(1);
  }

  find_obj(argv[0]);
  edit_params(argc, argv);
  for (int i = 0; i < cc_par_cnt; i++) {
    printf("%s ", cc_params[i]);
  }
  printf("\n");
  execvp(cc_params[0], (char **)cc_params);

  FATAL("Oops, failed to execute '%s' - check your PATH", cc_params[0]);

  return 0;
}


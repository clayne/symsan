// RUN: rm -rf %t.out
// RUN: mkdir -p %t.out
// RUN: python -c"import sys; sys.stdout.buffer.write(b'\xef\xbe\xad\xde')" > %t.bin
// RUN: clang -o %t.uninstrumented %s
// RUN: env KO_DONT_OPTIMIZE=1 KO_USE_FASTGEN=1 %ko-clang -o %t.fg %s
// RUN: env TAINT_OPTIONS="taint_file=%t.bin output_dir=%t.out" %fgtest %t.fg %t.bin
// RUN: %t.uninstrumented %t.out/id-0-0-1 | FileCheck --check-prefix=CHECK-GEN %s
// RUN: env KO_DONT_OPTIMIZE=1 KO_USE_Z3=1 %ko-clang -o %t.z3 %s
// RUN: env TAINT_OPTIONS="taint_file=%t.bin output_dir=%t.out" %t.z3 %t.bin
// RUN: %t.uninstrumented %t.out/id-0-0-1 | FileCheck --check-prefix=CHECK-GEN %s

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lib.h"

int main (int argc, char** argv) {
  if (argc < 2) {
    fprintf(stderr, "Usage: %s [file]\n", argv[0]);
    return -1;
  }

  uint32_t x = 0;
  FILE* fp = chk_fopen(argv[1], "rb");
  chk_fread(&x, sizeof(x), 1, fp);
  fclose(fp);

  if (x == 0xdeadbeef) {
    // CHECK-ORIG: Bad
    printf("Bad\n");
  }

  if (x == 0xbadf00d) {
    // CHECK-GEN: Good
    printf("Good\n");
  }
}

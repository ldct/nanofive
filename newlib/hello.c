// exercise newlib's printf (and friends) on nanofive
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fact(int n) { return n < 2 ? 1 : n * fact(n - 1); }

int main(void) {
  printf("Hello from newlib on nanofive!\n");
  printf("int: %d %i %d\n", 42, -17, 0);
  printf("unsigned/hex/oct: %u %x %X %o %#x\n", 3000000000u, 0xdead, 0xbeef, 8, 255);
  printf("long long: %lld %llx\n", -1234567890123LL, 0x123456789abcdefULL);
  printf("width/prec: [%5d] [%-5d] [%05d] [%.3s] [%8s] [%-8s]\n", 42, 42, 42, "abcdef", "hi", "hi");
  printf("char/str/pct: %c%c %s 100%%\n", 'o', 'k', "done");
  for (int i = 0; i <= 10; i++) printf("%d! = %d\n", i, fact(i));
  char buf[64];
  int n = snprintf(buf, sizeof buf, "%s-%d-%x", "snprintf", 7, 255);
  printf("%s (len %d)\n", buf, n);
  char *p = malloc(100);
  strcpy(p, "malloc works");
  puts(p);
  free(p);
  fprintf(stderr, "stderr too\n");
  return 3;
}

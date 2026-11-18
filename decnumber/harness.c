#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include "decNumber.h"
#include "cases.h"

extern void _exit(int);

/* The vendored newlib subset does not supply these. Traps are disabled in
   the test contexts; fail rather than silently ignoring an unexpected trap. */
int raise(int sig) {
  _exit(128 + sig);
  for (;;) {}
}

char *strcpy(char *dest, const char *src) {
  char *start = dest;
  while ((*dest++ = *src++) != '\0') {}
  return start;
}

/* Keep the same decNumber layout as jq, with trailing units for our inputs.
   These vectors have at most 160 coefficient digits. */
struct number {
  decNumber n;
  decNumberUnit extra[(160 + DECDPUN - 1) / DECDPUN - DECNUMUNITS];
};

_Static_assert(offsetof(struct number, extra) ==
               offsetof(decNumber, lsu) + sizeof(((decNumber *)0)->lsu),
               "coefficient units must be contiguous");

int main(void) {
  char text[160 + 15];
  for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
    struct number a, b, r;
    decContext ctx;
    decContextDefault(&ctx, DEC_INIT_BASE);
    /* Match jq's literal context; addition below uses a separate precision. */
    ctx.digits = INT32_MAX - (DECDPUN - 1) - (ctx.emax - ctx.emin - 1);
    if (ctx.digits > DEC_MAX_DIGITS) ctx.digits = DEC_MAX_DIGITS;
    ctx.traps = 0;
    decContextClearStatus(&ctx, DEC_Conversion_syntax);
    decNumberFromString(&a.n, cases[i].a, &ctx);
    if (cases[i].op != 'p') {
      decNumberFromString(&b.n, cases[i].b, &ctx);
      if (ctx.status) return 2;
      if (cases[i].op == 'c') {
        decNumberCompare(&r.n, &a.n, &b.n, &ctx);
      } else {
        ctx.digits = 17;
        ctx.round = DEC_ROUND_HALF_EVEN;
        decNumberAdd(&r.n, &a.n, &b.n, &ctx);
      }
    }
    const struct number *result = cases[i].op == 'p' ? &a : &r;
    const decNumber *n = &result->n;
    decNumberToString(n, text);
    printf("%s\t%lx\t%ld\t%ld\t%x", text, (unsigned long)ctx.status,
           (long)n->digits, (long)n->exponent, (unsigned)n->bits);
    if (!decNumberIsSpecial(n)) {
      const char *units = (const char *)result + offsetof(decNumber, lsu);
      for (int j = 0; j < (n->digits + DECDPUN - 1) / DECDPUN; j++) {
        decNumberUnit unit;
        memcpy(&unit, units + j * sizeof(unit), sizeof(unit));
        printf("\t%u", (unsigned)unit);
      }
    }
    puts("");
  }
  return 0;
}

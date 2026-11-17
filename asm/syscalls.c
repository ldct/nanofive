// newlib system call stubs for nanofive, mapped onto its RARS-style ecalls:
// a7 selects the service, arguments in a0/a1, result in a0 (see machine.ECALL)
#include <errno.h>
#include <sys/stat.h>
#undef errno
extern int errno;

static inline int ecall(int a7, int a0) {
  register int r_a0 asm("a0") = a0;
  register int r_a7 asm("a7") = a7;
  asm volatile("ecall" : "+r"(r_a0) : "r"(r_a7) : "memory");
  return r_a0;
}

void _exit(int code) { for (;;) ecall(93, code); }

int _write(int fd, const char *buf, int len) {
  if (fd != 1 && fd != 2) { errno = EBADF; return -1; }
  for (int i = 0; i < len; i++) ecall(11, (unsigned char)buf[i]);  // print char
  return len;
}

int _read(int fd, char *buf, int len) {
  if (fd != 0) { errno = EBADF; return -1; }
  int n = 0;
  while (n < len) {
    int c = ecall(12, 0);                // read char, -1 at end of input
    if (c < 0) break;
    buf[n++] = c;
    if (c == '\n') break;                // behave like a line-buffered tty
  }
  return n;
}

extern char _end[], __stack_limit[];
static char *heap_end = _end;
void *_sbrk(int incr) {
  char *prev = heap_end;
  if (heap_end + incr > __stack_limit) { errno = ENOMEM; return (void *)-1; }
  heap_end += incr;
  return prev;
}

int _close(int fd)                 { errno = EBADF; return -1; }
int _open(const char *p, int f, ...) { errno = ENOENT; return -1; }
int _lseek(int fd, int off, int w) { return 0; }
int _isatty(int fd)                { return fd <= 2; }
int _fstat(int fd, struct stat *st) { st->st_mode = S_IFCHR; return 0; }
int _getpid(void)                  { return 1; }
int _kill(int pid, int sig)        { _exit(128 + sig); }

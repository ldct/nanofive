#ifndef DECNUMBER_TEST_SIGNAL_H
#define DECNUMBER_TEST_SIGNAL_H
/* The vendored newlib subset does not include signal delivery. */
#define SIGFPE 8
int raise(int sig);
#endif

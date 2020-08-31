#include<stdlib.h>
void __VERIFIER_error() { abort(); }
void __VERIFIER_assume(int expression) { if (!expression) { LOOP: goto LOOP; }; return; }
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
      ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int() { int val; return val; }

int test() {
    int i, n, a, b;
    i = 0; a = 0; b = 0; n = __VERIFIER_nondet_int();
    __VERIFIER_assume(n >= 0 && n <= 1000000);
    while (i < n) {
        if (__VERIFIER_nondet_int()) {
            a = a + 1;
            b = b + 2;
        } else {
            a = a + 2;
            b = b + 1;
        }
        i = i + 1;
    }
    __VERIFIER_assert(a + b == 3*n);
    return 0;
}

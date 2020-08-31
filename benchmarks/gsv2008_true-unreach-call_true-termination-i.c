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
int main() {
    int x,y;
    x = -50;
    y = __VERIFIER_nondet_int();
    __VERIFIER_assume(-1000 < y && y < 1000000);
    while (x < 0) {
 x = x + y;
 y++;
    }
    __VERIFIER_assert(y > 0);
    return 0;
}

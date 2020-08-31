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
    int i, j;
    i = __VERIFIER_nondet_int();
    j = __VERIFIER_nondet_int();
    __VERIFIER_assume(i >= 0 && j >= 0);
    int x = i;
    int y = j;
    while(x != 0) {
        x--;
        y--;
    }
    if (i == j) {
        __VERIFIER_assert(y == 0);
    }
    return 0;
}

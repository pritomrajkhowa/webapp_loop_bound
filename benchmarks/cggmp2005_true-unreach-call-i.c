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
    int i,j;
    i = 1;
    j = 10;
    while (j >= i) {
        i = i + 2;
        j = -1 + j;
    }
    __VERIFIER_assert(j == 6);
    return 0;
}

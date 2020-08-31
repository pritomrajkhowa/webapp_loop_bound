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
    int x = 0;
    int y = 50;
    while(x < 100) {
 if (x < 50) {
     x = x + 1;
 } else {
     x = x + 1;
     y = y + 1;
 }
    }
    __VERIFIER_assert(y == 100);
    return 0;
}

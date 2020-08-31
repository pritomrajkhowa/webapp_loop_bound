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
    int a = __VERIFIER_nondet_int();
    int b = __VERIFIER_nondet_int();
    int res, cnt;
    __VERIFIER_assume(a <= 1000000);
    __VERIFIER_assume(0 <= b && b <= 1000000);
    res = a;
    cnt = b;
    while (cnt > 0) {
	cnt = cnt - 1;
	res = res + 1;
    }
    __VERIFIER_assert(res == a + b);
    return 0;
}

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
    int n, sum, i;
    n = __VERIFIER_nondet_int();
    if (!(1 <= n && n <= 1000)) return 0;
    sum = 0;
    for(i = 1; i <= n; i++) {
        sum = sum + i;
    }
    __VERIFIER_assert(2*sum == n*(n+1));
    return 0;
}

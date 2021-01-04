#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>

#define MAX ((__int64_t)1 << 62) - 1

void divstep(int *d, __int64_t *f, __int64_t *g) {
    if ((0 < *d) && (*g & 1)) {
      *d = -*d;
      __int64_t tmp;
      tmp = *f;
      *f = *g;
      *g = -tmp;
    }
    __int64_t g0 = *g & 1;
    *d = 1 + *d;
    *g = (*g + g0 * *f) / 2;
}

int divsteps_at_least(int n, int d, __int64_t f, __int64_t g) {
  while ((g != 0) && (n > 0)) {
    divstep(&d,&f,&g);
    n -= 1;
  }
  return (g != 0);
}

int divsteps(int d, __int64_t f, __int64_t g) {
  int n = 0;
  while (g != 0) {
    divstep(&d,&f,&g);
    n++;
  }
  return n;
}

int divsteps_fast(int d, __int64_t f, __int64_t g) {
  int n = 0;
  while (g != 0) {
    if ((0 < d) && (g & 1)) {
      d = -d;
      __int64_t tmp;
      tmp = f;
      f = g;
      g = -tmp;
    }
    __int64_t g0 = g & 1;
    d = 1 + d;
    g = (g + g0 * f) / 2;
    n += 1;
  }
  return n;
}

__int64_t w(int n) {
  __int64_t a, b, res, length;
  
  a = 1;
  b = 0;
  res = MAX;
  while (a * a < res) {
    length = a * a + b * b;
    if (length >= res) {
      a = a + 2;
      b = 0;
    }
    else if ((divsteps_at_least(n-1,1,a,b/2)) || (divsteps_at_least(n-1,1,a,-b/2))) {
      res = ((res < length) ? res : length);
      a = a + 2;
      b = 0;
    }
    else {
      b = b + 2;
    }
  }
  return res;
}

void table(int bound, __int64_t res[60]) {
  __int64_t a, b, a2, length;
  __int64_t large_bound = (__int64_t)1 << bound;
  for (int i = 0; i < 60; i++) res[i] = MAX;
  
  a = 1;
  b = 0;
  a2 = 1;
  while (a2 < large_bound) {
		if (a % 101 == 0) printf("%f%% done\n", (a2 * 100.0) / large_bound);
    a2 = a * a;
    __int64_t length = 0;
    while (length < large_bound) {
      length = a2 + b * b;			    
      int steps = divsteps(1,a,b/2);
      int steps_opp = divsteps(1,a,-b/2);
      int n = ((steps < steps_opp) ? steps_opp : steps);
      for (int i = 0; i <= n; i++) {
				if (length < res[i]) {
					res[i] = length;
				}
			}
      b += 2;
    }
    b = 0;
    a += 2;
  }
}

int main(int argc, char *argv[]) {
  int n;
  if (argc > 1) {
    n = (int)strtol(argv[1], NULL, 10);
    if ((argc > 2) && (strncmp(argv[2], "all", 3) == 0)) {
      __int64_t res[60];
      table(n, res);
      for (int i = 0; i < 60; i++) if (res[i] != MAX) printf("W%i = %" PRId64 "\n", i, res[i]);
    }
    else {
      __int64_t res = w(n);
      printf("%" PRId64 "\n", res);
    }
  }
}

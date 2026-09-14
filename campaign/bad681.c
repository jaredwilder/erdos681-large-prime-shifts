// Exact window-bad prime search for Erdos 681 residual: prime p is bad iff no odd k>=3 with
// k^4 < p-1+k has p-1+k composite and lpf(p-1+k) > k^2. Segmented sieve, OpenMP.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
#define SEG (1u<<24)
#define PAD 4096
int main(int argc, char **argv) {
    uint64_t LO = strtoull(argv[1], 0, 10), HI = strtoull(argv[2], 0, 10);
    uint64_t B = (uint64_t)sqrtl((long double)(HI + PAD)) + 2;
    char *s = calloc(B + 1, 1); uint32_t *P = malloc(sizeof(uint32_t) * (B / 2 + 10)); size_t np = 0;
    for (uint64_t i = 2; i <= B; i++) if (!s[i]) { P[np++] = i; for (uint64_t j = i * i; j <= B; j += i) s[j] = 1; }
    uint64_t nseg = (HI - LO + SEG - 1) / SEG, total_primes = 0, total_bad = 0;
    #pragma omp parallel for schedule(dynamic,1) reduction(+:total_primes,total_bad)
    for (uint64_t g = 0; g < nseg; g++) {
        uint64_t a = LO + g * SEG, b = a + SEG; if (b > HI) b = HI;
        uint64_t len = b - a + PAD;
        uint32_t *lpf = calloc(len, sizeof(uint32_t));
        for (size_t t = 0; t < np; t++) {
            uint64_t q = P[t], st = (a + q - 1) / q * q; if (st < q * q) st = q * q;
            for (uint64_t m = st; m < a + len; m += q) if (!lpf[m - a]) lpf[m - a] = (uint32_t)q;
        }
        for (uint64_t i = 0; i < b - a; i++) {
            uint64_t p = a + i; if (p < 5 || lpf[i]) continue;
            total_primes++;
            int bad = 1;
            for (uint64_t k = 3; k * k * k * k < p - 1 + k; k += 2) {
                uint32_t q = lpf[i + k - 1];
                if (q && (uint64_t)q > k * k) { bad = 0; break; }
            }
            if (bad) {
                total_bad++;
                #pragma omp critical
                { printf("BAD %llu\n", (unsigned long long)p); }
            }
        }
        free(lpf);
    }
    printf("RANGE %llu %llu PRIMES %llu BAD %llu\n", (unsigned long long)LO, (unsigned long long)HI,
           (unsigned long long)total_primes, (unsigned long long)total_bad);
    return 0;
}

// exact delta(K): share of reduced residues p mod P_ODD(K^2) with every odd 3<=k<=K killed
// (some odd prime q<=k^2 with q | p-1+k). Distribution over hit-masks, prime by prime.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int K = atoi(argv[1]);
    int n = (K - 1) / 2;               // shifts k = 3,5,...,K  -> index i = (k-3)/2
    size_t S = (size_t)1 << n;
    double *d = calloc(S, sizeof(double)), *e = calloc(S, sizeof(double));
    d[0] = 1.0;
    int Q = 2 * K;
    char *comp = calloc(Q + 1, 1);
    for (int i = 2; i * i <= Q; i++) if (!comp[i]) for (int j = i * i; j <= Q; j += i) comp[j] = 1;
    for (int q = 3; q <= Q; q++) {
        if (comp[q]) continue;
        // masks by residue r in 1..q-1 : kill k iff (r - 1 + k) % q == 0 and q <= k*k
        unsigned long long masks[64]; double cnt[64]; int nm = 0; double zero = q - 1;
        for (int i = 0; i < n; i++) {
            int k = 3 + 2 * i; if (q > k * k) continue;
            int r = ((1 - k) % q + q) % q; if (r == 0) continue;
            // accumulate mask for residue r
            int found = -1;
            for (int t = 0; t < nm; t++) if ((int)cnt[t] == -r) { found = t; break; }
            if (found < 0) { found = nm++; masks[found] = 0; cnt[found] = -r; }
            masks[found] |= 1ULL << i;
        }
        if (nm == 0) continue;
        zero = q - 1 - nm;
        memset(e, 0, S * sizeof(double));
        for (size_t s = 0; s < S; s++) {
            double v = d[s]; if (v == 0) continue;
            e[s] += v * zero / (q - 1);
            for (int t = 0; t < nm; t++) e[s | masks[t]] += v / (q - 1);
        }
        double *tmp = d; d = e; e = tmp;
    }
    { double cum[64] = {0}; for (size_t s = 0; s < S; s++) cum[n - __builtin_popcountll(s)] += d[s]; double mu = 0; for (int u = 0; u <= n; u++) mu += u * cum[u]; double acc = 0; int h = (int)(mu / 2); for (int u = 0; u <= h; u++) acc += cum[u]; printf("K %d shifts %d mu_red %.6f P_U_le_half %.6e\n", K, n, mu, acc); }
    return 0;
}

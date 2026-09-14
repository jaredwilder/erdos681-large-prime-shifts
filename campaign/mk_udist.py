src = open('deltaK.c').read()
src = src.replace('int Q = K * K;', 'int Q = 2 * K;')
old = 'printf("K %d shifts %d delta %.12e\\n", K, n, d[S - 1]);'
assert old in src
new = ('{ double cum[64] = {0}; for (size_t s = 0; s < S; s++) cum[n - __builtin_popcountll(s)] += d[s];'
       ' double mu = 0; for (int u = 0; u <= n; u++) mu += u * cum[u];'
       ' double acc = 0; int h = (int)(mu / 2); for (int u = 0; u <= h; u++) acc += cum[u];'
       ' printf("K %d shifts %d mu_red %.6f P_U_le_half %.6e\\n", K, n, mu, acc); }')
open('Udist.c', 'w').write(src.replace(old, new))

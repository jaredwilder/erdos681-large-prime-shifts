src = open('deltaK.c').read()
old = 'printf("K %d shifts %d delta %.12e\\n", K, n, d[S - 1]);'
assert old in src
new = ('{ double m1 = 0, m2 = 0; for (size_t s = 0; s < S; s++) { int u = n - __builtin_popcountll(s); m1 += u * d[s]; m2 += (double)u * u * d[s]; }'
       ' printf("K %d shifts %d mu %.6f var %.6f var_over_mu %.6f delta %.6e\\n", K, n, m1, m2 - m1 * m1, (m2 - m1 * m1) / m1, d[S - 1]); }')
open('Uvar.c', 'w').write(src.replace(old, new))

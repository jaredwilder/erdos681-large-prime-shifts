import sys, json, math, hashlib
N=int(sys.argv[1])
sp=bytearray([0])*(N+10**4); lpf=list(range(len(sp)))
L=len(sp)
for i in range(2,int(L**.5)+1):
    if lpf[i]==i:
        for j in range(i*i,L,i):
            if lpf[j]==j: lpf[j]=i
bad=[];recK=0;recNorm=0;rows=0
for p in range(5,N):
    if lpf[p]!=p: continue
    rows+=1; k=3; found=None
    while k**4 < p-1+k:
        m=p-1+k; q=lpf[m]
        if q!=m and q>k*k: found=(k,q); break
        k+=2
    if found is None: bad.append(p)
    else:
        if found[0]>recK: recK=found[0]; print("recK",p,found)
out={"N":N,"primes":rows,"bad":bad,"maxK":recK}
s=json.dumps(out); print(s); open(f"atlas_{N}.json","w").write(s)
print("HASH",hashlib.sha256(s.encode()).hexdigest())

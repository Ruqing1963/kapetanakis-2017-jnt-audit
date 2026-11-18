"""Verification for the note on G. Kapetanakis, "Prescribing coefficients of invariant irreducible
polynomials", J. Number Theory 180 (2017) 615-628 (author's repository text of 24 May 2017).

Run:  python verify_kapetanakis_jnt2017.py [gamma] [diag] [pure] [wsum] [thresh] [truth] [direct] [closure]
                                           [lemmas] [figures]                                  (default: all)
Writes ../data/*.json, ../data/verify_kapetanakis_jnt2017.txt (log), ../figures/fig_kapetanakis_jnt2017_1.pdf
and ../figures/fig_kapetanakis_jnt2017_2.pdf.

Action (paper, eq. (1)):  A o F = (bX+d)^deg(F) F((aX+c)/(bX+d)),  A = (a b; c d).

Parts
  gamma  : Section 2 of the paper, A = (1 0; alpha 1), Q = P(X^p - alpha^(p-1) X).  The m-th coefficient of Q
           against  sum_i gamma_i (P^R)_i  with gamma_i as printed in Theorem 2.8 and as corrected; Table 1.
  diag   : Section 3, A = U B U^-1, B = diag(alpha, 1), U = (a 0; c d):  Q = a^-n' d^n' P0(((aX+c)/d)^r).
           Formula q_m = a^-n' sum_i delta_i (P0)_(n-i); the case mu = 0 of Theorem 3.4(2).
  pure   : Section 3, [A] = [B]:  P0(X^r) irreducible  <=>  (-1)^n p_0 in C;  which kappa are attained.
  wsum   : the weighted sums w of both sections computed exactly and compared with main term and error bound
           (identity sum Lambda(H), c_j(psi) = -1, corrected conditions (S2) and (S3) of the note).
  thresh : the paper's inequality (5) and Table 2; inequality (8) and Table 3; thresholds of (S2) and (S3).
  truth  : exhaustive check of the conclusion of Theorem 2.8(4) for small (q, n).
  direct : the lower bounds (D2), (D3) of the note (counting over all admissible residue classes, no weights)
           against exact counts.
  closure: the finite ranges where (D2), (D3) are not positive, and an explicit irreducible polynomial for
           every case there (uniformly in the linear form and in kappa).
  lemmas : prescribed trace coefficient / constant term; R_n <= 2 q^(n/2); W(m) <= 4.9 m^(1/4); Table 1.
  figures: the two figures of the note.
"""
import sys, os, json, math, itertools, random
from fractions import Fraction
from sympy import Poly, symbols, factorint, primerange, isprime

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(ROOT, "data")
FIG = os.path.join(ROOT, "figures")
os.makedirs(DATA, exist_ok=True)
os.makedirs(FIG, exist_ok=True)
LOGF = open(os.path.join(DATA, "verify_kapetanakis_jnt2017.txt"), "a", encoding="utf8")
XS = symbols("x")


def say(*a):
    s = " ".join(str(t) for t in a)
    print(s, flush=True)
    LOGF.write(s + "\n")
    LOGF.flush()


def dump(name, obj):
    with open(os.path.join(DATA, name), "w", encoding="utf8") as fh:
        json.dump(obj, fh, indent=1)


# ------------------------------------------------------------------------------------------------- fields
class GF:
    """F_q, q = p^e.  Elements 0..q-1; base-p digits are coordinates; 0..p-1 is the prime field."""
    _cache = {}

    def __new__(cls, q):
        if q not in cls._cache:
            cls._cache[q] = super().__new__(cls)
            cls._cache[q]._init(q)
        return cls._cache[q]

    def _init(self, q):
        (p, e), = factorint(q).items()
        self.q, self.p, self.e = q, p, e
        if e == 1:
            red = None
        else:
            for tail in itertools.product(range(p), repeat=e):
                if Poly(XS ** e + sum(c * XS ** i for i, c in enumerate(tail)), XS, modulus=p).is_irreducible:
                    red = [(-c) % p for c in tail]
                    break
        dig = [[(a // p ** i) % p for i in range(e)] for a in range(q)]
        und = lambda d: sum(c * p ** i for i, c in enumerate(d))
        self.addt = [[und([(x + y) % p for x, y in zip(dig[a], dig[b])]) for b in range(q)] for a in range(q)]
        self.negt = [und([(-x) % p for x in dig[a]]) for a in range(q)]

        def mul(a, b):
            prod = [0] * (2 * e - 1)
            for i, x in enumerate(dig[a]):
                for j, y in enumerate(dig[b]):
                    prod[i + j] = (prod[i + j] + x * y) % p
            for k in range(2 * e - 2, e - 1, -1):
                c = prod[k]
                if c:
                    prod[k] = 0
                    for i in range(e):
                        prod[k - e + i] = (prod[k - e + i] + c * red[i]) % p
            return und(prod[:e])
        self.mult = [[mul(a, b) for b in range(q)] for a in range(q)]
        self.invt = [0] * q
        for a in range(1, q):
            self.invt[a] = next(b for b in range(1, q) if self.mult[a][b] == 1)
        self.ordt = [0] * q
        for a in range(1, q):
            k, x = 1, a
            while x != 1:
                x = self.mult[x][a]
                k += 1
            self.ordt[a] = k
        self.gen = next(a for a in range(1, q) if self.ordt[a] == q - 1)

    def pw(self, a, k):
        if k < 0:
            a, k = self.invt[a], -k
        r = 1
        while k:
            if k & 1:
                r = self.mult[r][a]
            a = self.mult[a][a]
            k >>= 1
        return r

    def tr(self, a):
        """absolute trace F_q -> F_p (as integer 0..p-1)."""
        s, x = 0, a
        for _ in range(self.e):
            s = self.addt[s][x]
            x = self.pw(x, self.p)
        return s

    def ints(self, k):
        return k % self.p

    # ---- polynomials: lists, low degree first, no trailing zeros
    def trim(self, a):
        while a and a[-1] == 0:
            a.pop()
        return a

    def padd(self, a, b):
        n = max(len(a), len(b))
        a2, b2 = a + [0] * (n - len(a)), b + [0] * (n - len(b))
        return self.trim([self.addt[x][y] for x, y in zip(a2, b2)])

    def pscale(self, a, c):
        return self.trim([self.mult[x][c] for x in a])

    def psub(self, a, b):
        return self.padd(a, [self.negt[x] for x in b])

    def pmul(self, a, b):
        if not a or not b:
            return []
        out = [0] * (len(a) + len(b) - 1)
        add, mul = self.addt, self.mult
        for i, x in enumerate(a):
            if x:
                mx = mul[x]
                for j, y in enumerate(b):
                    if y:
                        out[i + j] = add[out[i + j]][mx[y]]
        return self.trim(out)

    def pmod(self, a, f):
        a = list(a)
        df = len(f) - 1
        iv = self.invt[f[-1]]
        add, mul, neg = self.addt, self.mult, self.negt
        while len(a) - 1 >= df and a:
            c = mul[a[-1]][iv]
            if c:
                nc = neg[c]
                sh = len(a) - 1 - df
                for i, y in enumerate(f):
                    if y:
                        a[sh + i] = add[a[sh + i]][mul[nc][y]]
            a.pop()
            self.trim(a)
        return a

    def pgcd(self, a, b):
        a, b = list(a), list(b)
        while b:
            a, b = b, self.pmod(a, b)
        return self.pscale(a, self.invt[a[-1]]) if a else []

    def ppowmod(self, a, k, f):
        r = [1]
        a = self.pmod(a, f)
        while k:
            if k & 1:
                r = self.pmod(self.pmul(r, a), f)
            a = self.pmod(self.pmul(a, a), f)
            k >>= 1
        return r

    def compose(self, P, G):
        out = []
        for c in reversed(P):
            out = self.padd(self.pmul(out, G), [c] if c else [])
        return out

    def is_irreducible(self, f):
        n = len(f) - 1
        if n <= 0:
            return False
        if n == 1:
            return True
        x = [0, 1]
        h, hs = x, {}
        for k in range(1, n + 1):
            h = self.ppowmod(h, self.q, f)
            hs[k] = h
        if self.psub(hs[n], x):
            return False
        for l in factorint(n):
            g = self.pgcd(self.psub(hs[n // l], x), f)
            if len(g) != 1:
                return False
        return True

    def monic_irreducibles(self, n):
        key = ("irr", n)
        if key not in self.__dict__:
            out = []
            for tail in itertools.product(range(self.q), repeat=n):
                f = list(tail) + [1]
                if self.is_irreducible(f):
                    out.append(f)
            self.__dict__[key] = out
        return self.__dict__[key]

    def binom(self, N, k):
        if k < 0 or k > N:
            return 0
        return math.comb(N, k) % self.p


def prime_powers(lo, hi):
    out = []
    for q in range(lo, hi + 1):
        f = factorint(q)
        if len(f) == 1:
            out.append(q)
    return out


def pi_q(q, n):
    """number of monic irreducible polynomials of degree n over F_q."""
    s = 0
    for d in range(1, n + 1):
        if n % d == 0:
            f = factorint(d)
            if all(e == 1 for e in f.values()):
                s += (-1) ** len(f) * q ** (n // d)
    return s // n


# ------------------------------------------------------------------------------------------------- gamma
def gamma_corrected(K, alpha, n, m):
    """gamma_i, 0 <= i <= n, with q_m = sum_i gamma_i (P^R)_i  (corrected formula)."""
    p = K.p
    g = [0] * (n + 1)
    ap = K.pw(alpha, p - 1)
    nap = K.negt[ap]
    for i in range(max(0, n - m), n - (-(-m // p)) + 1):
        if (i - (n - m)) % (p - 1) == 0:
            k = (m - n + i) // (p - 1)
            g[i] = K.mult[K.binom(n - i, k)][K.pw(nap, n - i - k)]
    return g


def gamma_printed(K, alpha, n, m):
    """gamma_i as printed in Theorem 2.8; None where (m-n+i)/(p-1) is not an integer."""
    p = K.p
    g = [0] * (n + 1)
    na = K.negt[alpha]
    for i in range(max(0, n - m), n - (-(-m // p)) + 1):
        if (i - (m - n)) % (p - 1) == 0:
            if (m - n + i) % (p - 1):
                g[i] = None
            else:
                g[i] = K.mult[K.binom(n - i, (m - n + i) // (p - 1))][K.pw(na, p - n + i)]
    return g


def part_gamma():
    say("== gamma: coefficient formula of Theorem 2.8 ==")
    rng = random.Random(2017)
    tot = bad_c = bad_p = undef_p = 0
    byq = {}
    for q in [2, 3, 4, 5, 7, 8, 9]:
        K = GF(q)
        p = K.p
        nmax = {2: 9, 3: 6, 4: 6, 5: 4, 7: 3, 8: 4, 9: 4}[q]
        t = bc = bp = up = 0
        for alpha in range(1, q):
            G = [0, K.negt[K.pw(alpha, p - 1)]] + [0] * (p - 2) + [1]      # X^p - alpha^(p-1) X
            for n in range(1, nmax + 1):
                Ps = [[rng.randrange(q) for _ in range(n)] + [1] for _ in range(4)]
                Qs = [K.compose(P, G) for P in Ps]
                for m in range(0, p * n + 1):
                    gc, gp = gamma_corrected(K, alpha, n, m), gamma_printed(K, alpha, n, m)
                    okc = okp = True
                    for P, Q in zip(Ps, Qs):
                        qm = Q[m] if m < len(Q) else 0
                        PR = P[::-1]
                        sc = 0
                        for i in range(n + 1):
                            sc = K.addt[sc][K.mult[gc[i]][PR[i]]]
                        okc &= sc == qm
                        if None in gp:
                            okp = None
                        elif okp is not None:
                            sp = 0
                            for i in range(n + 1):
                                sp = K.addt[sp][K.mult[gp[i]][PR[i]]]
                            okp &= sp == qm
                    t += 1
                    bc += not okc
                    up += okp is None
                    bp += okp is False
        byq[q] = [t, bc, bp, up]
        say(f"q={q}: {t} tuples (alpha,n,m), 4 random P each; corrected formula wrong in {bc};"
            f" printed formula wrong in {bp}, undefined (non-integral lower index) in {up}")
        tot += t; bad_c += bc; bad_p += bp; undef_p += up
    say(f"total: {tot} tuples; corrected wrong: {bad_c}; printed wrong: {bad_p}; printed undefined: {undef_p}")
    # Table 1 of the paper: q = 3, degree 6, A = (1 0; 2 1)
    K = GF(3)
    inv = [f for f in K.monic_irreducibles(6) if K.compose(f, [2, 1]) == f]
    say("Table 1, A=(1 0; 2 1): invariant irreducibles of degree 6 over F_3 (coefficients X^0..X^6):", inv)
    gp, gc = gamma_printed(K, 2, 2, 4), gamma_corrected(K, 2, 2, 4)
    say(f"   m=4: coefficient of X^4 in each: {[f[4] for f in inv]}; printed gamma_0 = {gp[0]}, corrected gamma_0 = {gc[0]}")
    dump("gamma.json", {"by_q": byq, "table1": inv, "gamma0_printed": gp[0], "gamma0_corrected": gc[0]})


# -------------------------------------------------------------------------------------------------- diag
def frakC(K, r):
    return [x for x in range(1, K.q) if math.gcd(r, (K.q - 1) // K.ordt[x]) == 1]


def pure_invariants(K, r, n):
    """P0 in I_n with P0(X^r) irreducible (direct test)."""
    key = ("pure", r, n)
    if key not in K.__dict__:
        out = []
        for P in K.monic_irreducibles(n):
            Q = [0] * (r * n + 1)
            for j, c in enumerate(P):
                Q[j * r] = c
            if K.is_irreducible(Q):
                out.append(P)
        K.__dict__[key] = out
    return K.__dict__[key]


def part_diag():
    say("== diag: A = U B U^-1, B = diag(alpha,1), U = (a 0; c d) ==")
    cases = collapse_ok = paper_ok = formula_bad = inv_bad = 0
    fig = []
    for q in [3, 4, 5, 7, 8, 9, 11, 13]:
        K = GF(q)
        g = K.gen
        for alpha in range(2, q):
            r = K.ordt[alpha]
            C = frakC(K, r)
            for n in (1, 2, 3):
                npr = r * n
                if q ** n > 2500 or npr > 24:
                    continue
                P0s = pure_invariants(K, r, n)
                if not P0s:
                    continue
                for (a, c, d) in [(1, 1, 1), (1, g, 1), (g, 1, 1), (1, 1, g)]:
                    # Q = a^-n' d^n' P0(((aX+c)/d)^r)
                    lin = [K.mult[c][K.invt[d]], K.mult[a][K.invt[d]]]
                    linr = [1]
                    for _ in range(r):
                        linr = K.pmul(linr, lin)
                    scale = K.mult[K.pw(K.invt[a], npr)][K.pw(d, npr)]
                    Qs = [K.pscale(K.compose(P, linr), scale) for P in P0s]
                    # invariance under A = (alpha 0; c(alpha-1)/a 1):  Q(alpha X + c(alpha-1)/a) ~ Q
                    cA = K.mult[K.mult[c][K.addt[alpha][K.negt[1]]]][K.invt[a]]
                    for Q in Qs[:3]:
                        Q2 = K.compose(Q, [cA, alpha])
                        Q2 = K.pscale(Q2, K.invt[Q2[-1]])
                        inv_bad += Q2 != Q
                    for m in range(0, npr):
                        top = n - (-(-m // r))
                        delta = [K.mult[K.mult[K.binom((n - i) * r, m)][K.pw(a, m)]]
                                 [K.mult[K.pw(c, (n - i) * r - m)][K.pw(d, i * r)]] for i in range(top + 1)]
                        ainv = K.pw(K.invt[a], npr)
                        for P, Q in zip(P0s, Qs):
                            s = 0
                            for i in range(top + 1):
                                s = K.addt[s][K.mult[delta[i]][P[n - i]]]
                            formula_bad += K.mult[s][ainv] != Q[m]
                        nz = [i for i in range(top + 1) if delta[i]]
                        if nz == [0]:                                     # mu = 0
                            cases += 1
                            vals = sorted({Q[m] for Q in Qs})
                            collapse_ok += vals == [K.mult[delta[0]][ainv]]
                            paper_ok += vals == sorted({K.mult[delta[0]][x] for x in C})
                            if (a, c, d) == (1, 1, 1) and n == 1 and m == npr - 1:
                                fig.append([q, r, len(vals), len(C)])
    say(f"formula q_m = a^-n' sum_i delta_i (P0)_(n-i): violations {formula_bad}; invariance violations {inv_bad}")
    say(f"mu = 0 cases: {cases}; value set = {{delta_0 a^-n'}} in {collapse_ok}; value set = delta_0*C (paper) in {paper_ok}")
    K = GF(5)
    inv = [f for f in K.monic_irreducibles(2) if K.compose(f, [1, 4]) == f]
    say("q=5, A=(4 0; 1 1), n'=2: invariant irreducibles (X^0..X^2):", inv, " C =", frakC(K, 2))
    dump("diag.json", {"cases": cases, "collapse_ok": collapse_ok, "paper_ok": paper_ok, "fig": fig,
                       "example_q5": inv})


# -------------------------------------------------------------------------------------------------- pure
def part_pure():
    say("== pure: [A] = [B], invariants P0(X^r) ==")
    out, viol_cohen, viol_paper = [], 0, []
    missing = []
    for q in [3, 4, 5, 7, 8, 9, 11, 13]:
        K = GF(q)
        for r in [d for d in range(2, q) if (q - 1) % d == 0]:
            C = set(frakC(K, r))
            for n in (1, 2, 3):
                if q ** n > 2500 or r * n > 26:
                    continue
                P0s = pure_invariants(K, r, n)
                sgn = 1 if n % 2 == 0 else K.negt[1]
                consts = {P[0] for P in P0s}
                expect = {P[0] for P in K.monic_irreducibles(n) if K.mult[sgn][P[0]] in C}
                viol_cohen += consts != expect
                if not consts <= C:
                    viol_paper.append([q, r, n, sorted(consts), sorted(C)])
                for j in range(1, n):
                    att = {P[j] for P in P0s}
                    miss = sorted(set(range(q)) - att)
                    if miss:
                        missing.append([q, r, r * n, r * j, miss])
                out.append([q, r, n, len(P0s)])
    say(f"Cohen's criterion ((-1)^n p_0 in C) against direct irreducibility of P0(X^r): {viol_cohen} violations"
        f" in {len(out)} triples (q,r,n)")
    say(f"triples where some invariant has p_0 not in C (the paper's condition): {len(viol_paper)}; first:"
        f" {viol_paper[:4]}")
    say("missing kappa for 0 < m < n', r | m:  [q, r, n', m, missing]:")
    for t in missing:
        K = GF(t[0])
        why = "q even" if t[0] % 2 == 0 else ("q=3 mod 4, r even" if t[0] % 4 == 3 and t[1] % 2 == 0 else "?")
        say("   ", t, " n'=2r, m=r:", t[2] == 2 * t[1] and t[3] == t[1], " ", why)
    dump("pure.json", {"triples": out, "p0_not_in_C": viol_paper, "missing": missing})


# -------------------------------------------------------------------------------------------------- wsum
def mangoldt(K, H):
    """Lambda(H) for H with H(0) = 1 (up to a scalar: degree of P if H ~ P^k, else 0)."""
    n = len(H) - 1
    if n <= 0:
        return 0
    Hm = K.pscale(H, K.invt[H[-1]])
    for d in range(1, n + 1):
        if n % d == 0:
            for P in K.monic_irreducibles(d):
                R = [1]
                for _ in range(n // d):
                    R = K.pmul(R, P)
                if R == Hm:
                    return d
    return 0


def Lsum(q, mu):
    return sum(q ** j - 1 for j in range(1, mu))


def Gsum(q, mu):
    return sum(q ** (j / 2) for j in range(1, mu))


def part_wsum():
    say("== wsum: exact weighted sums ==")
    rng = random.Random(615)
    # identity sum_{H in G_(mu-1)} Lambda(H) = sum_{j=1}^{mu-1} (q^j - 1)   (the paper: (q^mu - 1)/(q - 1))
    for q, mu in [(2, 2), (2, 3), (2, 5), (3, 2), (3, 4), (4, 3), (5, 3), (7, 2)]:
        K = GF(q)
        tot = 0
        for d in range(0, mu):
            for tail in itertools.product(range(q), repeat=d):
                H = K.trim([1] + list(tail))
                if len(H) - 1 == d:
                    tot += mangoldt(K, H)
        say(f"q={q}, mu={mu}: sum Lambda(H) over G_(mu-1) = {tot}; sum(q^j-1) = {Lsum(q, mu)};"
            f" paper's (q^mu-1)/(q-1) = {(q**mu - 1)//(q - 1)}")
    # c_j(psi) = -1
    import cmath
    for q in [2, 3, 4, 5]:
        K = GF(q)
        p = K.p
        for j in range(1, 5 if q < 4 else 4):
            c = 0
            for d in range(1, j + 1):
                if j % d == 0:
                    for P in K.monic_irreducibles(j // d):
                        if P[0] == 0:
                            continue
                        t = K.tr(K.mult[P[1] if len(P) > 1 else 0][K.invt[P[0]]])
                        c += (j // d) * cmath.exp(2j * cmath.pi * t * d / p)
            say(f"q={q}: c_{j}(psi) = {c.real:+.6f}{c.imag:+.6f}i")
    # ---- Section 2: w = sum_H Lambda(H) #{T in I_n: psi(T) != 1, (T/T(0)) F = H mod X^(mu+1)}
    res2, worst2 = [], 0.0
    for q, ns, mus in [(2, range(6, 13), (2, 3, 4)), (3, range(4, 8), (2, 3)), (4, range(4, 6), (2,)),
                       (5, range(4, 6), (2,))]:
        K = GF(q)
        p = K.p
        for n in ns:
            irr = [T for T in K.monic_irreducibles(n)]
            for mu in mus:
                if mu > n // 2:
                    continue
                for alpha in ([1] if q == 2 else [1, K.gen]):
                    iap = K.invt[K.pw(alpha, p)]
                    gs = [K.pscale(T, K.invt[T[0]]) for T in irr]
                    gs = [g_ for g_ in gs if K.tr(K.mult[g_[1]][iap]) != 0]
                    Nstar = len(gs)
                    for _ in range(6):
                        F = [1] + [rng.randrange(q) for _ in range(mu)]
                        w = 0
                        for g_ in gs:
                            H = K.pmul(g_[:mu + 1], F)[:mu + 1]
                            H = K.trim(list(H))
                            if len(H) - 1 <= mu - 1:
                                w += mangoldt(K, H)
                        eps = 1 if K.tr(K.mult[F[1]][iap]) == 0 else -1 / (p - 1)
                        L = Lsum(q, mu)
                        main = Nstar / q ** mu * (L + (mu - 1) * eps)
                        bound = (q ** mu - p) / q ** mu * mu * Gsum(q, mu) * 2 * (p - 1) / (p * n) * \
                            ((mu + 1) * q ** (n / 2) + 1)
                        ratio = abs(w - main) / bound if bound else (0.0 if abs(w - main) < 1e-9 else 9.9)
                        worst2 = max(worst2, ratio)
                        res2.append([q, n, mu, alpha, w, main, bound])
    say(f"Section 2: {len(res2)} cases (q,n,mu,alpha,F); largest |w - main| / bound = {worst2:.4f} (must be <= 1)")
    ex = [r_ for r_ in res2 if r_[0] == 2 and r_[2] == 2][:4]
    say("   q=2, mu=2 examples [q,n,mu,alpha,w,main,bound]:", [[round(x, 3) if isinstance(x, float) else x for x in r_] for r_ in ex])
    # ---- Section 3: w = sum_H lam(H) #{T in I_n: 1/T(0) in (-1)^n C, (T/T(0)) F = H mod X^(mu+1)}
    res3, worst3 = [], 0.0
    for q, ns in [(3, range(3, 8)), (4, range(3, 6)), (5, range(3, 6)), (7, range(3, 5))]:
        K = GF(q)
        for r in [d for d in range(2, q) if (q - 1) % d == 0]:
            C = set(frakC(K, r))
            W = 2 ** len(factorint(r))
            for n in ns:
                sgn = 1 if n % 2 == 0 else K.negt[1]
                Cp = {K.mult[sgn][x] for x in C}
                irr = K.monic_irreducibles(n)
                gs = [K.pscale(T, K.invt[T[0]]) for T in irr if K.invt[T[0]] in Cp]
                for mu in (1, 2, 3):
                    if not (0 < mu < n / 2):
                        continue
                    L = 1 if mu == 1 else Lsum(q, mu)
                    Kb = 1 if mu == 1 else mu * Gsum(q, mu)
                    for _ in range(6):
                        F = [1] + [rng.randrange(q) for _ in range(mu)]
                        w = 0
                        for g_ in gs:
                            H = K.trim(list(K.pmul(g_[:mu + 1], F)[:mu + 1]))
                            if len(H) - 1 <= mu - 1:
                                w += 1 if mu == 1 else mangoldt(K, H)
                        U = (q - 1) * q ** mu
                        main = L * len(C) * pi_q(q, n) / U
                        bound = len(C) / U * W * (q ** mu * Kb * (mu + 2) + 2 * L) * q ** (n / 2) / n
                        worst3 = max(worst3, abs(w - main) / bound)
                        res3.append([q, r, n, mu, w, main, bound])
    say(f"Section 3: {len(res3)} cases (q,r,n,mu,F); largest |w - main| / bound = {worst3:.4f} (must be <= 1)")
    dump("wsum.json", {"sec2": res2, "worst2": worst2, "sec3": res3, "worst3": worst3})


# ------------------------------------------------------------------------------------------------ thresh
def paper5(q, n, mu):
    lhs = q ** (n / 2) * (q ** ((mu - 1) / 2) - 4 * mu) + 4 * mu / (q - 1)
    rhs = 2 * mu * q ** mu * (4 * mu + 1 / (2 * q ** (mu / 2)) + 4 * mu / q ** mu
                              + 1 / (2 * mu * q ** ((mu + 1) / 2) * (q - 1)))
    return lhs >= rhs


def cond_S2(q, n, mu):
    """corrected sufficient condition for Theorem 2.8(4) (log-free, floats; q^n fits for the ranges used)."""
    p = min(factorint(q))
    L = Lsum(q, mu) - (mu - 1) / (p - 1)
    if L <= 0:
        return False
    lhs = (pi_q(q, n) - (2 * q ** (n / 2) + 1) / n) * L
    rhs = 2 * (q ** mu - p) * mu * Gsum(q, mu) * ((mu + 1) * q ** (n / 2) + 1) / n
    return lhs > rhs


def cond_S3(q, n, mu, W):
    L = 1 if mu == 1 else Lsum(q, mu)
    Kb = 1 if mu == 1 else mu * Gsum(q, mu)
    return L * pi_q(q, n) > W * (q ** mu * Kb * (mu + 2) + 2 * L) * q ** (n / 2) / n


def paper8(q, n, mu):
    return q ** (n / 2) >= 2 * n * (mu + 1) * q ** ((mu + 1) / 2) + q / (q + 1)


def least_n(test, nmin, nmax):
    """least n0 such that test(n) holds for all n0 <= n <= nmax."""
    n0 = None
    for n in range(nmax, nmin - 1, -1):
        if test(n):
            n0 = n
        else:
            break
    return n0


NMAX = 140


def part_thresh():
    say("== thresh ==")
    out = {}
    # (5): sign of the factor q^((mu-1)/2) - 4 mu
    neg = {q: [mu for mu in range(2, 40) if q ** ((mu - 1) / 2) - 4 * mu <= 0] for q in [2, 3, 4, 5, 7, 8, 9, 11, 13, 27, 64, 67]}
    for q, v in neg.items():
        say(f"q={q}: q^((mu-1)/2) - 4mu <= 0 for mu in {v[:1]}..{v[-1:]}" if v else f"q={q}: factor positive for all mu >= 2")
    out["factor_nonpositive"] = neg
    # Table 2
    table2 = [(2, 26), (3, 16), (4, 12), (5, 10), (7, 8), (8, 8), (9, 8), (11, 8), (13, 6), (16, 6), (17, 6),
              (19, 6), (23, 6), (25, 6), (27, 6)]
    t2 = []
    for q, n0 in table2:
        fails = [mu for mu in range(2, n0 // 2 + 1) if not paper5(q, n0, mu)]
        anyn = all(not paper5(q, n, 2) for n in range(4, 300))
        t2.append([q, n0, fails, anyn])
        say(f"Table 2: q={q}, n={n0}: (5) fails for mu in {fails}; (5) with mu=2 fails for every 4<=n<300: {anyn}")
    out["table2"] = t2
    pp = prime_powers(67, 4000)
    for n, mu in [(4, 2), (5, 2), (6, 2), (6, 3), (7, 2), (7, 3)]:
        b = [q for q in pp if not paper5(q, n, mu)]
        say(f"(5) at (n,mu)=({n},{mu}) fails for prime powers 67 <= q <= {max(b) if b else None}")
    # corrected thresholds (S2)
    s2 = {}
    for q in prime_powers(2, 160):
        mus = (lambda n: range(3 if q == 2 else 2, n // 2 + 1))
        nmax = NMAX if q <= 4 else 80
        n0 = least_n(lambda n: all(cond_S2(q, n, mu) for mu in mus(n)), 4, nmax)
        s2[q] = n0
    say("(S2) holds for all 2 <= mu <= n/2 (mu >= 3 if q = 2) and n0 <= n <= nmax:  {q: n0} =", s2)
    out["S2_n0"] = s2
    qq = [q for q in prime_powers(2, 3000) if all(cond_S2(q, n, mu) for n in range(4, 40) for mu in range(2, n // 2 + 1))]
    bad = [q for q in prime_powers(2, 3000) if q not in qq]
    say(f"(S2) for all 4 <= n < 40 and all mu: holds for every prime power q with {max(bad) if bad else 1} < q <= 3000;"
        f" largest failing q = {max(bad) if bad else None}")
    out["S2_q0"] = max(bad) if bad else None
    for n in range(4, 12):
        b = [q for q in prime_powers(2, 3000) if not all(cond_S2(q, n, mu) for mu in range(2, n // 2 + 1))]
        say(f"   n={n}: (S2) for all mu holds for all prime powers q > {max(b) if b else 1}")
    # tail estimate used in the note: q^(n/4-1) > 10 n (n+4) for n >= 100
    say("tail estimate 2^(n/4-1) > 10 n(n+4) at n=100:", 2 ** 24 > 10 * 100 * 104)
    # (8), Table 3
    table3 = [(2, 47), (3, 25), (4, 19), (5, 15), (7, 13), (8, 11), (9, 11), (11, 9), (13, 9)] + \
             [(q, 7) for q in prime_powers(16, 29)]
    t3 = []
    for q, n0 in table3:
        cap = [(n, mu) for n in range(n0, n0 + 40) for mu in range(1, n // 2 + 1) if not paper8(q, n, mu)]
        strict = [(n, mu) for n in range(n0, n0 + 40) for mu in range(1, (n + 1) // 2) if mu < n / 2 and not paper8(q, n, mu)]
        t3.append([q, n0, cap, strict])
        if cap or strict:
            say(f"Table 3: q={q}, n>={n0}: (8) fails for mu<=n/2 at {cap}; for mu<n/2 at {strict}")
    say("Table 3 rows with a failure under the caption (mu <= n/2):", [t[0] for t in t3 if t[2]],
        "; under mu < n/2:", [t[0] for t in t3 if t[3]])
    f31 = [(q, n, mu) for q in prime_powers(31, 60) for n in range(5, 9) for mu in range(1, n // 2 + 1) if not paper8(q, n, mu)]
    say("(8) for q>=31, n>=5, mu<=n/2 fails at:", f31)
    out["table3"] = t3
    # corrected thresholds (S3) with W = W(q-1)
    s3 = {}
    for q in prime_powers(3, 160):
        W = 2 ** len(factorint(q - 1))
        nmax = NMAX if q <= 4 else 80
        s3[q] = least_n(lambda n: all(cond_S3(q, n, mu, W) for mu in range(1, n) if mu < n / 2), 3, nmax)
    say("(S3) with W = W(q-1) holds for all 0 < mu < n/2 and n0 <= n <= nmax:  {q: n0} =", s3)
    out["S3_n0"] = s3
    for n in range(3, 10):
        b = [q for q in prime_powers(3, 20000)
             if not all(cond_S3(q, n, mu, 2 ** len(factorint(q - 1))) for mu in range(1, n) if mu < n / 2)]
        say(f"   n={n}: (S3) for all mu < n/2 holds for all prime powers {max(b) if b else 2} < q <= 20000")
    dump("thresholds.json", out)


# ------------------------------------------------------------------------------------------------- truth
def part_truth():
    say("== truth: conclusion of Theorem 2.8(4), exhaustive ==")
    out = []
    for q, nmax in [(2, 13), (3, 7), (4, 5), (5, 4)]:
        K = GF(q)
        p = K.p
        for alpha in ([1] if q == 2 else [1, K.gen]):
            G = [0, K.negt[K.pw(alpha, p - 1)]] + [0] * (p - 2) + [1]
            iap = K.invt[K.pw(alpha, p)]
            for n in range(4, nmax + 1):
                Ps = [P for P in K.monic_irreducibles(n) if K.tr(K.mult[P[n - 1]][iap]) != 0]
                Qs = [K.compose(P, G) for P in Ps]
                for m in range(0, p * n + 1):
                    g = gamma_corrected(K, alpha, n, m)
                    nz = [i for i in range(n + 1) if g[i]]
                    if not nz:
                        continue
                    mu = max(nz)
                    if 2 <= mu <= n / 2:
                        att = {Q[m] for Q in Qs}
                        out.append([q, alpha, n, m, mu, len(att) == q])
    bad = [t for t in out if not t[5]]
    say(f"{len(out)} cases (q,alpha,n,m) with 2 <= mu <= n/2; every kappa attained in {len(out) - len(bad)};"
        f" failures: {bad[:10]}")
    q2 = [t for t in out if t[0] == 2 and t[4] == 2]
    say(f"   of which q=2, mu=2: {len(q2)} cases, all attained: {all(t[5] for t in q2)}")
    # q = 2, mu = 2 directly: T in I_n with T = 1 + X + c X^2 (mod X^3); bound (pi_2(n) - 3(3*2^(n/2)+1)/n)/4
    K = GF(2)
    cls = []
    for n in range(4, 17):
        cnt = {0: 0, 1: 0}
        for T in K.monic_irreducibles(n):
            if T[0] == 1 and T[1] == 1:
                cnt[T[2]] += 1
        bound = (pi_q(2, n) - 3 * (3 * 2 ** (n / 2) + 1) / n) / 4
        cls.append([n, cnt[0], cnt[1], bound])
        say(f"   q=2, n={n}: #T = 1+X (mod X^3): {cnt[0]}, #T = 1+X+X^2 (mod X^3): {cnt[1]}; lower bound {bound:.2f}")
    say("   n*pi_2(n) > 9*2^(n/2) + 3 for all 7 <= n <= 200:",
        all(n * pi_q(2, n) > 9 * 2 ** (n / 2) + 3 for n in range(7, 201)),
        "; 2^n - 2^(n/2+1) > 9*2^(n/2)+3 for n >= 8:", all(2 ** n - 2 ** (n / 2 + 1) > 9 * 2 ** (n / 2) + 3 for n in range(8, 201)))
    dump("truth.json", {"cases": out, "q2_mu2_classes": cls})


# ------------------------------------------------------------------------------------------------ direct
# Direct counting over the whole set of admissible residue classes (no weights Lambda).
def Rn(q, n):
    return q ** n - n * pi_q(q, n)                     # sum over proper divisors k of n of k*pi_q(k)


def Bgen(q, n, D):
    """|sum_{T in I_n} chi(T)| for a non-trivial Dirichlet character modulo X^D (Weil)."""
    return ((D - 1) * q ** (n / 2) + Rn(q, n)) / n


def Beven(q, n, D):
    """same for characters trivial on F_q^* (also Proposition 2.6 of the paper)."""
    return min(Bgen(q, n, D), (D * q ** (n / 2) + 1) / n)


def LB2(q, n, mu):
    """lower bound for #{P in I_n: Tr(c p_{n-1}) != 0, sum_i gamma_i p_{n-i} = kappa}, gamma_mu != 0."""
    p = min(factorint(q))
    S = q ** (mu - 1) * (1 - 1 / p)
    return S / q ** mu * (pi_q(q, n) - Beven(q, n, 2)) - (1 - 1 / q) * math.sqrt(S) * Beven(q, n, mu + 1)


def LB3(q, n, mu, W, nC):
    """lower bound for #{P in I_n: (-1)^n p_0 in C, sum_{i<=mu} delta_i p_{n-i} = kappa}, delta_mu != 0."""
    t = pi_q(q, n) - (W - 1) * Bgen(q, n, 1) - W * (q - 1) * q ** ((mu - 1) / 2) * Bgen(q, n, mu + 1)
    return nC / (q * (q - 1)) * t


def part_direct():
    say("== direct: exact counts against the lower bounds (D2), (D3) ==")
    rng = random.Random(180)
    worst2 = worst3 = None
    n2 = n3 = 0
    viol = []
    for q, ns in [(2, range(4, 14)), (3, range(4, 9)), (4, range(4, 7)), (5, range(4, 6)), (7, (4,)), (8, (4,)), (9, (4,))]:
        K = GF(q)
        p = K.p
        for n in ns:
            irr = K.monic_irreducibles(n)
            for mu in range(2, n):
                lb = LB2(q, n, mu)
                for _ in range(4):
                    c = rng.randrange(1, q)
                    gam = [rng.randrange(q) for _ in range(mu)] + [rng.randrange(1, q)]
                    cnt = [0] * q
                    for P in irr:
                        if K.tr(K.mult[c][P[n - 1]]) == 0:
                            continue
                        s = gam[0]
                        for i in range(1, mu + 1):
                            s = K.addt[s][K.mult[gam[i]][P[n - i]]]
                        cnt[s] += 1
                    n2 += 1
                    m = min(cnt)
                    if m < lb - 1e-9:
                        viol.append(["D2", q, n, mu, m, lb])
                    if lb > 0 and (worst2 is None or m / lb < worst2[0]):
                        worst2 = (m / lb, q, n, mu, m, lb)
    for q, ns in [(3, range(3, 9)), (4, range(3, 7)), (5, range(3, 6)), (7, range(3, 5)), (9, (3, 4)), (11, (3,)), (13, (3,))]:
        K = GF(q)
        for r in [d for d in range(2, q) if (q - 1) % d == 0]:
            C = set(frakC(K, r))
            W = 2 ** len(factorint(r))
            for n in ns:
                sgn = 1 if n % 2 == 0 else K.negt[1]
                irr = [P for P in K.monic_irreducibles(n) if K.mult[sgn][P[0]] in C]
                for mu in range(1, n):
                    lb = LB3(q, n, mu, W, len(C))
                    for _ in range(4):
                        dl = [0] + [rng.randrange(q) for _ in range(mu - 1)] + [rng.randrange(1, q)]
                        cnt = [0] * q
                        for P in irr:
                            s = 0
                            for i in range(1, mu + 1):
                                s = K.addt[s][K.mult[dl[i]][P[n - i]]]
                            cnt[s] += 1
                        n3 += 1
                        m = min(cnt)
                        if m < lb - 1e-9:
                            viol.append(["D3", q, r, n, mu, m, lb])
                        if lb > 0 and (worst3 is None or m / lb < worst3[0]):
                            worst3 = (m / lb, q, r, n, mu, m, lb)
    say(f"(D2): {n2} cases (q,n,mu,c,gamma), all kappa; violations of the lower bound: {[v for v in viol if v[0]=='D2']};"
        f" smallest count/bound where the bound is positive: {worst2}")
    say(f"(D3): {n3} cases (q,r,n,mu,delta), all kappa; violations: {[v for v in viol if v[0]=='D3']};"
        f" smallest count/bound where the bound is positive: {worst3}")
    dump("direct.json", {"n2": n2, "n3": n3, "violations": viol, "worst2": worst2, "worst3": worst3})


# ----------------------------------------------------------------------------------------------- closure
def W_of(m):
    return 2 ** len(factorint(m)) if m > 1 else 1


def find_poly(K, n, fixed, ok0=None):
    """first monic irreducible P of degree n with P[j] = fixed[j] for j in fixed (dict or callable filling),
    in lexicographic order of the free coefficients; ok0 = allowed constant terms (set) or None."""
    free = [j for j in range(n) if j not in fixed]
    for vals in itertools.product(range(K.q), repeat=len(free)):
        P = [0] * n + [1]
        for j, v_ in fixed.items():
            P[j] = v_
        for j, v_ in zip(free, vals):
            P[j] = v_
        if P[0] == 0 or (ok0 is not None and P[0] not in ok0):
            continue
        if K.is_irreducible(P):
            return P
    return None


def part_closure():
    say("== closure: where the direct bounds fail, and explicit polynomials there ==")
    out = {}
    # ---------------- (D2): one eigenvalue.  Box q < 64, n <= 60; outside it q^(n/4-1/2) >= 0.75n+5 suffices.
    fail2 = []
    for q in prime_powers(2, 63):
        for n in range(4, 61):
            mus = [mu for mu in range(2, n // 2 + 1) if LB2(q, n, mu) <= 0]
            if mus:
                fail2.append([q, n, mus])
    say("(D2) fails (2 <= mu <= n/2) exactly for (q, n, mu's):", fail2)
    tail2 = all(q ** (n / 4 - 0.5) >= 0.75 * n + 5 for q in prime_powers(2, 63) for n in range(61, 400)) and \
        all(64 ** (n / 4 - 0.5) >= 0.75 * n + 5 for n in range(4, 400))
    say("   tail condition q^(n/4-1/2) >= 0.75n+5 for q < 64, n > 60 and for q = 64, n >= 4:", tail2)
    out["fail2"] = fail2
    wit2, miss2, ncase2 = [], [], 0
    for q, n, mus in fail2:
        K = GF(q)
        nontr = {c: [g for g in range(q) if K.tr(K.mult[c][g]) != 0] for c in range(1, q)}
        for mu in mus:
            for c in range(1, q):
                for gam in itertools.product(range(q), repeat=mu - 1):       # gamma_1..gamma_{mu-1}; gamma_mu = 1
                    for kappa in range(q):
                        ncase2 += 1
                        found = None
                        for g1 in nontr[c]:
                            for mid in itertools.product(range(q), repeat=mu - 2):
                                g = [g1] + list(mid)                          # g_1..g_{mu-1}
                                s = 0
                                for gi, ga in zip(g, gam):
                                    s = K.addt[s][K.mult[ga][gi]]
                                gmu = K.addt[kappa][K.negt[s]]
                                fixed = {n - i - 1: g[i] for i in range(mu - 1)}
                                fixed[n - mu] = gmu
                                found = find_poly(K, n, fixed)
                                if found:
                                    break
                            if found:
                                break
                        if found:
                            if len(wit2) < 400:
                                wit2.append([q, n, mu, c, list(gam), kappa, found])
                        else:
                            miss2.append([q, n, mu, c, list(gam), kappa])
    say(f"   one eigenvalue: {ncase2} cases (q,n,mu,c,gamma,kappa) below the bound; without a polynomial: {len(miss2)}"
        f" {miss2[:12]}")
    out["cases2"], out["missing2"], out["witness2"] = ncase2, miss2, wit2
    # ---------------- (D3): two eigenvalues.  Box 3 <= q < 500, n <= 60 for n >= 4; n = 3 separately.
    fail3 = []
    for q in prime_powers(3, 499):
        for r in [d for d in range(2, q) if (q - 1) % d == 0]:
            nC = (q - 1) * int(__import__("sympy").totient(r)) // r
            for n in range(4, 61):
                mus = [mu for mu in range(1, n) if mu < n / 2 and LB3(q, n, mu, W_of(r), nC) <= 0]
                if mus:
                    fail3.append([q, r, n, mus])
    say("(D3) fails (n >= 4, 0 < mu < n/2) exactly for (q, r, n, mu's):", fail3)
    tail3 = all(q ** ((n - 2) / 4) >= 2.45 * (n + 5) for q in prime_powers(3, 499) for n in range(61, 300)) and \
        all(487 ** ((n - 2) / 4) >= 2.45 * (n + 5) for n in range(4, 300))
    say("   tail condition q^((n-2)/4) >= 2.45(n+5) for q < 500, n > 60 and for q = 487, n >= 4:", tail3)
    f33 = []
    for q in prime_powers(3, 150000):
        fq = factorint(q - 1)
        if 4 * 2 ** len(fq) <= q ** 0.5 * 0.5:
            continue
        for r in [d for d in __import__("sympy").divisors(q - 1) if d > 1]:
            nC = (q - 1) * int(__import__("sympy").totient(r)) // r
            if LB3(q, 3, 1, W_of(r), nC) <= 0:
                f33.append([q, int(r)])
    say(f"(D3) fails for n = 3 (mu = 1) for {len(f33)} pairs (q, r), q <= {max(t[0] for t in f33) if f33 else None}:", f33)
    out["fail3"], out["fail3_n3"] = fail3, f33
    wit3, miss3, ncase3 = [], [], 0
    todo = [(q, r, n, mus) for q, r, n, mus in fail3] + [(q, r, 3, [1]) for q, r in f33 if q <= 300]
    for q, r, n, mus in todo:
        K = GF(q)
        C = set(frakC(K, r))
        sgn = 1 if n % 2 == 0 else K.negt[1]
        ok0 = {K.mult[sgn][x] for x in C}                                   # allowed constant terms
        for mu in mus:
            for dl in itertools.product(range(q), repeat=mu - 1):           # delta_1..delta_{mu-1}; delta_mu = 1
                for kappa in range(q):
                    ncase3 += 1
                    found = None
                    for g in itertools.product(range(q), repeat=mu - 1):
                        s = 0
                        for gi, de in zip(g, dl):
                            s = K.addt[s][K.mult[de][gi]]
                        gmu = K.addt[kappa][K.negt[s]]
                        fixed = {n - i - 1: g[i] for i in range(mu - 1)}
                        fixed[n - mu] = gmu
                        found = find_poly(K, n, fixed, ok0)
                        if found:
                            break
                    if found:
                        if len(wit3) < 400:
                            wit3.append([q, r, n, mu, list(dl), kappa, found])
                    else:
                        miss3.append([q, r, n, mu, list(dl), kappa])
    say(f"   two eigenvalues: {ncase3} cases (q,r,n,mu,delta,kappa) below the bound"
        f" (n = 3 only for q <= 300); without a polynomial: {len(miss3)} {miss3[:20]}")
    out["cases3"], out["missing3"], out["witness3"] = ncase3, miss3, wit3
    # least n0 such that the direct bound is positive for all n >= n0 (all admissible mu; worst r for (D3))
    d2 = {q: 4 for q in prime_powers(2, 63)}
    for q, n, mus in fail2:
        d2[q] = max(d2[q], n + 1)
    d3 = {q: 3 for q in prime_powers(3, 499)}
    for q, r, n, mus in fail3:
        d3[q] = max(d3[q], n + 1)
    for q, r in f33:
        d3[q] = max(d3.get(q, 3), 4)
    say("(D2): least n0 by q (q < 64; 4 elsewhere):", {q: v_ for q, v_ in d2.items() if v_ > 4})
    say("(D3): least n0 by q (q < 500; 3 elsewhere):", {q: v_ for q, v_ in d3.items() if v_ > 3})
    out["D2_n0"], out["D3_n0"] = d2, d3
    # a few polynomials for the paper
    def show(P):
        return " + ".join((f"{c}" if j == 0 else (("" if c == 1 else str(c)) + ("X" if j == 1 else f"X^{j}")))
                          for j, c in reversed(list(enumerate(P))) if c)
    for key in (wit2, wit3):
        seen = set()
        for t in key:
            tag = tuple(t[:3]) if key is wit2 else tuple(t[:4])
            if tag not in seen and t[0] in (2, 3, 5, 7):
                seen.add(tag)
                say("   sample:", t[:-1], "->", show(t[-1]))
    dump("closure.json", out)


# ------------------------------------------------------------------------------------------------ lemmas
def part_lemmas():
    say("== lemmas: prescribed trace coefficient / constant term; Table 1 ==")
    bad_t, bad_c, cases = [], [], 0
    for q in [2, 3, 4, 5, 7, 8, 9]:
        K = GF(q)
        for n in range(1, {2: 10, 3: 7, 4: 5, 5: 5, 7: 4, 8: 4, 9: 4}[q] + 1):
            irr = K.monic_irreducibles(n)
            tr = {P[n - 1] for P in irr}
            co = {P[0] for P in irr}
            cases += 1
            if not set(range(1, q)) <= tr:
                bad_t.append([q, n])
            if n >= 2 and co != set(range(1, q)):
                bad_c.append([q, n])
    say(f"{cases} pairs (q,n): every non-zero value is p_(n-1) of some P in I_n, failures: {bad_t};"
        f" every non-zero value is p_0 of some P in I_n (n >= 2), failures: {bad_c}")
    rn = [(q, n) for q in prime_powers(2, 64) for n in range(2, 40) if Rn(q, n) > 2 * q ** (n / 2)]
    say("R_n <= 2 q^(n/2) fails for (q,n) in:", rn)
    say("W(m) <= 4.9 m^(1/4) fails for m <= 200000 in:", [m for m in range(1, 200001) if W_of(m) > 4.9 * m ** 0.25][:5],
        "; constant 64/30030^(1/4) =", round(64 / 30030 ** 0.25, 4))
    # Table 1 of the paper: q = 3, degree 6
    K = GF(3)

    def show(P):
        return " + ".join((f"{c}" if j == 0 else (("" if c == 1 else str(c)) + ("X" if j == 1 else f"X^{j}")))
                          for j, c in reversed(list(enumerate(P))) if c)
    t1 = {}
    for name, lin in [("(1 0; 2 1)", [2, 1]), ("(2 0; 1 1)", [1, 2]), ("(2 0; 0 1)", [0, 2])]:
        inv = []
        for f in K.monic_irreducibles(6):
            g = K.compose(f, lin)
            g = K.pscale(g, K.invt[g[-1]])
            if g == f:
                inv.append(f)
        t1[name] = [show(f) for f in inv]
        say(f"Table 1, A = {name}: {len(inv)} invariant irreducible sextics over F_3:", t1[name])
    dump("lemmas.json", {"table1": t1, "bad_trace": bad_t, "bad_const": bad_c})


def part_figures():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    th = json.load(open(os.path.join(DATA, "thresholds.json")))
    dg = json.load(open(os.path.join(DATA, "diag.json")))
    gm = json.load(open(os.path.join(DATA, "gamma.json")))["by_q"]
    cl = json.load(open(os.path.join(DATA, "closure.json")))
    plt.rcParams.update({"font.size": 8, "font.family": "serif", "mathtext.fontset": "cm",
                         "axes.linewidth": 0.6, "xtick.major.width": 0.6, "ytick.major.width": 0.6})
    # ---------------- figure 1
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(6.3, 2.5))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.2, top=0.8, wspace=0.26)
    qs = sorted(int(q) for q in gm)
    x = np_arange(len(qs))
    tot = [gm[str(q)][0] for q in qs]
    ax.bar([t - 0.27 for t in x], [gm[str(q)][2] / gm[str(q)][0] for q in qs], 0.27, color="C3")
    ax.bar(x, [gm[str(q)][3] / gm[str(q)][0] for q in qs], 0.27, color="C1")
    ax.bar([t + 0.27 for t in x], [gm[str(q)][1] / gm[str(q)][0] for q in qs], 0.27, color="C0")
    ax.plot([t + 0.27 for t in x], [0.012] * len(qs), "o", ms=3, color="C0")
    ax.set_xticks(list(x))
    ax.set_xticklabels([str(q) for q in qs])
    ax.set_xlabel(r"$q$")
    ax.set_ylabel(r"fraction of triples $(\alpha,n,m)$")
    ax.set_ylim(0, 0.75)
    ax.set_title("(a)", loc="left", fontsize=8, pad=3)
    ax.tick_params(length=2.5)
    pts = sorted({(t[0], t[1]): t for t in dg["fig"]}.values(), key=lambda t: (t[0], t[1]))
    xb = list(range(len(pts)))
    bx.plot(xb, [t[3] for t in pts], "D", ms=3.2, color="0.35", mfc="none", mew=0.8)
    bx.plot(xb, [t[2] for t in pts], "v", ms=3.6, color="C2")
    bx.set_xticks(xb)
    bx.set_xticklabels([f"({t[0]},{t[1]})" for t in pts], rotation=60, ha="right", fontsize=6.5)
    bx.set_ylabel(r"number of values of $q_m$")
    bx.set_ylim(0, max(t[3] for t in pts) + 1)
    bx.set_title("(b)", loc="left", fontsize=8, pad=3)
    bx.tick_params(length=2.5)
    h = [Line2D([], [], marker="s", ls="", ms=5, color="C3", label="printed formula wrong"),
         Line2D([], [], marker="s", ls="", ms=5, color="C1", label="printed formula undefined"),
         Line2D([], [], marker="o", ls="", ms=3, color="C0", label="corrected formula wrong (none)"),
         Line2D([], [], marker="D", ls="", ms=3.2, color="0.35", mfc="none", mew=0.8, label=r"claimed $\varphi(r)(q-1)/r$"),
         Line2D([], [], marker="v", ls="", ms=3.6, color="C2", label="observed")]
    fig.legend(handles=h, loc="upper center", ncol=3, frameon=False, bbox_to_anchor=(0.53, 1.01),
               fontsize=7, handlelength=1.2, columnspacing=1.3, handletextpad=0.4)
    out1 = os.path.join(FIG, "fig_kapetanakis_jnt2017_1.pdf")
    fig.savefig(out1)
    fig.savefig(out1.replace(".pdf", ".png"), dpi=200)
    # ---------------- figure 2
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(6.3, 2.5))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.17, top=0.8, wspace=0.24)
    t2 = th["table2"]
    qs = [t[0] for t in t2]
    xs = list(range(len(qs)))
    ax.plot(xs, [t[1] for t in t2], "s", ms=3.8, color="0.35", mfc="none", mew=0.8)
    ax.plot(xs, [th["S2_n0"][str(q)] for q in qs], "o", ms=3.3, color="C1")
    ax.plot(xs, [cl["D2_n0"].get(str(q), 4) for q in qs], "^", ms=3.6, color="C0")
    ax.axhline(4, color="C2", lw=1.0)
    t3 = {t[0]: t[1] for t in th["table3"]}
    q3 = [q for q in qs if q != 2] + [29]
    x3 = list(range(len(q3)))
    bx.plot(x3, [t3.get(q, float("nan")) for q in q3], "s", ms=3.8, color="0.35", mfc="none", mew=0.8)
    bx.plot(x3, [th["S3_n0"][str(q)] for q in q3], "o", ms=3.3, color="C1")
    bx.plot(x3, [cl["D3_n0"].get(str(q), 3) for q in q3], "^", ms=3.6, color="C0")
    bx.axhline(3, color="C2", lw=1.0)
    for a_, lab, tk, q_ in ((ax, "(a)", xs, qs), (bx, "(b)", x3, q3)):
        a_.set_xticks(tk)
        a_.set_xticklabels([str(q) for q in q_], fontsize=6.5)
        a_.set_xlabel(r"$q$")
        a_.set_yscale("log")
        a_.set_yticks([3, 4, 5, 7, 10, 20, 50])
        a_.set_yticklabels(["3", "4", "5", "7", "10", "20", "50"])
        a_.set_ylim(2.6, 60)
        a_.minorticks_off()
        a_.set_title(lab, loc="left", fontsize=8, pad=3)
        a_.tick_params(length=2.5)
    ax.set_ylabel(r"least admissible $n$")
    h = [Line2D([], [], marker="s", ls="", ms=3.8, color="0.35", mfc="none", mew=0.8, label="claimed (Tables 2, 3 of the original)"),
         Line2D([], [], marker="o", ls="", ms=3.3, color="C1", label="weighted count, repaired"),
         Line2D([], [], marker="^", ls="", ms=3.6, color="C0", label="direct bound"),
         Line2D([], [], color="C2", lw=1.0, label="proved here")]
    fig.legend(handles=h, loc="upper center", ncol=4, frameon=False, bbox_to_anchor=(0.53, 1.0),
               fontsize=7, handlelength=1.3, columnspacing=1.3, handletextpad=0.4)
    out2 = os.path.join(FIG, "fig_kapetanakis_jnt2017_2.pdf")
    fig.savefig(out2)
    fig.savefig(out2.replace(".pdf", ".png"), dpi=200)
    say("figures written:", out1, out2)


def np_arange(n):
    return list(range(n))


# ------------------------------------------------------------------------------------------------ figure
def part_figure():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    th = json.load(open(os.path.join(DATA, "thresholds.json")))
    dg = json.load(open(os.path.join(DATA, "diag.json")))
    plt.rcParams.update({"font.size": 8, "font.family": "serif", "mathtext.fontset": "cm",
                         "axes.linewidth": 0.6, "xtick.major.width": 0.6, "ytick.major.width": 0.6})
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(6.3, 2.6))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.2, top=0.8, wspace=0.26)
    t2 = th["table2"]
    qs = [t[0] for t in t2]
    xs = list(range(len(qs)))
    ax.plot(xs, [t[1] for t in t2], "s", ms=3.8, color="0.35", mfc="none", mew=0.8)
    ax.plot(xs, [th["S2_n0"][str(q)] for q in qs], "o", ms=3.3, color="C0")
    ax.plot(xs, [th["S3_n0"].get(str(q)) or float("nan") for q in qs], "^", ms=3.5, color="C2")
    ax.set_xticks(xs)
    ax.set_xticklabels([str(q) for q in qs], fontsize=6.5)
    ax.set_xlabel(r"$q$")
    ax.set_ylabel(r"least admissible $n$")
    ax.set_yscale("log")
    ax.set_yticks([5, 10, 20, 50, 100])
    ax.set_yticklabels(["5", "10", "20", "50", "100"])
    ax.set_title("(a)", loc="left", fontsize=8, pad=3)
    ax.tick_params(length=2.5)
    ax.minorticks_off()

    pts = sorted({(t[0], t[1]): t for t in dg["fig"]}.values(), key=lambda t: (t[0], t[1]))   # one per (q, r)
    xb = list(range(len(pts)))
    bx.plot(xb, [t[3] for t in pts], "D", ms=3.2, color="0.35", mfc="none", mew=0.8)
    bx.plot(xb, [t[2] for t in pts], "v", ms=3.6, color="C3")
    bx.set_xticks(xb)
    bx.set_xticklabels([f"({t[0]},{t[1]})" for t in pts], rotation=60, ha="right", fontsize=6.5)
    bx.set_ylabel(r"number of values of $q_m$")
    bx.set_ylim(0, max(t[3] for t in pts) + 1)
    bx.set_title("(b)", loc="left", fontsize=8, pad=3)
    bx.tick_params(length=2.5)
    h = [Line2D([], [], marker="s", ls="", ms=3.8, color="0.35", mfc="none", mew=0.8, label="Table 2 of [1], claimed"),
         Line2D([], [], marker="o", ls="", ms=3.3, color="C0", label=r"condition (S2)"),
         Line2D([], [], marker="^", ls="", ms=3.5, color="C2", label=r"condition (S3)"),
         Line2D([], [], marker="D", ls="", ms=3.2, color="0.35", mfc="none", mew=0.8, label=r"claimed: $\varphi(r)(q-1)/r$"),
         Line2D([], [], marker="v", ls="", ms=3.6, color="C3", label="observed")]
    fig.legend(handles=h, loc="upper center", ncol=5, frameon=False, bbox_to_anchor=(0.53, 1.0),
               fontsize=7, handlelength=1.2, columnspacing=1.3, handletextpad=0.4)
    out = os.path.join(FIG, "fig_kapetanakis_jnt2017.pdf")
    fig.savefig(out)
    fig.savefig(os.path.join(FIG, "fig_kapetanakis_jnt2017.png"), dpi=200)
    say("figure written:", out)


if __name__ == "__main__":
    parts = sys.argv[1:] or ["gamma", "diag", "pure", "wsum", "thresh", "truth", "direct", "closure", "lemmas",
                             "figures"]
    table = {"gamma": part_gamma, "diag": part_diag, "pure": part_pure, "wsum": part_wsum,
             "thresh": part_thresh, "truth": part_truth, "direct": part_direct, "closure": part_closure,
             "lemmas": part_lemmas, "figures": part_figures, "none": lambda: None}
    for name in parts:
        table[name]()

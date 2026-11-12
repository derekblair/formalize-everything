# Literature Kill-Check Verdict: A093085 vs. A112171 ($T_{32c}$)

## Executive Summary

The mined candidate identity between **OEIS A093085** (expansion of the Ramanujan theta quotient $\varphi(-x)/\psi(x^4)$) and **OEIS A112171** (coefficients of the Monster / replicable McKay–Thompson series $T_{32c}$):
$$\operatorname{A112171}(m) = (-1)^{\lceil m/4 \rceil} \operatorname{A093085}(m) = (-1)^{m + \lfloor m/4 \rfloor} \operatorname{A093085}(m) \qquad (m \ge 0)$$
is **DISGUISED**.

Although `A093085` and `A112171` do not directly cross-reference each other in the OEIS, both sequences are already explicitly decomposed in their respective OEIS records (and in the underlying Ramanujan theta-function and Moonshine replicable-function literature) into the **same level-16 / level-32 eta-quotient family** $B(y)$ (`A029838`) and its reciprocal $1/B(y)$ (`A083365`), related by the elementary sign twist $y = x^4 \mapsto -x^4$ (`A082303` $= T_{32e}$ and `A001935`).

---

## 1. Search Log

| Date (UTC) | Source / Database | Query / Resource | Result |
| :--- | :--- | :--- | :--- |
| 2026-10-24 | `oeisdata` (GitHub) | `seq/A093/A093085.seq`, `seq/A112/A112171.seq` | Full OEIS records for both target sequences. |
| 2026-10-24 | `oeisdata` (GitHub) | `seq/A029/A029838.seq`, `seq/A083/A083365.seq`, `seq/A082/A082303.seq`, `seq/A001/A001935.seq` | Full OEIS records for the 4-multisection components and their $(-1)^n$ sign twists. |
| 2026-10-24 | `oeisdata` (GitHub) | `seq/A131/A131124.seq`, `seq/A187/A187154.seq`, `seq/A107/A107035.seq`, `seq/A029/A029839.seq`, `seq/A029/A029841.seq`, `seq/A082/A082304.seq`, `seq/A112/A112143.seq` | Full OEIS records for the squares/inverses of A093085 and the level-8/16 Hauptmoduln ($8D, 8E, 16B, 16d$). |
| 2026-10-24 | `oeisdata` (GitHub) | `seq/A058/A058629.seq` ($32A$), `A058630.seq` ($32B$), `A058632.seq` ($32b$), `A107635.seq` ($32a$), `A112172.seq` ($32d$), `A112151.seq` ($16b$), `A112152.seq` ($16c$) | Full OEIS records for all class-32 and related class-16 replicable series. |
| 2026-10-24 | OEIS / LMS Lecture Notes | `https://oeis.org/A007242/a007242_1.pdf` — D. Alexander, C. Cummins, J. McKay, & C. Simons (1992), *Completely Replicable Functions* | Verified tabulation of non-monstrous replicable functions `16b`, `16c`, `16d`, `32a`–`32e` (pp. 92–93) and replication formulas (pp. 88–91). |
| 2026-10-24 | OEIS | `https://oeis.org/A010815/a010815.txt` — M. Somos (2019), *Introduction to Ramanujan theta functions* | Verified definitions of Ramanujan's $f(-x)$, $\varphi(x)$, $\psi(x)$, $\chi(x)$. |
| 2026-10-24 | arXiv (`0803.3419`) | J. McKay & D. Sevilla (2008), *Decomposing replicable functions*, *LMS J. Comput. Math.* 11, 146–171 (`latextable-allgraph2.tex`) | Verified exact rational decomposition poset edges for `32c`, `32d`, `32e`, `16b`, `16d`, `16B`, `8D`, `8E`. |
| 2026-10-24 | arXiv (`1810.07478`) | K. Acres & D. Broadhurst (2018), *Eta quotients and Rademacher sums* (`1810.tex`) | Verified Table 1 (line 456) entry for the level-8 Hauptmodul `A107035` / `A131124` (square of `A093085`). |
| 2026-10-24 | Web Search | `"Entry 25" "phi(q)" "psi(q^8)" "Ramanujan's Notebooks" "Part III"` and `"p. 221" "Entry 1" "Ramanujan's Notebooks" "Part III"` | Verified B. C. Berndt (1991), *Ramanujan's Notebooks, Part III*, Ch. 16 Entry 25 (p. 40) and Ch. 19 Entry 1(i) (p. 221). |

---

## 2. Check 1: Full OEIS Record Analysis & Quoted Evidence

### 2.1. OEIS A093085 (`seq/A093/A093085.seq`)
```text
%I A093085 #23 Sep 17 2025 21:44:02
%S A093085 1,-2,0,0,1,2,0,0,-1,-4,0,0,0,6,0,0,1,-8,0,0,0,12,0,0,-1,-18,0,0,-1,
%T A093085 24,0,0,2,-32,0,0,1,44,0,0,-2,-58,0,0,-1,76,0,0,2,-100,0,0,1,128,0,0,
%U A093085 -3,-164,0,0,-1,210,0,0,4,-264,0,0,2,332,0,0,-5,-416,0,0,-2,516,0,0,5,-640,0,0,2,790,0,0,-6,-968
%N A093085 Expansion of phi(-x) / psi(x^4) in powers of x where phi(), psi() are Ramanujan theta functions.
%C A093085 Ramanujan theta functions: f(q) (see A121373), phi(q) (A000122), psi(q) (A010054), chi(q) (A000700).
%C A093085 eta(q^2) * eta(q^8)^6 = eta(q)^2 * eta(q^4)^2 * eta(q^8) * eta(q^16)^2 + 2 * eta(q^2) * eta(q^4)^2 * eta(q^16)^4 is equivalent to the a(4*n), ..., a(4*n + 3) results.
%H A093085 G. C. Greubel, <a href="/A093085/b093085.txt">Table of n, a(n) for n = 0..1000</a>
%H A093085 Michael Somos, <a href="/A010815/a010815.txt">Introduction to Ramanujan theta functions</a>
%H A093085 Eric Weisstein's World of Mathematics, <a href="https://mathworld.wolfram.com/RamanujanThetaFunctions.html">Ramanujan Theta Functions</a>
%F A093085 Expansion of q^(1/2) * eta(q)^2 * eta(q^4) / (eta(q^2) * eta(q^8)^2) in powers of q.
%F A093085 Euler transform of period 8 sequence [ -2, -1, -2, -2, -2, -1, -2, 0, ...].
%F A093085 Given g.f. A(x), then B(q) = A(q)^2 / q satisfies 0 = f(B(q), B(q^2)) where f(u, v) = u * (u + 8) * (v + 4) - v^2.
%F A093085 G.f. is a period 1 Fourier series which satisfies f(-1 / (32 t)) = 32^(1/2) g(t) where q = exp(2 Pi i t) and g() is the g.f. for A187154.
%F A093085 G.f.: Product_{k>0} (1 - x^k)^2 / ((1 - x^(4*k - 2)) * (1 - x^(8*k))^2).
%F A093085 a(4*n + 2) = a(4*n + 3) = 0. a(4*n) = A029838(n). a(4*n + 1) =  -2 * A083365(n). Convolution square is A131124. Convolution inverse is A187154.
%F A093085 Empirical: Sum_{n>=0} a(n) / exp(n*Pi) = 2 * exp(-Pi / 2) * 2^(1/4) * (2+sqrt(2))^(1/2) = A388480. - _Simon Plouffe_, Sep 17 2025
%e A093085 G.f. = 1 - 2*x + x^4 + 2*x^5 - x^8 - 4*x^9 + 6*x^13 + x^16 - 8*x^17 + 12*x^21 - ...
%e A093085 G.f. = 1/q - 2*q + q^7 + 2*q^9 - q^15 - 4*q^17 + 6*q^25 + q^31 - 8*q^33 + ...
%Y A093085 Cf. A029838, A029839, A083365, A131124, A187154.
%A A093085 _Michael Somos_, Mar 20 2004, Oct 22 2007
```

### 2.2. OEIS A112171 (`seq/A112/A112171.seq`)
```text
%I A112171 #13 May 30 2026 16:40:25
%S A112171 1,2,0,0,-1,2,0,0,-1,4,0,0,0,6,0,0,1,8,0,0,0,12,0,0,-1,18,0,0,1,24,0,
%T A112171 0,2,32,0,0,-1,44,0,0,-2,58,0,0,1,76,0,0,2,100,0,0,-1,128,0,0,-3,164,
%U A112171 0,0,1,210,0,0,4,264,0,0,-2,332,0,0,-5,416,0,0,2,516,0,0,5,640,0,0,-2,790,0,0
%N A112171 McKay-Thompson series of class 32c for the Monster group.
%H A112171 G. C. Greubel, <a href="/A112171/b112171.txt">Table of n, a(n) for n = 0..2500</a>
%H A112171 D. Ford, J. McKay and S. P. Norton, <a href="https://doi.org/10.1080/00927879408825127">More on replicable functions</a>, Comm. Algebra 22, No. 13, 5175-5193 (1994).
%H A112171 <a href="/index/Mat#McKay_Thompson">Index entries for McKay-Thompson series for Monster simple group</a>
%F A112171 Expansion of A + 2*q/A, where A = q^(1/2)*(eta(q^4)/eta(q^16)), in powers of q. - _G. C. Greubel_, Jun 26 2018
%e A112171 T32c = 1/q +2*q -q^7 +2*q^9 -q^15 +4*q^17 +6*q^25 +q^31 +...
%t A112171 eta[q_] := q^(1/24)*QPochhammer[q]; A:= q^(1/2)*(eta[q^4]/eta[q^16]); a:= CoefficientList[Series[A + 2*q/A, {q, 0, 60}], q]; Table[a[[n]], {n, 1, 50}] (* _G. C. Greubel_, Jun 26 2018 *)
%o A112171 (PARI) q='q+O('q^80); A = eta(q^4)/eta(q^16); Vec(A + 2*q/A) \\ _G. C. Greubel_, Jun 26 2018
%K A112171 sign
%O A112171 0,2
%A A112171 _Michael Somos_, Aug 28 2005
```

### 2.3. Bridging OEIS Records (`A029838`, `A083365`, `A082303`, `A001935`, `A112172`)
- **A029838** (referenced in `A093085`):
  ```text
  %N A029838 Expansion of square root of q times normalized Hauptmodul for Gamma(4) in powers of q^8.
  %D A029838 B. C. Berndt, Ramanujan's Notebooks Part III, Springer-Verlag, see p. 221 Entry 1(i).
  %F A029838 Expansion of f(x) / f(-x^4) = phi(x) / psi(x) = psi(x) / psi(x^2) = ... in powers of x
  %F A029838 Expansion of q^(1/8) * eta(q^2)^3 / (eta(q) * eta(q^4)^2) in powers of q.
  %F A029838 A082303(n) = (-1)^n a(n). Convolution square is A029839. Convolution inverse is A083365.
  %t A029838 a[ n_] := SeriesCoefficient[ QPochhammer[ -q, -q] / QPochhammer[ q^4, q^4], {q, 0, n}]; (* _Michael Somos_, Aug 20 2014 *)
  ```
- **A082303** (referenced in `A029838`):
  ```text
  %N A082303 McKay-Thompson series of class 32e for the Monster group.
  %F A082303 Expansion of q^(1/8) * eta(q) / eta(q^4) in powers of q.
  %F A082303 a(n) = (-1)^n * A029838(n).
  ```
- **A083365** (referenced in `A093085` and `A029838`):
  ```text
  %N A083365 Expansion of psi(x) / phi(x) in powers of x where phi(), psi() are Ramanujan theta functions.
  %D A083365 B. C. Berndt, Ramanujan's Notebooks Part III, Springer-Verlag, see p. 221 Entry 1(i).
  %F A083365 Expansion of f(-x^4) / f(x) = psi(x) / phi(x) = psi(x^2) / psi(x) = ... in powers of x
  %F A083365 Expansion of q^(-1/8) * eta(q) * eta(q^4)^2 / eta(q^2)^3 in powers of q.
  %F A083365 A001935(n) = (-1)^n a(n).
  ```
- **A001935** (referenced in `A083365` and `A187154`):
  ```text
  %F A001935 Expansion of q^(-1/8) * eta(q^4) / eta(q) in powers of q. - _Michael Somos_, Mar 19 2004
  %F A001935 Expansion of psi(-x) / phi(-x) = ... = f(-x^4) / f(-x) in powers of x
  %F A001935 A083365(n) = (-1)^n a(n).
  ```
- **A112172** (sibling class `32d`):
  ```text
  %N A112172 McKay-Thompson series of class 32d for the Monster group.
  %F A112172 Expansion of A - 2*q/A, where A = q^(1/2)*eta(q^4)/eta(q^16), in powers of q. - _G. C. Greubel_, Jun 16 2018
  ```

---

## 3. Check 2: Conway–Norton / Ford–McKay–Norton & Eta-Product Structure of $T_{32c}$

1. **Monstrous vs. Non-Monstrous Replicable Status**:
   - In **J. H. Conway and S. P. Norton**, "Monstrous Moonshine", *Bull. London Math. Soc.* 11 (1979), 308–339, only the 171 *monstrous* McKay–Thompson series (denoted by uppercase ATLAS class names; at order 32 only `32A` = `A058629` and `32B` = `A058630`) appear.
   - Lowercase classes `32a`, `32b`, `32c`, `32d`, `32e` are **non-monstrous completely replicable functions**, first tabulated in **D. Alexander, C. Cummins, J. McKay, and C. Simons**, "Completely Replicable Functions", in *Groups, Combinatorics & Geometry* (Durham, 1990), LMS Lecture Note Ser. 165, Cambridge Univ. Press, 1992, pp. 87–98 (Table on p. 93), and further analyzed in **D. Ford, J. McKay, and S. P. Norton**, "More on replicable functions", *Comm. Algebra* 22 (1994), no. 13, 5175–5193, and **J. McKay and D. Sevilla**, "Decomposing replicable functions", *LMS J. Comput. Math.* 11 (2008), 146–171 (`arXiv:0803.3419`).

2. **Is $T_{32c}$ a single eta-quotient?**
   - **No.** $T_{32c}$ (`A112171`) is *not* a single holomorphic eta-quotient (its Euler transform sequence begins $[2, -3, 2, -4, 10, -19, 34, -63, 130, -263, \dots]$ and grows exponentially).
   - Instead, in the replicable-function tables (Alexander et al. 1992, p. 93; Ford–McKay–Norton 1994; McKay–Sevilla 2008, Appendix Table 1, lines `16b`, `32c`, `32d`, `32e`), `32e` (`A082303`) is the pure eta-quotient Hauptmodul of level 32 (symbol $8|4$, tabulated in **J. McKay and A. Sebbar**, "Fuchsian groups, automorphic functions and Schwarzians", *Math. Ann.* 318 (2000), 255–275, p. 274):
     $$T_{32e}(q) = \frac{\eta(q^8)}{\eta(q^{32})} = q^{-1} \prod_{k=1}^\infty \frac{1 - q^{8k}}{1 - q^{32k}},$$
     while `32c` and `32d` are degree-$(2,1)$ rational functions (harmonic sums) of $T_{32e}(q)$, indicated by the poset edges `16b -> (2:0, 32c) -> (2:1, 32e)` and `16b -> (2:0, 32d) -> (2:1, 32e)` in McKay–Sevilla (2008):
     $$T_{32c}(q) = \sqrt{T_{16b}(q^2) + 4} = T_{32e}(q) + \frac{2}{T_{32e}(q)} = \frac{\eta(q^8)}{\eta(q^{32})} + 2\,\frac{\eta(q^{32})}{\eta(q^8)},$$
     $$T_{32d}(q) = \sqrt{T_{16b}(q^2) - 4} = T_{32e}(q) - \frac{2}{T_{32e}(q)} = \frac{\eta(q^8)}{\eta(q^{32})} - 2\,\frac{\eta(q^{32})}{\eta(q^8)}.$$
   - In the OEIS power-series variable $x = q^2$ (multiplying by $q = x^{1/2}$ so the constant term is $1$), this is exactly Greubel's formula on `A112171`:
     $$F_{112171}(x) = A(x^4) + \frac{2x}{A(x^4)}, \qquad A(y) := y^{1/8}\frac{\eta(y)}{\eta(y^4)} = \frac{(y; y)_\infty}{(y^4; y^4)_\infty} = \sum_{n=0}^\infty \operatorname{A082303}(n)\,y^n,$$
     with reciprocal
     $$\frac{1}{A(y)} = y^{-1/8}\frac{\eta(y^4)}{\eta(y)} = \frac{(y^4; y^4)_\infty}{(y; y)_\infty} = \sum_{n=0}^\infty \operatorname{A001935}(n)\,y^n.$$

---

## 4. Check 3: Hauptmodul / Eta-Quotient Status of the A093085 Side

On the `A093085` side, the generating function IS a single holistic eta-quotient:
$$F_{093085}(x) = \frac{\varphi(-x)}{\psi(x^4)} = x^{1/2}\,\frac{\eta(x)^2\,\eta(q^4)}{\eta(x^2)\,\eta(x^8)^2}\Big|_{q=x} = \frac{(x; x)_\infty^2 (x^4; x^4)_\infty}{(x^2; x^2)_\infty (x^8; x^8)_\infty^2}.$$
- **Square as a $\Gamma_0(8)$ Hauptmodul**: Its square $x^{-1} F_{093085}(x)^2 = \left(\frac{\eta(x)^2\eta(x^4)}{\eta(x^2)\eta(x^8)^2}\right)^2$ is **OEIS A131124** (and its reciprocal is **OEIS A107035**, Fricke's $\tau_8(\omega)/16$, cited in **R. Fricke**, *Die elliptischen Funktionen und ihre Anwendungen*, Vol. 2, Teubner, 1922, p. 375, Eqs. (20), (21), (24); **Y. Yang**, "Transformation formulas for generalized Dedekind eta functions", *Bull. London Math. Soc.* 36 (2004), no. 5, 671–682, p. 679, Table 1, Entry 3; and **K. Acres and D. Broadhurst**, "Eta quotients and Rademacher sums", `arXiv:1810.07478` (2018), p. 10, Table 1, level 8).
- **Direct link to Monster class $8E$ (`A029841`)**: As explicitly recorded in `A131124` (`a(n) = A029841(n) unless n=0`), the square of $T_{093085}(q) := q^{-1} F_{093085}(q^2)$ is the Monster McKay–Thompson series $T_{8E}(q^2)$ (`A029841`, Hauptmodul for $\Gamma_0'(8)$, Conway–Norton 1979, p. 336) shifted by $-4$:
  $$T_{093085}(q)^2 = T_{8E}(q^2) - 4 = T_{16B}(q^4) - 4 + \frac{4}{T_{16B}(q^4)} = \left(B(q^8) - \frac{2}{B(q^8)}\right)^2,$$
  where $T_{16B}(y) = B(y^2)^2$ (`A029839`, McKay–Thompson series of class `16B`) is the normalized Hauptmodul for $\Gamma(4)$, and $B(y)$ (`A029838`) is its square root.
- **Why `A093085` is not itself a separate entry in the replicable tables**: While $T_{32c}(q) = \sqrt{T_{16b}(q^2) + 4}$ satisfies Norton's replicability conditions ($H_{1,15} = H_{3,5} = -1$), the 8th-root-of-unity twist $T_{093085}(q) = \sqrt{T_{8E}(q^2) - 4}$ has 2nd replicate $T_{8E}$ (`8E`) but fails odd-prime replicability at degree 15 ($H_{1,15} = -1 \ne H_{3,5} = +1$).

---

## 5. Check 4: Direct Symbolic Derivation from Published Identities

Both sides reduce to the exact same two-term expression via two textbook identities in **B. C. Berndt, *Ramanujan's Notebooks, Part III*** (Springer-Verlag, 1991):

### Step 1: 4-Dissection of `A093085` via Berndt Part III, Ch. 16, Entry 25 & Ch. 19, Entry 1(i)
By **Entry 25(i)–(ii) of Chapter 16** of Berndt's *Ramanujan's Notebooks, Part III* (p. 40), splitting $\varphi(-x) = \sum_{n=-\infty}^\infty (-1)^n x^{n^2}$ into even $n = 2k$ and odd $n = 2k+1$ gives the 2-dissection:
$$\varphi(-x) = \varphi(x^4) - 2x\,\psi(x^8).$$
Dividing by $\psi(x^4)$ immediately decomposes the `A093085` theta quotient into its $4n$ and $4n+1$ multisections:
$$F_{093085}(x) = \frac{\varphi(-x)}{\psi(x^4)} = \frac{\varphi(x^4)}{\psi(x^4)} - 2x\,\frac{\psi(x^8)}{\psi(x^4)}.$$
By **Entry 1(i) of Chapter 19** of Berndt's *Ramanujan's Notebooks, Part III* (p. 221, explicitly cited in both `A029838` and `A083365`, and in **W. Duke**, *Bull. Amer. Math. Soc.* 42 (2005), 137–162, Eqs. (9.1), (9.3)), the theta quotients $\varphi(y)/\psi(y)$ and $\psi(y^2)/\psi(y)$ are reciprocals given by the eta-quotient $B(y)$ (`A029838`) and $1/B(y)$ (`A083365`):
$$B(y) := \frac{\varphi(y)}{\psi(y)} = \frac{\psi(y)}{\psi(y^2)} = \frac{f(y)}{f(-y^4)} = \frac{(-y; -y)_\infty}{(y^4; y^4)_\infty} = \frac{(y^2; y^2)_\infty^3}{(y; y)_\infty (y^4; y^4)_\infty^2} = \sum_{n=0}^\infty \operatorname{A029838}(n)\,y^n,$$
$$\frac{1}{B(y)} = \frac{\psi(y)}{\varphi(y)} = \frac{\psi(y^2)}{\psi(y)} = \frac{f(-y^4)}{f(y)} = \frac{(y^4; y^4)_\infty}{(-y; -y)_\infty} = \frac{(y; y)_\infty (y^4; y^4)_\infty^2}{(y^2; y^2)_\infty^3} = \sum_{n=0}^\infty \operatorname{A083365}(n)\,y^n.$$
Setting $y = x^4$ yields the exact formula recorded in the `%C` and `%F` lines of `A093085`:
$$F_{093085}(x) = B(x^4) - \frac{2x}{B(x^4)} = \sum_{n=0}^\infty \operatorname{A029838}(n)\,x^{4n} - 2x \sum_{n=0}^\infty \operatorname{A083365}(n)\,x^{4n}. \tag{1}$$
Written out over a common denominator using $F_{093085}(x) = x^{1/2}\frac{\eta(x)^2\eta(x^4)}{\eta(x^2)\eta(x^8)^2}$ and $B(x^4) = x^{1/2}\frac{\eta(x^8)^3}{\eta(x^4)\eta(x^{16})^2}$, Equation (1) is the eta-product identity stated in the `%C` field of `A093085`:
$$\eta(q^2)\,\eta(q^8)^6 = \eta(q)^2\,\eta(q^4)^2\,\eta(q^8)\,\eta(q^{16})^2 + 2\,\eta(q^2)\,\eta(q^4)^2\,\eta(q^{16})^4.$$

### Step 2: Sign Twist $y \mapsto -y$ ($x^4 \mapsto -x^4$) to `A112171` ($T_{32c}$)
In Ramanujan's notation $f(-y) = (y; y)_\infty$, replacing $y \mapsto -y$ in $B(y) = f(y)/f(-y^4) = (-y; -y)_\infty / (y^4; y^4)_\infty$ simply changes $(-y; -y)_\infty$ to $(y; y)_\infty$ while leaving $(y^4; y^4)_\infty$ invariant (equivalently, via the Euler identity $(-y; -y)_\infty = (y^2; y^2)_\infty^3 / [(y; y)_\infty (y^4; y^4)_\infty]$, expressly noted in `A029838`, `A082303`, `A083365`, and `A001935`):
$$A(y) := B(-y) = \frac{f(-y)}{f(-y^4)} = \frac{(y; y)_\infty}{(y^4; y^4)_\infty} = y^{-1/8}\cdot y^{1/8}\frac{\eta(y)}{\eta(y^4)} = \sum_{n=0}^\infty (-1)^n \operatorname{A029838}(n)\,y^n = \sum_{n=0}^\infty \operatorname{A082303}(n)\,y^n,$$
$$\frac{1}{A(y)} = \frac{1}{B(-y)} = \frac{f(-y^4)}{f(-y)} = \frac{(y^4; y^4)_\infty}{(y; y)_\infty} = \sum_{n=0}^\infty (-1)^n \operatorname{A083365}(n)\,y^n = \sum_{n=0}^\infty \operatorname{A001935}(n)\,y^n.$$
Substituting $y = x^4$ into Greubel's formula on `A112171` ($F_{112171}(x) = A(x^4) + 2x/A(x^4)$) gives:
$$F_{112171}(x) = B(-x^4) + \frac{2x}{B(-x^4)} = \sum_{n=0}^\infty (-1)^n \operatorname{A029838}(n)\,x^{4n} + 2x \sum_{n=0}^\infty (-1)^n \operatorname{A083365}(n)\,x^{4n}. \tag{2}$$

### Step 3: Term-by-Term Comparison of (1) and (2)
Comparing Equations (1) and (2) coefficient by coefficient:
- $\operatorname{A112171}(4n) = \operatorname{A082303}(n) = (-1)^n \operatorname{A029838}(n) = (-1)^n \operatorname{A093085}(4n)$,
- $\operatorname{A112171}(4n+1) = 2\operatorname{A001935}(n) = 2(-1)^n \operatorname{A083365}(n) = -(-1)^n \operatorname{A093085}(4n+1)$,
- $\operatorname{A112171}(4n+2) = \operatorname{A093085}(4n+2) = 0$,
- $\operatorname{A112171}(4n+3) = \operatorname{A093085}(4n+3) = 0$.

Thus, both sequences are built from the exact same level-16/32 eta-quotient pair (`A029838` and `A083365`), differing only by the sign twist $x^4 \mapsto -x^4$ (and $x \mapsto -x$ on the odd multisection, with class $32d$ = `A112172` having the same $-2x$ sign as `A093085`).

---

VERDICT: DISGUISED — B. C. Berndt, *Ramanujan's Notebooks, Part III* (Springer, 1991), Ch. 16, Entry 25(i)–(ii), p. 40 and Ch. 19, Entry 1(i), p. 221; D. Alexander, C. Cummins, J. McKay, and C. Simons, "Completely Replicable Functions", *LMS Lecture Note Ser.* 165 (1992), 87–98 (Table on p. 93); D. Ford, J. McKay, and S. P. Norton, "More on replicable functions", *Comm. Algebra* 22 (1994), no. 13, 5175–5193; J. McKay and D. Sevilla, "Decomposing replicable functions", *LMS J. Comput. Math.* 11 (2008), 146–171 (`arXiv:0803.3419`, Appendix Table 1, lines `16b`, `32c`, `32d`, `32e`); and OEIS records A093085 (M. Somos, 2004/2007), A112171 (M. Somos, 2005; G. C. Greubel, 2018), A029838, A083365, A082303, and A001935.
LITCHECK COMPLETE

# Paper 4: Fourier Endpoint Minimax and Autocorrelation-Deficit Rank Bounds for Finite Abelian Character Tables

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript.
- `references.bib` — Clean BibTeX bibliography.
- `verify_endpoint_minimax.py` — Standalone Python 3 (stdlib only) exact verifier performing cyclotomic-field Gaussian elimination over $\mathbb{Q}[x]/(\Phi_N(x))$ for bit-reversal cuts ($N=1,2,4,8,16$), all 3,136 critical $3\times 5$ blocks and all 4,900 half-size $4\times 4$ blocks of $F_8$, even-even rank-$N/4$ blocks ($N=4,8,16$), all 4,468 nonempty rectangles across $C_2\times C_2, C_3, C_4, C_6$, and exact rational identities for $B_L$, Table 1, and $S_N$ through $N=4096$.
- `FourierEndpointMinimax.lean` — Zero-dependency Lean 4 formal verifier (core `Init` only, verified in Lean 4.36.0 with zero `sorry` and pure kernel reduction) symbolically proving the strict critical-rectangle moment bound $B_L < L+1$ for all $L \ge 2$, the autocorrelation-deficit moment algebra, odd-set translation non-invariance in $\mathbb{Z}/2^m\mathbb{Z}$, the bit-reversal recurrence bound $r_N(k) \le N/4+1$ and attainment $r_N(N/2-1) = N/4+1$ for all $m \ge 3$, and the closed-form cut-rank sum $S_N$ for all $m \ge 0$; plus pure-kernel finite cyclotomic-field and group-rectangle certificates.

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.CO` (Combinatorics) / `math.CA` (Classical Analysis and ODEs)
- **MSC 2020:** Primary `15A03`, `42A99`; Secondary `15B10`, `05E16`, `65T50`
- **Target journals (zero-fee):** *Linear Algebra and its Applications*, *SIAM Journal on Matrix Analysis and Applications*.

## Verify Computations and Lean Proofs
```bash
python3 verify_endpoint_minimax.py
lean FourierEndpointMinimax.lean
```

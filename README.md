# kapetanakis-2017-jnt-audit

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24350768.svg)](https://doi.org/10.5281/zenodo.24350768)

Paper, verification program and data for

> Ruqing Chen, *Prescribing coefficients of invariant irreducible polynomials over finite fields:
> counterexamples, corrected formulas, and complete restoration* (2026).

The note audits

> G. Kapetanakis, *Prescribing coefficients of invariant irreducible polynomials*,
> J. Number Theory **180** (2017), 615–628, [doi:10.1016/j.jnt.2017.05.003](https://doi.org/10.1016/j.jnt.2017.05.003)

in the author's repository text dated 24 May 2017. The printed version was not compared and may differ.

## Summary

For a lower-triangular `A ∈ GL(2,q)`, the paper under audit studies which coefficients of the monic
irreducible polynomials over `F_q` invariant under `A` are forced and which can be prescribed. The note shows
that

- the coefficient formula of Theorem 2.8 is wrong;
- inequality (5) cannot hold for `μ = 2` when `q ≤ 64`, so every row of Table 2 fails;
- Theorem 3.4(2) is false: the coefficient takes a single value, not `φ(r)(q−1)/r` values;
- the diagonal case of Theorem 3.4 is misstated twice;
- the proof of Theorem 3.4(3) does not control the constant term.

It then gives complete statements and proofs (Theorems A and B). Both existence statements hold with no
exceptional pairs: for one eigenvalue every `κ ∈ F_q` occurs whenever `2 ≤ μ ≤ n/2`, and for two eigenvalues
whenever `1 ≤ μ < n/2`. The finitely many cases not reached by the bounds (5710 and 719 cases) are settled by
explicit polynomials, listed in `data/closure.json`.

## Contents

| Path | Content |
| --- | --- |
| `kapetanakis_invariant_polynomials_audit.tex`, `.pdf` | the note |
| `code/verify_kapetanakis_jnt2017.py` | verification program |
| `data/verify_kapetanakis_jnt2017.txt` | log of the program |
| `data/*.json` | machine-readable results, one file per part (below) |
| `figures/` | the two figures of the note |

Parts of the program and their output files:

| Part | Output | What is checked |
| --- | --- | --- |
| `gamma` | `gamma.json` | coefficient formula of Theorem 2.8, as printed and as corrected; Table 1 |
| `diag` | `diag.json` | two eigenvalues: formula for `q_m`; the case `μ = 0` of Theorem 3.4(2) |
| `pure` | `pure.json` | `[A] = [B]`: irreducibility criterion `(−1)^n p_0 ∈ C`; attained values |
| `wsum` | `wsum.json` | weighted sums `w` computed exactly; conditions (S2), (S3) |
| `thresh` | `thresholds.json` | inequalities (5), (8) and Tables 2, 3 of the paper; thresholds of (S2), (S3) |
| `truth` | `truth.json` | exhaustive check of the conclusion of Theorem 2.8(4) for small `(q, n)` |
| `direct` | `direct.json` | lower bounds (D2), (D3) against exact counts |
| `closure` | `closure.json` | ranges where (D2), (D3) are not positive; an explicit polynomial for every case |
| `lemmas` | `lemmas.json` | prescribed trace coefficient and constant term; auxiliary inequalities |
| `figures` | `figures/*.pdf` | the two figures |

## Running

Requires Python 3 with `sympy` and `matplotlib` (results in this repository: Python 3.12.4, sympy 1.13.1,
matplotlib 3.8.4).

```
pip install -r requirements.txt
cd code
python verify_kapetanakis_jnt2017.py            # all parts
python verify_kapetanakis_jnt2017.py gamma diag # selected parts
```

The program rewrites `data/*.json` and the figures, and appends to `data/verify_kapetanakis_jnt2017.txt`.

## Citation

```bibtex
@misc{chen2026kapetanakis,
  author = {Chen, Ruqing},
  title  = {Prescribing coefficients of invariant irreducible polynomials over finite fields:
            counterexamples, corrected formulas, and complete restoration},
  year   = {2026},
  doi    = {10.5281/zenodo.24350768},
  url    = {https://doi.org/10.5281/zenodo.24350768}
}
```

See also `CITATION.cff`.

## License

Code (`code/`): MIT, see `LICENSE`. Paper, figures and data: [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

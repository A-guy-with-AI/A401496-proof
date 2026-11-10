# A proof of the conjectured formula for OEIS A401496

This repository contains a proof, machine-checked in Lean 4, of the formula conjectured in OEIS [A401496](https://oeis.org/A401496):

> For every n ≥ 1, the number a(n) of Riordan graphs of order n (fixed vertex labels) whose complement is again a Riordan graph is
>
> **a(n) = 1 + Σ_{k=0}^{n−2} 2^⌊3k/2⌋**  (the sum is empty for n = 1).

Values: 1, 2, 4, 12, 28, 92, 220, 732, 1756, 5852, …

The conjecture and the data are due to **Arnauld Mesinga Mwafise** (OEIS A401496, October 2026; software [riordan-graph-enumerator](https://github.com/arnauldmwafise/riordan-graph-enumerator), [doi:10.5281/zenodo.23676628](https://doi.org/10.5281/zenodo.23676628)). Riordan graphs were introduced by Cheon, Jung, Kitaev and Mojallal, *Riordan graphs I: Structural properties*, Linear Algebra Appl. 579 (2019), [arXiv:1710.04604](https://arxiv.org/abs/1710.04604).

## Main idea

A Riordan graph of order n corresponds to a binary Riordan matrix R(g, f) of size m = n − 1 over F₂. Taking the complement adds the full lower-triangular matrix P. If 1 ≤ val(g) = v < m, then

  R + P is a Riordan matrix ⇔ t^v (f + t)² ≡ 0 (mod t^m).

The complement map is an involution. It exchanges these solutions with the solutions for which g(0) = 1, except for the pair {0, P}. Counting the solutions of the condition above gives the formula. A related "sum of two Riordan arrays" obstruction appears in Bang et al., *On sums, derivatives, and flips of Riordan arrays*, J. Integer Seq. 26 (2023), [arXiv:2210.02566](https://arxiv.org/abs/2210.02566).

Consequences: a(n) = 8a(n−2) − 4, a(2k) = (10·8^(k−1) + 4)/7, a(2k+1) = (3·8^k + 4)/7.

## Contents

| File | Description |
|---|---|
| `A401496_proof.pdf` | The paper (English), with the full proof, references and credits |
| `A401496_proof.tex` | LaTeX source of the paper |
| `A401496.lean` | Complete Lean 4 formalization (1038 lines) |
| `checks/verif_riordan_chatgpt.cpp`, `checks/enumerate_chatgpt.py` | Independent exhaustive enumeration for n ≤ 13 |
| `checks/verify_characterization.py` | Brute-force check of the characterization for small m |

## The formal statement

```lean
theorem A401496_formula (n : ℕ) (hn : 0 < n) :
    a n = 1 + ∑ k ∈ Finset.range (n - 1), 2 ^ (3 * k / 2)
```

The definition of `a` follows the OEIS description literally. It takes all pairs of truncated series (g, f) over `ZMod 2` with f(0) = 0, the finite set of the resulting matrices, and the number of matrices in that set whose complement is also in the set.

## How to check

Requirements: Lean `4.36.0-rc2` and Mathlib commit `9d581dfff2e41de989072ea63abf3daf69311520`.

```bash
lake env lean A401496.lean
```

Expected output: no errors and no `sorry`. `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`, and the control `#eval` prints `[1, 2, 4, 12, 28, 92]`.

SHA-256 of `A401496.lean`:
`66ded426dce65d5f81df5e790edd39f93e3bcd951eb2cfa86d48dc3ba9778517`

Independent checks (optional):

```bash
python3 checks/enumerate_chatgpt.py 13        # needs clang++
python3 checks/verify_characterization.py 10
```

## Scope

- This result counts **labeled** graphs: the complement must be Riordan for the same vertex order.
- It does not settle the unlabeled version of Problem 3 of Cheon–Jung–Kitaev–Mojallal (complement isomorphic to a Riordan graph).
- We know of no earlier proof, but we cannot rule one out.

## Credits and use of AI

This work was produced under the pseudonym A-guy-with-AI, in collaboration with two AI systems:

- **Claude (Anthropic)**: the characterization and the first written proof; an independent recompilation and audit of the Lean file.
- **ChatGPT (OpenAI)**: review of the proof and corrections of edge cases; the independent enumeration; the references; the complete Lean formalization.

Mathematical credit for the conjecture and the data goes to A. Mesinga Mwafise.

## License

MIT, see `LICENSE`.

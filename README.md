# Colombo's determinant problem: a single-file Lean proof

For distinct real numbers $x_1,\ldots,x_N$, with integers $N\ge2$ and $D\ge1$,
let $A_{ij}=(x_j-x_i)^D$. This project proves the complete criterion

$$\det A\ne0\quad\Longleftrightarrow\quad N\le D+1\ \text{and}\ (N\text{ even or }D\text{ even}).$$

- [Paper (PDF)](paper/colombo_interpolation.pdf)
- [Editable LaTeX manuscript](paper/colombo_interpolation.tex)
- [Complete single-file Lean proof](DifferencePowerSingle.lean)
- [Original compilation and axiom audit](verification/original-verification.txt)
- [Publication-copy verification](verification/publication-verification.txt)
- [Development context and limitations](docs/DEVELOPMENT.md)

The proof-specific definitions and lemmas are all in `DifferencePowerSingle.lean`.
Its only import is `Mathlib`. The final theorem states the full biconditional for
arbitrary parameters and injective real node functions. Its audited axioms are
`propext`, `Classical.choice`, and `Quot.sound`, with no unfinished proof or added
mathematical axiom.

## Proof organization

An auxiliary polynomial encodes the signs of a hypothetical kernel vector.
Directional differentiation turns its associated homogeneous power sum into a
positive sum of even powers; a projective Rolle bound then limits its real roots.
Ordinary interpolation handles opposite parities. For even size and even exponent,
the identity $\sum_i c_i f'(x_i)=0$ cancels the leading coefficient of a second
interpolant, reducing its degree to at most $N-2$ and giving the final contradiction.

The paper compares this construction with Ma's Pfaffian positivity approach and
Li, Tie, Wang, and Liu's algebraic root-count approach. The criterion and the
classical root-count principle are not claimed as new results.

## Reproduce the formal check

The project pins Lean **4.32.0** and mathlib **v4.32.0**, with the mathlib commit
and transitive dependency revisions recorded in `lake-manifest.json`.
With [elan](https://github.com/leanprover/elan) installed:

```sh
git clone https://github.com/HappyAny/colombo-determinant-lean.git
cd colombo-determinant-lean
lake exe cache get
lake env lean DifferencePowerSingle.lean
```

The last command prints the final theorem type and its transitive axiom list.
`lake build` also builds the proof library. A fresh installation may download
the toolchain and dependencies. The original session used an existing local
Lean/mathlib cache; this later reproduction setup is a separate stage.

The source remains byte-for-byte identical to the original verified file:

```text
fadaff4dbbbdf86a594bddb5472d5f9e5be5edd8deac2afe4f2ba38ae29bb98e
```

Run `python scripts/check_source.py` to check the published file checksums.
This integrity check supplements the Lean check; it does not replace it.

## Build the paper

From the repository root, use Tectonic or XeLaTeX with Latin Modern OpenType fonts:

```sh
tectonic --outdir paper paper/colombo_interpolation.tex
```

The supplied PDF was built with Tectonic 0.17.0. The manuscript is in English.

## Session note

According to the user's record, the original mathematical solution and complete
Lean formalization took approximately **50 minutes** with **GPT-6 Astra**, reasoning
effort **max**, **Codex as the sole harness**, **fast mode disabled**, and **no special
orchestration skills**. The user-written prompts were brief and did not supply a
detailed proof strategy. **Online search was explicitly prohibited during that
original solution and formalization.** Literature comparison, manuscript writing,
and publication followed afterwards.

Astra's training-data and prior-knowledge coverage is unknown. An offline session
cannot rule out prior exposure to related material. Timing and workflow observations
are therefore **for reference only**, not a controlled benchmark or an assurance of
model-level originality. The theorem has a separate Lean kernel verification record.

The paper raises, without claiming to settle, whether stronger models reduce the
marginal value of additional task-specific orchestration. This single case does not
establish a trend or make the execution and verification environment unnecessary.

## Related work

- Qianli Ma, [Colombo's Determinant Problem](https://arxiv.org/abs/2609.00101).
- Kun Li, Li Tie, Peng Wang, and Zihan Liu,
  [An algebraic proof of Colombo's difference-power determinant conjecture](https://arxiv.org/abs/2608.28274).
- Bruce Reznick, [On the length of binary forms](https://arxiv.org/abs/1007.5485), Section 3.

The manuscript identifies the external source-code snapshots used for comparison.
Neither complete external Lean project was rebuilt locally for that comparison.

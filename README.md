# Colombo's determinant problem: a single-file Lean proof

**This project began with [this WeChat article](https://mp.weixin.qq.com/s/WPqkTamXIVE1wvFoRIaNMA).**
After reading it, I wanted to try **GPT-6 Astra**, which I expected to be a more
capable model, and see whether it could **reproduce the mathematical conclusion
and produce a complete proof using the default Codex harness**. That experiment
became this repository.

Here, reproduction means obtaining the same determinant criterion together with
a complete mathematical proof and a checkable, single-file Lean formalization.
The article motivated my choice of problem. **The AI's original solving and
formalization stage was explicitly prohibited from using online search.** Reading
the research papers and comparing their code took place after the original proof
artifact had been checked.

## Environment and AI settings

The original experiment used the following setup. Model settings, prompting,
elapsed time, and quota usage are reported from my session record; the included
verification logs document the Lean checks. The local shell version below was
recorded for this project.

| Item | Setup |
| --- | --- |
| Local environment | Windows, x86-64; PowerShell 7.6.5 |
| Model | GPT-6 Astra |
| Reasoning effort | max |
| Harness | **Default Codex harness**, with its ordinary instructions and tools; Codex was the sole harness |
| Fast mode | **Disabled** |
| Special orchestration skills | **None** during the original solution and formalization |
| Task prompts | **Brief**: solve the supplied problem without online search and formalize it in Lean; no detailed proof strategy was supplied |
| Online search | **Explicitly prohibited** during the original mathematical solution and Lean formalization |
| Lean environment | Pre-existing local **Lean 4.32.0 / mathlib v4.32.0** installation and dependency caches |
| Reported duration | **Approximately 50 minutes** for the original solution and formalization; later literature comparison, manuscript writing, and publication are excluded |
| Reported quota usage | Only **approximately 1–2% of the weekly usage allowance on the 20x plan** for this experiment |
| Formal check | Complete single-file proof compiled successfully; the final theorem uses only `propext`, `Classical.choice`, and `Quot.sound` |
| Model knowledge coverage | **Unknown**, including its exact training-data coverage and prior exposure to related material |

The expectation that Astra would be more capable motivated this attempt; this
project does not measure a performance advantage over another model. Because its
prior knowledge is unknown, the timing, quota usage, and workflow observations are **for
reference only**. The mathematical theorem has its own Lean verification record.

## Original conversation

Read the [Chinese original](docs/conversation/initial-two-rounds.md) or the
[English translation](docs/conversation/initial-two-rounds-en.md).
The excerpts cover the initial no-search agreement and the first complete solution
and Lean formalization, including the problem image, visible progress updates,
and final responses. The original exchange was in Chinese; the English version
was translated afterwards.

The core problem-solving exchange took **50 minutes 12 seconds** from the
problem submission to the first complete response, where the excerpts end.
Time labels show elapsed time from the first retained message. The
[provenance manifest](docs/conversation/manifest.json) records the relative
message times, hashes, and presentation changes.

## Result and artifacts

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

## Interpreting the experiment

Astra's training-data and prior-knowledge coverage is unknown. An offline session
cannot rule out prior exposure to related material. Timing, quota usage, and workflow observations
are therefore **for reference only**, not a controlled benchmark or an assurance of
model-level originality. The theorem has a separate Lean kernel verification record.

This experiment made me wonder: **as models become more capable, does the marginal
value of additional harness engineering decrease?** My working hypothesis is that
some planning, task decomposition, tool selection, and error correction that once
needed explicit orchestration may increasingly be handled by the model within a
general-purpose harness. If so, a brief task description and a reliable verification
loop could be enough for more tasks, reducing the need for custom workflows.

Codex still supplied tool execution, context management, and access to compiler
feedback in this project; Lean provided an independent check of the resulting proof.
Those functions were part of the experiment. The possibility I find interesting is
that stronger models could reduce how much task-specific coordination we need to
build on top of that foundation. Reliable tools and verification would still have
a clear role, especially as the tasks we attempt become more demanding.

This is a thought prompted by one session. We did not compare models or harnesses
under matched conditions, so this repository cannot show that extra orchestration
would have helped less, or establish a general trend. Testing the idea would require
repeated runs across models and harness designs on the same tasks, with matched
resource budgets, measuring verified completion, cost, and failure modes.

## Related work

- Qianli Ma, [Colombo's Determinant Problem](https://arxiv.org/abs/2609.00101).
- Kun Li, Li Tie, Peng Wang, and Zihan Liu,
  [An algebraic proof of Colombo's difference-power determinant conjecture](https://arxiv.org/abs/2608.28274).
- Bruce Reznick, [On the length of binary forms](https://arxiv.org/abs/1007.5485), Section 3.

The manuscript identifies the external source-code snapshots used for comparison.
Neither complete external Lean project was rebuilt locally for that comparison.

# Core problem-solving process: the no-search agreement and initial formalization

[Chinese original](initial-two-rounds.md)

This is an English translation of an excerpt from the original Codex conversation. It preserves the user prompts, the AI's visible progress updates, and its final responses. The original exchange was in Chinese; this translation was prepared afterwards. The date is **6 September 2026**. Time labels show elapsed minutes and seconds from the first message (T+mm:ss), rounded to the nearest second.

The excerpt begins with the initial agreement prohibiting online search and ends with the final response reporting the first complete solution and Lean formalization.

The public edition preserves the wording of the source excerpt with formatting adjustments: the image is linked within the repository; historical local file links point to the corresponding manuscript, current complete Lean proof, and reproduction instructions, with their displayed text retained; mathematical delimiters use GitHub syntax; and interface-specific memory citation markup is omitted. This English version translates the retained messages, including the text within mathematical displays, while preserving the mathematical notation and Lean code. It does not rewrite the original answers to match the later paper. Editorial notes are marked. Tool calls and system instructions are outside the scope of this excerpt.

## Timing

| Stage | User submission | AI final response | Elapsed time in the log |
| --- | --- | --- | --- |
| Preliminary agreement prohibiting online search | T+00:00 | T+00:10 | About 10 seconds |
| Initial solution and complete Lean formalization (then split across files) | T+01:11 | T+51:23 | 50 minutes 12 seconds |

The reported "approximately 50 minutes" refers to the initial solution and complete Lean formalization. These are wall-clock intervals from the conversation log, not measurements of model computation time alone.

## Translated conversation

### Preliminary agreement: no online search

**T+00:00 — HappyAny**

I will give you a mathematics problem. I would like you to solve it without searching the internet.

**T+00:10 — AI · Final response**

Please send the problem. I will respect the **no online search** condition, derive the solution independently, and provide a clear, checkable argument. If any part remains unproved, I will state that explicitly.

### Solving the problem and formalizing it in Lean

**T+01:11 — HappyAny**

After finding an approach, remember to formalize the proof in Lean.
![Original problem image](initial-problem.jpg)

> Editorial note: The image asks the following question. Given integers $N\ge 2,D\ge 1$, distinct real numbers $x_1,\ldots,x_N$, and the matrix $A_{N,D}(x)=[(x_j-x_i)^D]_{i,j=1}^{N}$, when is its determinant nonzero? This is a translation of the text in the image, not an additional original prompt.

**T+01:17 — AI · Progress update**

I will first derive a necessary and sufficient condition for the determinant to be nonzero, then formalize and check the proof using the local Lean environment, without searching the internet at any point.

**T+02:25 — AI · Progress update**

I have identified two cases in which the determinant must vanish: when $N>D+1$, the rank is insufficient; when both $D$ and $N$ are odd, the matrix is skew-symmetric of odd order. The key remaining question is whether the determinant is nonzero for every choice of distinct real numbers in all other cases.

**T+04:43 — AI · Progress update**

The candidate criterion is that $\det A\ne0$ if and only if $N\le D+1$ and at least one of $D$ and $N$ is even. All 840 small integer test cases agree with it, but they cannot replace a proof of sufficiency. Lean and mathlib are already cached locally, so formalization and checking can proceed offline.

**T+13:34 — AI · Progress update**

I have found a proof approach covering all cases, with the criterion stated above. The key is to use Rolle's theorem to control the number of real roots of a polynomial. In the most difficult case, where both $D$ and $N$ are even, the alternating signs of the kernel vector and the derivative give a contradiction. I am now translating these steps into Lean lemmas.

**T+20:13 — AI · Progress update**

The informal proof is complete. Lean has checked the vanishing of the derivative pairing, the determinant of order two, and several other steps. The projective Rolle lemma with multiplicities, needed for sufficiency in general, is still being formalized. I will distinguish the informal argument from the parts that Lean has actually checked.

**T+28:53 — AI · Progress update**

The key projective Rolle lemma has now passed Lean checking, including the treatment of real-root multiplicities under reciprocal substitution. The general necessary conditions and nonvanishing when $N=D+1$ have also passed. What remains is to connect the sign-control argument to the matrix kernel condition.

**T+41:05 — AI · Progress update**

The real-root bound has now been fully checked by Lean: from an auxiliary polynomial satisfying specified sign conditions, it gives an upper bound on the number of roots of the original polynomial. To simplify the final formal connection, I am constructing this auxiliary polynomial by Lagrange interpolation. Next I will check the theorem giving the full necessary and sufficient condition.

**T+45:20 — AI · Progress update**

The full necessary and sufficient condition has passed the local Lean 4.32.0 check. The main theorem's axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or additional axioms. I am now organizing the proof, offline reproduction scripts, and verification logs, and saving a knowledge-library snapshot in accordance with your existing convention.

**T+51:23 — AI · Final response**

The conclusion is
$$
\boxed{\det A_{N,D}(x)\ne0
\iff N\le D+1\quad\text{and}\quad(D\text{ is even or }N\text{ is even}).}
$$
Thus the answer does not depend on the specific values of the distinct real numbers.

**The complete necessary and sufficient condition has passed local Lean checking**, with no online search throughout the process. Here is the proof.

First consider necessity. By the binomial expansion, every column of the matrix belongs to
$$
\operatorname{span}\{(1)_i,(x_i)_i,\ldots,(x_i^D)_i\},
$$
so its rank is at most $D+1$. Also, if $D$ is odd, then $A^T=-A$; when $N$ is odd as well, the determinant must vanish.

The key to sufficiency is a real-root counting lemma. For a real homogeneous binary polynomial $F(u,v)$, let $R(F)$ denote the number of real projective roots counted with multiplicity, including roots at infinity. **One nonzero directional differentiation reduces this root count by at most one.** This is Rolle's theorem with multiplicities: change coordinates so that the differentiation direction becomes $\partial_u$, apply ordinary Rolle's theorem to the finite roots, and retain the multiplicity of the root at infinity.

Now order the nodes as $x_1<\cdots<x_N$. Suppose there is a nonzero kernel vector $c$, and set
$$
F(u,v)=\sum_jc_j(u-x_jv)^D,\qquad f(t)=F(t,1).
$$
Since $Ac=0$, every $x_i$ is a root of $f$, so $R(F)\ge N$. At least two coefficients $c_j$ are nonzero; otherwise the polynomial could not vanish at all these nodes.

Discard the zero coefficients, and suppose the remaining coefficient sequence has $s$ sign changes. Choose a real root in each gap corresponding to a sign change, obtaining a polynomial $q$, and adjust its overall sign so that
$$
c_jq(x_j)>0\qquad(c_j\ne0).
$$
If necessary, add one more root to the right of all the nodes. We can therefore choose
$$
k=\deg q\in\{s,s+1\},\qquad k\equiv D\pmod2.
$$

If $k\le D$, differentiate successively in the directions corresponding to the roots of $q$. Using
$$
(a\partial_u+\partial_v)(u-xv)^d
=d(a-x)(u-xv)^{d-1},
$$
the result, after multiplication by a nonzero constant, is
$$
\sum_j c_jq(x_j)(u-x_jv)^{D-k}.
$$
This is a strictly positive homogeneous form: the exponent is even, the coefficients are positive, and at least two distinct linear factors cannot vanish simultaneously. It therefore has no real projective roots. Iterating Rolle's theorem gives
$$
\boxed{R(F)\le k.}
$$

When $D$ and $N$ have opposite parity, $N-1$ has the same parity as $D$, and $s\le N-1$, so we can take $k\le N-1$. Hence
$$
N\le R(F)\le N-1,
$$
a contradiction.

It remains to consider the case where both $D$ and $N$ are even; here $D\ge N$. If $s\le N-2$, we can similarly choose an even $k\le N-2$, again obtaining a contradiction. Thus $s=N-1$: every $c_i$ is nonzero, and their signs strictly alternate.

Taking $k=N$ now gives $R(F)=N$. Thus $f$ has exactly these $N$ real roots, all of them simple. Consequently,
$$
f'(x_1),\ldots,f'(x_N)
$$
also have strictly alternating signs. All the products $c_if'(x_i)$ are nonzero and have the same sign, so their sum cannot vanish. But
$$
\sum_i c_if'(x_i)
=D\sum_{i,j}c_ic_j(x_i-x_j)^{D-1}=0,
$$
because $D-1$ is odd, and exchanging $i$ and $j$ cancels the terms in pairs. This contradiction proves sufficiency.

The main theorem checked by Lean is:

```lean
theorem determinant_ne_zero_iff {N D : ℕ}
    (hN : 2 ≤ N) (_hD : 1 ≤ D)
    (x : Fin N → ℝ) (hx : Function.Injective x) :
    (A D x).det ≠ 0 ↔
      N ≤ D+1 ∧ (Even D ∨ Even N)
```

Using Lean 4.32.0, the main theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`, with **no `sorryAx` and no additional axioms**.

[Complete derivation](../../paper/colombo_interpolation.pdf) · [Main Lean proof](../../DifferencePowerSingle.lean) · [Real-root counting proof](../../DifferencePowerSingle.lean) · [Offline reproduction instructions](../../README.md)

The proof and source snapshot have also been archived in Agent Library, and their file hashes have been checked.

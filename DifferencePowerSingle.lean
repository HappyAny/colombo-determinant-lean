import Mathlib

/-!
# 实数差幂矩阵：从题目到完整充要条件的单文件证明

题目：N ≥ 2，D ≥ 1，x : Fin N → ℝ 单射（即节点互异），
      Aᵢⱼ = (xⱼ - xᵢ)^D。何时 det A ≠ 0？
结论：det A ≠ 0 ↔ N ≤ D + 1 ∧ (Even D ∨ Even N)。

本文件仅依赖 Mathlib；本题所用的辅助定义和引理均在下方按依赖顺序证明。
Lean 4.32.0 / mathlib v4.32.0。最后的 theorem 直接写出题目的矩阵，
文件末尾打印其类型和完整传递依赖的公理审计。

阅读主线：
1. 二项式分解给出秩上界；奇次幂给出反对称性，得到必要条件。
2. 若 Ac = 0，则 f(t) = Σ cⱼ(t-xⱼ)^D 在全部 N 个节点处为零。
3. 给实根按重数计数，并补上无穷远点处的重数；射影 Rolle 定理
   说明一次非零方向导数至多损失一个实根。
4. 一个与 c 在节点处同号的低次多项式 g 提供一组求导方向；
   求导后的系数同号且幂次为偶数，因而没有实根，反推出 f 的根数上界。
5. 插值 g(xᵢ)=cᵢ 得到 N-1 的上界，解决 N、D 奇偶性相反的情形。
6. N、D 均偶时，反对称导数恒等式让另一个插值多项式降至 N-2 次，
   再次与至少 N 个根矛盾。于是核为零，行列式非零。

自然数 N、D 加上下界，准确表达原题的正整数范围。
-/

open scoped BigOperators
open Matrix Finset Polynomial

namespace DifferencePowerSingle


/-!
## 1. 定义矩阵并证明必要性

二项式展开给出 A = L R，其中 L 只有 D+1 列，故 rank A ≤ D+1。
另外，D 为奇数时 Aᵀ = -A；如果 N 也为奇数，则 det A = -det A = 0。
这两步合起来给出 N ≤ D+1 且 D、N 至少有一个为偶数。
-/

def A {N : ℕ} (D : ℕ) (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (x j - x i) ^ D

def leftFactor {N : ℕ} (D : ℕ) (x : Fin N → ℝ) : Matrix (Fin N) (Fin (D+1)) ℝ :=
  fun i k => (-x i) ^ (k : ℕ)

def rightFactor {N : ℕ} (D : ℕ) (x : Fin N → ℝ) : Matrix (Fin (D+1)) (Fin N) ℝ :=
  fun k j => x j ^ (D - (k : ℕ)) * (D.choose (k : ℕ) : ℝ)

theorem factorization {N : ℕ} (D : ℕ) (x : Fin N → ℝ) :
    A D x = leftFactor D x * rightFactor D x := by
  ext i j
  simp only [A, leftFactor, rightFactor, Matrix.mul_apply]
  rw [show (∑ k : Fin (D+1), (-x i)^(k : ℕ) * (x j^(D-(k : ℕ)) * (D.choose (k : ℕ) : ℝ))) =
      ∑ k ∈ Finset.range (D+1), (-x i)^k * (x j^(D-k) * (D.choose k : ℝ)) from
    Fin.sum_univ_eq_sum_range (fun k => (-x i)^k * (x j^(D-k) * (D.choose k : ℝ))) (D+1)]
  simpa only [sub_eq_neg_add, mul_assoc] using (add_pow (-x i) (x j) D)

theorem rank_le {N : ℕ} (D : ℕ) (x : Fin N → ℝ) :
    (A D x).rank ≤ D + 1 := by
  rw [factorization]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem det_zero_of_large {N D : ℕ} (x : Fin N → ℝ) (h : D + 1 < N) :
    (A D x).det = 0 := by
  by_contra hn
  have hu : IsUnit (A D x) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
  have hr := Matrix.rank_of_isUnit (A D x) hu
  have hb := rank_le D x
  simp only [Fintype.card_fin] at hr
  omega

theorem transpose_of_odd {N D : ℕ} (x : Fin N → ℝ) (hD : Odd D) :
    (A D x)ᵀ = -A D x := by
  ext i j
  simpa only [A, Matrix.transpose_apply, Matrix.neg_apply, neg_sub] using
    hD.neg_pow (x j - x i)

theorem det_zero_of_odd_odd {N D : ℕ} (x : Fin N → ℝ)
    (hD : Odd D) (hN : Odd N) : (A D x).det = 0 := by
  have h := Matrix.det_transpose (A D x)
  rw [transpose_of_odd x hD, Matrix.det_neg, Fintype.card_fin, hN.neg_one_pow] at h
  linarith

theorem necessary {N D : ℕ} (x : Fin N → ℝ) (h : (A D x).det ≠ 0) :
    N ≤ D + 1 ∧ (Even D ∨ Even N) := by
  constructor
  · by_contra hn
    exact h (det_zero_of_large x (by omega))
  · by_contra hn
    push Not at hn
    exact h (det_zero_of_odd_odd x (Nat.not_even_iff_odd.mp hn.1)
      (Nat.not_even_iff_odd.mp hn.2))

/-!
## 2. 从核向量得到一个在所有节点处消失的多项式

以下始终使用同一个定义 powerSum。若 Ac = 0，则
f(xᵢ) = (-1)^D (Ac)ᵢ = 0。
非零核向量至少在两个不同节点处有非零系数；否则另一行的核方程立即矛盾。
这保证后面出现的正偶次幂和在每一点都严格为正。
-/

noncomputable def powerSum {N : ℕ} (d : ℕ) (x c : Fin N → ℝ) : ℝ[X] :=
  ∑ j, C (c j) * (X-C (x j))^d

theorem powerSum_eval {N : ℕ} (d : ℕ) (x c : Fin N → ℝ) (t : ℝ) :
    (powerSum d x c).eval t = ∑ i, c i*(t-x i)^d := by
  simp [powerSum, Polynomial.eval_finsetSum]

theorem powerSum_degree {N : ℕ} (d : ℕ) (x c : Fin N → ℝ) :
    (powerSum d x c).natDegree ≤ d := by
  unfold powerSum
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
    mul_one, zero_add, le_refl]

theorem kernel_gives_roots {N D : ℕ} (x c : Fin N → ℝ)
    (hc : (A D x).mulVec c = 0) (i : Fin N) :
    (powerSum D x c).eval (x i) = 0 := by
  have hi := congrFun hc i
  change (∑ j, (x j - x i)^D * c j) = 0 at hi
  rw [powerSum_eval]
  calc
    (∑ j, c j * (x i - x j)^D) = (-1 : ℝ)^D * (∑ j, (x j - x i)^D * c j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show x i - x j = (-1 : ℝ) * (x j - x i) by ring, mul_pow]
      ring
    _ = 0 := by rw [hi, mul_zero]

theorem kernel_support_two {N D : ℕ} (hN : 2 ≤ N) (x c : Fin N → ℝ)
    (hx : Function.Injective x) (hc0 : c ≠ 0) (hc : (A D x).mulVec c = 0) :
    ∃ i j, x i ≠ x j ∧ c i ≠ 0 ∧ c j ≠ 0 := by
  classical
  have hi0 : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  obtain ⟨i, hi⟩ := hi0
  by_contra h
  have hother : ∀ k, k ≠ i → c k = 0 := by
    intro k hk
    by_contra hck
    exact h ⟨i, k, fun he => hk (hx he).symm, hi, hck⟩
  let j : Fin N := ⟨if i.val = 0 then 1 else 0, by split_ifs <;> omega⟩
  have hji : j ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [j] at hv
    split_ifs at hv <;> omega
  have hh := congrFun hc j
  change (∑ k, (x k-x j)^D*c k) = 0 at hh
  rw [Finset.sum_eq_single i] at hh
  · exact (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr
      (fun he => hji (hx he).symm))) hi) hh
  · intro k _ hk
    rw [hother k hk, mul_zero]
  · simp

/-!
## 3. 明确根数约定，并从节点互异得到下界 N

当 p ≠ 0 且 natDegree p ≤ d 时，projectiveRoots d p 为
实根总重数 + (d - natDegree p)；第二项是齐次化后无穷远点处的重数。
nonrealDefect 是次数减去实根总重数，便于证明实射影换元不改变根数。
节点互异且全部是 p 的根，所以非零 p 的射影实根数至少为 N。
后续工作的目标是为同一个多项式证明小于 N 的上界。
-/

noncomputable def nonrealDefect (p : ℝ[X]) : ℕ := p.natDegree - p.roots.card

noncomputable def projectiveRoots (d : ℕ) (p : ℝ[X]) : ℕ :=
  p.roots.card + (d - p.natDegree)

theorem projectiveRoots_eq {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    projectiveRoots d p = d - nonrealDefect p := by
  have h := Polynomial.card_roots' p
  simp only [projectiveRoots, nonrealDefect]
  omega

noncomputable def nodeSet {N : ℕ} (x : Fin N → ℝ) : Finset ℝ := Finset.univ.image x

theorem nodeSet_card {N : ℕ} (x : Fin N → ℝ) (hx : Function.Injective x) :
    (nodeSet x).card = N := by
  simp [nodeSet, Finset.card_image_of_injective _ hx]

theorem nodeSet_le_roots {N : ℕ} (x : Fin N → ℝ) (p : ℝ[X]) (hp : p ≠ 0)
    (hr : ∀ i, p.eval (x i) = 0) : (nodeSet x).val ≤ p.roots := by
  apply Finset.val_le_iff_val_subset.mpr
  intro a ha
  change a ∈ Finset.univ.image x at ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact (Polynomial.mem_roots hp).mpr (hr i)

theorem roots_lower_bound {N d : ℕ} (x : Fin N → ℝ) (hx : Function.Injective x)
    (p : ℝ[X]) (hp : p ≠ 0) (hr : ∀ i, p.eval (x i) = 0) :
    N ≤ projectiveRoots d p := by
  have hh := Multiset.card_le_card (nodeSet_le_roots x p hp hr)
  change (nodeSet x).card ≤ p.roots.card at hh
  rw [nodeSet_card x hx] at hh
  dsimp [projectiveRoots]
  omega

/-!
## 4. 从普通 Rolle 定理到射影 Rolle 定理

先把多项式分解成全部实线性因子与无实根余因子，证明倒数换元保持
nonrealDefect；再处理反射（带次数补齐）和实平移。
chart 对应齐次坐标 (u,v) = (a s+t,s)，unchart 是其逆变换。
polar d a p 是沿 (a,1) 的齐次方向导数，以原来的仿射坐标表示。
在 chart 中应用 Mathlib 的带重数 Rolle 不等式，再换回原坐标，得到：
R_d(p) ≤ R_{d-1}(polar d a p) + 1，只要该方向导数不为零。
-/

theorem nonrealDefect_mul {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    nonrealDefect (p*q) = nonrealDefect p + nonrealDefect q := by
  have hpr := Polynomial.card_roots' p
  have hqr := Polynomial.card_roots' q
  simp only [nonrealDefect, Polynomial.natDegree_mul hp hq,
    Polynomial.roots_mul (mul_ne_zero hp hq), Multiset.card_add]
  omega

theorem nonrealDefect_zero_of_splits {p : ℝ[X]} (hp : p.Splits) :
    nonrealDefect p = 0 := by
  simp [nonrealDefect, hp.natDegree_eq_card_roots]

theorem projective_rolle_at_infinity {d : ℕ} {p : ℝ[X]}
    (hd : p.natDegree ≤ d) (hp : p.derivative ≠ 0) :
    projectiveRoots d p ≤ projectiveRoots (d-1) p.derivative + 1 := by
  have h := Polynomial.card_roots_le_derivative p
  have hpos : 0 < p.natDegree := by
    by_contra hn
    have hz : p.natDegree = 0 := by omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero hz, Polynomial.derivative_C] at hp
    exact hp rfl
  simp only [projectiveRoots, Polynomial.natDegree_derivative]
  omega

theorem reverse_root_free {p : ℝ[X]} (hp : p ≠ 0) (hr : p.roots = 0) :
    p.reverse.roots = 0 := by
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro z hz
  have hre : p.reverse ≠ 0 := fun h => hp (Polynomial.reverse_eq_zero.mp h)
  have he : p.reverse.eval z = 0 := (Polynomial.mem_roots hre).mp hz
  by_cases hz0 : z = 0
  · subst z
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse] at he
    exact hp (Polynomial.leadingCoeff_eq_zero.mp he)
  · letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
    have hh := Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id ℝ) (z⁻¹) p
    simp only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id] at hh
    have hm : z⁻¹ ∈ p.roots := (Polynomial.mem_roots hp).mpr (hh.mp he)
    simp [hr] at hm

theorem nonrealDefect_reverse_root_free {p : ℝ[X]} (hp : p ≠ 0) (hr : p.roots = 0) :
    nonrealDefect p.reverse = nonrealDefect p := by
  have h0 : p.coeff 0 ≠ 0 := by
    intro h
    have hm : (0 : ℝ) ∈ p.roots := (Polynomial.mem_roots hp).mpr (by
      change p.eval 0 = 0
      rwa [← Polynomial.coeff_zero_eq_eval_zero])
    simp [hr] at hm
  have ht : p.natTrailingDegree = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    exact Or.inr h0
  simp [nonrealDefect, reverse_root_free hp hr, hr, Polynomial.reverse_natDegree, ht]

theorem nonrealDefect_reverse (p : ℝ[X]) :
    nonrealDefect p.reverse = nonrealDefect p := by
  by_cases hp : p = 0
  · simp [hp, nonrealDefect]
  obtain ⟨q, hq, hdeg, hroots⟩ := p.exists_prod_multiset_X_sub_C_mul
  let r : ℝ[X] := (p.roots.map fun a => X - C a).prod
  have hr : r ≠ 0 := (Polynomial.monic_multisetProd_X_sub_C _).ne_zero
  have hqn : q ≠ 0 := by
    intro hz
    simp [hz] at hq
    exact hp hq.symm
  have hs : r.Splits := by
    dsimp [r]
    exact Polynomial.Splits.multisetProd (fun f hf => by
      obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hf
      exact Polynomial.Splits.X_sub_C a)
  have hsr : r.reverse.Splits := by
    dsimp [r]
    generalize p.roots = s
    induction s using Multiset.induction_on with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero]
      apply Polynomial.Splits.of_natDegree_le_one
      exact (Polynomial.reverse_natDegree_le _).trans (by simp)
    | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.reverse_mul_of_domain]
      apply Polynomial.Splits.mul _ ih
      apply Polynomial.Splits.of_natDegree_le_one
      exact (Polynomial.reverse_natDegree_le _).trans (by simp)
  change nonrealDefect p.reverse = nonrealDefect p
  have hfactor : r * q = p := hq
  rw [← hfactor, Polynomial.reverse_mul_of_domain]
  rw [nonrealDefect_mul (Polynomial.reverse_eq_zero.not.mpr hr)
      (Polynomial.reverse_eq_zero.not.mpr hqn),
    nonrealDefect_mul hr hqn, nonrealDefect_zero_of_splits hs,
    nonrealDefect_zero_of_splits hsr, nonrealDefect_reverse_root_free hqn hroots]

theorem nonrealDefect_reflect {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    nonrealDefect (p.reflect d) = nonrealDefect p := by
  by_cases hp0 : p = 0
  · simp [hp0, Polynomial.reflect_zero]
  have he : p.reflect d = p.reverse * X^(d-p.natDegree) := by
    have hh := Polynomial.reflect_mul p (1 : ℝ[X]) (le_refl p.natDegree)
      (show (1 : ℝ[X]).natDegree ≤ d-p.natDegree by simp)
    simpa [Nat.add_sub_of_le hp, Polynomial.reflect_one, Polynomial.reverse] using hh
  rw [he, nonrealDefect_mul (Polynomial.reverse_eq_zero.not.mpr hp0) (by simp),
    nonrealDefect_reverse, nonrealDefect_zero_of_splits (Polynomial.Splits.X_pow _), add_zero]

theorem translate_degree (p : ℝ[X]) (a : ℝ) :
    (p.comp (X + C a)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp]
  simp

theorem nonrealDefect_translate (p : ℝ[X]) (a : ℝ) :
    nonrealDefect (p.comp (X+C a)) = nonrealDefect p := by
  have hr := Polynomial.roots_comp_C_mul_X_add_C p (1 : ℝ) a isUnit_one
  simp only [C_1, one_mul] at hr
  simp only [nonrealDefect, translate_degree, hr, Multiset.card_map]

noncomputable def chart (d : ℕ) (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (p.comp (X+C a)).reflect d

noncomputable def unchart (d : ℕ) (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (p.reflect d).comp (X+C (-a))

theorem chart_degree {d : ℕ} (a : ℝ) {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    (chart d a p).natDegree ≤ d := by
  unfold chart
  exact (Polynomial.natDegree_reflect_le).trans (by simpa [translate_degree] using hp)

theorem unchart_degree {d : ℕ} (a : ℝ) {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    (unchart d a p).natDegree ≤ d := by
  unfold unchart
  rw [translate_degree]
  exact (Polynomial.natDegree_reflect_le).trans (max_le le_rfl hp)

theorem nonrealDefect_chart {d : ℕ} (a : ℝ) {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    nonrealDefect (chart d a p) = nonrealDefect p := by
  unfold chart
  rw [nonrealDefect_reflect (by simpa [translate_degree] using hp), nonrealDefect_translate]

theorem nonrealDefect_unchart {d : ℕ} (a : ℝ) {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    nonrealDefect (unchart d a p) = nonrealDefect p := by
  unfold unchart
  rw [nonrealDefect_translate, nonrealDefect_reflect hp]

noncomputable def polar (d : ℕ) (a : ℝ) (p : ℝ[X]) : ℝ[X] :=
  unchart (d-1) a (chart d a p).derivative

theorem projective_rolle {d : ℕ} (a : ℝ) {p : ℝ[X]}
    (hd : p.natDegree ≤ d) (hp : polar d a p ≠ 0) :
    projectiveRoots d p ≤ projectiveRoots (d-1) (polar d a p) + 1 := by
  have hchart := chart_degree a hd
  have hderiv : (chart d a p).derivative.natDegree ≤ d-1 := by
    rw [Polynomial.natDegree_derivative]
    omega
  have hdn : (chart d a p).derivative ≠ 0 := by
    intro h
    apply hp
    simp [polar, unchart, h, Polynomial.reflect_zero]
  have hr := projective_rolle_at_infinity hchart hdn
  have hu := unchart_degree a hderiv
  rw [projectiveRoots_eq hchart, nonrealDefect_chart a hd,
    projectiveRoots_eq hderiv] at hr
  rw [polar, projectiveRoots_eq hd, projectiveRoots_eq hu,
    nonrealDefect_unchart a hderiv]
  exact hr

/-!
## 5. 计算方向导数并逐次传递根数上界

关键恒等式：polar d a ((X-x)^d) = d(a-x)(X-x)^(d-1)。
因此连续选取方向 a₁,…,a_k 后，除去非零公共常数，系数变为
cᵢ ∏(aⱼ-xᵢ)，幂次变为 d-k；每次求导至多损失一个实根。
如果最终幂次为偶数、所有权重非负，且两个不同节点处的权重为正，
则最终多项式处处为正，最高次系数也为正，连无穷远处都没有根。
于是原多项式非零，且射影实根数至多为求导次数 k。
-/

theorem reflect_pow_linear (p : ℝ[X]) (hp : p.natDegree ≤ 1) (d : ℕ) :
    (p^d).reflect d = (p.reflect 1)^d := by
  induction d with
  | zero => simp [Polynomial.reflect_one]
  | succ d ih =>
    have hpd : (p^d).natDegree ≤ d := by
      rw [Polynomial.natDegree_pow]
      simpa only [mul_one] using Nat.mul_le_mul_left d hp
    rw [pow_succ, Polynomial.reflect_mul (F := d) (G := 1) (p^d) p hpd hp]
    rw [ih, pow_succ]

theorem reflect_X_add_C (b : ℝ) :
    (X+C b : ℝ[X]).reflect 1 = 1 + C b * X := by
  simp [Polynomial.reflect_add]

theorem reflect_one_add_C_mul_X (b : ℝ) :
    (1+C b*X : ℝ[X]).reflect 1 = X+C b := by
  have h := congrArg (Polynomial.reflect 1) (reflect_X_add_C b)
  simpa only [Polynomial.reflect_reflect] using h.symm

theorem polar_add (d : ℕ) (a : ℝ) (p q : ℝ[X]) :
    polar d a (p+q) = polar d a p + polar d a q := by
  simp only [polar, chart, unchart, Polynomial.add_comp, Polynomial.reflect_add,
    Polynomial.derivative_add]

theorem polar_C_mul (d : ℕ) (a b : ℝ) (p : ℝ[X]) :
    polar d a (C b * p) = C b * polar d a p := by
  simp only [polar, chart, unchart, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.reflect_C_mul, Polynomial.derivative_C_mul]

theorem polar_zero (d : ℕ) (a : ℝ) : polar d a 0 = 0 := by
  simp [polar, chart, unchart, Polynomial.reflect_zero]

theorem polar_sum {ι : Type*} (s : Finset ι) (d : ℕ) (a : ℝ) (p : ι → ℝ[X]) :
    polar d a (∑ i ∈ s, p i) = ∑ i ∈ s, polar d a (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polar_zero]
  | @insert i s hi ih => simp [Finset.sum_insert hi, polar_add, ih]

theorem polar_power (d : ℕ) (a x : ℝ) :
    polar d a ((X-C x)^d) = C ((d : ℝ)*(a-x)) * (X-C x)^(d-1) := by
  have hlin : (X+C (a-x) : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hlin' : (1+C (a-x)*X : ℝ[X]).natDegree ≤ 1 := by
    compute_degree
  have hcomp : ((X-C x : ℝ[X])^d).comp (X+C a) = (X+C (a-x))^d := by
    simp only [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    congr 1
    simp only [map_sub]
    ring
  unfold polar chart unchart
  rw [hcomp, reflect_pow_linear _ hlin d, reflect_X_add_C]
  rw [Polynomial.derivative_pow]
  have hdr : (1+C (a-x)*X : ℝ[X]).derivative = C (a-x) := by simp
  rw [hdr]
  have hprod : (C (d : ℝ) * (1+C (a-x)*X)^(d-1) * C (a-x)) =
      C ((d : ℝ)*(a-x)) * (1+C (a-x)*X)^(d-1) := by
    simp only [map_mul]
    ring
  rw [hprod, Polynomial.reflect_C_mul, reflect_pow_linear _ hlin' (d-1),
    reflect_one_add_C_mul_X]
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
    Polynomial.add_comp, Polynomial.X_comp]
  congr 2
  simp only [map_sub, map_neg]
  ring

theorem polar_powerSum {N : ℕ} (d : ℕ) (a : ℝ) (x c : Fin N → ℝ) :
    polar d a (powerSum d x c) =
      C (d : ℝ) * powerSum (d-1) x (fun i => c i*(a-x i)) := by
  unfold powerSum
  rw [polar_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [polar_C_mul, polar_power]
  simp only [map_mul]
  ring

theorem projectiveRoots_C_mul {d : ℕ} {a : ℝ} (ha : a ≠ 0) (p : ℝ[X]) :
    projectiveRoots d (C a*p) = projectiveRoots d p := by
  simp only [projectiveRoots, Polynomial.roots_C_mul p ha,
    Polynomial.natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr ha)]

def weightsAfter {N : ℕ} (as : List ℝ) (x c : Fin N → ℝ) : Fin N → ℝ :=
  fun i => c i * (as.map (fun a => a-x i)).prod

theorem iterated_root_bound {N d : ℕ} (as : List ℝ) (x c : Fin N → ℝ)
    (hlen : as.length ≤ d)
    (hn : powerSum (d-as.length) x (weightsAfter as x c) ≠ 0) :
    powerSum d x c ≠ 0 ∧
      projectiveRoots d (powerSum d x c) ≤
        projectiveRoots (d-as.length) (powerSum (d-as.length) x (weightsAfter as x c)) + as.length := by
  induction as generalizing d c with
  | nil =>
    have hw : weightsAfter [] x c = c := by funext i; simp [weightsAfter]
    simp only [hw, List.length_nil, Nat.sub_zero, add_zero] at hn ⊢
    exact ⟨hn, le_rfl⟩
  | cons a as ih =>
    have hd : 0 < d := by simp only [List.length_cons] at hlen; omega
    have hsmall : as.length ≤ d-1 := by simp only [List.length_cons] at hlen; omega
    have hdeg : d-1-as.length = d-(a::as).length := by simp; omega
    have hw : weightsAfter as x (fun i => c i*(a-x i)) = weightsAfter (a::as) x c := by
      funext i
      simp [weightsAfter, mul_assoc]
    have hmid := ih (c := fun i => c i*(a-x i)) hsmall (by simpa [hdeg, hw] using hn)
    have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    have hpn : polar d a (powerSum d x c) ≠ 0 := by
      rw [polar_powerSum]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr hdn) hmid.1
    have horig : powerSum d x c ≠ 0 := by
      intro h
      exact hpn (by rw [h, polar_zero])
    have hr := projective_rolle a (powerSum_degree d x c) hpn
    rw [polar_powerSum, projectiveRoots_C_mul hdn] at hr
    constructor
    · exact horig
    · have hm := hmid.2
      rw [hdeg, hw] at hm
      simp only [List.length_cons] at hm ⊢
      omega

theorem powerSum_top_coeff {N : ℕ} (d : ℕ) (x c : Fin N → ℝ) :
    (powerSum d x c).coeff d = ∑ i, c i := by
  simp only [powerSum, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hm := (Polynomial.monic_X_sub_C (x i)).pow d
  have hd : ((X-C (x i) : ℝ[X])^d).natDegree = d := by
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hh : ((X-C (x i) : ℝ[X])^d).coeff d = 1 := by
    have hh' : ((X-C (x i) : ℝ[X])^d).coeff (((X-C (x i) : ℝ[X])^d).natDegree) = 1 := hm
    simpa only [hd] using hh'
  rw [hh, mul_one]

theorem positive_powerSum {N d : ℕ} (x c : Fin N → ℝ) (he : Even d)
    (hc : ∀ i, 0 ≤ c i)
    (hij : ∃ i j, x i ≠ x j ∧ 0 < c i ∧ 0 < c j) :
    powerSum d x c ≠ 0 ∧ projectiveRoots d (powerSum d x c) = 0 := by
  obtain ⟨i, j, hx, hi, hj⟩ := hij
  have hpos : ∀ t : ℝ, 0 < (powerSum d x c).eval t := by
    intro t
    rw [powerSum_eval]
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (hc k) (he.pow_nonneg (t-x k))
    · by_cases hti : t = x i
      · have hne : t-x j ≠ 0 := by rw [hti]; exact sub_ne_zero.mpr hx
        exact ⟨j, Finset.mem_univ _, mul_pos hj
          (lt_of_le_of_ne (he.pow_nonneg _) (Ne.symm (pow_ne_zero d hne)))⟩
      · exact ⟨i, Finset.mem_univ _, mul_pos hi
          (lt_of_le_of_ne (he.pow_nonneg _) (Ne.symm (pow_ne_zero d (sub_ne_zero.mpr hti))))⟩
  have hn : powerSum d x c ≠ 0 := by
    intro hz
    have hh := hpos 0
    rw [hz, Polynomial.eval_zero] at hh
    exact (lt_irrefl 0) hh
  have hsum : 0 < ∑ k, c k := Finset.sum_pos' (fun k _ => hc k) ⟨i, Finset.mem_univ _, hi⟩
  have hd : (powerSum d x c).natDegree = d := by
    apply le_antisymm (powerSum_degree d x c)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [powerSum_top_coeff]
    exact ne_of_gt hsum
  have hr : (powerSum d x c).roots = 0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro t ht
    exact ne_of_gt (hpos t) ((Polynomial.mem_roots hn).mp ht)
  exact ⟨hn, by simp [projectiveRoots, hr, hd]⟩

theorem root_bound_of_positive_weights {N d : ℕ} (as : List ℝ) (x c : Fin N → ℝ)
    (hlen : as.length ≤ d) (he : Even (d-as.length))
    (hc : ∀ i, 0 ≤ weightsAfter as x c i)
    (hij : ∃ i j, x i ≠ x j ∧ 0 < weightsAfter as x c i ∧
      0 < weightsAfter as x c j) :
    powerSum d x c ≠ 0 ∧ projectiveRoots d (powerSum d x c) ≤ as.length := by
  have hf := positive_powerSum x (weightsAfter as x c) he hc hij
  have hb := iterated_root_bound as x c hlen hf.1
  exact ⟨hb.1, by simpa [hf.2] using hb.2⟩

theorem powerSum_scale {N : ℕ} (d : ℕ) (x c : Fin N → ℝ) (s : ℝ) :
    powerSum d x (fun i => s*c i) = C s * powerSum d x c := by
  simp only [powerSum, map_mul, Finset.mul_sum, mul_assoc]

theorem root_bound_of_signed_weights {N d : ℕ} (as : List ℝ) (x c : Fin N → ℝ)
    (hlen : as.length ≤ d) (he : Even (d-as.length)) (s : ℝ) (hs : s ≠ 0)
    (hc : ∀ i, 0 ≤ s*weightsAfter as x c i)
    (hij : ∃ i j, x i ≠ x j ∧ 0 < s*weightsAfter as x c i ∧
      0 < s*weightsAfter as x c j) :
    powerSum d x c ≠ 0 ∧ projectiveRoots d (powerSum d x c) ≤ as.length := by
  have hw : ∀ i, weightsAfter as x (fun i => s*c i) i = s*weightsAfter as x c i := by
    intro i
    simp [weightsAfter, mul_assoc]
  have hb := root_bound_of_positive_weights as x (fun i => s*c i) hlen he
    (fun i => by rw [hw]; exact hc i) (by simpa only [hw] using hij)
  rw [powerSum_scale, projectiveRoots_C_mul hs] at hb
  refine ⟨?_, hb.2⟩
  intro h
  exact hb.1 (by rw [h, mul_zero])

/-!
## 6. 将“同号辅助多项式”转成根数上界

这是充分性部分的核心引理 root_bound_of_sign_polynomial：
若 deg g ≤ m ≤ d、d-m 为偶数，且 cᵢ ≠ 0 时 cᵢ g(xᵢ) > 0，
并且至少两个不同节点处 cᵢ ≠ 0，则 f ≠ 0 且 R_d(f) ≤ m。

证明：取 g 的所有实根（含重数）作为方向。没有实根的余因子在整个
实轴上同号，所以这些求导方向使权重在一次整体缩放后全为非负。
若剩余幂次的奇偶性不对，补一个大于所有节点的方向；由 d-m 为偶数
可知此时仍有一个次数名额。接着应用第 5 步的结论。
-/

theorem root_free_same_sign {q : ℝ[X]} (hq : q ≠ 0) (hr : q.roots = 0) (a b : ℝ) :
    0 < q.eval a * q.eval b := by
  have hn : ∀ t, q.eval t ≠ 0 := by
    intro t ht
    have hh := (Polynomial.mem_roots hq).mpr ht
    simp [hr] at hh
  rcases lt_or_gt_of_ne (hn a) with ha | ha <;>
    rcases lt_or_gt_of_ne (hn b) with hb | hb
  · exact mul_pos_of_neg_of_neg ha hb
  · obtain ⟨t, ht⟩ := intermediate_value_univ a b q.continuous ⟨ha.le, hb.le⟩
    exact (hn t ht).elim
  · obtain ⟨t, ht⟩ := intermediate_value_univ b a q.continuous ⟨hb.le, ha.le⟩
    exact (hn t ht).elim
  · exact mul_pos ha hb

theorem prod_sub_swap (as : List ℝ) (t : ℝ) :
    (as.map (fun a => a-t)).prod = (-1 : ℝ)^as.length * (as.map (fun a => t-a)).prod := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ih]; ring

theorem root_bound_of_sign_polynomial {N d m : ℕ} (x c : Fin N → ℝ)
    (hm : m ≤ d) (hpar : Even (d-m)) (g : ℝ[X]) (hg : g.natDegree ≤ m)
    (halign : ∀ i, c i ≠ 0 → 0 < c i*g.eval (x i))
    (hsupp : ∃ i j, x i ≠ x j ∧ c i ≠ 0 ∧ c j ≠ 0) :
    powerSum d x c ≠ 0 ∧ projectiveRoots d (powerSum d x c) ≤ m := by
  classical
  obtain ⟨i, j, hxij, hci, hcj⟩ := hsupp
  have hgn : g ≠ 0 := by
    intro h
    have hh := halign i hci
    simp [h] at hh
  obtain ⟨q, hfactor, hdeg, hqr⟩ := g.exists_prod_multiset_X_sub_C_mul
  have hqn : q ≠ 0 := by
    intro h
    simp [h] at hfactor
    exact hgn hfactor.symm
  let as := g.roots.toList
  have hlen : as.length ≤ m := by
    have hcr := Polynomial.card_roots' g
    simp only [as, Multiset.length_toList]
    omega
  let s : ℝ := (-1 : ℝ)^as.length * q.eval 0
  have hq0 : q.eval 0 ≠ 0 := by
    have hh := root_free_same_sign hqn hqr 0 0
    intro hz
    simp [hz] at hh
  have hsn : s ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hq0
  have hnonzero : ∀ k, c k ≠ 0 → 0 < s*weightsAfter as x c k := by
    intro k hck
    have hqk := root_free_same_sign hqn hqr 0 (x k)
    have hcg := halign k hck
    have hf : (as.map (fun a => x k-a)).prod * q.eval (x k) = g.eval (x k) := by
      simpa [as, Polynomial.eval_multiset_prod, Polynomial.eval_mul] using
        congrArg (Polynomial.eval (x k)) hfactor
    have hsquare : ((-1 : ℝ)^as.length)^2 = 1 := by
      rw [← pow_mul, mul_comm as.length 2, pow_mul]
      norm_num
    have heq : (s*weightsAfter as x c k)*(q.eval (x k))^2 =
        (q.eval 0*q.eval (x k))*(c k*g.eval (x k)) := by
      dsimp [s, weightsAfter]
      rw [prod_sub_swap, ← hf]
      calc
        _ = ((-1 : ℝ)^as.length)^2 *
          ((q.eval 0*q.eval (x k))*(c k*((as.map (fun a => x k-a)).prod*q.eval (x k)))) := by ring
        _ = _ := by rw [hsquare, one_mul]
    have hh : 0 < (s*weightsAfter as x c k)*(q.eval (x k))^2 := by
      rw [heq]
      exact mul_pos hqk hcg
    exact pos_of_mul_pos_left hh (sq_nonneg _)
  have hnonneg : ∀ k, 0 ≤ s*weightsAfter as x c k := by
    intro k
    by_cases hc : c k = 0
    · simp [weightsAfter, hc]
    · exact (hnonzero k hc).le
  by_cases he : Even (d-as.length)
  · have hb := root_bound_of_signed_weights as x c (hlen.trans hm) he s hsn hnonneg
      ⟨i, j, hxij, hnonzero i hci, hnonzero j hcj⟩
    exact ⟨hb.1, hb.2.trans hlen⟩
  · have hlt : as.length < m := by
      by_contra hh
      have heq : as.length = m := by omega
      exact he (by simpa [heq] using hpar)
    obtain ⟨a, ha⟩ := (Set.finite_range x).bddAbove
    have hap : ∀ k, 0 < (a+1)-x k := by
      intro k
      have hh := ha (Set.mem_range_self k)
      linarith
    have hw : ∀ k, s*weightsAfter ((a+1)::as) x c k =
        (s*weightsAfter as x c k)*((a+1)-x k) := by
      intro k
      simp only [weightsAfter, List.map_cons, List.prod_cons]
      ring
    have hp : Even (d-((a+1)::as).length) := by
      obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp he
      refine ⟨r, ?_⟩
      simp only [List.length_cons]
      omega
    have hb := root_bound_of_signed_weights ((a+1)::as) x c
      (by simp only [List.length_cons]; omega) hp s hsn
      (fun k => by rw [hw]; exact mul_nonneg (hnonneg k) (hap k).le)
      ⟨i, j, hxij, by rw [hw]; exact mul_pos (hnonzero i hci) (hap i),
        by rw [hw]; exact mul_pos (hnonzero j hcj) (hap j)⟩
    exact ⟨hb.1, hb.2.trans (by simp only [List.length_cons]; omega)⟩

/-!
## 7. 普通插值解决 N、D 奇偶性相反的情形

令 g 是满足 g(xᵢ)=cᵢ 的 Lagrange 插值多项式；deg g ≤ N-1，
而非零 cᵢ 处 cᵢ g(xᵢ)=cᵢ² > 0。
如果 D-(N-1) 为偶数，第 6 步给出 R_D(f) ≤ N-1；
第 2、3 步给出 R_D(f) ≥ N。矛盾，因此核向量只能为零。
-/

noncomputable def interpolate {N : ℕ} (x c : Fin N → ℝ) : ℝ[X] :=
  Lagrange.interpolate Finset.univ x c

theorem interpolate_degree {N : ℕ} (x c : Fin N → ℝ) (hx : Function.Injective x) :
    (interpolate x c).natDegree ≤ N-1 := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa only [interpolate, Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_le (s := Finset.univ) c hx.injOn

theorem interpolate_eval {N : ℕ} (x c : Fin N → ℝ) (hx : Function.Injective x) (i : Fin N) :
    (interpolate x c).eval (x i) = c i :=
  Lagrange.eval_interpolate_at_node c hx.injOn (Finset.mem_univ i)

theorem kernel_root_bound {N D m : ℕ} (hN : 2 ≤ N) (x c : Fin N → ℝ)
    (hx : Function.Injective x) (hc0 : c ≠ 0) (hc : (A D x).mulVec c = 0)
    (hm : m ≤ D) (hNm : N-1 ≤ m) (hpar : Even (D-m)) :
    powerSum D x c ≠ 0 ∧ projectiveRoots D (powerSum D x c) ≤ m := by
  apply root_bound_of_sign_polynomial x c hm hpar (interpolate x c)
    ((interpolate_degree x c hx).trans hNm)
  · intro i hi
    rw [interpolate_eval x c hx]
    exact mul_self_pos.mpr hi
  · exact kernel_support_two hN x c hx hc0 hc

theorem kernel_zero_of_opposite_parity {N D : ℕ} (hN : 2 ≤ N) (hND : N ≤ D+1)
    (hpar : Even (D-(N-1))) (x c : Fin N → ℝ) (hx : Function.Injective x)
    (hc : (A D x).mulVec c = 0) : c = 0 := by
  by_contra hc0
  have hb := kernel_root_bound hN x c hx hc0 hc (m := N-1) (by omega) le_rfl hpar
  have hr := roots_lower_bound (d := D) x hx (powerSum D x c) hb.1
    (fun i => kernel_gives_roots x c hc i)
  omega

/-!
## 8. N、D 均偶时，用反对称恒等式再降低插值次数

D 为正偶数时，D-1 为奇数；交换双重求和的指标便得到
Σᵢ cᵢ f'(xᵢ)=D Σᵢⱼ cᵢcⱼ(xᵢ-xⱼ)^(D-1)=0。
先用 m=N 的根数上界确定 f 的全部实根恰好是各节点，且都是单根。
再由上述恒等式构造次数至多 N-2 的同号辅助多项式；
第 6 步的上界与第 3 步的下界再次矛盾。下方在各个转折处展开说明。
-/

theorem skew_sum_zero {N k : ℕ} (x c : Fin N → ℝ) (hk : Odd k) :
    (∑ i, ∑ j, c i * c j * (x i - x j)^k) = 0 := by
  let s : ℝ := ∑ i, ∑ j, c i * c j * (x i - x j)^k
  have hs : s = -s := by
    dsimp [s]
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show x j - x i = -(x i - x j) by ring, hk.neg_pow]
    ring
  dsimp [s] at hs
  linarith

theorem derivative_pairing_zero {N D : ℕ} (hD : 0 < D) (he : Even D)
    (x c : Fin N → ℝ) :
    (∑ i, c i * (powerSum D x c).derivative.eval (x i)) = 0 := by
  have ho : Odd (D - 1) := by
    obtain ⟨k, hk⟩ := he
    exact ⟨k - 1, by omega⟩
  have hz := skew_sum_zero x c ho
  simp only [powerSum, Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_pow,
    Polynomial.derivative_sub, Polynomial.derivative_X, sub_zero,
    mul_one, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]
  calc
    (∑ i, c i * ∑ j, c j * ((D : ℝ) * (x i - x j)^(D-1))) =
        (D : ℝ) * ∑ i, ∑ j, c i * c j * (x i - x j)^(D-1) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hz, mul_zero]

theorem kernel_zero_of_even_even {N D : ℕ} (hN : 2 ≤ N) (hND : N ≤ D)
    (heD : Even D) (heN : Even N) (x c : Fin N → ℝ) (hx : Function.Injective x)
    (hc : (A D x).mulVec c = 0) : c = 0 := by
  classical
  by_contra hc0
  have hpar : Even (D-N) := by
    obtain ⟨a, ha⟩ := heD
    obtain ⟨b, hb⟩ := heN
    exact ⟨a-b, by omega⟩
  -- 先用 m=N 得到至多 N 个根；全部 N 个节点是根，故恰好各为单根。
  have hb := kernel_root_bound hN x c hx hc0 hc hND (by omega) hpar
  let f := powerSum D x c
  have hfn : f ≠ 0 := hb.1
  have hfr : ∀ i, f.eval (x i) = 0 := fun i => kernel_gives_roots x c hc i
  have hnodes : (nodeSet x).val = f.roots := by
    apply Multiset.eq_of_le_of_card_le (nodeSet_le_roots x f hfn hfr)
    change f.roots.card ≤ (nodeSet x).card
    rw [nodeSet_card x hx]
    have hh := hb.2
    dsimp [projectiveRoots] at hh
    change (powerSum D x c).roots.card ≤ N
    omega
  -- 于是 f=P*q，P=∏(X-xᵢ)，而 q 没有实根。
  let P := Lagrange.nodal Finset.univ x
  have hprod : (f.roots.map fun a => X-C a).prod = P := by
    rw [← hnodes]
    change (∏ a ∈ Finset.univ.image x, (X-C a)) = ∏ i : Fin N, (X-C (x i))
    rw [Finset.prod_image]
    intro i _ j _ hij
    exact hx hij
  obtain ⟨q, hfactor, _, hqr⟩ := f.exists_prod_multiset_X_sub_C_mul
  rw [hprod] at hfactor
  have hqn : q ≠ 0 := by
    intro hq
    simp [hq] at hfactor
    exact hfn hfactor.symm
  -- wᵢ=P'(xᵢ)≠0，且 f'(xᵢ)=wᵢ*q(xᵢ)。
  let w : Fin N → ℝ := fun i => ∏ j ∈ Finset.univ.erase i, (x i-x j)
  have hwn : ∀ i, w i ≠ 0 := by
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (fun hij => (Finset.mem_erase.mp hj).1 (hx hij).symm)
  have hder : ∀ i, f.derivative.eval (x i) = w i*q.eval (x i) := by
    intro i
    rw [← hfactor, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul]
    have hpzero : P.eval (x i) = 0 := Lagrange.eval_nodal_at_node (Finset.mem_univ i)
    have hpder : P.derivative.eval (x i) = w i := by
      rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]
    rw [hpzero, hpder]
    ring
  -- 插值 g(xᵢ)=cᵢ*f'(xᵢ)*wᵢ；其 N-1 次系数为 Σ cᵢ*f'(xᵢ)=0。
  let r : Fin N → ℝ := fun i => c i*f.derivative.eval (x i)*w i
  let g := interpolate x r
  have hgdeg : g.natDegree ≤ N-1 := interpolate_degree x r hx
  have hgcoeff : g.coeff (N-1) = 0 := by
    have hh := Lagrange.coeff_eq_sum hx.injOn (P := g)
      (Lagrange.degree_interpolate_lt r hx.injOn)
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    rw [hh]
    have hsum : (∑ i, c i*f.derivative.eval (x i)) = 0 :=
      derivative_pairing_zero (by omega) heD x c
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro i _
    change g.eval (x i) / w i = c i*f.derivative.eval (x i)
    rw [interpolate_eval x r hx]
    dsimp [r]
    exact mul_div_cancel_right₀ _ (hwn i)
  -- 因而 deg g≤N-2，而非通常的 N-1。
  have hgsmall : g.natDegree ≤ N-2 := by
    by_cases hg0 : g = 0
    · simp [hg0]
    · have hlead : g.coeff g.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
      by_contra hlt
      have heq : g.natDegree = N-1 := by omega
      rw [heq, hgcoeff] at hlead
      exact hlead rfl
  -- 乘以 q(0) 后与 c 同号：cᵢ*g'(xᵢ)=q(0)q(xᵢ)(cᵢ*wᵢ)²>0。
  let g' : ℝ[X] := C (q.eval 0)*g
  have hg'deg : g'.natDegree ≤ N-2 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans hgsmall
  have halign : ∀ i, c i ≠ 0 → 0 < c i*g'.eval (x i) := by
    intro i hi
    have hqpos := root_free_same_sign hqn hqr 0 (x i)
    have hwpos : 0 < (c i*w i)^2 := sq_pos_of_ne_zero (mul_ne_zero hi (hwn i))
    calc
      c i*g'.eval (x i) = (q.eval 0*q.eval (x i))*(c i*w i)^2 := by
        dsimp [g']
        rw [Polynomial.eval_mul, Polynomial.eval_C, interpolate_eval x r hx]
        dsimp [r]
        rw [hder]
        ring
      _ > 0 := mul_pos hqpos hwpos
  have hpar' : Even (D-(N-2)) := by
    obtain ⟨a, ha⟩ := heD
    obtain ⟨b, hb⟩ := heN
    exact ⟨a-b+1, by omega⟩
  -- 第 6 步现给出至多 N-2 个根，与至少 N 个根矛盾。
  have hfinal := root_bound_of_sign_polynomial x c (m := N-2) (by omega) hpar' g'
    hg'deg halign (kernel_support_two hN x c hx hc0 hc)
  have hlower := roots_lower_bound (d := D) x hx f hfn hfr
  change N ≤ projectiveRoots D (powerSum D x c) at hlower
  omega

/-!
## 9. 回到原题，合并为充要条件

左向右直接使用第 1 步。右向左按 N、D 的奇偶性分类：
同时为偶数用第 8 步；奇偶性相反用第 7 步；同时为奇数被假设排除。
所有许可情形的核都为零，故矩阵可逆、行列式非零。

最终定理显式写出原题的矩阵及全部假设。它没有把根数上界或任何
充分性结论额外当作假设：这些内容都已在本文件中逐一证明。
-/

theorem determinant_ne_zero_iff {N D : ℕ} (hN : 2 ≤ N) (_hD : 1 ≤ D)
    (x : Fin N → ℝ) (hx : Function.Injective x) :
    (Matrix.det (fun i j : Fin N => (x j - x i)^D)) ≠ 0 ↔
      N ≤ D+1 ∧ (Even D ∨ Even N) := by
  change (A D x).det ≠ 0 ↔ N ≤ D+1 ∧ (Even D ∨ Even N)
  constructor
  · exact necessary x
  · rintro ⟨hND, he⟩
    have hker : ∀ c : Fin N → ℝ, (A D x).mulVec c = 0 → c = 0 := by
      intro c hc
      rcases Nat.even_or_odd D with hd | hd <;> rcases Nat.even_or_odd N with hn | hn
      · apply kernel_zero_of_even_even hN (by
          obtain ⟨a, ha⟩ := hd
          obtain ⟨b, hb⟩ := hn
          omega) hd hn x c hx hc
      · apply kernel_zero_of_opposite_parity hN hND _ x c hx hc
        obtain ⟨a, ha⟩ := hd
        obtain ⟨b, hb⟩ := hn
        exact ⟨a-b, by omega⟩
      · apply kernel_zero_of_opposite_parity hN hND _ x c hx hc
        obtain ⟨a, ha⟩ := hd
        obtain ⟨b, hb⟩ := hn
        exact ⟨a+1-b, by omega⟩
      · rcases he with he | he
        · obtain ⟨a, ha⟩ := hd
          obtain ⟨b, hb⟩ := he
          omega
        · obtain ⟨a, ha⟩ := hn
          obtain ⟨b, hb⟩ := he
          omega
    have hinj : Function.Injective (A D x).mulVec := by
      intro a b hab
      apply sub_eq_zero.mp
      apply hker
      rw [Matrix.mulVec_sub, hab, sub_self]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hinj))

-- Lean 检查最终命题，并打印其传递依赖的公理。
#check determinant_ne_zero_iff
#print axioms determinant_ne_zero_iff

end DifferencePowerSingle

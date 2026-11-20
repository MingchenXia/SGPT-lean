import SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMap
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

/-!
# Products in `C^{k,r}_b(E, F)`

For `r ≤ 1`, every derivative `Dʲ f` (`j ≤ k`) of `f ∈ C^{k,r}_b(E, F)` is `r`-Hölder with
constant `2 ‖f‖` (`holderWith_iteratedFDeriv`: the lower derivatives are bounded and Lipschitz).
Consequently, for a continuous bilinear map `B : F₁ →L F₂ →L G`, the map `x ↦ B (f x) (g x)` lies
in `C^{k,r}_b(E, G)` with

`‖B (f, g)‖ ≤ 2 ^ (k + 3) ‖B‖ ‖f‖ ‖g‖`  (`norm_bilinear_le`).

This covers products of functions (`B` = multiplication) and multiplication of a vector-valued map
by a scalar function (`B` = scalar multiplication), e.g. by cut-off functions or by the
coefficients of a differential operator.

The Hölder estimate of `Dᵏ (B (f, g))` avoids the explicit Leibniz formula: with
`τ_v z = z + v`,
`Dᵏ h (x + v) - Dᵏ h x = Dᵏ (h ∘ τ_v - h) x` and
`h ∘ τ_v - h = B (f ∘ τ_v - f, g ∘ τ_v) + B (f, g ∘ τ_v - g)`,
so the Leibniz *bound* `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear` applied to the
two terms, together with `‖Dʲ f (x + v) - Dʲ f x‖ ≤ 2 ‖f‖ ‖v‖ ^ r`, gives the estimate
(Gilbarg--Trudinger, (4.7) for `k = 0`).

Part of the linear track `L1` of the plan for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMap

variable {k : ℕ} {r : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For `r ≤ 1` every derivative `Dʲ f`, `j ≤ k`, of `f ∈ C^{k,r}_b` is `(2 ‖f‖, r)`-Hölder:
the top derivative by definition, the lower ones because they are bounded by `‖f‖` and
`‖f‖`-Lipschitz. -/
theorem holderWith_iteratedFDeriv (hr : r ≤ 1) (f : BoundedContDiffHolderMap k r E F) {j : ℕ}
    (hj : j ≤ k) : HolderWith (2 * ‖f‖₊) r (iteratedFDeriv ℝ j f) := by
  rcases hj.lt_or_eq with hjk | rfl
  · refine HolderWith.of_dist_le fun x y => ?_
    have hf0 : 0 ≤ ‖f‖ := norm_nonneg f
    have h1 : dist (iteratedFDeriv ℝ j f x) (iteratedFDeriv ℝ j f y) ≤ 2 * ‖f‖ := by
      rw [dist_eq_norm]
      refine (norm_sub_le _ _).trans ?_
      linarith [f.norm_iteratedFDeriv_apply_le hjk.le x, f.norm_iteratedFDeriv_apply_le hjk.le y]
    have h2 : dist (iteratedFDeriv ℝ j f x) (iteratedFDeriv ℝ j f y) ≤ ‖f‖ * dist x y := by
      rw [dist_eq_norm, dist_eq_norm, ← norm_neg, neg_sub, ← norm_neg (x - y), neg_sub]
      refine Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ)
        (fun z _ => (f.contDiff.differentiable_iteratedFDeriv (by exact_mod_cast hjk) z))
        (fun z _ => ?_) convex_univ (mem_univ _) (mem_univ _)
      rw [norm_fderiv_iteratedFDeriv]
      exact f.norm_iteratedFDeriv_apply_le hjk z
    push_cast
    have hd := dist_nonneg (x := x) (y := y)
    rcases le_total (dist x y) 1 with hd1 | hd1
    · calc _ ≤ ‖f‖ * dist x y := h2
        _ ≤ ‖f‖ * dist x y ^ (r : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hd hd1 (by exact_mod_cast hr))
            hf0
        _ ≤ 2 * ‖f‖ * dist x y ^ (r : ℝ) := by
          have := Real.rpow_nonneg hd (r : ℝ)
          nlinarith
    · calc _ ≤ 2 * ‖f‖ := h1
        _ ≤ 2 * ‖f‖ * dist x y ^ (r : ℝ) :=
          le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hd1 r.coe_nonneg)
  · have h := f.iteratedFDerivHolder.holderWith
    rw [coe_iteratedFDerivHolder] at h
    refine h.mono ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    have h1 := f.iteratedFDerivHolder.nnHolderNorm_le_norm
    rw [coe_iteratedFDerivHolder] at h1
    linarith [f.norm_iteratedFDerivHolder_le, norm_nonneg f]

/-- `‖Dʲ f (x + v) - Dʲ f x‖ ≤ 2 ‖f‖ ‖v‖ ^ r` for `j ≤ k` and `r ≤ 1`. -/
theorem norm_iteratedFDeriv_add_sub_le (hr : r ≤ 1) (f : BoundedContDiffHolderMap k r E F)
    {j : ℕ} (hj : j ≤ k) (x v : E) :
    ‖iteratedFDeriv ℝ j f (x + v) - iteratedFDeriv ℝ j f x‖ ≤ 2 * ‖f‖ * ‖v‖ ^ (r : ℝ) := by
  have h := (f.holderWith_iteratedFDeriv hr hj).dist_le (x + v) x
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h
  simpa using h

variable {F₁ F₂ G : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂]
  [NormedSpace ℝ F₂] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The Leibniz bound `‖Dⁱ (B (a, b)) x‖ ≤ ‖B‖ ∑ⱼ (i choose j) ‖Dʲ a x‖ ‖Dⁱ⁻ʲ b x‖` with all
derivatives bounded by `A` and `A'`. -/
private theorem norm_iteratedFDeriv_bilinear_le (B : F₁ →L[ℝ] F₂ →L[ℝ] G) {a : E → F₁}
    {b : E → F₂} {i : ℕ} (ha : ContDiff ℝ i a) (hb : ContDiff ℝ i b) (x : E) {A A' : ℝ}
    (hA : ∀ j ≤ i, ‖iteratedFDeriv ℝ j a x‖ ≤ A) (hA' : ∀ j ≤ i, ‖iteratedFDeriv ℝ j b x‖ ≤ A') :
    ‖iteratedFDeriv ℝ i (fun y => B (a y) (b y)) x‖ ≤ ‖B‖ * 2 ^ i * A * A' := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le i))
  refine (B.norm_iteratedFDeriv_le_of_bilinear ha hb x le_rfl).trans ?_
  have hsum : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j a x‖ *
      ‖iteratedFDeriv ℝ (i - j) b x‖ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * A * A' := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    gcongr
    · exact hA j hj'
    · exact hA' (i - j) (Nat.sub_le i j)
  have hcs : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * A * A' = 2 ^ i * A * A' := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    congr 2
    exact_mod_cast Nat.sum_range_choose i
  rw [show ‖B‖ * 2 ^ i * A * A' = ‖B‖ * (2 ^ i * A * A') by ring, ← hcs]
  exact mul_le_mul_of_nonneg_left hsum (norm_nonneg B)

/-- Leibniz bound for `x ↦ B (f x) (g x)`: `‖Dⁱ (B (f, g)) x‖ ≤ ‖B‖ 2ⁱ ‖f‖ ‖g‖` for `i ≤ k`. -/
theorem norm_iteratedFDeriv_bilinear_apply_le (B : F₁ →L[ℝ] F₂ →L[ℝ] G)
    (f : BoundedContDiffHolderMap k r E F₁) (g : BoundedContDiffHolderMap k r E F₂) {i : ℕ}
    (hi : i ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * 2 ^ i * ‖f‖ * ‖g‖ :=
  norm_iteratedFDeriv_bilinear_le B (f.contDiff.of_le (by exact_mod_cast hi))
    (g.contDiff.of_le (by exact_mod_cast hi)) x
    (fun j hj => f.norm_iteratedFDeriv_apply_le (hj.trans hi) x)
    (fun j hj => g.norm_iteratedFDeriv_apply_le (hj.trans hi) x)

/-- Hölder estimate for `x ↦ B (f x) (g x)`, `r ≤ 1`:
`[Dᵏ (B (f, g))]_r ≤ 2 ^ (k + 2) ‖B‖ ‖f‖ ‖g‖`. -/
theorem holderWith_iteratedFDeriv_bilinear (hr : r ≤ 1) (B : F₁ →L[ℝ] F₂ →L[ℝ] G)
    (f : BoundedContDiffHolderMap k r E F₁) (g : BoundedContDiffHolderMap k r E F₂) :
    HolderWith (‖B‖₊ * 2 ^ (k + 2) * ‖f‖₊ * ‖g‖₊) r
      (iteratedFDeriv ℝ k fun y => B (f y) (g y)) := by
  refine HolderWith.of_dist_le fun x y => ?_
  set h : E → G := fun z => B (f z) (g z) with hh
  have hcd : ContDiff ℝ k h := (B.contDiff.comp f.contDiff).clm_apply g.contDiff
  set v := y - x with hv
  have hy : y = x + v := by rw [hv, add_sub_cancel]
  -- `h ∘ τ_v - h` as a sum of two bilinear expressions
  have hfτ : ContDiff ℝ k fun z => f (z + v) := f.contDiff.comp (contDiff_id.add contDiff_const)
  have hgτ : ContDiff ℝ k fun z => g (z + v) := g.contDiff.comp (contDiff_id.add contDiff_const)
  have hsplit : (fun z => h (z + v)) - h = (fun z => B (f (z + v) - f z) (g (z + v))) +
      fun z => B (f z) (g (z + v) - g z) := by
    funext z
    simp only [hh, Pi.sub_apply, Pi.add_apply, map_sub, sub_apply]
    abel
  have hc1 : ContDiff ℝ k fun z => B (f (z + v) - f z) (g (z + v)) :=
    (B.contDiff.comp (hfτ.sub f.contDiff)).clm_apply hgτ
  have hc2 : ContDiff ℝ k fun z => B (f z) (g (z + v) - g z) :=
    (B.contDiff.comp f.contDiff).clm_apply (hgτ.sub g.contDiff)
  have hhτ : ContDiff ℝ k fun z => h (z + v) := hcd.comp (contDiff_id.add contDiff_const)
  have hdiff : iteratedFDeriv ℝ k h y - iteratedFDeriv ℝ k h x =
      iteratedFDeriv ℝ k (fun z => B (f (z + v) - f z) (g (z + v))) x +
        iteratedFDeriv ℝ k (fun z => B (f z) (g (z + v) - g z)) x := by
    rw [hy, ← iteratedFDeriv_comp_add_right (f := h) k v x,
      ← iteratedFDeriv_sub_apply hhτ.contDiffAt hcd.contDiffAt, hsplit,
      iteratedFDeriv_add_apply hc1.contDiffAt hc2.contDiffAt]
  -- the two Leibniz bounds
  have b1 := norm_iteratedFDeriv_bilinear_le B (hfτ.sub f.contDiff) hgτ x
    (A := 2 * ‖f‖ * ‖v‖ ^ (r : ℝ)) (A' := ‖g‖)
    (fun j hj => by
      change ‖iteratedFDeriv ℝ j ((fun z => f (z + v)) - ⇑f) x‖ ≤ _
      rw [iteratedFDeriv_sub_apply (hfτ.of_le (by exact_mod_cast hj)).contDiffAt
        (f.contDiff.of_le (by exact_mod_cast hj)).contDiffAt, iteratedFDeriv_comp_add_right]
      exact f.norm_iteratedFDeriv_add_sub_le hr hj x v)
    (fun j hj => by
      rw [iteratedFDeriv_comp_add_right]
      exact g.norm_iteratedFDeriv_apply_le hj _)
  have b2 := norm_iteratedFDeriv_bilinear_le B f.contDiff (hgτ.sub g.contDiff) x
    (A := ‖f‖) (A' := 2 * ‖g‖ * ‖v‖ ^ (r : ℝ))
    (fun j hj => f.norm_iteratedFDeriv_apply_le hj x)
    (fun j hj => by
      change ‖iteratedFDeriv ℝ j ((fun z => g (z + v)) - ⇑g) x‖ ≤ _
      rw [iteratedFDeriv_sub_apply (hgτ.of_le (by exact_mod_cast hj)).contDiffAt
        (g.contDiff.of_le (by exact_mod_cast hj)).contDiffAt, iteratedFDeriv_comp_add_right]
      exact g.norm_iteratedFDeriv_add_sub_le hr hj x v)
  rw [dist_comm, dist_eq_norm, hdiff]
  refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans_eq ?_)
  rw [dist_comm, dist_eq_norm, ← hv]
  push_cast
  ring

/-- The map `x ↦ B (f x) (g x)` for a continuous bilinear map `B` and `f`, `g` in `C^{k,r}_b`,
`r ≤ 1`, as an element of `C^{k,r}_b`. -/
def bilinear (hr : r ≤ 1) (B : F₁ →L[ℝ] F₂ →L[ℝ] G) (f : BoundedContDiffHolderMap k r E F₁)
    (g : BoundedContDiffHolderMap k r E F₂) : BoundedContDiffHolderMap k r E G where
  toFun x := B (f x) (g x)
  contDiff' := (B.contDiff.comp f.contDiff).clm_apply g.contDiff
  bounded' i hi := ⟨‖B‖ * 2 ^ i * ‖f‖ * ‖g‖, norm_iteratedFDeriv_bilinear_apply_le B f g hi⟩
  memHolder' := (holderWith_iteratedFDeriv_bilinear hr B f g).memHolder

@[simp]
theorem coe_bilinear (hr : r ≤ 1) (B : F₁ →L[ℝ] F₂ →L[ℝ] G)
    (f : BoundedContDiffHolderMap k r E F₁) (g : BoundedContDiffHolderMap k r E F₂) :
    ⇑(bilinear hr B f g) = fun x => B (f x) (g x) :=
  rfl

private theorem sum_range_two_pow_le (k : ℕ) : ∑ i ∈ Finset.range k, (2 : ℝ) ^ i ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith [pow_pos (two_pos : (0 : ℝ) < 2) k]

/-- **Product estimate** in `C^{k,r}_b`, `r ≤ 1`: `‖B (f, g)‖ ≤ 2 ^ (k + 3) ‖B‖ ‖f‖ ‖g‖`. -/
theorem norm_bilinear_le (hr : r ≤ 1) (B : F₁ →L[ℝ] F₂ →L[ℝ] G)
    (f : BoundedContDiffHolderMap k r E F₁) (g : BoundedContDiffHolderMap k r E F₂) :
    ‖bilinear hr B f g‖ ≤ 2 ^ (k + 3) * ‖B‖ * ‖f‖ * ‖g‖ := by
  set P : ℝ := ‖B‖ * ‖f‖ * ‖g‖ with hP
  have hP0 : 0 ≤ P := by positivity
  have hD : ∀ i ≤ k, ‖(bilinear hr B f g).iteratedFDerivBCF i‖ ≤ 2 ^ i * P := fun i hi =>
    (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => by
      rw [coe_iteratedFDerivBCF _ hi]
      refine (norm_iteratedFDeriv_bilinear_apply_le B f g hi x).trans_eq ?_
      rw [hP]; ring
  have hH : ‖(bilinear hr B f g).iteratedFDerivHolder‖ ≤ 2 ^ k * P + 2 ^ (k + 2) * P := by
    have h := (bilinear hr B f g).iteratedFDerivHolder.norm_le_of_holderWith
      (C := ‖B‖₊ * 2 ^ (k + 2) * ‖f‖₊ * ‖g‖₊) (by
        rw [coe_iteratedFDerivHolder]
        exact holderWith_iteratedFDeriv_bilinear hr B f g)
    rw [iteratedFDerivHolder_toBoundedContinuousFunction] at h
    refine h.trans (add_le_add (hD k le_rfl) (le_of_eq ?_))
    push_cast
    rw [hP]; ring
  have hS : ∑ i ∈ Finset.range k, ‖(bilinear hr B f g).iteratedFDerivBCF i‖ ≤ 2 ^ k * P :=
    (Finset.sum_le_sum fun i hi => hD i (Finset.mem_range.1 hi).le).trans (by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_range_two_pow_le k) hP0)
  rw [norm_def]
  have h2 : (0 : ℝ) ≤ 2 ^ k * P := by positivity
  calc _ ≤ 2 ^ k * P + (2 ^ k * P + 2 ^ (k + 2) * P) := add_le_add hS hH
    _ ≤ 2 ^ (k + 3) * P := by rw [pow_add, pow_add]; nlinarith
    _ = _ := by rw [hP]; ring

end SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMap

import SGPT.Foundations.Analysis.Pending.BoundedContDiffHolderMap

set_option autoImplicit false

/-!
# Lowering the Hölder exponent: `C^{k,r}_b ⊂ C^{k,s}_b` for `s ≤ r`

On an arbitrary metric space `X` (bounded or not), a bounded `r`-Hölder map is `s`-Hölder for
every `s ≤ r`, with `[f]_s ≤ max ([f]_r, 2 ‖f‖_∞)`: use `d ^ r ≤ d ^ s` for `d ≤ 1` and the bound
`2 ‖f‖_∞` for `d ≥ 1` (`BoundedHolderMap.holderWith_of_le`).  Applied to the top derivative this
gives the continuous inclusion `C^{k,r}_b(E, F) → C^{k,s}_b(E, F)` of norm `≤ 3`
(`BoundedContDiffHolderMap.ofLECLM`), and the interpolation inequality of the top derivative
(`BoundedContDiffHolderMap.holderWith_iteratedFDeriv_interpolate`).

Part of the linear track `L1` of the plan for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace SGPT.Foundations.Analysis.Pending

namespace BoundedHolderMap

variable {r s : ℝ≥0} {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]

/-- On any metric space, `[f]_s ≤ max ([f]_r, 2 ‖f‖_∞)` for `s ≤ r`. -/
theorem holderWith_of_le (f : BoundedHolderMap r X F) (hsr : s ≤ r) :
    HolderWith (max (nnHolderNorm r f) (2 * ‖f.toBoundedContinuousFunction‖₊)) s f := by
  refine HolderWith.of_dist_le fun x y => ?_
  have hd := dist_nonneg (x := x) (y := y)
  push_cast
  rcases le_total (dist x y) 1 with hd1 | hd1
  · calc dist (f x) (f y) ≤ nnHolderNorm r f * dist x y ^ (r : ℝ) := f.holderWith.dist_le x y
      _ ≤ nnHolderNorm r f * dist x y ^ (s : ℝ) := by
          rcases hd.eq_or_lt with h0 | h0
          · rw [← h0]
            rcases (zero_le : (0 : ℝ≥0) ≤ s).eq_or_lt with hs | hs
            · rw [← hs]; simp only [NNReal.coe_zero, Real.rpow_zero]
              exact mul_le_mul_of_nonneg_left
                (Real.zero_rpow_le_one _) (NNReal.coe_nonneg _)
            · rw [Real.zero_rpow (NNReal.coe_pos.2 (hs.trans_le hsr)).ne',
                Real.zero_rpow (NNReal.coe_pos.2 hs).ne']
          · exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_ge h0 hd1 (by exact_mod_cast hsr))
              (NNReal.coe_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd _)
  · calc dist (f x) (f y) ≤ 2 * ‖f.toBoundedContinuousFunction‖ :=
          f.toBoundedContinuousFunction.dist_le_two_norm x y
      _ ≤ 2 * ‖f.toBoundedContinuousFunction‖ * dist x y ^ (s : ℝ) :=
          le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hd1 s.coe_nonneg)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd _)

end BoundedHolderMap

namespace BoundedContDiffHolderMap

variable {k : ℕ} {r s : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inclusion `C^{k,r}_b(E, F) → C^{k,s}_b(E, F)` for `s ≤ r`. -/
def ofLE (hsr : s ≤ r) (f : BoundedContDiffHolderMap k r E F) :
    BoundedContDiffHolderMap k s E F where
  toFun := f
  contDiff' := f.contDiff
  bounded' _ hi := f.bounded hi
  memHolder' := by
    have h := f.iteratedFDerivHolder.holderWith_of_le hsr
    rw [coe_iteratedFDerivHolder] at h
    exact h.memHolder

@[simp]
theorem coe_ofLE (hsr : s ≤ r) (f : BoundedContDiffHolderMap k r E F) : ⇑(ofLE hsr f) = f :=
  rfl

theorem iteratedFDerivBCF_ofLE (hsr : s ≤ r) (f : BoundedContDiffHolderMap k r E F) (i : ℕ) :
    (ofLE hsr f).iteratedFDerivBCF i = f.iteratedFDerivBCF i := by
  by_cases hi : i ≤ k
  · ext1 x
    rw [coe_iteratedFDerivBCF _ hi, coe_iteratedFDerivBCF _ hi, coe_ofLE]
  · rw [iteratedFDerivBCF_of_lt _ (not_le.1 hi), iteratedFDerivBCF_of_lt _ (not_le.1 hi)]

/-- `‖f‖_{k,s} ≤ 3 ‖f‖_{k,r}` for `s ≤ r`. -/
theorem norm_ofLE_le (hsr : s ≤ r) (f : BoundedContDiffHolderMap k r E F) :
    ‖ofLE hsr f‖ ≤ 3 * ‖f‖ := by
  have hH : ‖(ofLE hsr f).iteratedFDerivHolder‖ ≤ 3 * ‖f.iteratedFDerivHolder‖ := by
    have h := f.iteratedFDerivHolder.holderWith_of_le hsr
    have h' : HolderWith (max (nnHolderNorm r ⇑f.iteratedFDerivHolder)
        (2 * ‖f.iteratedFDerivHolder.toBoundedContinuousFunction‖₊)) s
        (ofLE hsr f).iteratedFDerivHolder := by
      have he : ⇑(ofLE hsr f).iteratedFDerivHolder = ⇑f.iteratedFDerivHolder := by
        rw [coe_iteratedFDerivHolder, coe_iteratedFDerivHolder, coe_ofLE]
      rw [he]
      exact h
    refine ((ofLE hsr f).iteratedFDerivHolder.norm_le_of_holderWith h').trans ?_
    rw [iteratedFDerivHolder_toBoundedContinuousFunction, iteratedFDerivBCF_ofLE,
      ← iteratedFDerivHolder_toBoundedContinuousFunction, BoundedHolderMap.norm_def]
    push_cast
    have h1 := norm_nonneg f.iteratedFDerivHolder.toBoundedContinuousFunction
    have h2 := (nnHolderNorm r ⇑f.iteratedFDerivHolder).coe_nonneg
    rcases le_total (nnHolderNorm r ⇑f.iteratedFDerivHolder : ℝ)
      (2 * ‖f.iteratedFDerivHolder.toBoundedContinuousFunction‖) with hm | hm
    · rw [max_eq_right hm]; linarith
    · rw [max_eq_left hm]; linarith
  rw [norm_def, norm_def]
  have hS : ∑ i ∈ Finset.range k, ‖(ofLE hsr f).iteratedFDerivBCF i‖ =
      ∑ i ∈ Finset.range k, ‖f.iteratedFDerivBCF i‖ :=
    Finset.sum_congr rfl fun i _ => by rw [iteratedFDerivBCF_ofLE]
  rw [hS]
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range k) => norm_nonneg (f.iteratedFDerivBCF i)
  linarith

/-- The inclusion `C^{k,r}_b(E, F) →L[ℝ] C^{k,s}_b(E, F)` for `s ≤ r` (norm `≤ 3`). -/
def ofLECLM (hsr : s ≤ r) :
    BoundedContDiffHolderMap k r E F →L[ℝ] BoundedContDiffHolderMap k s E F :=
  LinearMap.mkContinuous
    { toFun := ofLE hsr
      map_add' _ _ := ext fun _ => rfl
      map_smul' _ _ := ext fun _ => rfl } 3 (norm_ofLE_le hsr)

@[simp]
theorem ofLECLM_apply (hsr : s ≤ r) (f : BoundedContDiffHolderMap k r E F) :
    ofLECLM hsr f = ofLE hsr f :=
  rfl

/-- **Interpolation** of the top derivative: `[Dᵏ f]_{r t} ≤ [Dᵏ f]_r ^ t (2 ‖Dᵏ f‖_∞) ^ (1 - t)`
for `0 ≤ t ≤ 1`. -/
theorem holderWith_iteratedFDeriv_interpolate (f : BoundedContDiffHolderMap k r E F) {t : ℝ≥0}
    (ht : t ≤ 1) :
    HolderWith (nnHolderNorm r (iteratedFDeriv ℝ k f) ^ (t : ℝ) *
      (2 * ‖f.iteratedFDerivBCF k‖₊) ^ ((1 - t : ℝ≥0) : ℝ)) (r * t) (iteratedFDeriv ℝ k f) := by
  have h := f.iteratedFDerivHolder.holderWith_interpolate ht
  rw [coe_iteratedFDerivHolder, iteratedFDerivHolder_toBoundedContinuousFunction] at h
  exact h

end BoundedContDiffHolderMap

end SGPT.Foundations.Analysis.Pending

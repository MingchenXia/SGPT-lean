import SGPT.PSH.HermitianProductsResidualSplitting

/-!
# Actual monotonicity under a semipositive smooth background increment

The exact residual splitting expresses the difference as a finite sum of
positive genuine Hermitian subproducts. This applies to nonclosed forms.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorCalculus LocalBedfordTaylorContinuity LocalBedfordTaylorLocality
  LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorCollar
  LocalBedfordTaylorDecreasing TopDegreeDensity ConstantFormProducts
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

theorem wedgeForm_unit_current {r : ℕ} (T : LocalProductCurrent n U r) :
    wedgeForm (r := r) (k := 0) rfl T
      (contDiffOn_const (c := (coordinateWedgeUnit : RealForm n 0))) = T := by
  classical
  ext γ φ
  rw [wedgeForm_apply_eq (r := r) (k := 0) rfl T
    (α := fun _ : ComplexModel n => (coordinateWedgeUnit : RealForm n 0))
    contDiffOn_const (fun _ _ => (kahlerPower n 0).2)
    (fun _ : Unit => fun _ : ComplexModel n => (1 : ℝ))
    (fun _ => contDiffOn_const) (fun _ => kahlerPower n 0)
    (fun _ _ => by simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]; rfl)]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have eγ : wedgeSpan n rfl γ (kahlerPower n 0) = γ := by
    apply Subtype.ext
    rw [coe_wedgeSpan_apply rfl _ _ (by omega)]
    change wedgeTo (by omega : 2 * r + 0 = 2 * r) (γ : RealForm n (2 * r))
      (coordinateWedgeUnit : RealForm n 0) = γ
    rw [wedgeTo_unit_right (by omega) rfl]
    rfl
  have eφ : mulSmoothOnCLM (contDiffOn_const (c := (1 : ℝ))) φ = φ := by
    ext x
    simp only [mulSmoothOnCLM_apply, mul_one]
  rw [eγ, eφ]

theorem residualSplitTerm_univ_of_approximation (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (f : ℕ → Fin p → ComplexModel n → ℝ)
    (hf : ∀ i, IsDecreasingApproximation U (v i) (fun j => f j i))
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (hτS : ∀ z ∈ U, τ z ∈ formSpan n 1) :
    residualSplitTerm p r v hσ hτ T Finset.univ = backgroundExpansion p r v hσ T := by
  classical
  have heq (j : ℕ) : residualSplitTerm p r (f j) hσ hτ T Finset.univ =
      backgroundExpansion p r (f j) hσ T := by
    rw [residualSplitTerm_smooth p r (f j) (fun i => ((hf i).1 j).1)
      (fun i => ((hf i).1 j).2.1) hσ hτ hσS hτS T hT hTc,
      Finset.piecewise_univ,
      backgroundExpansion_smooth p r (f j) (fun i => ((hf i).1 j).1)
        (fun i => ((hf i).1 j).2.1) hσ hσS T hT hTc]
    rfl
  have hleft := residualSplitTerm_decreasing p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) hσ hτ Finset.univ
  have hright := backgroundExpansion_decreasing p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) hσ
  ext γ φ
  apply tendsto_nhds_unique (hleft γ φ)
  simpa only [heq] using hright γ φ

theorem residualSplitTerm_univ (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (hτS : ∀ z ∈ U, τ z ∈ formSpan n 1) :
    residualSplitTerm p r v hσ hτ T Finset.univ = backgroundExpansion p r v hσ T := by
  classical
  apply eq_of_local
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel n) := ⟨Metric.ball x (a / 2), Metric.isOpen_ball⟩
  have hAU : A ≤ U := fun z hz => hball (Metric.ball_subset_ball (by linarith) hz)
  have hArel : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  refine ⟨A, hAU, Metric.mem_ball_self (half_pos ha), ?_⟩
  rw [residualSplitTerm_restrict hAU p r T hT hTc v hv hσ hτ,
    backgroundExpansion_restrict hAU p r T hT hTc v hv hσ]
  have happrox : ∀ i, ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation A (v i) f := fun i =>
    HolomorphicPullback.exists_decreasingMollifierApproximation (hv i) hArel
  choose f hf using happrox
  exact residualSplitTerm_univ_of_approximation p r (restrict hAU T)
    (isPositive_restrict hT hAU) (isClosedAny_restrict hTc hAU) v
    (fun i => isLocallyBoundedPshOn_mono (hv i) hAU) (fun j i => f i j) hf
    (hσ.mono hAU) (hτ.mono hAU)
    (fun z hz => hσS z (hAU hz)) (fun z hz => hτS z (hAU hz))

theorem isPositive_finset_sum {ι : Type*} {r : ℕ} (s : Finset ι)
    (T : ι → LocalProductCurrent n U r) (hT : ∀ i ∈ s, IsPositive (T i)) :
    IsPositive (∑ i ∈ s, T i) := by
  intro κ _ γ φ hγ
  simp only [LinearMap.sum_apply, _root_.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_nonneg fun i hi => hT i hi κ γ φ hγ

/-- Increasing a smooth background by a semipositive real one-one form
increases the actual nonclosed-background product current. -/
theorem isPositive_backgroundExpansion_add_sub
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ τ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U)
    (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hτpos : ∀ z ∈ U, IsSemipositiveOneOne (τ z)) :
    IsPositive (backgroundExpansion p r v (hσ.add hτ) T - backgroundExpansion p r v hσ T) := by
  classical
  rw [backgroundExpansion_split p r T hT hTc v hv hσ hτ
    (fun z hz => oneOne_mem_formSpan (hσ11 z hz))
    (fun z hz => oneOne_mem_formSpan (hτpos z hz).1)]
  have heq : (∑ s : Finset (Fin p), residualSplitTerm p r v hσ hτ T s) -
      backgroundExpansion p r v hσ T =
      ∑ s ∈ (Finset.univ : Finset (Finset (Fin p))).erase Finset.univ,
        residualSplitTerm p r v hσ hτ T s := by
    rw [← residualSplitTerm_univ p r T hT hTc v hv hσ hτ
      (fun z hz => oneOne_mem_formSpan (hσ11 z hz))
      (fun z hz => oneOne_mem_formSpan (hτpos z hz).1)]
    exact sub_eq_iff_eq_add.mpr (Finset.sum_erase_add _ _ (Finset.mem_univ Finset.univ)).symm
  rw [heq]
  exact isPositive_finset_sum _ _ (fun s _ =>
    isPositive_residualSplitTerm p r T hT hTc v hv hσ hτ hσ11 hfactor hτpos s)

end SGPT.PSH.HermitianProducts

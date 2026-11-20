import SGPT.PSH.HermitianProducts

/-!
# Open restriction of the local nonclosed-background expansion

Smooth exterior products and the literal finite Hermitian expansion commute
with restriction to an open subset. These identities concern the actual
coefficient-distribution currents; correction independence and global gluing
are separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar
  LocalBedfordTaylorDecreasing
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U V : Opens (ComplexModel n)}

/-- An actual smooth-form wedge depends only on the form on its open
current domain; values of ambient representatives outside it are irrelevant. -/
theorem wedgeForm_congr {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m)
    {α β : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U)
    (heq : EqOn α β U) : wedgeForm h T hα = wedgeForm h T hβ := by
  classical
  ext γ φ
  simp only [wedgeForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ext z
  simp only [mulSmoothOnCLM_apply]
  by_cases hz : z ∈ U
  · rw [formCoeff, formCoeff, heq hz]
  · rw [testFunction_eq_zero_of_notMem φ hz, zero_mul, zero_mul]

/-- Each literal Hermitian subset term depends only on its actual potential
and smooth residual representatives on the current domain. -/
theorem backgroundExpansionTerm_congr (p r : ℕ)
    (T : LocalProductCurrent n U (r + p))
    (v w : Fin p → ComplexModel n → ℝ) (heq : ∀ i, EqOn (v i) (w i) U)
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U) (hres : EqOn σ τ U)
    (s : Finset (Fin p)) :
    backgroundExpansionTerm p r v hσ T s = backgroundExpansionTerm p r w hτ T s := by
  classical
  dsimp only [backgroundExpansionTerm]
  rw [btProduct_congr s.card (r + (p - s.card))
    (fun i => v (s.orderEmbOfFin rfl i)) (fun i => w (s.orderEmbOfFin rfl i)) _
    (fun i z hz => heq _ hz)]
  apply wedgeForm_congr
  intro z hz
  change TopDegreeDensity.wedgeProd (p - s.card) (fun _ => σ z) =
    TopDegreeDensity.wedgeProd (p - s.card) (fun _ => τ z)
  rw [hres hz]

/-- The actual nonclosed-background expansion is independent of ambient
representative values outside its open domain. -/
theorem backgroundExpansion_congr (p r : ℕ)
    (T : LocalProductCurrent n U (r + p))
    (v w : Fin p → ComplexModel n → ℝ) (heq : ∀ i, EqOn (v i) (w i) U)
    {σ τ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hτ : ContDiffOn ℝ ∞ τ U) (hres : EqOn σ τ U) :
    backgroundExpansion p r v hσ T = backgroundExpansion p r w hτ T := by
  classical
  unfold backgroundExpansion
  exact Finset.sum_congr rfl fun s _ =>
    backgroundExpansionTerm_congr p r T v w heq hσ hτ hres s

/-- Smooth wedging commutes with actual open restriction, including arbitrary
nonclosed smooth forms and arbitrary current bases. -/
theorem wedgeForm_restrict (hVU : V ≤ U) {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m)
    {σ : ComplexModel n → RealForm n (2 * k)} (hσ : ContDiffOn ℝ ∞ σ U) :
    restrict hVU (wedgeForm h T hσ) =
      wedgeForm h (restrict hVU T) (hσ.mono hVU) := by
  classical
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply, wedgeForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ext z
  simp only [extTest_apply, mulSmoothOnCLM_apply]

private theorem castLPC_restrict {a b : ℕ} (h : a = b)
    (hVU : V ≤ U) (T : LocalProductCurrent n U a) :
    restrict hVU (castLPC h T) = castLPC h (restrict hVU T) := by
  subst h
  rfl

/-- A subset term of the literal local Hermitian expansion has the same
current after restriction as the term constructed on the smaller domain. -/
theorem backgroundExpansionTerm_restrict (hVU : V ≤ U) (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    restrict hVU (backgroundExpansionTerm p r v hσ T s) =
      backgroundExpansionTerm p r v (hσ.mono hVU) (restrict hVU T) s := by
  classical
  dsimp only [backgroundExpansionTerm]
  rw [wedgeForm_restrict,
    ← btProduct_restrict hVU s.card (r + (p - s.card))
      (fun i => v (s.orderEmbOfFin rfl i)) _
      (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc) (fun i => hv _),
    castLPC_restrict]

/-- The finite local expansion for a nonclosed Hermitian background commutes
with open restriction. This is locality for the chosen correction. -/
theorem backgroundExpansion_restrict (hVU : V ≤ U) (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    restrict hVU (backgroundExpansion p r v hσ T) =
      backgroundExpansion p r v (hσ.mono hVU) (restrict hVU T) := by
  classical
  ext γ φ
  simp only [backgroundExpansion, LocalBedfordTaylorLocality.restrict_apply, LinearMap.sum_apply, _root_.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have he := congrArg (fun R => R γ φ)
    (backgroundExpansionTerm_restrict hVU p r T hT hTc v hv hσ s)
  simpa only [LocalBedfordTaylorLocality.restrict_apply] using he

end SGPT.PSH.HermitianProducts

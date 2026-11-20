import SGPT.PSH.HermitianProductsResidualSplitting
import SGPT.PSH.HermitianComparisonLowerTrace
import SGPT.PSH.HermitianGlobalMeasure

/-!
# Genuine permutation symmetry of nonclosed-background products

Symmetry of the actual smooth exterior product passes through the actual
decreasing Bedford--Taylor limits on each inner coordinate ball. No
permutation or multilinearity certificate is assumed for bounded products.
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
  LocalBedfordTaylorDecreasing TopDegreeDensity ConstantFormProducts NormalDirectionVanishing
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

theorem backgroundExpansion_comp_perm_smooth (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) (π : Equiv.Perm (Fin p)) :
    backgroundExpansion p r (fun i => v (π i)) hσ T = backgroundExpansion p r v hσ T := by
  rw [backgroundExpansion_smooth p r _ (fun i => hv (π i)) (fun i => hvp (π i)) hσ hσS T hT hTc,
    backgroundExpansion_smooth p r v hv hvp hσ hσS T hT hTc]
  apply wedgeForm_congr
  intro x _
  exact wedgeProd_comp_perm p (fun i => ddcForm (v i) x + σ x) π

theorem backgroundExpansion_comp_perm_of_approximation (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (f : ℕ → Fin p → ComplexModel n → ℝ)
    (hf : ∀ i, IsDecreasingApproximation U (v i) (fun j => f j i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) (π : Equiv.Perm (Fin p)) :
    backgroundExpansion p r (fun i => v (π i)) hσ T = backgroundExpansion p r v hσ T := by
  have hleft := backgroundExpansion_decreasing p r T hT hTc
    (fun j i => f j (π i)) (fun i => v (π i))
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf (π i)).1 j)) (fun i => hv (π i))
    (fun i z hz => (hf (π i)).2.1 z hz) (fun i z hz => (hf (π i)).2.2 z hz) hσ
  have hright := backgroundExpansion_decreasing p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) hσ
  have heq (j : ℕ) := backgroundExpansion_comp_perm_smooth p r T hT hTc (f j)
    (fun i => ((hf i).1 j).1) (fun i => ((hf i).1 j).2.1) hσ hσS π
  ext γ φ
  apply tendsto_nhds_unique (hleft γ φ)
  simpa only [heq] using hright γ φ

/-- Symmetry of the actual bounded nonclosed-background product on every
open coordinate domain. The radial mollifiers are constructed internally. -/
theorem backgroundExpansion_comp_perm (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1) (π : Equiv.Perm (Fin p)) :
    backgroundExpansion p r (fun i => v (π i)) hσ T = backgroundExpansion p r v hσ T := by
  classical
  apply eq_of_local
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel n) := ⟨Metric.ball x (a / 2), Metric.isOpen_ball⟩
  have hAU : A ≤ U := fun z hz => hball (Metric.ball_subset_ball (by linarith) hz)
  have hArel : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  refine ⟨A, hAU, Metric.mem_ball_self (half_pos ha), ?_⟩
  have happrox : ∀ i, ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation A (v i) f := fun i =>
    HolomorphicPullback.exists_decreasingMollifierApproximation (hv i) hArel
  choose f hf using happrox
  rw [backgroundExpansion_restrict hAU p r T hT hTc _ (fun i => hv (π i)),
    backgroundExpansion_restrict hAU p r T hT hTc v hv]
  exact backgroundExpansion_comp_perm_of_approximation p r (restrict hAU T)
    (isPositive_restrict hT hAU) (isClosedAny_restrict hTc hAU) v
    (fun i => isLocallyBoundedPshOn_mono (hv i) hAU) (fun j i => f i j) hf
    (hσ.mono hAU) (fun z hz => hσS z (hAU hz)) π

end SGPT.PSH.HermitianProducts

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCollar
  LocalBedfordTaylorSmoothProductDensity
open Hermitian SGPT.PSH.HermitianComparisonLowerTrace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- The original actual patch product is symmetric in its bounded native
Hermitian potentials, with positivity and local corrections internal. -/
theorem BackgroundPatch.current_comp_perm (P : BackgroundPatch omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (π : Equiv.Perm (Fin (m + 1))) : P.current (fun i => u (π i)) = P.current u := by
  exact HermitianProducts.backgroundExpansion_comp_perm (m + 1) 0 _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i))
    P.residual_smooth (fun z hz => oneOne_mem_formSpan (P.residual_isOneOne z hz)) π

variable [MeasurableSpace M] [BorelSpace M]

omit [BorelSpace M] in
theorem BackgroundPatch.pushTraceMeasure_current_comp_perm (P : BackgroundPatch omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (π : Equiv.Perm (Fin (m + 1))) :
    P.geometry.pushTraceMeasure (P.current (fun i => u (π i)))
        (P.current_isPositive _ (fun i => hu (π i)) (fun i => hb (π i))) =
      P.geometry.pushTraceMeasure (P.current u) (P.current_isPositive u hu hb) := by
  apply congrArg P.geometry.pushMeasure
  apply traceMeasure_eq_of_trace_tests
  intro φ
  exact congrArg (fun T => T (kahlerPower (m + 1) 0) φ) (P.current_comp_perm u hu hb π)

/-- The canonical nonclosed Hermitian mixed measure is symmetric in its
original bounded potentials. This is an equality of actual global measures. -/
theorem globalMixedMeasure_comp_perm [CompactSpace M]
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (π : Equiv.Perm (Fin (m + 1))) :
    globalMixedMeasure omega (fun i => u (π i)) (fun i => hu (π i)) (fun i => hb (π i)) =
      globalMixedMeasure omega u hu hb := by
  let C := Classical.choice (nonempty_backgroundFiniteCover omega)
  rw [globalMixedMeasure_eq_cover C, globalMixedMeasure_eq_cover C]
  change FiniteMeasureGluing.glue (fun j => ((C.patch j).geometry.source : Set M))
      (fun j => (C.patch j).geometry.pushTraceMeasure ((C.patch j).current (fun i => u (π i)))
        ((C.patch j).current_isPositive _ (fun i => hu (π i)) (fun i => hb (π i)))) =
    FiniteMeasureGluing.glue (fun j => ((C.patch j).geometry.source : Set M))
      (fun j => (C.patch j).geometry.pushTraceMeasure ((C.patch j).current u)
        ((C.patch j).current_isPositive u hu hb))
  apply congrArg
  funext j
  exact (C.patch j).pushTraceMeasure_current_comp_perm u hu hb π

end SGPT.PSH.HermitianGlobalProducts

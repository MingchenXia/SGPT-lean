import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyChartIntegrals

set_option autoImplicit false

/-! # Actual compact mixed NP measures produce local corrected-gap weight integrability -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.CompactNonPluripolarChartWeightIntegrability

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches GlobalNonPluripolar
  RelativeEnergy RelativeEnergyIntegrability MixedNonPluripolar
  SingularModelEnergyChartIntegrals

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {η : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}

/-- Actual patch integrability is equivalent to integrability of the inverse-chart pullback, when the coordinate measure is supported on the patch domain. -/
theorem _root_.SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches.Patch.integrable_pushMeasure_iff
    (P : Patch η s) {μ : Measure (ComplexModel n)}
    (hμ : μ (P.domain : Set (ComplexModel n))ᶜ = 0) (F : M → ℝ) :
    Integrable F (P.pushMeasure μ) ↔ Integrable (fun z => F (P.chart.val.symm z)) μ := by
  rw [Patch.pushMeasure, P.measurableEmbedding_toManifold.integrable_map_iff]
  have h := integrableOn_iff_comap_subtypeVal (μ := μ) P.domain.isOpen.measurableSet
    (f := fun z => F (P.chart.val.symm z))
  change Integrable (fun z : P.domain => F (P.chart.val.symm z))
    (μ.comap Subtype.val) ↔ _
  change IntegrableOn (fun z => F (P.chart.val.symm z)) P.domain μ ↔
    Integrable (fun z : P.domain => F (P.chart.val.symm z)) (μ.comap Subtype.val) at h
  rw [← h]
  change Integrable _ (μ.restrict P.domain) ↔ _
  rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)]

variable [CompactSpace M]

private theorem integrable_chart_of_global
    (hs : ∀ i, ThetaPlurisubharmonic (η i).val (s i)) (P : Patch η s)
    (F : M → ℝ) (hF : Integrable F (globalMixedMeasure η s hs)) :
    Integrable (fun z => F (P.chart.val.symm z))
      (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic) := by
  apply (P.integrable_pushMeasure_iff
    (mixedTruncationLimitMeasure_compl P.plurisubharmonic) F).mp
  change Integrable F
    (P.pushMeasure (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic))
  have heq : (globalMixedMeasure η s hs).restrict (P.source : Set M) =
      P.pushMeasure (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic) :=
    globalMixedMeasure_restrict_patch hs P
  rw [← heq]
  exact hF.restrict

variable {α β : SmoothRealForm n M 2} {W Φ : M → EReal}

/-- Genuine compact-host same-type integrability and the actual global NP patch characterization produce inverse-chart gap integrability. -/
theorem integrable_chart_canonicalDiff (omega : KahlerBackground n M)
    (hW : ThetaPlurisubharmonic α W) (hΦ : ThetaPlurisubharmonic β Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ)
    (hs : ∀ i, ThetaPlurisubharmonic (η i).val (s i)) (P : Patch η s) :
    Integrable (fun z => canonicalERealDiffToReal (W (P.chart.val.symm z))
      (Φ (P.chart.val.symm z)))
      (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic) := by
  exact integrable_chart_of_global hs P (fun x => canonicalERealDiffToReal (W x) (Φ x))
    (integrable_canonicalDiff_globalMixedMeasure (eta := η) (s := s) omega hW hΦ hWΦ hs)

/-- A common finite local correction cancels, and an actual continuous compact cutoff preserves the internally produced local integrability. -/
theorem integrable_mul_corrected_canonicalDiff (omega : KahlerBackground n M)
    (hW : ThetaPlurisubharmonic α W) (hΦ : ThetaPlurisubharmonic β Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ)
    (hs : ∀ i, ThetaPlurisubharmonic (η i).val (s i)) (P : Patch η s)
    {χ : ComplexModel n → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (ρ : ComplexModel n → ℝ) :
    Integrable (fun z => χ z * canonicalERealDiffToReal
      (chartFunction W P.chart z + (ρ z : EReal))
      (chartFunction Φ P.chart z + (ρ z : EReal)))
      (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic) := by
  let μ := mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic
  have hi : Integrable (fun z => canonicalERealDiffToReal
      (chartFunction W P.chart z + (ρ z : EReal))
      (chartFunction Φ P.chart z + (ρ z : EReal))) μ := by
    refine (integrable_chart_canonicalDiff omega hW hΦ hWΦ hs P).congr ?_
    filter_upwards [] with z
    rw [canonicalDiff_add_common]
    rfl
  obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuousOn hχ.continuousOn
  have hbound (z : ComplexModel n) : ‖χ z‖ ≤ max C 0 := by
    by_cases hz : z ∈ tsupport χ
    · exact (hC z hz).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  exact hi.bdd_mul hχ.aestronglyMeasurable (Eventually.of_forall hbound)

/-- Equality of actual corrected PSH potentials on the ordinary chart domain internally identifies canonical NP measures and transports the produced weight integrability. -/
theorem integrable_mul_corrected_canonicalDiff_of_eqOn (omega : KahlerBackground n M)
    (hW : ThetaPlurisubharmonic α W) (hΦ : ThetaPlurisubharmonic β Φ)
    (hWΦ : SameSingularityTypeOn W Φ univ)
    (hs : ∀ i, ThetaPlurisubharmonic (η i).val (s i)) (P : Patch η s)
    {v : Fin n → ComplexModel n → EReal} (hv : ∀ i, PlurisubharmonicOn (v i) P.domain)
    (heq : ∀ i, EqOn (P.corrected i) (v i) P.domain)
    {χ : ComplexModel n → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (ρ : ComplexModel n → ℝ) :
    Integrable (fun z => χ z * canonicalERealDiffToReal
      (chartFunction W P.chart z + (ρ z : EReal))
      (chartFunction Φ P.chart z + (ρ z : EReal)))
      (mixedTruncationLimitMeasure P.domain v hv) := by
  rw [← mixedTruncationLimitMeasure_congr P.plurisubharmonic hv heq]
  exact integrable_mul_corrected_canonicalDiff omega hW hΦ hWΦ hs P hχ hχc ρ

end

end SGPT.Foundations.Analysis.Pending.CompactNonPluripolarChartWeightIntegrability

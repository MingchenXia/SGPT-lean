import SGPT.PSH.HermitianPureTraceSelectedReadback

/-! # Corrected ordinary traces are bounded by canonical pure Hermitian traces -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianPureTraceReadback

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorCollar LocalBedfordTaylorForms
open Hermitian HermitianGlobalProducts HermitianProducts
  HermitianComparisonLowerTrace HermitianComparisonTraceDomination HermitianComparisonPureTraces

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

private theorem backgroundSmooth (P : BackgroundPatch omega) :
    ContDiffOn ℝ ∞ (omega.form.coeff P.geometry.chart) P.geometry.domain :=
  (omega.form.smooth P.geometry.chart).mono P.geometry.domain_le_target

private theorem backgroundSemipositive (P : BackgroundPatch omega) :
    ∀ z ∈ P.geometry.domain, IsSemipositiveOneOne (omega.form.coeff P.geometry.chart z) := by
  intro z hz
  exact ⟨omega.isTypeOneOne P.geometry.chart z (P.geometry.domain_le_target hz),
    omega.isSemipositive P.geometry.chart z (P.geometry.domain_le_target hz)⟩

/-- The actual ordinary BT trace of the original corrected potentials. -/
def correctedOrdinaryTraceMeasure (P : BackgroundPatch omega) (hdeg : r + p = m + 1)
    (v : Fin p → M → EReal) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal)) :
    Measure (ComplexModel (m + 1)) :=
  (isPositive_btProduct p r (fun i => P.correctedReal (v i))
    (oneCurrentOf (U := P.geometry.domain) hdeg) (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) (fun i => P.correctedReal_isLocallyBoundedPshOn (hv i) (hvb i))).1.traceMeasure

/-- The complementary degree displayed by an original patch does not change its trace. -/
theorem powerTraceMeasure_currentOfDegree_eq_lowerTraceMeasure
    (P : BackgroundPatch omega) (hdeg : r + p = m + 1)
    (v : Fin p → M → EReal) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal)) :
    powerTraceMeasure (P.currentOfDegree p r hdeg v)
      (P.currentOfDegree_isPositive p r hdeg v hv hvb)
      (backgroundSmooth P) (backgroundSemipositive P) =
      lowerTraceMeasure P (by omega : p ≤ m + 1) v hv hvb := by
  let heq : r = m + 1 - p := by omega
  exact (powerTraceMeasure_castLPC heq (P.currentOfDegree p r hdeg v)
    (P.currentOfDegree_isPositive p r hdeg v hv hvb)
    (backgroundSmooth P) (backgroundSemipositive P)).symm.trans
      (powerTraceMeasure_congr _ _ (backgroundSmooth P) (backgroundSemipositive P)
        (cast_backgroundExpansion_unit heq hdeg (by omega)
          (fun i => P.correctedReal (v i)) P.residual_smooth))

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Finiteness of a lower trace on the original domain is inherited from its
canonical global mixed measure, rather than from an extra mass hypothesis. -/
theorem lowerTraceMeasure_ne_top
    (P : BackgroundPatch omega) (hp : p ≤ m + 1)
    (v : Fin p → M → EReal) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal))
    (A : Set (ComplexModel (m + 1))) (hA : A ⊆ P.geometry.domain) :
    lowerTraceMeasure P hp v hv hvb A ≠ (⊤ : ENNReal) := by
  let hpl : p + (m + 1 - p) = m + 1 := by omega
  let μ := lowerTraceMeasure P hp v hv hvb
  let ν := globalMixedMeasure omega (completeWithZeros hpl v)
    (completeWithZeros_isHermitianPSH hpl v hv) (completeWithZeros_bounded hpl v hvb)
  have hread : ν.restrict P.geometry.source = P.geometry.pushMeasure μ :=
    globalMixedMeasure_completeWithZeros_restrict_patch hpl v hv hvb P
  let := globalMixedMeasure_isFiniteMeasure (completeWithZeros hpl v)
    (completeWithZeros_isHermitianPSH hpl v hv) (completeWithZeros_bounded hpl v hvb)
  apply ne_top_of_le_ne_top (measure_ne_top ν Set.univ)
  calc
    μ A ≤ P.geometry.pushMeasure μ Set.univ := by
      rw [P.geometry.pushMeasure_apply]
      exact measure_mono (fun z hz => ⟨hA hz, Set.mem_univ _⟩)
    _ = ν P.geometry.source := by
      rw [← hread, Measure.restrict_apply' P.geometry.source.isOpen.measurableSet]
      simp
    _ ≤ ν Set.univ := measure_mono (Set.subset_univ _)

/-- The actual corrected ordinary BT trace is bounded by a finite sum of
canonical pure Hermitian trace masses. Every lower product, its finiteness,
and the subset coefficient bound are constructed from the original data. -/
theorem btProduct_traceMass_le_pureTrace_sum
    (P : BackgroundPatch omega) (hp : p < m + 1) (hdeg : r + p = m + 1)
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (v : Fin p → M → EReal) (hvalues : ∀ i, v i = u ∨ v i = fun _ => 0)
    (A : Set (ComplexModel (m + 1))) (E : Set M)
    (hA : A ⊆ P.geometry.domain) (hAE : ∀ z ∈ A, P.geometry.chart.val.symm z ∈ E)
    (C : NNReal) (hC : 1 ≤ C)
    (hres : ∀ z ∈ P.geometry.domain,
      IsSemipositiveOneOne ((C : ℝ) • omega.form.coeff P.geometry.chart z - -P.residual z))
    (hbeta : ∀ z ∈ P.geometry.domain,
      IsSemipositiveOneOne ((C : ℝ) • omega.form.coeff P.geometry.chart z - kahlerForm (m + 1))) :
    (correctedOrdinaryTraceMeasure P hdeg v (binaryFamily_isHermitianPSH hu v hvalues)
      (binaryFamily_bounded hb v hvalues) A).toReal ≤
      2 ^ p * (C : ℝ) ^ (m + 1) *
        ∑ j ∈ Finset.range (m + 1), pureTraceMass omega hu hb E j := by
  classical
  let hv := binaryFamily_isHermitianPSH hu v hvalues
  let hvb := binaryFamily_bounded hb v hvalues
  let vs := fun (s : Finset (Fin p)) (i : Fin s.card) => v (s.orderEmbOfFin rfl i)
  let μ := fun s : Finset (Fin p) => lowerTraceMeasure P (by
    have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
    omega) (vs s) (fun i => hv _) (fun i => hvb _)
  have hselected (s : Finset (Fin p)) :
      powerTraceMeasure
        (selectedBackgroundCurrent p r (fun i => P.correctedReal (v i)) P.residual_smooth
          (oneCurrentOf (U := P.geometry.domain) hdeg) s)
        (isPositive_selectedBackgroundCurrent p r _ (isPositive_oneCurrentOf _)
          (isClosedAny_oneCurrentOf _) _
          (fun i => P.correctedReal_isLocallyBoundedPshOn (hv i) (hvb i))
          P.residual_smooth P.residual_isOneOne (fun i => P.factor_isPositive (hv i) (hvb i)) s)
        (backgroundSmooth P) (backgroundSemipositive P) = μ s := by
    have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
    refine (powerTraceMeasure_congr _
      (P.currentOfDegree_isPositive s.card (p - s.card + r) (by omega)
        (vs s) (fun i => hv _) (fun i => hvb _))
      (backgroundSmooth P) (backgroundSemipositive P)
      (selectedBackgroundCurrent_eq_currentOfDegree P p r hdeg v s)).trans ?_
    exact powerTraceMeasure_currentOfDegree_eq_lowerTraceMeasure P (by
      have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
      omega) (vs s) (fun i => hv _) (fun i => hvb _)
  have hminus : ∀ z ∈ P.geometry.domain, IsSemipositiveOneOne (-P.residual z) := by
    intro z hz
    constructor
    · intro a b
      simp only [ContinuousAlternatingMap.neg_apply]
      rw [P.residual_isOneOne z hz a b]
    · intro a
      simp only [BackgroundPatch.residual, ContinuousAlternatingMap.neg_apply,
        ContinuousAlternatingMap.sub_apply]
      linarith [P.dominates z hz a]
  have hmeasure : correctedOrdinaryTraceMeasure P hdeg v hv hvb ≤
      ∑ s : Finset (Fin p), C ^ (p - s.card + r) • μ s := by
    have h := btProduct_traceMeasure_le_hermitian_trace_sum p r
      (oneCurrentOf (U := P.geometry.domain) hdeg) (isPositive_oneCurrentOf _)
      (isClosedAny_oneCurrentOf _) (fun i => P.correctedReal (v i))
      (fun i => P.correctedReal_isLocallyBoundedPshOn (hv i) (hvb i))
      P.residual_smooth (backgroundSmooth P)
      P.residual_isOneOne (fun i => P.factor_isPositive (hv i) (hvb i)) hminus
      (backgroundSemipositive P) C hres hbeta
    simpa only [correctedOrdinaryTraceMeasure, hselected] using h
  have hfinite (s : Finset (Fin p)) : μ s A ≠ (⊤ : ENNReal) :=
    lowerTraceMeasure_ne_top P _ (vs s) (fun i => hv _) (fun i => hvb _) A hA
  have htermfinite (s : Finset (Fin p)) :
      (C : ENNReal) ^ (p - s.card + r) * μ s A ≠ (⊤ : ENNReal) :=
    ENNReal.mul_ne_top (by simp) (hfinite s)
  have hbound (s : Finset (Fin p)) : (μ s A).toReal ≤
      ∑ j ∈ Finset.range (m + 1), pureTraceMass omega hu hb E j := by
    have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
    exact lower_binary_traceMass_le_pureTrace_sum P (by omega) hu hb (vs s)
      (fun i => hvalues _) A E hA hAE
  have hexp (s : Finset (Fin p)) : (C : ℝ) ^ (p - s.card + r) ≤ (C : ℝ) ^ (m + 1) := by
    apply pow_le_pow_right₀ (show (1 : ℝ) ≤ C by exact_mod_cast hC)
    omega
  calc
    (correctedOrdinaryTraceMeasure P hdeg v hv hvb A).toReal ≤
        (∑ s : Finset (Fin p), (C : ENNReal) ^ (p - s.card + r) * μ s A).toReal := by
      apply ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun s _ => htermfinite s))
      simpa only [Measure.finsetSum_apply, Measure.coe_nnreal_smul_apply, ENNReal.coe_pow] using hmeasure A
    _ = ∑ s : Finset (Fin p), (C : ℝ) ^ (p - s.card + r) * (μ s A).toReal := by
      rw [ENNReal.toReal_sum (fun s _ => htermfinite s)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]
    _ ≤ ∑ _s : Finset (Fin p), (C : ℝ) ^ (m + 1) *
        ∑ j ∈ Finset.range (m + 1), pureTraceMass omega hu hb E j := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul (hexp s) (hbound s) ENNReal.toReal_nonneg (by positivity)
    _ = 2 ^ p * (C : ℝ) ^ (m + 1) *
        ∑ j ∈ Finset.range (m + 1), pureTraceMass omega hu hb E j := by
      simp [Fintype.card_finset, mul_assoc]

end SGPT.PSH.HermitianPureTraceReadback

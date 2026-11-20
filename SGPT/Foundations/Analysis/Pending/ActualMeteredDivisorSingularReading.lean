import SGPT.Foundations.Analysis.Pending.ActualOpenLogarithmicDivisorSingularity
import SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueACAddition
import SGPT.Foundations.Analysis.Pending.SourceBedfordTaylorTraceNormalization
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor

set_option autoImplicit false

/-! # Full singular chart readings of genuine metered divisors

The complete mathematical statement and ENTIRE proof precede this import baseline.
No positivity, desired current identity or part equality is an input.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualMeteredDivisorSingularReading
open FirstPass StronglyPositiveForms HolomorphicIdealSheaves GlobalCurrents
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
  LocalCurrentLebesgue ActualDistributionTwoFormReading LocalPositiveCurrentGluing
  ActualPositiveCurrentLebesgueUniqueness ActualPositiveCurrentLebesgueACAddition
  SourceBedfordTaylorTraceNormalization

open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {U V : Opens (ComplexModel (m + 1))}

private def readerLinear : DistributionForm U 2 →ₗ[ℝ] LocalProductCurrent (m + 1) U m where
  toFun := complementaryRead
  map_add' A B := by
    ext γ φ
    simp only [complementaryRead, AlternatingMap.add_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply,
      _root_.smul_apply, _root_.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext γ φ
    have hmul (r s : ℝ) : r * (c * s) = c * (r * s) := by ring
    simp only [complementaryRead, AlternatingMap.smul_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    simp only [hmul, ← Finset.mul_sum]

private theorem reader_restrict (hVU : V ≤ U) (A : DistributionForm U 2) :
    restrict hVU (complementaryRead A) =
      complementaryRead (LelongPoincareDivisor.restrictForm A hVU) := by
  ext γ φ
  simp only [complementaryRead, LocalBedfordTaylorLocality.restrict_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
    LelongPoincareDivisor.restrictForm_apply, extTest]

private theorem trace_congr {S T : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hT : IsPositive T) (heq : S = T) :
    hS.traceMeasure = hT.traceMeasure := by
  subst T
  rfl

private theorem zero_trace :
    (isPositive_zero : IsPositive (0 : LocalProductCurrent (m + 1) U m)).traceMeasure = 0 := by
  let hZ : IsPositive (0 : LocalProductCurrent (m + 1) U m) := isPositive_zero
  apply eq_of_forall_testFunction_integral_eq hZ.traceMeasure_compl (by simp)
    (fun K hK hKU => hZ.traceMeasure_lt_top hK hKU) (by intros; simp)
  intro φ
  rw [hZ.integral_traceMeasure]
  simp

private theorem finite_singular {ι : Type*} (s : Finset ι)
    (T : ι → LocalProductCurrent (m + 1) U m) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hT : ∀ i, IsPositive (T i))
    (hs : ∀ i, (hT i).traceMeasure ⟂ₘ volume) :
    ∃ hS : IsPositive (∑ i ∈ s, a i • T i), hS.traceMeasure ⟂ₘ volume := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      refine ⟨isPositive_zero, ?_⟩
      rw [zero_trace]
      exact Measure.MutuallySingular.zero_left
  | @insert i s hi ih =>
      obtain ⟨hS, hsS⟩ := ih
      let hiT := (hT i).smul (ha i)
      have hsi : hiT.traceMeasure ⟂ₘ volume := by
        rw [traceMeasure_smul (hT i) (ha i)]
        exact (hs i).smul_nnreal (Real.toNNReal (a i))
      have hsum : (hiT.add hS).traceMeasure ⟂ₘ volume := by
        rw [traceMeasure_add hiT hS]
        exact hsi.add_left hsS
      simpa only [Finset.sum_insert hi] using ⟨hiT.add hS, hsum⟩

private theorem singular_parts {T : LocalProductCurrent (m + 1) U m}
    (hT : IsPositive T) (hs : hT.traceMeasure ⟂ₘ volume) :
    sgPart hT = T ∧ acPart hT = 0 := by
  constructor
  · exact (ofMeasure_congr hT (sgMeasure_le hT) le_rfl
      (Measure.singularPart_eq_self.mpr hs)).trans (ofMeasure_traceMeasure hT)
  · ext γ φ
    rw [acPart, ofMeasure_apply, acMeasure,
      (Measure.withDensity_rnDeriv_eq_zero _ _).mpr hs, integral_zero_measure]
    rfl

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem presentation_reading
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1))) (E : MeteredEffectiveQDivisor (m + 1) M)
    (e : ComplexChart (m + 1) M) (P : LelongPoincareDivisor.LocalPresentation E) :
    ∃ hC : IsPositive (complementaryRead
      (LelongPoincareDivisor.restrictForm
        ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)
        (P.chartDomain_le e))), hC.traceMeasure ⟂ₘ volume := by
  classical
  let C (i : Fin P.N) := complementaryRead
    (DivisorIntegrationCurrent.divisorCurrent (P.differentiableOn_chartG e i)
      (P.frequently_chartG_ne e i))
  have hCi (i : Fin P.N) : ∃ hC : IsPositive (C i), hC.traceMeasure ⟂ₘ volume := by
    obtain ⟨_, hC, hs, _, _⟩ :=
      ActualOpenLogarithmicDivisorSingularity.exists_positive_singular_divisor_reading
        (P.differentiableOn_chartG e i) (P.frequently_chartG_ne e i)
    exact ⟨hC, hs⟩
  choose hC hs using hCi
  let a (i : Fin P.N) : ℝ := (LelongPoincareDivisor.haarFactor b : ℝ) * (P.a i : ℝ)
  have ha (i : Fin P.N) : 0 ≤ a i := mul_nonneg
    (LelongPoincareDivisor.haarFactor b).coe_nonneg (by exact_mod_cast P.a_nonneg i)
  have heq : complementaryRead (LelongPoincareDivisor.restrictForm
      ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)
      (P.chartDomain_le e)) = ∑ i, a i • C i := by
    rw [LelongPoincareDivisor.restrictForm_coefficients_eq_sum b (Nat.succ_pos m) P e]
    change readerLinear ((LelongPoincareDivisor.haarFactor b : ℝ) • ∑ i, (P.a i : ℝ) •
      DivisorIntegrationCurrent.divisorCurrent (P.differentiableOn_chartG e i)
        (P.frequently_chartG_ne e i)) = _
    rw [map_smul, map_sum]
    simp only [map_smul, Finset.smul_sum, smul_smul]
    rfl
  obtain ⟨hS, hsS⟩ := finite_singular Finset.univ C a ha hC hs
  simpa only [heq] using ⟨hS, hsS⟩

/-- A genuine metered divisor internally produces a positive singular full
complementary reader on every entire chart target, with both canonical parts. -/
theorem exists_positive_singular_chart_reading
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1))) (E : MeteredEffectiveQDivisor (m + 1) M)
    (e : ComplexChart (m + 1) M) :
    let C := complementaryRead
      ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)
    ∃ hC : IsPositive C, hC.traceMeasure ⟂ₘ volume ∧ sgPart hC = C ∧ acPart hC = 0 := by
  classical
  let C := complementaryRead
    ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E).coefficients b e)
  have hlocal (P : LelongPoincareDivisor.LocalPresentation E) :
      ∃ hP : IsPositive (restrict (P.chartDomain_le e) C), hP.traceMeasure ⟂ₘ volume := by
    dsimp only [C]
    rw [reader_restrict]
    exact presentation_reading b E e P
  have hC : IsPositive C := isPositive_of_local_restrict (by
    intro x hx
    obtain ⟨P, hxP⟩ := LelongPoincareDivisor.chartDomain_cover E e x hx
    obtain ⟨hP, _⟩ := hlocal P
    exact ⟨P.chartDomain e, P.chartDomain_le e, hxP, hP⟩)
  have hac : acPart hC = 0 := by
    ext γ φ
    have heq : acPart hC γ = (0 : 𝓓'(chartTarget e, ℝ)) := by
      apply LelongPoincareDivisor.eq_of_forall_restrict_eq
        (fun P : LelongPoincareDivisor.LocalPresentation E => P.chartDomain e)
        (fun P => P.chartDomain_le e) (LelongPoincareDivisor.chartDomain_cover E e)
      intro P
      change restrict (P.chartDomain_le e) (acPart hC) γ = 0
      rw [acPart_restrict]
      obtain ⟨hP, hsP⟩ := hlocal P
      have hs : (isPositive_restrict hC (P.chartDomain_le e)).traceMeasure ⟂ₘ volume := by
        simpa only [trace_congr hP (isPositive_restrict hC (P.chartDomain_le e)) rfl] using hsP
      rw [(singular_parts (isPositive_restrict hC (P.chartDomain_le e)) hs).2]
      rfl
    exact congrArg (fun D : 𝓓'(chartTarget e, ℝ) => D φ) heq
  have hsg : sgPart hC = C := by simpa only [hac, add_zero] using sgPart_add_acPart hC
  have hs : hC.traceMeasure ⟂ₘ volume := by
    have hs' := (part_trace_classes hC).2.1
    rw [trace_congr (isPositive_sgPart hC) hC hsg] at hs'
    exact hs'
  exact ⟨hC, hs, hsg, hac⟩

end SGPT.Foundations.Analysis.Pending.ActualMeteredDivisorSingularReading

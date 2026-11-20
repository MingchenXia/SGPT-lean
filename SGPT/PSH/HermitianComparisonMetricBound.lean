import SGPT.PSH.HermitianComparisonTraceDomination
import SGPT.Foundations.Analysis.Pending.NaturalHermitianMetricCoefficients
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# Compact Hermitian geometry produces the trace-domination constants

Strict positivity on the compact coordinate set gives a genuine uniform
lower line bound. The smooth fixed correction and coordinate forms then
admit a common Hermitian dominator chosen independently of every potential.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonMetricBound

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.NaturalHermitianMetricCoefficients
  SGPT.Foundations.Analysis.Pending.KahlerDomination
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open scoped Topology ContDiff

variable {n : ℕ}

/-- Genuine compact coercivity in the original coordinate norm, including
the empty compact set and the zero-dimensional tangent model. -/
theorem exists_compact_line_lower_bound
    (a : ComplexModel n → RealForm n 2) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (ha : ContinuousOn a K)
    (hpos : ∀ x ∈ K, IsStrictlyPositive (a x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ a x ![v, Complex.I • v] := by
  classical
  by_cases hKne : K.Nonempty
  · rcases subsingleton_or_nontrivial (ComplexModel n) with hs | hn
    · let _ := hs
      refine ⟨1, zero_lt_one, fun x hx v => ?_⟩
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      change (1 : ℝ) * ‖(0 : ComplexModel n)‖ ^ 2 ≤ associatedMetric (a x) 0 0
      rw [← associatedMetricCLM_apply]
      simp
    · let _ := hn
      let : CompactSpace K := isCompact_iff_compactSpace.mp hK
      let S := sphere (0 : ComplexModel n) (1 : ℝ)
      let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
      obtain ⟨x₀, hx₀⟩ := hKne
      obtain ⟨v₀, hv₀⟩ : (sphere (0 : ComplexModel n) (1 : ℝ)).Nonempty :=
        NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1)
      let p₀ : K × S := (⟨x₀, hx₀⟩, ⟨v₀, hv₀⟩)
      let : Nonempty (K × S) := ⟨p₀⟩
      let F : K × S → ℝ := fun p => associatedMetricCLM (a p.1) p.2 p.2
      have ha' : Continuous (fun x : K => a x) := ha.domRestrict
      have hf : Continuous F := by
        exact ((associatedMetricCLM.continuous.comp (ha'.comp continuous_fst)).clm_apply
          (continuous_subtype_val.comp continuous_snd)).clm_apply
          (continuous_subtype_val.comp continuous_snd)
      obtain ⟨p, _hp, hmin⟩ := (isCompact_univ : IsCompact (univ : Set (K × S))).exists_isMinOn
        univ_nonempty hf.continuousOn
      have hvnorm : ‖(p.2 : ComplexModel n)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2.property
      have hvne : (p.2 : ComplexModel n) ≠ 0 := fun h => by simp [h] at hvnorm
      refine ⟨F p, ?_, ?_⟩
      · change 0 < associatedMetricCLM (a p.1) p.2 p.2
        rw [associatedMetricCLM_apply]
        exact hpos p.1 p.1.property p.2 hvne
      · intro x hx v
        by_cases hv : v = 0
        · subst v
          change F p * ‖(0 : ComplexModel n)‖ ^ 2 ≤ associatedMetric (a x) 0 0
          rw [← associatedMetricCLM_apply]
          simp
        · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
          have hu : ‖v‖⁻¹ • v ∈ S := mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hv)
          have hm := hmin (show (⟨x, hx⟩, ⟨‖v‖⁻¹ • v, hu⟩) ∈ (univ : Set (K × S)) from mem_univ _)
          change F p ≤ associatedMetricCLM (a x) (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at hm
          simp only [map_smul, smul_apply, smul_eq_mul] at hm
          have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖v‖)
          have hcancel : (‖v‖⁻¹ * (‖v‖⁻¹ * associatedMetricCLM (a x) v v)) * ‖v‖ ^ 2 =
              associatedMetricCLM (a x) v v := by field_simp
          rw [hcancel, associatedMetricCLM_apply] at hmul
          exact hmul
  · refine ⟨1, zero_lt_one, fun x hx => False.elim (hKne ⟨x, hx⟩)⟩

/-- Compact strict Hermitian positivity produces the common dominator for
any fixed smooth real `(1,1)` form. The constant is chosen before potentials. -/
theorem exists_compact_semipositive_domination
    (a b : ComplexModel n → RealForm n 2) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (ha : ContinuousOn a K) (hb : ContinuousOn b K)
    (ha11 : ∀ x ∈ K, IsOneOne (a x)) (hb11 : ∀ x ∈ K, IsOneOne (b x))
    (hpos : ∀ x ∈ K, IsStrictlyPositive (a x)) :
    ∃ C : NNReal, ∀ x ∈ K, IsSemipositiveOneOne ((C : ℝ) • a x - b x) := by
  obtain ⟨c, hc, hlow⟩ := exists_compact_line_lower_bound a hK ha hpos
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hb
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  let C : NNReal := ⟨(B + 1) / c, div_nonneg (by linarith) hc.le⟩
  refine ⟨C, ?_⟩
  intro x hx
  refine ⟨?_, ?_⟩
  · intro v w
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      ha11 x hx v w, hb11 x hx v w]
  · intro v
    have hbnd : b x ![v, Complex.I • v] ≤ B * ‖v‖ ^ 2 := by
      have hop : ‖b x‖ ≤ B := (hB₀ x hx).trans (le_max_left _ _)
      exact ((le_abs_self _).trans (abs_lineValue_le _ _)).trans
        (mul_le_mul_of_nonneg_right hop (sq_nonneg ‖v‖))
    have hl := mul_le_mul_of_nonneg_left (hlow x hx v) C.coe_nonneg
    have hCc : (C : ℝ) * c = B + 1 := by
      change ((B + 1) / c) * c = B + 1
      exact div_mul_cancel₀ _ hc.ne'
    change 0 ≤ (C : ℝ) * a x ![v, Complex.I • v] - b x ![v, Complex.I • v]
    rw [← mul_assoc, hCc] at hl
    nlinarith [sq_nonneg ‖v‖]

end SGPT.PSH.HermitianComparisonMetricBound

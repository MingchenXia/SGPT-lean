import SGPT.Toric.ProjectiveLineSection
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass

/-- An independently defined original global holomorphic dual-line section:
an actual fiberwise linear functional, with holomorphic coefficients in both
genuine nonvanishing affine frames. -/
structure ProjectiveHolomorphicSection where
  toSection : (p : Projectivization ℂ (Fin 2 → ℂ)) → projectiveDualFiber p
  holomorphic : ∀ b : Bool, Differentiable ℂ (fun z : ComplexModel 1 ↦
    toSection ((projectiveModelChart b).symm z) (projectiveAffineFiberLift b z))

/-- Its actual scalar-coordinate coefficient in either original affine frame. -/
def ProjectiveHolomorphicSection.coefficient (s : ProjectiveHolomorphicSection)
    (b : Bool) (z : ℂ) : ℂ :=
  s.toSection ((projectiveModelChart b).symm (projectiveModelEquiv z))
    (projectiveAffineFiberLift b (projectiveModelEquiv z))

theorem ProjectiveHolomorphicSection.differentiable_coefficient
    (s : ProjectiveHolomorphicSection) (b : Bool) :
    Differentiable ℂ (s.coefficient b) :=
  (s.holomorphic b).comp projectiveModelEquiv.differentiable

/-- Genuine reciprocal coordinates identify the same original quotient point. -/
theorem projectiveModelChart_symm_reciprocal {z : ℂ} (hz : z ≠ 0) :
    (projectiveModelChart false).symm (projectiveModelEquiv z) =
      (projectiveModelChart true).symm (projectiveModelEquiv z⁻¹) := by
  change projectiveLineHomeomorph
    (projectiveFiniteChart.symm (projectiveModelEquiv.symm (projectiveModelEquiv z))) =
    projectiveLineHomeomorph
      (projectiveInfinityChart.symm (projectiveModelEquiv.symm (projectiveModelEquiv z⁻¹)))
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [projectiveFiniteChart_symm, projectiveInfinityChart_symm,
    projectiveReciprocal_coe (inv_ne_zero hz), inv_inv]

/-- The true dual-line coefficient transition follows from actual homogeneous
scaling at the same quotient point, not a section compatibility certificate. -/
theorem ProjectiveHolomorphicSection.coefficient_transition
    (s : ProjectiveHolomorphicSection) {z : ℂ} (hz : z ≠ 0) :
    s.coefficient false z = z * s.coefficient true z⁻¹ := by
  have hp := projectiveModelChart_symm_reciprocal hz
  have hm := projectiveAffineLift_mem false (projectiveModelEquiv z)
  have hm' : projectiveAffineLift false (projectiveModelEquiv z) ∈
      ((projectiveModelChart true).symm (projectiveModelEquiv z⁻¹)).submodule := hp ▸ hm
  have hread : s.toSection ((projectiveModelChart false).symm (projectiveModelEquiv z))
      (projectiveAffineFiberLift false (projectiveModelEquiv z)) =
      s.toSection ((projectiveModelChart true).symm (projectiveModelEquiv z⁻¹))
        ⟨projectiveAffineLift false (projectiveModelEquiv z), hm'⟩ := by
    have hs (p q : Projectivization ℂ (Fin 2 → ℂ)) (he : p = q)
        (v : Fin 2 → ℂ) (hv : v ∈ p.submodule) :
        s.toSection p ⟨v, hv⟩ = s.toSection q ⟨v, he ▸ hv⟩ := by
      subst q
      rfl
    exact hs _ _ hp _ hm
  have hlift : (⟨projectiveAffineLift false (projectiveModelEquiv z), hm'⟩ :
      ((projectiveModelChart true).symm (projectiveModelEquiv z⁻¹)).submodule) =
      z • projectiveAffineFiberLift true (projectiveModelEquiv z⁻¹) := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [projectiveAffineFiberLift, projectiveAffineLift, hz]
  change _ = z * _
  unfold ProjectiveHolomorphicSection.coefficient
  rw [hread, hlift, map_smul]
  rfl

/-- Genuine entire coefficients related by the original dual-line transition
are affine linear. The derivative-extended slope and Liouville are reused,
so no polynomial-growth or section-classification certificate is assumed. -/
theorem entire_affine_of_projective_transition {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : ContinuousAt g 0)
    (hfg : ∀ z ≠ 0, f z = z * g z⁻¹) (z : ℂ) :
    f z = g 0 * z + f 0 := by
  have hd : Differentiable ℂ (dslope f 0) :=
    differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := univ) (by simp)).mpr hf.differentiableOn)
  have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [← Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded (α := ℂ))
  have hn : Tendsto (norm : ℂ → ℝ) (cocompact ℂ) atTop := by
    simpa only [← Metric.cobounded_eq_cocompact] using
      (tendsto_norm_cobounded_atTop (E := ℂ))
  have hlim : Tendsto (dslope f 0) (cocompact ℂ) (𝓝 (g 0)) := by
    have h := (hg.tendsto.comp hinv).sub (hinv.mul_const (f 0))
    simp only [zero_mul, sub_zero] at h
    apply h.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop 0)] with w hw
    have hw0 : w ≠ 0 := norm_pos_iff.mp hw
    rw [dslope_of_ne f hw0, slope, sub_zero, hfg w hw0]
    simp only [smul_eq_mul]
    field_simp
    change g (1 / w) * w - f 0 = w * g (1 / w) - f 0
    ring
  have hs := sub_smul_dslope f 0 z
  rw [hd.apply_eq_of_tendsto_cocompact z hlim, sub_zero, smul_eq_mul] at hs
  calc
    f z = (f z - f 0) + f 0 := (sub_add_cancel _ _).symm
    _ = z * g 0 + f 0 := by rw [← hs]
    _ = g 0 * z + f 0 := by ring

/-- Liouville applied to actual section coefficients supplies their affine
formula in both original charts, including the point at infinity. -/
theorem ProjectiveHolomorphicSection.coefficient_affine
    (s : ProjectiveHolomorphicSection) (b : Bool) (z : ℂ) :
    s.coefficient b z =
      if b then s.coefficient true 0 + s.coefficient false 0 * z
        else s.coefficient true 0 * z + s.coefficient false 0 := by
  cases b
  · exact entire_affine_of_projective_transition
      (s.differentiable_coefficient false)
      (s.differentiable_coefficient true).continuous.continuousAt
      (fun z hz ↦ s.coefficient_transition hz) z
  · have hreverse : ∀ w ≠ 0,
        s.coefficient true w = w * s.coefficient false w⁻¹ := by
      intro w hw
      rw [s.coefficient_transition (inv_ne_zero hw), inv_inv]
      simp [hw]
    simpa only [ite_true, add_comm] using entire_affine_of_projective_transition
      (s.differentiable_coefficient true)
      (s.differentiable_coefficient false).continuous.continuousAt hreverse z

/-- The already produced faithful metric makes the actual nonzero affine lift
a faithful evaluator on the original dual fiber. -/
theorem projectiveDual_eq_of_affineLift (b : Bool) (z : ComplexModel 1)
    {ell eta : projectiveDualFiber ((projectiveModelChart b).symm z)}
    (heq : ell (projectiveAffineFiberLift b z) = eta (projectiveAffineFiberLift b z)) :
    ell = eta := by
  have hv : (ell - eta) (projectiveAffineFiberLift b z) = 0 := by
    change ell (projectiveAffineFiberLift b z) - eta (projectiveAffineFiberLift b z) = 0
    exact sub_eq_zero.mpr heq
  apply sub_eq_zero.mp
  apply (projectiveFiberMetric_eq_zero_iff _ _).mp
  rw [projectiveFiberMetric_eq_ratio _ _ (projectiveAffineFiberLift b z)
    (projectiveAffineFiberLift_ne_zero b z), hv, norm_zero, zero_div]

/-- Every independently defined original global holomorphic section is the
actual homogeneous linear form supplied by its original two endpoint values. -/
theorem ProjectiveHolomorphicSection.eq_linearSection (s : ProjectiveHolomorphicSection) :
    s.toSection = projectiveLinearSection
      ![s.coefficient true 0, s.coefficient false 0] := by
  funext p
  obtain ⟨b, hp⟩ := projectiveQuotientScalarChart_cover p
  have hsrc : p ∈ (projectiveModelChart b).source := by
    rwa [projectiveModelChart_source]
  let z := projectiveModelChart b p
  have hpoint : (projectiveModelChart b).symm z = p :=
    (projectiveModelChart b).left_inv hsrc
  rw [← hpoint]
  apply projectiveDual_eq_of_affineLift
  have hc := s.coefficient_affine b (projectiveModelEquiv.symm z)
  change s.toSection ((projectiveModelChart b).symm
      (projectiveModelEquiv (projectiveModelEquiv.symm z)))
      (projectiveAffineFiberLift b (projectiveModelEquiv (projectiveModelEquiv.symm z))) =
      (if b then s.coefficient true 0 + s.coefficient false 0 * projectiveModelEquiv.symm z
        else s.coefficient true 0 * projectiveModelEquiv.symm z + s.coefficient false 0) at hc
  rw [projectiveModelEquiv.apply_symm_apply z] at hc
  rw [projectiveLinearSection_chart_coefficient]
  simpa using hc

/-- Two original homogeneous linear forms giving the same global section
have exactly the same coefficients. -/
theorem projectiveLinearSection_injective : Function.Injective projectiveLinearSection := by
  intro a c heq
  have hread (b : Bool) := congrArg (fun S :
      (p : Projectivization ℂ (Fin 2 → ℂ)) → projectiveDualFiber p ↦
        S ((projectiveModelChart b).symm (projectiveModelEquiv 0))
          (projectiveAffineFiberLift b (projectiveModelEquiv 0))) heq
  have hzero : a 0 = c 0 := by
    simpa [projectiveLinearSection_chart_coefficient] using hread true
  have hone : a 1 = c 1 := by
    simpa [projectiveLinearSection_chart_coefficient] using hread false
  funext i
  fin_cases i
  · exact hzero
  · exact hone

/-- Exact original global section classification: every genuine holomorphic
section is represented by one and only one homogeneous linear form. -/
theorem ProjectiveHolomorphicSection.existsUnique_linearSection
    (s : ProjectiveHolomorphicSection) :
    ∃! a : Fin 2 → ℂ, s.toSection = projectiveLinearSection a := by
  refine ⟨![s.coefficient true 0, s.coefficient false 0], s.eq_linearSection, ?_⟩
  intro a ha
  exact projectiveLinearSection_injective (ha.symm.trans s.eq_linearSection)

/-- Conversely every original homogeneous linear form is genuinely a global
holomorphic section in the original quotient atlas. -/
def projectiveLinearHolomorphicSection (a : Fin 2 → ℂ) : ProjectiveHolomorphicSection where
  toSection := projectiveLinearSection a
  holomorphic := differentiable_projectiveLinearSection_chart_coefficient a

end SGPT.Toric

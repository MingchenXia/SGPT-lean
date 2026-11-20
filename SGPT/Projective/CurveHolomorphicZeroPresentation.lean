import SGPT.Projective.CurveDivisorPointMass
import Mathlib.Analysis.Analytic.Order

/-! Every actual nonzero holomorphic curve germ at a zero manufactures
its actual regular multiplicity presentation and isolated original zero.
Blueprint: curve-holomorphic-zero-presentation.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open DivisorRegularLocus

/-- The literal original unique complex coordinate, with its actual inverse. -/
def curveScalarCoordinate : ComplexModel 1 ≃L[ℂ] ℂ :=
  PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)

/-- Ordinary actual holomorphy and a nonzero germ PRODUCE the genuine
regular presentation, its exact analytic order and actual one-point zero set. -/
theorem exists_curve_regularPresentation (g : ComplexModel 1 → ℂ) (x : ComplexModel 1)
    (hg : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ g z)
    (hgerm : ∃ᶠ z in 𝓝 x, g z ≠ 0) (hzero : g x = 0) :
    ∃ P : RegularPresentation g x,
      analyticOrderAt (fun z : ℂ => g (curveScalarCoordinate.symm z))
        (curveScalarCoordinate x) = (P.m : ℕ∞) ∧
      ∀ z ∈ P.U, g z = 0 → z = x := by
  let e := curveScalarCoordinate
  let F : ℂ → ℂ := fun z => g (e.symm z)
  have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      e.symm.continuous.continuousAt.tendsto (x := e x)
  have hF : AnalyticAt ℂ F (e x) := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [ht.eventually hg] with z hz
    exact hz.comp z e.symm.differentiableAt
  have hFne : ¬ ∀ᶠ z in 𝓝 (e x), F z = 0 := by
    intro h
    have hgz : ∀ᶠ z in 𝓝 x, g z = 0 := by
      simpa only [F, ContinuousLinearEquiv.symm_apply_apply] using
        e.continuous.continuousAt.tendsto.eventually h
    exact hgerm (hgz.mono fun _ hz hne => hne hz)
  obtain ⟨k, v, hv, hvne, hfac⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hFne
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    have hh := hfac.self_of_nhds
    have hx0 : F (e x) = 0 := by simpa only [F, ContinuousLinearEquiv.symm_apply_apply] using hzero
    rw [hk0, pow_zero, one_smul, hx0] at hh
    exact hvne hh.symm
  have hvdiff : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ (fun y => v (e y)) z := by
    filter_upwards [e.continuous.continuousAt.tendsto.eventually
      (Complex.analyticAt_iff_eventually_differentiableAt.mp hv)] with z hz
    exact hz.comp z e.differentiableAt
  have hvnonzero : ∀ᶠ z in 𝓝 x, v (e z) ≠ 0 :=
    e.continuous.continuousAt.tendsto.eventually
      (hv.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hvne))
  have hfactor : ∀ᶠ z in 𝓝 x, g z = (e z - e x) ^ k * v (e z) := by
    simpa only [F, ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul] using
      e.continuous.continuousAt.tendsto.eventually hfac
  obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp ((hvdiff.and hvnonzero).and hfactor)
  have he : e.toContinuousLinearMap ≠ 0 := by
    intro he0
    have he1 := congrArg (fun T : ComplexModel 1 →L[ℂ] ℂ => T (e.symm 1)) he0
    exact one_ne_zero (by simpa only [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] using he1)
  let P : RegularPresentation g x := {
    U := U
    isOpen := hUopen
    mem := hxU
    m := k
    m_pos := hk
    h := fun z => e z - e x
    v := fun z => v (e z)
    h_diff := (e.differentiable.sub_const (e x)).differentiableOn
    v_diff := fun z hz => ((hU z hz).1.1).differentiableWithinAt
    h_zero := sub_self _
    dh_ne := fun z _ => by
      rw [fderiv_sub_const]
      simpa only [ContinuousLinearEquiv.fderiv] using he
    v_ne := fun z hz => (hU z hz).1.2
    eq := fun z hz => (hU z hz).2 }
  refine ⟨P, hF.analyticOrderAt_eq_natCast.mpr ⟨v, hv, hvne, hfac⟩, ?_⟩
  intro z hz hgz
  apply e.injective
  exact sub_eq_zero.mp ((P.g_eq_zero_iff hz).mp hgz)

end SGPT.Projective.NumEq.AlgebraicCurveDegree

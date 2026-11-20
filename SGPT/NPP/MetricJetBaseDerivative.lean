import SGPT.NPP.MetricJetOverlap
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Actual base derivatives of a smooth family with vanishing fibre jets

Blueprint first: `dnt-big-metric-jet-base-derivative.tex`. This manufactures
first-base derivative bounds from identities of the actual family, rather
than differentiating a mere value inequality. It is auxiliary calculus;
no global Chern family or envelope regularity is asserted.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

section Partial
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The literal first partial derivative with respect to the actual base. -/
def basePartial (F : E × E → G) (q : E × E) : E →L[ℝ] G :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ E E)

/-- The literal first partial derivative with respect to the actual tangent variable. -/
def fiberPartial (F : E × E → G) (q : E × E) : E →L[ℝ] G :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ E E)

theorem fderiv_base_slice {F : E × E → G} {z v : E}
    (hF : DifferentiableAt ℝ F (z, v)) :
    fderiv ℝ (fun a => F (a, v)) z = basePartial F (z, v) := by
  exact (hF.hasFDerivAt.comp z
    ((hasFDerivAt_id z).prodMk (hasFDerivAt_const v z))).fderiv

theorem fderiv_fiber_slice {F : E × E → G} {z v : E}
    (hF : DifferentiableAt ℝ F (z, v)) :
    fderiv ℝ (fun a => F (z, a)) v = fiberPartial F (z, v) := by
  exact (hF.hasFDerivAt.comp v
    ((hasFDerivAt_const z v).prodMk (hasFDerivAt_id v))).fderiv

/-- Joint smoothness of the literal derivative fields on the same actual open set. -/
theorem contDiffOn_basePartial
    {F : E × E → G} {W : Set (E × E)} (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) : ContDiffOn ℝ ∞ (basePartial F) W := by
  have H : ContDiffOn ℝ ∞ (fderiv ℝ F) W := hF.fderiv_of_isOpen hW (by simp)
  exact H.clm_comp contDiffOn_const

theorem contDiffOn_fiberPartial
    {F : E × E → G} {W : Set (E × E)} (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) : ContDiffOn ℝ ∞ (fiberPartial F) W := by
  have H : ContDiffOn ℝ ∞ (fderiv ℝ F) W := hF.fderiv_of_isOpen hW (by simp)
  exact H.clm_comp contDiffOn_const

/-- Symmetry of the actual second derivative commutes the actual partials. -/
theorem fiberPartial_basePartial_eq_flip
    {F : E × E → G} {q : E × E} (hF : ContDiffAt ℝ 2 F q) :
    fiberPartial (basePartial F) q = (basePartial (fiberPartial F) q).flip := by
  have hd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) q) q :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hb := hd.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inl ℝ E E) q)
  have hv := hd.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inr ℝ E E) q)
  change HasFDerivAt (basePartial F) _ q at hb
  change HasFDerivAt (fiberPartial F) _ q at hv
  apply ContinuousLinearMap.ext
  intro b
  apply ContinuousLinearMap.ext
  intro a
  simp only [fiberPartial, basePartial, hb.fderiv, hv.fderiv,
    ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.zero_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, map_zero, zero_add,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  exact (hF.isSymmSndFDerivAt (by norm_num [minSmoothness])) (0, b) (a, 0)

/-- Actual second derivative of a fibre slice, using equality on the actual open set. -/
theorem second_fderiv_fiber_slice
    {F : E × E → G} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ V)) {z v : E} (hz : z ∈ U) (hv : v ∈ V) :
    fderiv ℝ (fderiv ℝ (fun a => F (z, a))) v =
      fiberPartial (fiberPartial F) (z, v) := by
  have heq : fderiv ℝ (fun a => F (z, a)) =ᶠ[𝓝 v]
      fun a => fiberPartial F (z, a) := by
    filter_upwards [hV.mem_nhds hv] with a ha
    exact fderiv_fiber_slice (((hF.differentiableOn (by simp)).differentiableAt
      ((hU.prod hV).mem_nhds ⟨hz, ha⟩)))
  rw [heq.fderiv_eq]
  exact fderiv_fiber_slice (((contDiffOn_fiberPartial (hU.prod hV) hF).differentiableOn
    (by simp)).differentiableAt ((hU.prod hV).mem_nhds ⟨hz, hv⟩))

/-- A literal zero base slice has literal zero base derivative. -/
theorem basePartial_eq_zero_of_slice_zero
    {F : E × E → G} {U : Set E} (hU : IsOpen U) {z v : E} (hz : z ∈ U)
    (hF : DifferentiableAt ℝ F (z, v)) (hzero : ∀ a ∈ U, F (a, v) = 0) :
    basePartial F (z, v) = 0 := by
  have heq : (fun a => F (a, v)) =ᶠ[𝓝 z] (fun _ => (0 : G)) := by
    filter_upwards [hU.mem_nhds hz] with a ha
    exact hzero a ha
  rw [← fderiv_base_slice hF, heq.fderiv_eq]
  simp only [fderiv_const_apply]


/-- The actual first base derivative inherits the actual vanishing fibre
two-jet, by actual mixed derivative commutation on a neighbourhood. -/
theorem basePartial_zero_fiber_two_jet
    {F : E × E → G} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ V)) (h0V : (0 : E) ∈ V)
    (hzero : ∀ z ∈ U, F (z, 0) = 0)
    (hVzero : ∀ z ∈ U, fiberPartial F (z, 0) = 0)
    (hVVzero : ∀ z ∈ U, fiberPartial (fiberPartial F) (z, 0) = 0)
    {z : E} (hz : z ∈ U) :
    basePartial F (z, 0) = 0 ∧
      fiberPartial (basePartial F) (z, 0) = 0 ∧
      fiberPartial (fiberPartial (basePartial F)) (z, 0) = 0 := by
  have hW := hU.prod hV
  have hq : (z, (0 : E)) ∈ U ×ˢ V := ⟨hz, h0V⟩
  have hVF := contDiffOn_fiberPartial hW hF
  have hVVF := contDiffOn_fiberPartial hW hVF
  have hBVF := contDiffOn_basePartial hW hVF
  have hF2 : ContDiffAt ℝ 2 F (z, (0 : E)) :=
    (hF.contDiffAt (hW.mem_nhds hq)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hVF2 : ContDiffAt ℝ 2 (fiberPartial F) (z, (0 : E)) :=
    (hVF.contDiffAt (hW.mem_nhds hq)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hBF0 : basePartial F (z, (0 : E)) = 0 :=
    basePartial_eq_zero_of_slice_zero hU hz
      ((hF.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hq)) hzero
  have hBVF0 : basePartial (fiberPartial F) (z, (0 : E)) = 0 :=
    basePartial_eq_zero_of_slice_zero hU hz
      ((hVF.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hq)) hVzero
  have hBVVF0 : basePartial (fiberPartial (fiberPartial F)) (z, (0 : E)) = 0 :=
    basePartial_eq_zero_of_slice_zero hU hz
      ((hVVF.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hq)) hVVzero
  have hVBVF0 : fiberPartial (basePartial (fiberPartial F)) (z, (0 : E)) = 0 := by
    rw [fiberPartial_basePartial_eq_flip hVF2, hBVVF0]
    simp
  refine ⟨hBF0, ?_, ?_⟩
  · rw [fiberPartial_basePartial_eq_flip hF2, hBVF0]
    simp
  · have heq : fiberPartial (basePartial F) =ᶠ[𝓝 (z, (0 : E))]
        fun q => (basePartial (fiberPartial F) q).flip := by
      filter_upwards [hW.mem_nhds hq] with q hq
      exact fiberPartial_basePartial_eq_flip
        ((hF.contDiffAt (hW.mem_nhds hq)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    change (fderiv ℝ (fiberPartial (basePartial F)) (z, 0)).comp
      (ContinuousLinearMap.inr ℝ E E) = 0
    rw [heq.fderiv_eq]
    let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E G).toContinuousLinearEquiv.toContinuousLinearMap
    have H := flipL.hasFDerivAt.comp (z, (0 : E))
      (((hBVF.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hq)).hasFDerivAt)
    change HasFDerivAt (fun q => (basePartial (fiberPartial F) q).flip) _ (z, 0) at H
    rw [H.fderiv]
    apply ContinuousLinearMap.ext
    intro c
    apply ContinuousLinearMap.ext
    intro b
    apply ContinuousLinearMap.ext
    intro a
    have hh := congrArg (fun T => T c a b) hVBVF0
    change (fderiv ℝ (basePartial (fiberPartial F)) (z, 0)
      ((ContinuousLinearMap.inr ℝ E E) c)) a b = 0
    simpa only [fiberPartial, ContinuousLinearMap.comp_apply, _root_.zero_apply] using hh

end Partial


/-- A manufactured cubic bound for the actual first base derivative follows
from actual identities on a neighbourhood, not from differentiating a value bound. -/
theorem exists_local_cubic_base_derivative_bound_of_zero_two_jet
    {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ComplexModel n × ComplexModel n → G} {U V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F (U ×ˢ V))
    (h0V : (0 : ComplexModel n) ∈ V)
    (hzero : ∀ z ∈ U, F (z, 0) = 0)
    (hVzero : ∀ z ∈ U, fiberPartial F (z, 0) = 0)
    (hVVzero : ∀ z ∈ U, fiberPartial (fiberPartial F) (z, 0) = 0)
    {z : ComplexModel n} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : ComplexModel n) r ⊆ V ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ v ∈ closedBall (0 : ComplexModel n) r,
        ‖basePartial F (z, v)‖ ≤ M * ‖v‖ ^ 3 := by
  have hW := hU.prod hV
  have hBF := contDiffOn_basePartial hW hF
  have hVBF := contDiffOn_fiberPartial hW hBF
  have hslice : ContDiffOn ℝ 3 (fun v => basePartial F (z, v)) V :=
    (hBF.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨hz, hv⟩)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  obtain ⟨h0, h1, h2⟩ := basePartial_zero_fiber_two_jet hU hV hF h0V hzero hVzero hVVzero hz
  have hd1 : fderiv ℝ (fun v => basePartial F (z, v)) 0 = 0 := by
    rw [fderiv_fiber_slice
      ((hBF.differentiableOn (by simp)).differentiableAt (hW.mem_nhds ⟨hz, h0V⟩)), h1]
  have hd2 : fderiv ℝ (fderiv ℝ (fun v => basePartial F (z, v))) 0 = 0 := by
    rw [second_fderiv_fiber_slice hU hV hBF hz h0V, h2]
  obtain ⟨r, hr, hrV, M, hM, hbound⟩ :=
    exists_local_cubic_bound_of_zero_two_jet hV hslice h0V h0 hd1 hd2
  exact ⟨r, hr, hrV, M, hM, fun v hv => (hbound v hv).2⟩

end SGPT.NPP.DNTBig

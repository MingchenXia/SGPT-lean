import SGPT.Bergman.SiuUniformGenerationGauge

/-!
# Descent of the actual smooth frame's logarithmic `∂̄` form

The logarithmic form is defined using the original preferred frame at each
point.  Its equality with the form in every fixed atlas frame is proved from
the actual scalar transition.  This gives smoothness and closedness on the
whole prescribed coordinate domain, rather than an assumed gauge certificate.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Bundle Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.LineBundle.TMetric SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {L : HermitianHolomorphicLineBundle.{0, 0} n X}

def smoothFrameCoefficient (c : ComplexChart n X) (s : (x : X) → L.Fiber x)
    (e : AtlasFrame L) (z : ComplexModel n) : ℂ :=
  e.val.continuousLinearMapAt ℂ (c.val.symm z) (s (c.val.symm z))

theorem isOpen_chart_frameDomain (c : ComplexChart n X) {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hDt : D ⊆ c.val.target) (e : AtlasFrame L) :
    IsOpen (D ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  have heq : D ∩ c.val.symm ⁻¹' e.val.baseSet =
      D ∩ (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
    ext z
    exact ⟨fun hz => ⟨hz.1, hDt hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
  rw [heq]
  exact hD.inter (c.val.isOpen_inter_preimage_symm e.val.open_baseSet)

theorem smoothFrameCoefficient_ne_zero
    (c : ComplexChart n X) {D : Set (ComplexModel n)} (hDt : D ⊆ c.val.target)
    (s : (x : X) → L.Fiber x)
    (hs0 : ∀ x ∈ c.val.source ∩ c.val ⁻¹' D, s x ≠ 0)
    (e : AtlasFrame L) {z : ComplexModel n} (hz : z ∈ D) (hze : c.val.symm z ∈ e.val.baseSet) :
    smoothFrameCoefficient c s e z ≠ 0 := by
  let := e.property
  have hx0 : s (c.val.symm z) ≠ 0 := hs0 _
    ⟨c.val.map_target (hDt hz), by simpa only [mem_preimage, c.val.right_inv (hDt hz)] using hz⟩
  intro hzero
  have heq := trivialization_eq_coef_smul_frame e.val hze (s (c.val.symm z))
  change s (c.val.symm z) = smoothFrameCoefficient c s e z • e.val.symm (c.val.symm z) 1 at heq
  rw [hzero, zero_smul] at heq
  exact hx0 heq

/-- The actual section coefficient transforms by the actual holomorphic unit. -/
theorem smoothFrameCoefficient_transition
    (c : ComplexChart n X) (s : (x : X) → L.Fiber x) (e f : AtlasFrame L)
    {z : ComplexModel n} (he : c.val.symm z ∈ e.val.baseSet)
    (hf : c.val.symm z ∈ f.val.baseSet) :
    smoothFrameCoefficient c s e z =
      frameTransition f e (c.val.symm z) * smoothFrameCoefficient c s f z := by
  let := e.property
  let := f.property
  have hrepr := trivialization_eq_coef_smul_frame f.val hf (s (c.val.symm z))
  have hcoef : e.val.continuousLinearMapAt ℂ (c.val.symm z) (f.val.symm (c.val.symm z) 1) =
      frameTransition f e (c.val.symm z) := by
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val he]
    exact (Trivialization.coordChangeL_apply f.val e.val ⟨hf, he⟩ 1).symm
  unfold smoothFrameCoefficient
  conv_lhs => rw [hrepr]
  rw [map_smul, smul_eq_mul, hcoef, mul_comm]

/-- The scalar form is defined at every point from original atlas data. -/
def smoothFrameGauge (c : ComplexChart n X) (s : (x : X) → L.Fiber x)
    (j : Fin n) (z : ComplexModel n) : ℂ :=
  logarithmicDbar (smoothFrameCoefficient c s (prefFrame L (c.val.symm z))) j z

/-- Its equality with the logarithmic form in every fixed atlas frame proves
that the point-indexed definition has no frame dependence. -/
theorem smoothFrameGauge_eq
    (c : ComplexChart n X) {D : Set (ComplexModel n)} (hD : IsOpen D) (hDt : D ⊆ c.val.target)
    (s : (x : X) → L.Fiber x)
    (hs : ∀ e : AtlasFrame L, ContDiffOn ℝ ∞ (smoothFrameCoefficient c s e)
      (D ∩ c.val.symm ⁻¹' e.val.baseSet))
    (hs0 : ∀ x ∈ c.val.source ∩ c.val ⁻¹' D, s x ≠ 0)
    (e : AtlasFrame L) (j : Fin n) {z : ComplexModel n}
    (hz : z ∈ D) (hze : c.val.symm z ∈ e.val.baseSet) :
    smoothFrameGauge c s j z = logarithmicDbar (smoothFrameCoefficient c s e) j z := by
  let f := prefFrame L (c.val.symm z)
  have hzf : c.val.symm z ∈ f.val.baseSet := mem_prefFrame L _
  have hfg : smoothFrameCoefficient c s f =ᶠ[𝓝 z]
      fun w => frameTransition e f (c.val.symm w) * smoothFrameCoefficient c s e w := by
    filter_upwards [(c.val.isOpen_inter_preimage_symm
      (f.val.open_baseSet.inter e.val.open_baseSet)).mem_nhds ⟨hDt hz, hzf, hze⟩] with w hw
    exact smoothFrameCoefficient_transition c s f e hw.2.1 hw.2.2
  have hg : DifferentiableAt ℝ (smoothFrameCoefficient c s e) z :=
    ((hs e).contDiffAt ((isOpen_chart_frameDomain c hD hDt e).mem_nhds ⟨hz, hze⟩)).differentiableAt
      (by simp)
  have hh : DifferentiableAt ℂ (fun w => frameTransition e f (c.val.symm w)) z :=
    FactorizedWeightForm.differentiableAt_comp_chart_symm c (hDt hz)
      (frameTransition_mdifferentiableAt e f ⟨hze, hzf⟩)
  exact logarithmicDbar_eq_of_holomorphic_factor hg hh hfg
    (smoothFrameCoefficient_ne_zero c hDt s hs0 f hz hzf)
    (smoothFrameCoefficient_ne_zero c hDt s hs0 e hz hze) j

theorem smoothFrameGauge_eventuallyEq
    (c : ComplexChart n X) {D : Set (ComplexModel n)} (hD : IsOpen D) (hDt : D ⊆ c.val.target)
    (s : (x : X) → L.Fiber x)
    (hs : ∀ e : AtlasFrame L, ContDiffOn ℝ ∞ (smoothFrameCoefficient c s e)
      (D ∩ c.val.symm ⁻¹' e.val.baseSet))
    (hs0 : ∀ x ∈ c.val.source ∩ c.val ⁻¹' D, s x ≠ 0)
    (e : AtlasFrame L) (j : Fin n) {z : ComplexModel n}
    (hz : z ∈ D) (hze : c.val.symm z ∈ e.val.baseSet) :
    smoothFrameGauge c s j =ᶠ[𝓝 z] logarithmicDbar (smoothFrameCoefficient c s e) j := by
  filter_upwards [(isOpen_chart_frameDomain c hD hDt e).mem_nhds ⟨hz, hze⟩] with w hw
  exact smoothFrameGauge_eq c hD hDt s hs hs0 e j hw.1 hw.2

theorem contDiffOn_smoothFrameGauge
    (c : ComplexChart n X) {D : Set (ComplexModel n)} (hD : IsOpen D) (hDt : D ⊆ c.val.target)
    (s : (x : X) → L.Fiber x)
    (hs : ∀ e : AtlasFrame L, ContDiffOn ℝ ∞ (smoothFrameCoefficient c s e)
      (D ∩ c.val.symm ⁻¹' e.val.baseSet))
    (hs0 : ∀ x ∈ c.val.source ∩ c.val ⁻¹' D, s x ≠ 0)
    (j : Fin n) : ContDiffOn ℝ ∞ (smoothFrameGauge c s j) D := by
  intro z hz
  let e := prefFrame L (c.val.symm z)
  have hze : c.val.symm z ∈ e.val.baseSet := mem_prefFrame L _
  have hU := isOpen_chart_frameDomain c hD hDt e
  have hlocal := contDiffOn_logarithmicDbar hU (hs e)
    (fun w hw => smoothFrameCoefficient_ne_zero c hDt s hs0 e hw.1 hw.2) j
  exact ((hlocal.contDiffAt (hU.mem_nhds ⟨hz, hze⟩)).congr_of_eventuallyEq
    (smoothFrameGauge_eventuallyEq c hD hDt s hs hs0 e j hz hze)).contDiffWithinAt

theorem isDbarClosedOn_smoothFrameGauge
    (c : ComplexChart n X) {D : Set (ComplexModel n)} (hD : IsOpen D) (hDt : D ⊆ c.val.target)
    (s : (x : X) → L.Fiber x)
    (hs : ∀ e : AtlasFrame L, ContDiffOn ℝ ∞ (smoothFrameCoefficient c s e)
      (D ∩ c.val.symm ⁻¹' e.val.baseSet))
    (hs0 : ∀ x ∈ c.val.source ∩ c.val ⁻¹' D, s x ≠ 0) :
    IsDbarClosedOn (smoothFrameGauge c s) D := by
  intro i j z hz
  let e := prefFrame L (c.val.symm z)
  have hze : c.val.symm z ∈ e.val.baseSet := mem_prefFrame L _
  have heq (k : Fin n) := smoothFrameGauge_eventuallyEq c hD hDt s hs hs0 e k hz hze
  change dbarDir (coordVec i) (smoothFrameGauge c s j) z =
    dbarDir (coordVec j) (smoothFrameGauge c s i) z
  rw [dbarDir_congr (heq j), dbarDir_congr (heq i)]
  exact isDbarClosedOn_logarithmicDbar (isOpen_chart_frameDomain c hD hDt e) (hs e)
    (fun w hw => smoothFrameCoefficient_ne_zero c hDt s hs0 e hw.1 hw.2) i j z ⟨hz, hze⟩

end SGPT.Bergman.SiuUniformGeneration

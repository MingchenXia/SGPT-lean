import SGPT.Trace.TwistedL2FunctionalTwistedDatumLocalYoungDraft
import SGPT.PSH.GlobalL2CoverSystem
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Frame transitions and the flat model `X = ℂⁿ`

Blueprint `claude-tl2-main.tex` (lane TL2-MAIN, package E1.B, the main twisted estimate on
open sets of `ℂⁿ`).  This file collects the bookkeeping needed to read a finite family of local
test pieces `h_i ⊗ e_i` (each in its own frame `e_i` of `L`) as one global `L`-valued vector field.

* `frameTrans L e e' x`: the coefficient of the frame vector of `e` in the frame `e'`, so that
  `e(x) = frameTrans e e' x • e'(x)` on the overlap (`frame_eq_frameTrans_smul`); it is
  nonvanishing, satisfies the cocycle rule, relates the frame norms and the coefficients of
  sections, and is holomorphic in chart coordinates (`differentiableOn_frameTrans`).
* On `X = ℂⁿ` (the model space with its unique atlas chart `chart0`): every atlas chart is the
  identity (`chart_eq`), and the chart density of a smooth positive volume is unique
  (`chartDensity_unique`).
* `transp e₀ e h`: the coefficient field, in the frame `e`, of the local piece `h ⊗ e₀`
  (`h` written in the frame `e₀`).  It is smooth on the base set of `e` and transforms by
  `frameTrans` under a change of the target frame (`transp_eventuallyEq`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

section Frames

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The coefficient of the frame vector of `e` in the frame `e'`:
`e(x) = frameTrans L e e' x • e'(x)` on `base e ∩ base e'`. -/
def frameTrans (e e' : AtlasFrame L) (x : X) : ℂ :=
  frameCoeff L e' (fun y => e.val.symm y 1) x

variable {L}

theorem frame_eq_frameTrans_smul (e e' : AtlasFrame L) {x : X}
    (hx : x ∈ e.val.baseSet ∩ e'.val.baseSet) :
    e.val.symm x 1 = frameTrans L e e' x • e'.val.symm x 1 :=
  eq_frameCoeff_smul e' hx.2 _

theorem frameTrans_self (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) :
    frameTrans L e e x = 1 :=
  frameCoeff_symm_one e hx

theorem frameTrans_ne_zero (e e' : AtlasFrame L) {x : X}
    (hx : x ∈ e.val.baseSet ∩ e'.val.baseSet) : frameTrans L e e' x ≠ 0 := by
  intro h0
  have h := frame_eq_frameTrans_smul e e' hx
  rw [h0, zero_smul] at h
  exact frame_ne_zero e hx.1 h

/-- The cocycle rule `t_{e e''} = t_{e e'} t_{e' e''}`. -/
theorem frameTrans_mul (e e' e'' : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet)
    (hx' : x ∈ e'.val.baseSet) (hx'' : x ∈ e''.val.baseSet) :
    frameTrans L e e'' x = frameTrans L e e' x * frameTrans L e' e'' x := by
  have h := frame_eq_frameTrans_smul e e' ⟨hx, hx'⟩
  change (e''.val ⟨x, e.val.symm x 1⟩).2 = _
  rw [h, frameCoeff_smul_apply e'' hx'']
  rfl

theorem frameTrans_mul_symm (e e' : AtlasFrame L) {x : X}
    (hx : x ∈ e.val.baseSet ∩ e'.val.baseSet) :
    frameTrans L e e' x * frameTrans L e' e x = 1 := by
  rw [← frameTrans_mul e e' e hx.1 hx.2 hx.1, frameTrans_self e hx.1]

theorem frameNormSq_eq_frameTrans (e e' : AtlasFrame L) {x : X}
    (hx : x ∈ e.val.baseSet ∩ e'.val.baseSet) :
    frameNormSq L e x = ‖frameTrans L e e' x‖ ^ 2 * frameNormSq L e' x := by
  simp only [frameNormSq]
  rw [frame_eq_frameTrans_smul e e' hx, norm_smul, mul_pow]

/-- Coefficients of a section in two frames: `G_{e'} = t_{e e'} G_e`. -/
theorem frameCoeff_eq_frameTrans_mul (e e' : AtlasFrame L) (G : (x : X) → L.Fiber x) {x : X}
    (hx : x ∈ e.val.baseSet ∩ e'.val.baseSet) :
    frameCoeff L e' G x = frameTrans L e e' x * frameCoeff L e G x := by
  have hG := eq_frameCoeff_smul e hx.1 (G x)
  have h := frame_eq_frameTrans_smul e e' hx
  change (e'.val ⟨x, G x⟩).2 = _
  conv_lhs => rw [hG, h, smul_smul]
  rw [frameCoeff_smul_apply e' hx.2, frameCoeff_symm_one e' hx.2, mul_one]
  change _ = _ * (e.val ⟨x, G x⟩).2
  ring

theorem frameTrans_eq_continuousLinearMapAt (e e' : AtlasFrame L) {x : X}
    (hx : x ∈ e'.val.baseSet) :
    frameTrans L e e' x = e'.val.continuousLinearMapAt ℂ x (e.val.symm x 1) := by
  have := e'.property
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e'.val hx]
  rfl

/-- Frame transitions are holomorphic in chart coordinates. -/
theorem differentiableOn_frameTrans (c : ComplexChart n X) (e e' : AtlasFrame L) :
    DifferentiableOn ℂ (fun z => frameTrans L e e' (c.val.symm z))
      (c.val.target ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ e'.val.baseSet)) := by
  have := e.property
  have := e'.property
  refine (SGPT.PSH.GlobalL2.differentiableOn_coef_frame e.val e'.val c
    (S := c.val.target ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ e'.val.baseSet))
    inter_subset_left fun z hz => hz.2).congr fun z hz => ?_
  exact frameTrans_eq_continuousLinearMapAt e e' hz.2.2

end Frames

/-! ### The model space `ℂⁿ` -/

section Model

variable {n : ℕ}

/-- The unique chart of the atlas of the model space `ℂⁿ`. -/
def chart0 : ComplexChart n (ComplexModel n) :=
  ⟨OpenPartialHomeomorph.refl _, chartedSpaceSelf_atlas.mpr rfl⟩

theorem chart_eq (c : ComplexChart n (ComplexModel n)) : c = chart0 :=
  Subtype.ext (chartedSpaceSelf_atlas.mp c.property)

@[simp] theorem chart0_symm_apply (z : ComplexModel n) : (chart0 (n := n)).val.symm z = z := rfl

@[simp] theorem chart0_apply (z : ComplexModel n) : (chart0 (n := n)).val z = z := rfl

@[simp] theorem chart0_target : (chart0 (n := n)).val.target = univ := rfl

@[simp] theorem chart0_source : (chart0 (n := n)).val.source = univ := rfl

/-- A chart density on `ℂⁿ` is a density of the volume itself. -/
theorem measure_eq_withDensity {μ : Measure (ComplexModel n)} {c : ComplexChart n (ComplexModel n)}
    {ρ : ComplexModel n → ℝ} (h : IsChartDensity μ c ρ) :
    μ = volume.withDensity (fun z => ENNReal.ofReal (ρ z)) := by
  obtain rfl := chart_eq c
  have h3 := h.2.2
  simp only [chart0_source, chart0_target, Measure.restrict_univ] at h3
  rw [← h3]
  exact (Measure.map_id).symm

theorem continuous_of_isChartDensity {μ : Measure (ComplexModel n)}
    {c : ComplexChart n (ComplexModel n)} {ρ : ComplexModel n → ℝ} (h : IsChartDensity μ c ρ) :
    Continuous ρ := by
  obtain rfl := chart_eq c
  have := h.1.continuousOn
  rw [chart0_target] at this
  exact continuousOn_univ.mp this

theorem pos_of_isChartDensity {μ : Measure (ComplexModel n)}
    {c : ComplexChart n (ComplexModel n)} {ρ : ComplexModel n → ℝ} (h : IsChartDensity μ c ρ)
    (z : ComplexModel n) : 0 < ρ z := by
  obtain rfl := chart_eq c
  exact h.2.1 z (by simp)

/-- **Uniqueness of chart densities on `ℂⁿ`.** -/
theorem chartDensity_unique {μ : Measure (ComplexModel n)}
    {c c' : ComplexChart n (ComplexModel n)} {ρ ρ' : ComplexModel n → ℝ}
    (h : IsChartDensity μ c ρ) (h' : IsChartDensity μ c' ρ') : ρ = ρ' := by
  have hc := continuous_of_isChartDensity h
  have hc' := continuous_of_isChartDensity h'
  have heq : volume.withDensity (fun z => ENNReal.ofReal (ρ z)) =
      volume.withDensity (fun z => ENNReal.ofReal (ρ' z)) :=
    (measure_eq_withDensity h).symm.trans (measure_eq_withDensity h')
  have hae : (fun z => ENNReal.ofReal (ρ z)) =ᵐ[volume] fun z => ENNReal.ofReal (ρ' z) :=
    (withDensity_eq_iff_of_sigmaFinite (ENNReal.measurable_ofReal.comp hc.measurable).aemeasurable
      (ENNReal.measurable_ofReal.comp hc'.measurable).aemeasurable).mp heq
  have hae' : ρ =ᵐ[volume] ρ' := hae.mono fun z hz => by
    have h1 := pos_of_isChartDensity h z
    have h2 := pos_of_isChartDensity h' z
    exact (ENNReal.ofReal_eq_ofReal_iff h1.le h2.le).mp hz
  exact (Continuous.ae_eq_iff_eq volume hc hc').mp hae'

end Model

/-! ### Transport of local pieces between frames on `ℂⁿ` -/

section Transport

variable {n : ℕ} (L : HermitianHolomorphicLineBundle.{0, 0} n (ComplexModel n))

open Classical in
/-- The coefficient field, in the frame `e`, of the piece `h ⊗ e₀`. -/
def transp (e₀ e : AtlasFrame L) (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    ComplexModel n :=
  if z ∈ e₀.val.baseSet then frameTrans L e₀ e z • h z else 0

variable {L}

theorem differentiableOn_frameTrans_model (e e' : AtlasFrame L) :
    DifferentiableOn ℂ (frameTrans L e e') (e.val.baseSet ∩ e'.val.baseSet) := by
  exact (differentiableOn_frameTrans (L := L) chart0 e e').mono fun z hz => ⟨trivial, hz⟩

theorem contDiffOn_frameTrans (e e' : AtlasFrame L) :
    ContDiffOn ℝ ∞ (frameTrans L e e') (e.val.baseSet ∩ e'.val.baseSet) := by
  have hO : IsOpen (e.val.baseSet ∩ e'.val.baseSet) := e.val.open_baseSet.inter e'.val.open_baseSet
  exact contDiffOn_real_of_differentiableOn_complex (differentiableOn_frameTrans_model e e') hO

theorem transp_eq_zero_of_notMem {e₀ e : AtlasFrame L} {h : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hz : z ∉ tsupport h) : transp L e₀ e h z = 0 := by
  unfold transp
  split_ifs
  · rw [image_eq_zero_of_notMem_tsupport hz, smul_zero]
  · rfl

theorem tsupport_transp_subset (e₀ e : AtlasFrame L) (h : ComplexModel n → ComplexModel n) :
    tsupport (transp L e₀ e h) ⊆ tsupport h := by
  apply closure_minimal _ (isClosed_tsupport h)
  intro z hz
  by_contra hn
  exact hz (transp_eq_zero_of_notMem hn)

/-- Near a point outside `tsupport h` the transported field vanishes. -/
theorem transp_eventuallyEq_zero {e₀ e : AtlasFrame L} {h : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hz : z ∉ tsupport h) : transp L e₀ e h =ᶠ[𝓝 z] 0 := by
  filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hz] with y hy
  exact transp_eq_zero_of_notMem hy

theorem eventuallyEq_zero_of_notMem_tsupport {h : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hz : z ∉ tsupport h) : h =ᶠ[𝓝 z] 0 := by
  filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hz] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

/-- Near a point of `base e₀ ∩ base e`, the transport is `t • h`. -/
theorem transp_eventuallyEq_smul {e₀ e : AtlasFrame L} (h : ComplexModel n → ComplexModel n)
    {z : ComplexModel n} (hz : z ∈ e₀.val.baseSet) :
    transp L e₀ e h =ᶠ[𝓝 z] fun y => frameTrans L e₀ e y • h y := by
  filter_upwards [e₀.val.open_baseSet.mem_nhds hz] with y hy
  classical
  simp only [transp, if_pos hy]

theorem contDiffOn_transp {e₀ e : AtlasFrame L} {h : ComplexModel n → ComplexModel n}
    (hh : ContDiff ℝ ∞ h) (hts : tsupport h ⊆ e₀.val.baseSet) :
    ContDiffOn ℝ ∞ (transp L e₀ e h) e.val.baseSet := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hz₀ : z ∈ e₀.val.baseSet
  · have hO : IsOpen (e₀.val.baseSet ∩ e.val.baseSet) :=
      e₀.val.open_baseSet.inter e.val.open_baseSet
    have ht : ContDiffAt ℝ ∞ (frameTrans L e₀ e) z :=
      (contDiffOn_frameTrans e₀ e).contDiffAt (hO.mem_nhds ⟨hz₀, hz⟩)
    exact (ht.smul hh.contDiffAt).congr_of_eventuallyEq (transp_eventuallyEq_smul h hz₀)
  · have hz' : z ∉ tsupport h := fun h' => hz₀ (hts h')
    exact contDiffAt_const.congr_of_eventuallyEq (transp_eventuallyEq_zero hz')

/-- The transport into the frame of the piece itself is the piece. -/
theorem transp_self {e₀ : AtlasFrame L} {h : ComplexModel n → ComplexModel n}
    (hts : tsupport h ⊆ e₀.val.baseSet) : transp L e₀ e₀ h = h := by
  funext z
  unfold transp
  split_ifs with hz
  · rw [frameTrans_self e₀ hz, one_smul]
  · exact (image_eq_zero_of_notMem_tsupport fun h' => hz (hts h')).symm

/-- **Change of target frame**: near `z ∈ base e ∩ base e'`, the transport into `e'` is
`t_{e e'}` times the transport into `e`. -/
theorem transp_eventuallyEq (e₀ e e' : AtlasFrame L) (h : ComplexModel n → ComplexModel n)
    {z : ComplexModel n} (hz : z ∈ e.val.baseSet ∩ e'.val.baseSet) :
    transp L e₀ e' h =ᶠ[𝓝 z] fun y => frameTrans L e e' y • transp L e₀ e h y := by
  filter_upwards [(e.val.open_baseSet.inter e'.val.open_baseSet).mem_nhds hz] with y hy
  unfold transp
  split_ifs with h₀
  · rw [smul_smul, frameTrans_mul e₀ e e' h₀ hy.1 hy.2, mul_comm (frameTrans L e e' y)]
  · rw [smul_zero]

/-- Near `z ∈ base e ∩ base e₀` a piece is `t_{e e₀}` times its transport into `e`. -/
theorem eventuallyEq_frameTrans_smul_transp {e₀ e : AtlasFrame L}
    {h : ComplexModel n → ComplexModel n} (hts : tsupport h ⊆ e₀.val.baseSet)
    {z : ComplexModel n} (hz : z ∈ e.val.baseSet ∩ e₀.val.baseSet) :
    h =ᶠ[𝓝 z] fun y => frameTrans L e e₀ y • transp L e₀ e h y := by
  have := transp_eventuallyEq e₀ e e₀ h hz
  rwa [transp_self hts] at this

end Transport

end SGPT.Trace.TwistedL2

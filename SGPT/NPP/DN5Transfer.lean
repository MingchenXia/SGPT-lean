import SGPT.NPP.DN5Fibre
import SGPT.NPP.DN2LogChart
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-!
# Joint Levi forms under coordinate changes

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, proof, first paragraph: "All bounds are
uniform over the centers, because the constructions are made in the charts of a fixed finite
atlas").  The joint Levi bound `SGPT.NPP.DN2.JointLeviLowerBound` is read in every chart and for
every local potential of `θ`; the Levi form is natural under the holomorphic map
`(z, w) ↦ (τ(z), w)` (`τ` a coordinate change) and two local potentials differ by a pluriharmonic
function.  Hence a bound in one chart, for one potential, gives the bound in every chart, for every
potential (`jointLeviLowerBound_of_chart`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NPP.DN2

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Levi forms -/

section Levi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem leviForm_congr {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) (a : E) :
    leviForm u x a = leviForm v x a := by
  have h1 : fderiv ℝ u =ᶠ[𝓝 x] fderiv ℝ v := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ u) x = fderiv ℝ (fderiv ℝ v) x := h1.fderiv_eq
  simp only [leviForm, realHessian_eq_fderiv, h2]

/-- The Levi form of a function of the first factor. -/
theorem leviForm_comp_fst {ρ : E → ℝ} {z : E} (hρ : ContDiffAt ℝ 2 ρ z) (w : ℂ) (v : E) (η : ℂ) :
    leviForm (fun p : E × ℂ => ρ p.1) (z, w) (v, η) = leviForm ρ z v := by
  have h := leviForm_comp_holomorphic (Φ := Prod.fst) (u := ρ) (p := (z, w))
    contDiffAt_fst hρ (v, η)
  rw [h, fderiv_fst]
  rfl

/-- The Levi form of `(z, w) ↦ ‖w‖²` is `‖η‖²`. -/
theorem leviForm_normSq_snd (z : E) (w : ℂ) (v : E) (η : ℂ) :
    leviForm (fun p : E × ℂ => ‖p.2‖ ^ 2) (z, w) (v, η) = ‖η‖ ^ 2 := by
  have hu : ContDiffAt ℝ 2 (fun y : ℂ => ‖y‖ ^ 2) w := (contDiff_norm_sq ℝ).contDiffAt
  have h := leviForm_comp_holomorphic (Φ := Prod.snd) (u := fun y : ℂ => ‖y‖ ^ 2) (p := (z, w))
    contDiffAt_snd hu (v, η)
  rw [h, fderiv_snd]
  exact leviForm_norm_sq w η

end Levi

/-! ### Potentials and forms under coordinate changes -/

/-- The Levi form of a local potential of `θ` is `π θ(v, iv)`. -/
theorem leviForm_potential {θ : SmoothRealForm N Y 2} {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ} (hρ : IsSmoothLocalPotential θ e W ρ)
    {z : ComplexModel N} (hz : z ∈ W) (v : ComplexModel N) :
    leviForm ρ z v = Real.pi * θ.coeff e z ![v, Complex.I • v] := by
  have hρz : ContDiffAt ℝ 2 ρ z :=
    (hρ.2.2.1.contDiffAt (hρ.1.mem_nhds hz)).of_le (by norm_cast)
  have h := smoothDDC_complexDiagonal_eq_leviForm hρz v
  rw [hρ.2.2.2 hz] at h
  rw [h]
  field_simp

/-- A two-form evaluated on `(v, iv)` under a coordinate change. -/
theorem coeff_apply_I_transition (β : SmoothRealForm N Y 2) {e e' : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ (chartTransition e e').source) (v : ComplexModel N) :
    β.coeff e z ![v, Complex.I • v] =
      β.coeff e' (chartTransition e e' z)
        ![chartTransitionDerivative e e' z v, Complex.I • chartTransitionDerivative e e' z v] := by
  rw [β.compatible e e' z hz]
  congr 1
  funext i
  fin_cases i
  · rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact chartTransitionDerivative_complex_smul e e' z hz Complex.I v

theorem chartNormSq_transition (wY : KahlerBackground N Y) {e e' : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ (chartTransition e e').source) (v : ComplexModel N) :
    chartNormSq wY e z v = chartNormSq wY e' (chartTransition e e' z)
      (chartTransitionDerivative e e' z v) :=
  coeff_apply_I_transition wY.form.val hz v

/-! ### The joint function in a chart -/

/-- The joint function `(z, w) ↦ H(e⁻¹ z, |w|)` in the chart `e` (without potential). -/
def jointFun (H : Y → ℝ → ℝ) (e : ComplexChart N Y) : ComplexModel N × ℂ → ℝ :=
  fun p => H (e.val.symm p.1) ‖p.2‖

theorem chartJoint_eq (H : Y → ℝ → ℝ) (e : ComplexChart N Y) (ρ : ComplexModel N → ℝ) :
    chartJoint H e ρ = fun p => jointFun H e p + ρ p.1 := rfl

theorem jointFun_eventuallyEq_transition (H : Y → ℝ → ℝ) {e e' : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ (chartTransition e e').source) (w : ℂ) :
    jointFun H e =ᶠ[𝓝 (z, w)] fun p => jointFun H e' (chartTransition e e' p.1, p.2) := by
  have hev : ∀ᶠ p : ComplexModel N × ℂ in 𝓝 (z, w), p.1 ∈ (chartTransition e e').source :=
    continuous_fst.continuousAt.preimage_mem_nhds ((chartTransition e e').open_source.mem_nhds hz)
  filter_upwards [hev] with p hp
  have hp' := mem_transition_source_iff.mp hp
  simp only [jointFun, transition_apply, e'.val.left_inv hp'.2]

/-- **Naturality of the joint Levi form under a coordinate change.** -/
theorem leviForm_jointFun_transition (H : Y → ℝ → ℝ) {e e' : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ (chartTransition e e').source) {w : ℂ}
    (hJ : ContDiffAt ℝ 2 (jointFun H e') (chartTransition e e' z, w)) (v : ComplexModel N)
    (η : ℂ) :
    ContDiffAt ℝ 2 (jointFun H e) (z, w) ∧
      leviForm (jointFun H e) (z, w) (v, η) =
        leviForm (jointFun H e') (chartTransition e e' z, w)
          (chartTransitionDerivative e e' z v, η) := by
  let Φ : ComplexModel N × ℂ → ComplexModel N × ℂ := fun p => (chartTransition e e' p.1, p.2)
  have hτ : ContDiffAt ℂ ∞ (chartTransition e e') z :=
    HolomorphicMaps.chartTransition_contDiffAt e e' hz
  have hΦ : ContDiffAt ℂ 2 Φ (z, w) :=
    ((hτ.of_le (by norm_cast)).comp (z, w) contDiffAt_fst).prodMk contDiffAt_snd
  have hev : jointFun H e =ᶠ[𝓝 (z, w)] (jointFun H e' ∘ Φ) :=
    jointFun_eventuallyEq_transition H hz w
  refine ⟨?_, ?_⟩
  · exact (hJ.comp (z, w) (hΦ.restrict_scalars ℝ)).congr_of_eventuallyEq hev
  · rw [leviForm_congr hev]
    have h := leviForm_comp_holomorphic (Φ := Φ) (u := jointFun H e') (p := (z, w)) hΦ hJ (v, η)
    rw [show (jointFun H e' ∘ Φ) = fun q => jointFun H e' (Φ q) from rfl, h]
    congr 1
    have h1 := (hτ.differentiableAt (by simp)).hasFDerivAt.comp (z, w)
      (hasFDerivAt_fst (𝕜 := ℂ) (p := (z, w)))
    have hd := h1.prodMk (hasFDerivAt_snd (𝕜 := ℂ) (p := (z, w)))
    have hd' : HasFDerivAt Φ (((fderiv ℂ (chartTransition e e') z).comp
        (ContinuousLinearMap.fst ℂ (ComplexModel N) ℂ)).prod
          (ContinuousLinearMap.snd ℂ (ComplexModel N) ℂ)) (z, w) := hd
    rw [hd'.fderiv, transitionDerivative_apply_eq_complex hz]
    rfl

/-- **Transfer of the joint Levi bound**: a bound at `(τ z, w)` in the chart `e'`, for one local
potential, gives `JointLeviLowerBound` at `(z, w)` in the chart `e` (for every local potential). -/
theorem jointLeviLowerBound_of_chart (θ : ClosedRealOneOneForm N Y) (wY : KahlerBackground N Y)
    (H : Y → ℝ → ℝ) {e e' : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ (chartTransition e e').source) {w : ℂ}
    (hJ : ContDiffAt ℝ 2 (jointFun H e') (chartTransition e e' z, w))
    {W' : Set (ComplexModel N)} {ρ' : ComplexModel N → ℝ} (hzW' : chartTransition e e' z ∈ W')
    (hρ' : IsSmoothLocalPotential θ.val e' W' ρ') {a₁ a₂ a₃ : ℝ}
    (hb : ∀ (v : ComplexModel N) (η : ℂ),
      -(a₁ * chartNormSq wY e' (chartTransition e e' z) v) -
          a₂ * Real.sqrt (chartNormSq wY e' (chartTransition e e' z) v) * ‖η‖ - a₃ * ‖η‖ ^ 2 ≤
        leviForm (chartJoint H e' ρ') (chartTransition e e' z, w) (v, η)) :
    JointLeviLowerBound θ wY H e z w a₁ a₂ a₃ := by
  intro W ρ hzW hρ v η
  set z' := chartTransition e e' z
  set D := chartTransitionDerivative e e' z
  obtain ⟨hJe, hlevi⟩ := leviForm_jointFun_transition H hz hJ v η
  have hρz : ContDiffAt ℝ 2 ρ z := (hρ.2.2.1.contDiffAt (hρ.1.mem_nhds hzW)).of_le (by norm_cast)
  have hρ'z : ContDiffAt ℝ 2 ρ' z' :=
    (hρ'.2.2.1.contDiffAt (hρ'.1.mem_nhds hzW')).of_le (by norm_cast)
  have hρ1 : ContDiffAt ℝ 2 (fun p : ComplexModel N × ℂ => ρ p.1) (z, w) :=
    hρz.comp (z, w) contDiffAt_fst
  have hρ'1 : ContDiffAt ℝ 2 (fun p : ComplexModel N × ℂ => ρ' p.1) (z', w) :=
    hρ'z.comp (z', w) contDiffAt_fst
  have hsum : leviForm (chartJoint H e ρ) (z, w) (v, η) =
      leviForm (jointFun H e) (z, w) (v, η) + leviForm ρ z v := by
    rw [chartJoint_eq]
    have h := leviForm_add hJe hρ1 (v, η)
    rw [← leviForm_comp_fst hρz w v η]
    exact h
  have hsum' : leviForm (chartJoint H e' ρ') (z', w) (D v, η) =
      leviForm (jointFun H e') (z', w) (D v, η) + leviForm ρ' z' (D v) := by
    rw [chartJoint_eq]
    have h := leviForm_add hJ hρ'1 (D v, η)
    rw [← leviForm_comp_fst hρ'z w (D v) η]
    exact h
  have hpot : leviForm ρ z v = leviForm ρ' z' (D v) := by
    rw [leviForm_potential hρ hzW, leviForm_potential hρ' hzW',
      coeff_apply_I_transition θ.val hz v]
  have hnorm : chartNormSq wY e z v = chartNormSq wY e' z' (D v) :=
    chartNormSq_transition wY hz v
  rw [hsum, hlevi, hpot, ← hsum', hnorm]
  exact hb (D v) η

/-- The same chart, another potential. -/
theorem jointLeviLowerBound_of_potential (θ : ClosedRealOneOneForm N Y)
    (wY : KahlerBackground N Y) (H : Y → ℝ → ℝ) {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) {w : ℂ} (hJ : ContDiffAt ℝ 2 (jointFun H e) (z, w))
    {W' : Set (ComplexModel N)} {ρ' : ComplexModel N → ℝ} (hzW' : z ∈ W')
    (hρ' : IsSmoothLocalPotential θ.val e W' ρ') {a₁ a₂ a₃ : ℝ}
    (hb : ∀ (v : ComplexModel N) (η : ℂ),
      -(a₁ * chartNormSq wY e z v) - a₂ * Real.sqrt (chartNormSq wY e z v) * ‖η‖ -
          a₃ * ‖η‖ ^ 2 ≤ leviForm (chartJoint H e ρ') (z, w) (v, η)) :
    JointLeviLowerBound θ wY H e z w a₁ a₂ a₃ := by
  have hzs : z ∈ (chartTransition e e).source :=
    mem_transition_source_iff.mpr ⟨hz, e.val.map_target hz⟩
  have hτ : chartTransition e e z = z := by
    simp only [transition_apply, e.val.right_inv hz]
  have hD : chartTransitionDerivative e e z = ContinuousLinearMap.id ℝ _ :=
    transitionDerivative_self hz
  refine jointLeviLowerBound_of_chart θ wY H hzs (by rw [hτ]; exact hJ) (by rw [hτ]; exact hzW')
    hρ' ?_
  intro v η
  rw [hτ]
  exact hb v η

end SGPT.NPP.DN5

import SGPT.PSH.GlobalL2CoverBasics
import SGPT.Foundations.Analysis.Pending.ThetaPshChartLimitGluing
import SGPT.Foundations.Analysis.Pending.LocalPotentials

/-!
# Local criteria for `θ`-plurisubharmonicity

Blueprint `claude-global-l2b.tex`, node `claude-global-l2b:transfer`.  Tools for the pole
functions of `claude-global-l2:point-pole`:

* `thetaPlurisubharmonic_of_local`: the `θ`-psh criterion (`ThetaPlurisubharmonic`, which tests
  *every* atlas chart) follows from ONE chart at every point: a chart `d` at `y`, an open
  `W ∋ d(y)`, a smooth local potential `ρ` of `θ` on `W` with `u ∘ d⁻¹ + ρ` psh on `W`.  (Chart
  transitions are holomorphic, local potentials transport along them, and psh functions pull back
  by holomorphic maps.)
* `exists_kahler_potential`: near every chart point, `B ω` has a smooth local potential `ρ` with
  `Levi(ρ)(v) = π B ω(v, iv)`.
* `plurisubharmonicOn_coe_add_coe`: a smooth function plus a smooth potential, with nonnegative
  total Levi form, is psh.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **One chart at every point suffices for `θ`-plurisubharmonicity.** -/
theorem thetaPlurisubharmonic_of_local {θ : SmoothRealForm n M 2} {u : M → EReal}
    (h : ∀ y : M, ∃ (d : ComplexChart n M) (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ),
      y ∈ d.val.source ∧ d.val y ∈ W ∧ IsSmoothLocalPotential θ d W ρ ∧
      PlurisubharmonicOn (fun w => chartFunction u d w + (ρ w : EReal)) W) :
    ThetaPlurisubharmonic θ u := by
  intro e z hz
  obtain ⟨d, W, ρ, hyd, hyW, hρ, hpsh⟩ := h (e.val.symm z)
  set F := chartTransition e d with hF
  have hzF : z ∈ F.source := by
    rw [hF, chartTransition, OpenPartialHomeomorph.trans_source]
    exact ⟨by simpa using hz, hyd⟩
  have hFz : F z = d.val (e.val.symm z) :=
    Pending.ThetaPshChartLimitGluing.chartTransition_apply_eq e d z
  set W' : Set (ComplexModel n) := F.source ∩ F ⁻¹' W with hW'
  have hW'o : IsOpen W' := F.isOpen_inter_preimage hρ.1
  refine ⟨W', ρ ∘ F, ⟨hzF, by rw [mem_preimage, hFz]; exact hyW⟩,
    Pending.ThetaPshChartLimitGluing.isSmoothLocalPotential_comp_transition e d hρ, ?_⟩
  have hFd : DifferentiableOn ℂ F W' := fun w hw =>
    ((chartTransition_contDiffAt e d hw.1).differentiableAt (by simp)).differentiableWithinAt
  have hcomp := Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hW'o hFd
    (fun w hw => hw.2) hpsh
  intro w hw
  refine (hcomp w hw).congr ?_
  filter_upwards [hW'o.mem_nhds hw] with w' hw'
  have hsrc : e.val.symm w' ∈ d.val.source := by
    have := hw'.1
    rw [hF, chartTransition, OpenPartialHomeomorph.trans_source] at this
    exact this.2
  simp only [chartFunction, Function.comp_apply]
  rw [Pending.ThetaPshChartLimitGluing.chartTransition_apply_eq e d w', d.val.left_inv hsrc]

/-- **Local potentials of `B ω`** with the Levi form `π B ω(v, iv)`. -/
theorem exists_kahler_potential (ωb : KahlerBackground n M) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) (B : ℝ) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ), z ∈ W ∧
      IsSmoothLocalPotential (B • ωb.form).val e W ρ ∧
      ∀ w ∈ W, ∀ v : ComplexModel n,
        leviForm ρ w v = Real.pi * B * ωb.form.val.coeff e w ![v, Complex.I • v] := by
  obtain ⟨W, ρ₀, hzW, hρ₀⟩ :=
    Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials ωb.form e z hz
  have hsm : ContDiffOn ℝ ∞ (fun y => B * ρ₀ y) W := contDiffOn_const.mul hρ₀.2.2.1
  have hddc : ∀ w ∈ W, smoothDDC (fun y => B * ρ₀ y) w = (B • ωb.form).val.coeff e w := by
    intro w hw
    have := smoothDDC_smul hρ₀.1 hρ₀.2.2.1 B hw
    simp only [smul_eq_mul] at this
    rw [this, hρ₀.2.2.2 hw, ClosedRealOneOneForm.coeff_smul]
  refine ⟨W, fun y => B * ρ₀ y, hzW, ⟨hρ₀.1, hρ₀.2.1, hsm, fun w hw => hddc w hw⟩,
    fun w hw v => ?_⟩
  have h2 : ContDiffAt ℝ 2 (fun y => B * ρ₀ y) w :=
    ((hsm w hw).contDiffAt (hρ₀.1.mem_nhds hw)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdiag := smoothDDC_complexDiagonal_eq_leviForm h2 v
  rw [hddc w hw, ClosedRealOneOneForm.coeff_smul] at hdiag
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hdiag
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at hdiag
  linarith

/-- A smooth function plus a smooth function, with nonnegative total Levi form, is psh. -/
theorem plurisubharmonicOn_coe_add_coe {W : Set (ComplexModel n)} (hW : IsOpen W)
    {f ρ : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f W) (hρ : ContDiffOn ℝ ∞ ρ W)
    (hlev : ∀ w ∈ W, ∀ v : ComplexModel n, 0 ≤ leviForm f w v + leviForm ρ w v) :
    PlurisubharmonicOn (fun w => (f w : EReal) + (ρ w : EReal)) W := by
  have h := plurisubharmonicOn_of_contDiffOn_levi_nonneg hW (u := f + ρ) (hf.add hρ)
    (fun w hw v => by
      have h2 : ∀ {g : ComplexModel n → ℝ}, ContDiffOn ℝ ∞ g W → ContDiffAt ℝ 2 g w := fun hg =>
        ((hg w hw).contDiffAt (hW.mem_nhds hw)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      rw [leviForm_add (h2 hf) (h2 hρ)]
      exact hlev w hw v)
  intro w hw
  refine (h w hw).congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, EReal.coe_add]

/-- A potential with nonnegative Levi form is psh. -/
theorem plurisubharmonicOn_coe_of_levi_nonneg {W : Set (ComplexModel n)} (hW : IsOpen W)
    {ρ : ComplexModel n → ℝ} (hρ : ContDiffOn ℝ ∞ ρ W)
    (hlev : ∀ w ∈ W, ∀ v : ComplexModel n, 0 ≤ leviForm ρ w v) :
    PlurisubharmonicOn (fun w => (ρ w : EReal)) W :=
  plurisubharmonicOn_of_contDiffOn_levi_nonneg hW hρ hlev

/-- A constant plus a potential of `B ω` (`B ≥ 0`) is psh on the domain of the potential. -/
theorem plurisubharmonicOn_const_add_kahler_potential (ωb : KahlerBackground n M)
    {e : ComplexChart n M} {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hρ : IsSmoothLocalPotential (B • ωb.form).val e W ρ)
    (hlev : ∀ w ∈ W, ∀ v : ComplexModel n,
      leviForm ρ w v = Real.pi * B * ωb.form.val.coeff e w ![v, Complex.I • v]) (C : ℝ) :
    PlurisubharmonicOn (fun w => ((C : ℝ) : EReal) + (ρ w : EReal)) W := by
  have h := plurisubharmonicOn_coe_add_coe hρ.1 (f := fun _ => C) contDiffOn_const hρ.2.2.1
    (fun w hw v => by
      rw [leviForm_const, zero_add, hlev w hw v]
      have hω := ωb.isSemipositive e w (hρ.2.1 hw) v
      positivity)
  exact h

end SGPT.PSH.GlobalL2

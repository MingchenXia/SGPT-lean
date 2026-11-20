import SGPT.PSH.GlobalL2Gluing
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence
import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
import SGPT.Foundations.Analysis.FirstPass.HermitianGeometry
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import SGPT.Foundations.Analysis.SmoothPlurisubharmonic
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

/-!
# Elementary inputs for the chart-ball covers

Blueprint `claude-global-l2:cover`, `claude-global-l2:local-weights`.  Generic facts used to build
a `GluingSystem` on a compact complex manifold:

* `exists_neg_le_leviForm_of_contDiffOn`: a smooth function has Levi form `≥ -C|ξ|²` on a
  compact set;
* `plurisubharmonicOn_of_contDiffOn_levi_nonneg`: a smooth function with nonnegative Levi form on
  an open set is plurisubharmonic there;
* `exists_lineValue_lower_bound_of_isCompact'`: a Hermitian form is `≥ m|ξ|²` on a compact part of
  a chart (copied from `SGPT.Okounkov.TranscendentalL2`, to keep this layer independent of the
  Okounkov files);
* `plurisubharmonicOn_add_localPotential`: `ρ + φ ∘ e⁻¹` is psh for every smooth local potential
  `ρ` of `θ` and every `θ`-psh `φ` (copied likewise);
* `setLIntegral_chart_ball`: reading a set integral over a chart ball through a smooth positive
  volume, for integrands measurable in the chart.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

/-! ### Levi forms of smooth functions -/

/-- A smooth function has Levi form bounded below by `-C|ξ|²` on every compact subset of its
domain. -/
theorem exists_neg_le_leviForm_of_contDiffOn {U K : Set (ComplexModel n)} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ v : ComplexModel n, -(C * ‖v‖ ^ 2) ≤ leviForm u z v := by
  have hc : ContinuousOn (fun z => iteratedFDeriv ℝ 2 u z) K := fun z hz =>
    ((hu.contDiffAt (hU.mem_nhds (hKU hz))).continuousAt_iteratedFDeriv
      (by norm_cast)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨|B|, abs_nonneg B, fun z hz v => ?_⟩
  have hH : ∀ a : ComplexModel n, |realHessian u z a a| ≤ |B| * ‖a‖ ^ 2 := by
    intro a
    have h := (iteratedFDeriv ℝ 2 u z).le_opNorm ![a, a]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [realHessian, ← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 2 u z ![a, a]‖ ≤ ‖iteratedFDeriv ℝ 2 u z‖ * (‖a‖ * ‖a‖) := h
      _ ≤ |B| * (‖a‖ * ‖a‖) :=
          mul_le_mul_of_nonneg_right ((hB z hz).trans (le_abs_self B)) (by positivity)
      _ = |B| * ‖a‖ ^ 2 := by ring
  have h1 := neg_le_of_abs_le (hH v)
  have h2 := neg_le_of_abs_le (hH (Complex.I • v))
  rw [norm_smul, Complex.norm_I, one_mul] at h2
  rw [leviForm]
  have hB0 : 0 ≤ |B| * ‖v‖ ^ 2 := by positivity
  linarith

/-- A smooth function with nonnegative Levi form on an open set is plurisubharmonic there. -/
theorem plurisubharmonicOn_of_contDiffOn_levi_nonneg {U : Set (ComplexModel n)} (hU : IsOpen U)
    {u : ComplexModel n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hL : ∀ z ∈ U, ∀ v : ComplexModel n, 0 ≤ leviForm u z v) :
    PlurisubharmonicOn (fun z => (u z : EReal)) U := by
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hU hu hx
  have hmem : {y | u y = g y} ∩ U ∈ 𝓝 x := inter_mem heq (hU.mem_nhds hx)
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp hmem
  have heqV : EqOn u g V := fun y hy => (hVsub hy).1
  have hlevi : ∀ y ∈ V, ∀ v : ComplexModel n, 0 ≤ leviForm g y v := by
    intro y hy v
    have hloc : u =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with t ht
      exact heqV ht
    have hH : iteratedFDeriv ℝ 2 u y = iteratedFDeriv ℝ 2 g y :=
      (hloc.iteratedFDeriv ℝ 2).eq_of_nhds
    have : leviForm g y v = leviForm u y v := by
      simp only [leviForm, realHessian, hH]
    rw [this]
    exact hL y (hVsub hy).2 v
  have hpshg : PlurisubharmonicOn (fun y => (g y : EReal)) V :=
    plurisubharmonicOn_of_levi_nonneg (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      hV hlevi
  apply (hpshg x hxV).congr
  filter_upwards [hV.mem_nhds hxV] with y hy
  rw [heqV hy]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A Hermitian form is uniformly positive on a compact piece of a chart** (copied from
`SGPT.Okounkov.TranscendentalL2.exists_lineValue_lower_bound_of_isCompact`). -/
theorem exists_lineValue_lower_bound_of_isCompact' {β : SmoothRealForm n M 2}
    (hβ : β.IsHermitian) (e : ComplexChart n M) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKe : K ⊆ e.val.target) :
    ∃ m : ℝ, 0 < m ∧ ∀ w ∈ K, ∀ v : ComplexModel n,
      m * ‖v‖ ^ 2 ≤ β.coeff e w ![v, Complex.I • v] := by
  refine hK.induction_on (p := fun S => ∃ m : ℝ, 0 < m ∧ ∀ w ∈ S, ∀ v : ComplexModel n,
      m * ‖v‖ ^ 2 ≤ β.coeff e w ![v, Complex.I • v]) ⟨1, one_pos, fun w hw => absurd hw id⟩
    (fun S T hST ⟨m, hm, hT⟩ => ⟨m, hm, fun w hw => hT w (hST hw)⟩)
    (fun S T ⟨m, hm, hS⟩ ⟨m', hm', hT⟩ => ⟨min m m', lt_min hm hm', fun w hw v => ?_⟩) ?_
  · rcases hw with hw | hw
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans (hS w hw v)
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans (hT w hw v)
  · intro w₀ hw₀
    have hw₀t : w₀ ∈ e.val.target := hKe hw₀
    obtain ⟨m, hm, hmle⟩ :=
      SGPT.Foundations.Analysis.Pending.KahlerDomination.exists_lineValue_lower_bound (hβ e w₀ hw₀t).2
    have htgt : e.val.target ∈ 𝓝 w₀ := e.val.open_target.mem_nhds hw₀t
    have hβc : ContinuousAt (β.coeff e) w₀ := ((β.smooth e).continuousOn).continuousAt htgt
    have h1 : ∀ᶠ w in 𝓝 w₀, ‖β.coeff e w - β.coeff e w₀‖ < m / 2 := by
      simpa [dist_eq_norm] using Metric.tendsto_nhds.mp hβc (m / 2) (by positivity)
    refine ⟨{w | ‖β.coeff e w - β.coeff e w₀‖ < m / 2}, mem_nhdsWithin_of_mem_nhds h1,
      m / 2, by positivity, fun w hw v => ?_⟩
    have hv2 : (0 : ℝ) ≤ ‖v‖ ^ 2 := by positivity
    have hsplit : β.coeff e w ![v, Complex.I • v]
        = β.coeff e w₀ ![v, Complex.I • v]
          + (β.coeff e w - β.coeff e w₀) ![v, Complex.I • v] := by simp
    have hdrift := neg_le_of_abs_le (SGPT.Foundations.Analysis.Pending.KahlerDomination.abs_lineValue_le
      (β.coeff e w - β.coeff e w₀) v)
    have := hmle v
    have hw' : ‖β.coeff e w - β.coeff e w₀‖ < m / 2 := hw
    nlinarith [mul_le_mul_of_nonneg_right hw'.le hv2]

/-- `ρ + φ ∘ e⁻¹` is psh on `W` for a smooth local potential `ρ` of `θ` on `W` (copied from
`SGPT.Okounkov.TranscendentalL2.plurisubharmonicOn_localPotential_add`). -/
theorem plurisubharmonicOn_add_localPotential {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (hφ : IsThetaPshPotential θ φ) (d : ComplexChart n M) {W : Set (ComplexModel n)}
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ d W ρ) :
    PlurisubharmonicOn (fun x => (ρ x : EReal) + φ (d.val.symm x)) W := by
  intro x hx
  obtain ⟨W', ρ', hxW', hρ', hpsh⟩ := hφ.1 d x (hρ.2.1 hx)
  have hWo : IsOpen (W ∩ W') := hρ.1.inter hρ'.1
  have hsm : ContDiffOn ℝ ∞ (fun y => ρ y - ρ' y) (W ∩ W') :=
    (hρ.2.2.1.mono inter_subset_left).sub (hρ'.2.2.1.mono inter_subset_right)
  have hzero : ∀ y ∈ W ∩ W', smoothDDC (fun y => ρ y - ρ' y) y = 0 := by
    intro y hy
    rw [PositiveClasses.smoothDDC_sub hWo (hρ.2.2.1.mono inter_subset_left)
      (hρ'.2.2.1.mono inter_subset_right) hy, hρ.2.2.2 hy.1, hρ'.2.2.2 hy.2, sub_self]
  have hph := plurisubharmonicOn_coe_of_smoothDDC_eq_zero hWo hsm hzero
  have hadd := (hpsh.mono inter_subset_right).add hph
  obtain ⟨U, hU, hxU, hdisc⟩ := hadd x ⟨hx, hxW'⟩
  refine ⟨U ∩ (W ∩ W'), hU.inter hWo, ⟨hxU, hx, hxW'⟩, (hdisc.mono inter_subset_left).congr ?_⟩
  intro y _
  show (chartFunction φ d y + (ρ' y : EReal)) + ((ρ y - ρ' y : ℝ) : EReal) =
    (ρ y : EReal) + φ (d.val.symm y)
  rw [add_assoc, ← EReal.coe_add, add_sub_cancel, add_comm]
  rfl

/-! ### Reading integrals in a chart -/

variable [MeasurableSpace M] [BorelSpace M]

/-- **Reading a set integral in a chart.**  If `μ` is `ρ(z) dz` in the chart `e`, then for an open
`B` inside the chart target and every `f ≥ 0` measurable in the chart,
`∫_{e⁻¹(B)} f dμ = ∫_B f(e⁻¹ z) ρ(z) dz`. -/
theorem setLIntegral_chart_ball {μ : Measure M} (e : ComplexChart n M)
    {ρ : ComplexModel n → ℝ} (hρc : ContinuousOn ρ e.val.target)
    (hmap : Measure.map e.val (μ.restrict e.val.source) =
      (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {B : Set (ComplexModel n)} (hB : IsOpen B) (hBt : B ⊆ e.val.target)
    {f : M → ℝ≥0∞} (hf : AEMeasurable (fun z => f (e.val.symm z)) (volume.restrict B)) :
    ∫⁻ x in e.val.source ∩ e.val ⁻¹' B, f x ∂μ =
      ∫⁻ z in B, f (e.val.symm z) * ENNReal.ofReal (ρ z) := by
  set ν := μ.restrict e.val.source with hν
  have hBm : MeasurableSet B := hB.measurableSet
  have he : AEMeasurable e.val ν :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hmapB : Measure.map e.val (ν.restrict (e.val ⁻¹' B)) =
      (volume.restrict B).withDensity (fun z => ENNReal.ofReal (ρ z)) := by
    rw [← Measure.restrict_map_of_aemeasurable he hBm, hmap, restrict_withDensity hBm,
      Measure.restrict_restrict hBm, inter_eq_left.mpr hBt]
  have hρ : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict B) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hρc.mono hBt)).aemeasurable hBm
  have hS : MeasurableSet (e.val.source ∩ e.val ⁻¹' B) :=
    (e.val.isOpen_inter_preimage hB).measurableSet
  calc ∫⁻ x in e.val.source ∩ e.val ⁻¹' B, f x ∂μ
      = ∫⁻ x in e.val.source ∩ e.val ⁻¹' B, f (e.val.symm (e.val x)) ∂μ :=
        setLIntegral_congr_fun hS fun x hx => by rw [e.val.left_inv hx.1]
    _ = ∫⁻ x, f (e.val.symm (e.val x)) ∂(ν.restrict (e.val ⁻¹' B)) := by
        rw [hν, Measure.restrict_restrict' e.val.open_source.measurableSet, inter_comm]
    _ = ∫⁻ z, f (e.val.symm z) ∂(Measure.map e.val (ν.restrict (e.val ⁻¹' B))) := by
        refine (lintegral_map' (f := fun z => f (e.val.symm z)) ?_ he.restrict).symm
        rw [hmapB]
        exact hf.mono_ac (withDensity_absolutelyContinuous _ _)
    _ = ∫⁻ z in B, f (e.val.symm z) * ENNReal.ofReal (ρ z) := by
        rw [hmapB, lintegral_withDensity_eq_lintegral_mul₀ hρ hf]
        refine lintegral_congr fun z => ?_
        simp only [Pi.mul_apply]
        ring

end SGPT.PSH.GlobalL2

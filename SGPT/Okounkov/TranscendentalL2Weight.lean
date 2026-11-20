import SGPT.Okounkov.TranscendentalL2Statement
import SGPT.Okounkov.TranscendentalL2Pushdown
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.DivisorMetric
import SGPT.Foundations.Analysis.Pending.GlobalRelativeJacobianIdeal
import SGPT.Foundations.Analysis.Pending.LeviFormHolomorphicComp
import SGPT.Foundations.Analysis.Pending.PointPoleExtension
import SGPT.Foundations.Analysis.Pending.WeightedWirtingerAdjoint

/-!
# Weights on a modification: Levi bounds in charts

Plan `tok/RELGEN3` step P6 and the generic part of P8 (blueprint `l2:volume-weight`,
`l2:transported-weight`, chapter `claude-tok-l2`).

* `leviForm_ge_of_thetaPlurisubharmonicOn`: a `θ`-psh function which is smooth near a chart
  point has Levi form `≥ -π θ(v, iv)` there.
* `exists_real_weight_of_isDivisorMetric`: the weight of a divisor metric is a smooth real
  function near every point where it is finite.
* `exists_lineValue_lower_bound_of_isCompact`: a Kähler form is uniformly positive on a compact
  piece of a chart.
* `dbarDir_comp_of_differentiableAt`: `∂̄` commutes with holomorphic changes of variables.
* the relative Jacobian divisor: its weight `Γ = ψ_R` (for a metric given by
  `DivisorMetric.exists_divisorMetric`) is finite off the exceptional set and
  `|det D(d ∘ π ∘ e⁻¹)|² e^{-Γ}` is bounded above and below near every point
  (`exists_jacobian_weight_bounds`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalL2

open Set Filter MeasureTheory Metric Complex
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending

section Generic

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Levi form of a smooth `θ`-psh function** (blueprint `l2:transported-weight`): if `u` is
`θ`-psh over `Ω` and its chart expression is a smooth real function `uℝ` on an open set `O`, then
`Levi uℝ (w)(v) ≥ -π θ_e(w)(v, iv)` at the points of `O` lying over `Ω`. -/
theorem leviForm_ge_of_thetaPlurisubharmonicOn {θ : SmoothRealForm n M 2} {u : M → EReal}
    {Ω : Set M} (hu : ThetaPlurisubharmonicOn θ u Ω) (e : ComplexChart n M)
    {O : Set (ComplexModel n)} (hO : IsOpen O) {uℝ : ComplexModel n → ℝ}
    (hs : ContDiffOn ℝ ∞ uℝ O) (heq : ∀ w ∈ O, chartFunction u e w = (uℝ w : EReal))
    {w : ComplexModel n} (hw : w ∈ O) (hwt : w ∈ e.val.target) (hwΩ : e.val.symm w ∈ Ω)
    (v : ComplexModel n) :
    -(Real.pi * θ.coeff e w ![v, Complex.I • v]) ≤ leviForm uℝ w v := by
  obtain ⟨W, ρ, hwW, hρ, hpsh⟩ := hu e w hwt hwΩ
  set U : TopologicalSpace.Opens (ComplexModel n) := ⟨W ∩ O, hρ.1.inter hO⟩ with hU
  have hwU : w ∈ U := ⟨hwW, hw⟩
  have hsU : ContDiffOn ℝ ∞ (fun y => uℝ y + ρ y) U :=
    (hs.mono fun y hy => hy.2).add (hρ.2.2.1.mono fun y hy => hy.1)
  have hpU : PlurisubharmonicOn (fun y => ((uℝ y + ρ y : ℝ) : EReal)) U := by
    intro y hy
    obtain ⟨V, hV, hyV, hdisc⟩ := hpsh y hy.1
    refine ⟨V ∩ (W ∩ O), hV.inter ((hρ.1.inter hO)), ⟨hyV, hy⟩, ?_⟩
    refine (hdisc.mono inter_subset_left).congr ?_
    intro t ht
    show chartFunction u e t + _ = ((uℝ t + ρ t : ℝ) : EReal)
    rw [heq t ht.2.2, EReal.coe_add]
  have h0 := leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hsU hpU hwU v
  have h2u : ContDiffAt ℝ 2 uℝ w :=
    ((hs w hw).contDiffAt (hO.mem_nhds hw)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h2ρ : ContDiffAt ℝ 2 ρ w :=
    ((hρ.2.2.1 w hwW).contDiffAt (hρ.1.mem_nhds hwW)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hadd : leviForm (fun y => uℝ y + ρ y) w v = leviForm uℝ w v + leviForm ρ w v :=
    leviForm_add h2u h2ρ v
  have hρlevi : leviForm ρ w v = Real.pi * θ.coeff e w ![v, Complex.I • v] := by
    have h := smoothDDC_complexDiagonal_eq_leviForm h2ρ v
    rw [hρ.2.2.2 hwW] at h
    rw [h]
    field_simp
  linarith

/-- **The weight of a divisor metric is smooth where it is finite**: near a point `t` with
`ψ_E(t) ≠ -∞`, in any chart at `t`, `ψ_E ∘ e⁻¹` is a smooth real function. -/
theorem exists_real_weight_of_isDivisorMetric {D : EffectiveDivisor n M}
    {E : MeteredEffectiveQDivisor n M} (hE : DivisorMetric.IsDivisorMetric D E) {t : M}
    (ht : E.weight t ≠ ⊥) (e : ComplexChart n M) (hte : t ∈ e.val.source) :
    ∃ O : Set (ComplexModel n), IsOpen O ∧ e.val t ∈ O ∧ O ⊆ e.val.target ∧
      ContDiffOn ℝ ∞ (fun w => (E.weight (e.val.symm w)).toReal) O ∧
      ∀ w ∈ O, E.weight (e.val.symm w) = ((E.weight (e.val.symm w)).toReal : EReal) := by
  obtain ⟨V, hV, htV, g, hg, -, h', hh', hw⟩ := hE t
  have hgt : g t ≠ 0 := by
    intro h0
    apply ht
    rw [hw t htV, generatorLog_eq_log_sum]
    simp [h0]
  have hgc : ContinuousOn g V := hg.continuousOn
  set V' : Set M := V ∩ g ⁻¹' {0}ᶜ with hV'
  have hV'o : IsOpen V' := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  set O : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' V' with hO
  have hOo : IsOpen O := e.val.isOpen_inter_preimage_symm hV'o
  have hform : ∀ w ∈ O, E.weight (e.val.symm w) =
      ((Real.log (‖g (e.val.symm w)‖ ^ 2) + h' (e.val.symm w) : ℝ) : EReal) := by
    intro w hwO
    have hg0 : g (e.val.symm w) ≠ 0 := hwO.2.2
    rw [hw _ hwO.2.1, generatorLog_eq_log_sum]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [ENNReal.log_ofReal_of_pos (by positivity), ← EReal.coe_add]
  have hform' : ∀ w ∈ O, (E.weight (e.val.symm w)).toReal =
      Real.log (‖g (e.val.symm w)‖ ^ 2) + h' (e.val.symm w) := by
    intro w hwO
    rw [hform w hwO, EReal.toReal_coe]
  refine ⟨O, hOo, ⟨e.val.map_source hte, ?_⟩, inter_subset_left, ?_, ?_⟩
  · rw [mem_preimage, e.val.left_inv hte]
    exact ⟨htV, hgt⟩
  · have hgd : DifferentiableOn ℂ (fun w => g (e.val.symm w)) O :=
      (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg).mono
        fun w hw => ⟨hw.1, hw.2.1⟩
    have hgs : ContDiffOn ℝ ∞ (fun w => g (e.val.symm w)) O :=
      (contDiffOn_of_differentiableOn_complex hgd hOo).restrict_scalars ℝ
    have hns : ContDiffOn ℝ ∞ (fun w => ‖g (e.val.symm w)‖ ^ 2) O :=
      (contDiff_norm_sq ℝ).comp_contDiffOn hgs
    have hlog : ContDiffOn ℝ ∞ (fun w => Real.log (‖g (e.val.symm w)‖ ^ 2)) O :=
      hns.log fun w hw => by
        have : g (e.val.symm w) ≠ 0 := hw.2.2
        positivity
    have hhs : ContDiffOn ℝ ∞ (fun w => h' (e.val.symm w)) O :=
      (hh' e).mono fun w hw => ⟨hw.1, hw.2.1⟩
    exact (hlog.add hhs).congr hform'
  · intro w hwO
    rw [hform w hwO, EReal.toReal_coe]

/-- **A Kähler form is uniformly positive on a compact piece of a chart.** -/
theorem exists_lineValue_lower_bound_of_isCompact {β : SmoothRealForm n M 2}
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
    obtain ⟨m, hm, hmle⟩ := KahlerDomination.exists_lineValue_lower_bound (hβ e w₀ hw₀t).2
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
    have hdrift := neg_le_of_abs_le (KahlerDomination.abs_lineValue_le
      (β.coeff e w - β.coeff e w₀) v)
    have := hmle v
    have hw' : ‖β.coeff e w - β.coeff e w₀‖ < m / 2 := hw
    nlinarith [mul_le_mul_of_nonneg_right hw'.le hv2]

/-- **`∂̄` commutes with holomorphic maps**: `∂̄_ξ (f ∘ S)(x) = ∂̄_{DS(x) ξ} f (S x)`. -/
theorem dbarDir_comp_of_differentiableAt {S : ComplexModel n → ComplexModel n}
    {f : ComplexModel n → ℂ} {x : ComplexModel n} (hS : DifferentiableAt ℂ S x)
    (hf : DifferentiableAt ℝ f (S x)) (ξ : ComplexModel n) :
    CauchyGreen.dbarDir ξ (fun y => f (S y)) x =
      CauchyGreen.dbarDir (fderiv ℝ S x ξ) f (S x) := by
  have hSr : HasFDerivAt S ((fderiv ℂ S x).restrictScalars ℝ) x :=
    hS.hasFDerivAt.restrictScalars ℝ
  have hc : fderiv ℝ (fun y => f (S y)) x =
      (fderiv ℝ f (S x)).comp ((fderiv ℂ S x).restrictScalars ℝ) :=
    (hf.hasFDerivAt.comp x hSr).fderiv
  have hSx : fderiv ℝ S x = (fderiv ℂ S x).restrictScalars ℝ := hSr.fderiv
  simp only [CauchyGreen.dbarDir, hc, hSx, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul]

/-- A `θ`-psh function has upper semicontinuous chart expressions over `Ω`. -/
theorem upperSemicontinuousOn_chartFunction_of_thetaPlurisubharmonicOn
    {θ : SmoothRealForm n M 2} {u : M → EReal} {Ω : Set M}
    (hu : ThetaPlurisubharmonicOn θ u Ω) (e : ComplexChart n M) :
    UpperSemicontinuousOn (chartFunction u e) (e.val.target ∩ e.val.symm ⁻¹' Ω) := by
  intro w hw
  obtain ⟨W, ρ, hwW, hρ, hpsh⟩ := hu e w hw.1 hw.2
  have h1 : UpperSemicontinuousAt (fun y => chartFunction u e y + (ρ y : EReal)) w :=
    (hpsh w hwW).upperSemicontinuousAt
  have hρc : ContinuousAt ρ w :=
    (hρ.2.2.1.continuousOn).continuousAt (hρ.1.mem_nhds hwW)
  have h2 : UpperSemicontinuousAt (fun y => ((-ρ y : ℝ) : EReal)) w :=
    (continuous_coe_real_ereal.continuousAt.comp hρc.neg).upperSemicontinuousAt
  have h3 : UpperSemicontinuousAt
      (fun y => (chartFunction u e y + (ρ y : EReal)) + ((-ρ y : ℝ) : EReal)) w :=
    h1.add' h2 (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _)))
  have heq : (fun y => (chartFunction u e y + (ρ y : EReal)) + ((-ρ y : ℝ) : EReal)) =
      chartFunction u e := by
    funext y
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  rw [heq] at h3
  exact h3.upperSemicontinuousWithinAt _

/-- **Chart independence of local weighted integrability over an open set** `Ω` on which the
chart expressions of the weight are upper semicontinuous (TN
`ChartWeightedL2.multiplierIntegrableAt_chart`, with the weight replaced by `⊤` off `Ω`). -/
theorem multiplierIntegrableAt_chart_of_isOpen {u : M → EReal} {Ω : Set M} (hΩ : IsOpen Ω)
    (hu : ∀ e : ComplexChart n M,
      UpperSemicontinuousOn (chartFunction u e) (e.val.target ∩ e.val.symm ⁻¹' Ω))
    {c : ℝ} (hc : c ≠ 0) {g : M → ℂ} (e f : ComplexChart n M) {x : M} (hxΩ : x ∈ Ω)
    (hex : x ∈ e.val.source) (hfx : x ∈ f.val.source)
    (h : MultiplierIntegrableAt (chartFunction u f) c (fun z => g (f.val.symm z))
      (f.val x) volume) :
    MultiplierIntegrableAt (chartFunction u e) c (fun z => g (e.val.symm z)) (e.val x) volume := by
  classical
  set u' : M → EReal := fun t => if t ∈ Ω then u t else ⊤ with hu'
  have hloc : ∀ k : ComplexChart n M, ∀ {y : M}, y ∈ Ω → y ∈ k.val.source →
      chartFunction u' k =ᶠ[𝓝 (k.val y)] chartFunction u k := by
    intro k y hyΩ hyk
    have hmem : k.val.target ∩ k.val.symm ⁻¹' Ω ∈ 𝓝 (k.val y) :=
      (k.val.isOpen_inter_preimage_symm hΩ).mem_nhds
        ⟨k.val.map_source hyk, by rw [mem_preimage, k.val.left_inv hyk]; exact hyΩ⟩
    filter_upwards [hmem] with w hw
    simp only [chartFunction, hu']
    exact if_pos hw.2
  have husc : UpperSemicontinuousOn (chartFunction u' e) (ChartWeightedL2.overlapDomain e f) := by
    intro w hw
    by_cases hwΩ : e.val.symm w ∈ Ω
    · have hwt : w ∈ e.val.target := hw.1
      have hmem : e.val.target ∩ e.val.symm ⁻¹' Ω ∈ 𝓝 w :=
        (e.val.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hwt, hwΩ⟩
      have h1 : UpperSemicontinuousAt (chartFunction u e) w := by
        intro y hy
        have := hu e w ⟨hwt, hwΩ⟩ y hy
        rwa [nhdsWithin_eq_nhds.mpr hmem] at this
      have heq : chartFunction u' e =ᶠ[𝓝 w] chartFunction u e := by
        filter_upwards [hmem] with w' hw'
        simp only [chartFunction, hu']
        exact if_pos hw'.2
      have h2 : UpperSemicontinuousAt (chartFunction u' e) w := by
        intro y hy
        have hy' : chartFunction u e w < y := by
          rwa [← heq.self_of_nhds]
        filter_upwards [h1 y hy', heq] with w' hw' hweq
        rwa [hweq]
      exact h2.upperSemicontinuousWithinAt _
    · intro y hy
      simp only [chartFunction, hu', if_neg hwΩ] at hy
      exact absurd hy (not_lt.mpr le_top)
  have h' : MultiplierIntegrableAt (chartFunction u' f) c (fun z => g (f.val.symm z))
      (f.val x) volume :=
    h.congr (hloc f hxΩ hfx).symm (EventuallyEq.refl _ _)
  have h'' := ChartWeightedL2.multiplierIntegrableAt_chart (u := u') (μ := volume) e f hex hfx
    husc hc h'
  exact h''.congr (hloc e hxΩ hex) (EventuallyEq.refl _ _)

end Generic

section Modification

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

open SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
open SGPT.Foundations.Analysis.Pending.GlobalRelativeJacobianIdeal

/-- The chart expression of a map which is holomorphic at one point is a holomorphic germ
there. -/
theorem coordinateMap_contDiffAt_of_contMDiffAt {f : X → Z} (d : ComplexChart n X)
    (e : ComplexChart n Z) {z : ComplexModel n} (hz : z ∈ coordinateDomain f d e)
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f (d.val.symm z)) :
    ContDiffAt ℂ ∞ (coordinateMap f d e) z := by
  have h := (contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas d.property)
    (IsManifold.subset_maximalAtlas e.property)
    (d.val.map_target hz.1) hz.2).mp hf
  simpa [coordinateMap, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, d.val.right_inv hz.1,
    contDiffWithinAt_univ] using h.2

omit [IsComplexManifold n Z] in
/-- The Jacobian of a change of charts does not vanish. -/
theorem complexJacobian_chartTransition_ne_zero (d d' : ComplexChart n X) {x : ComplexModel n}
    (hx : x ∈ (chartTransition d d').source) :
    complexJacobian (chartTransition d d') x ≠ 0 := by
  have hx' : x ∈ d.val.target ∧ d.val.symm x ∈ d'.val.source := by
    simpa [chartTransition, OpenPartialHomeomorph.trans_source] using hx
  have h := complexJacobian_coordinateMap_ne_zero (π := (id : X → X)) contMDiff_id
    (A := ∅) (B := ∅) (s := id) isClosed_empty isClosed_empty (by simp) contMDiffOn_id
    (fun y _ => rfl) d d' (y := d.val.symm x) (d.val.map_target hx'.1) hx'.2 (by simp)
  rw [d.val.right_inv hx'.1] at h
  exact h

/-- The chain rule for the Jacobian under a change of target chart. -/
theorem complexJacobian_coordinateMap_change_target {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (e : ComplexChart n Z) (d d' : ComplexChart n X) {z : ComplexModel n}
    (hz : z ∈ coordinateDomain π e d) (hz' : z ∈ coordinateDomain π e d') :
    complexJacobian (coordinateMap π e d') z =
      complexJacobian (chartTransition d d') (coordinateMap π e d z) *
        complexJacobian (coordinateMap π e d) z := by
  have heq : coordinateMap π e d' =ᶠ[𝓝 z] (chartTransition d d') ∘ coordinateMap π e d := by
    filter_upwards [(coordinateDomain_isOpen hπ e d).mem_nhds hz] with w hw
    exact coordinateMap_change_target hw
  have hτ := (chartTransition_contDiffAt d d'
    (coordinateMap_mem_transition_source hz hz')).differentiableAt (by simp)
  have hF := (coordinateMap_contDiffAt hπ e d hz).differentiableAt (by simp)
  simp only [complexJacobian]
  rw [heq.fderiv_eq, fderiv_comp z hτ hF, ContinuousLinearMap.det]
  change LinearMap.det ((fderiv ℂ (chartTransition d d') (coordinateMap π e d z)).toLinearMap.comp
    (fderiv ℂ (coordinateMap π e d) z).toLinearMap) = _
  exact LinearMap.det_comp _ _

/-- The Jacobian of a holomorphic germ is continuous at the point. -/
theorem continuousAt_complexJacobian {F : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hF : ContDiffAt ℂ ∞ F z) : ContinuousAt (complexJacobian F) z := by
  have h1 : ContinuousAt (fderiv ℂ F) z :=
    (hF.fderiv_right (m := 0) (by simp)).continuousAt
  exact ContinuousLinearMap.continuous_det.continuousAt.comp h1

/-- **The weight of the relative Jacobian divisor** (blueprint `l2:volume-weight`): if `E_R`
metrizes the relative Jacobian divisor `R` of `π`, then near every point `y`, in a preferred chart
`e` of `Z` and any chart `d` of `X` at `π y`, `|det D(d ∘ π ∘ e⁻¹)|² e^{-ψ_R ∘ e⁻¹}` is bounded
above and below by positive constants at the points where the Jacobian does not vanish, and
`ψ_R` is finite there. -/
theorem exists_jacobian_weight_bounds {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric (actualRelativeJacobianDivisor (n := n) hπ) ER)
    (a : Z) (d : ComplexChart n X) {y : Z} (hya : y ∈ (complexChartAt (n := n) a).val.source)
    (hyd : π y ∈ d.val.source) :
    ∃ O : Set (ComplexModel n), IsOpen O ∧ (complexChartAt (n := n) a).val y ∈ O ∧
      O ⊆ coordinateDomain π (complexChartAt (n := n) a) d ∧ ∃ c C : ℝ, 0 < c ∧
      ∀ w ∈ O, complexJacobian (coordinateMap π (complexChartAt (n := n) a) d) w ≠ 0 →
        ER.weight ((complexChartAt (n := n) a).val.symm w) ≠ ⊥ ∧
        c ≤ Complex.normSq (complexJacobian (coordinateMap π (complexChartAt (n := n) a) d) w) *
          Real.exp (-(ER.weight ((complexChartAt (n := n) a).val.symm w)).toReal) ∧
        Complex.normSq (complexJacobian (coordinateMap π (complexChartAt (n := n) a) d) w) *
          Real.exp (-(ER.weight ((complexChartAt (n := n) a).val.symm w)).toReal) ≤ C := by
  set e := complexChartAt (n := n) a with he
  set d₁ := complexChartAt (n := n) (π y) with hd₁
  set J : Z → ℂ := chartJacobianFunction (n := n) π a (π y) with hJ
  set U₁ : Set Z := e.val.source ∩ π ⁻¹' d₁.val.source with hU₁
  have hU₁o : IsOpen U₁ := e.val.open_source.inter (d₁.val.open_source.preimage hπ.1.continuous)
  have hyU₁ : y ∈ U₁ := ⟨hya, mem_complexChartAt_source (π y)⟩
  have hJd : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) J U₁ := fun t ht =>
    (holomorphicAt_chartJacobianFunction (n := n) hπ.1 a (π y) ht.1 ht.2).self_of_nhds
      |>.mdifferentiableWithinAt
  have hJnz : ∀ W : Set Z, IsOpen W → W ⊆ U₁ → W.Nonempty → ∃ t ∈ W, J t ≠ 0 := by
    rintro W hW hWU ⟨t₀, ht₀⟩
    have hfreq := frequently_chartJacobianFunction_ne_zero (n := n) hπ a (π y) t₀
      (hWU ht₀).1 (hWU ht₀).2
    obtain ⟨t, ht, htW⟩ := (hfreq.and_eventually (hW.mem_nhds ht₀)).exists
    exact ⟨t, htW, ht⟩
  have hgen₁ : ∀ t ∈ U₁, ∀ f, (actualRelativeJacobianDivisor (n := n) hπ).ideal.mem t f ↔
      IsInSpanAt (n := n) (· = J) t f := fun t ht f =>
    mem_relativeJacobianIdeal_iff_chart (n := n) hπ.1 a (π y) ht.1 ht.2 f
  obtain ⟨VR, hVR, hyVR, gR, hgR, hgen₂, h', hh', hw⟩ := hER y
  obtain ⟨V₀, uu, hV₀, hyV₀, hV₀sub, huhol, hune, hgeq⟩ :=
    DivisorMetric.exists_unit_of_generators hU₁o hVR hJd hgR hJnz hgen₁ hgen₂ hyU₁ hyVR
  have hh'c : ContinuousOn h' VR := TranscendentalRelGen.continuousOn_of_chartSmooth hVR hh'
  set T : ComplexModel n → ℂ := complexJacobian (chartTransition d₁ d) with hT
  set q : Z → ℝ := fun t => Complex.normSq (T (d₁.val (π t))) /
    (Complex.normSq (uu t) * Real.exp (h' t)) with hq
  have hyd₁ : π y ∈ d₁.val.source := mem_complexChartAt_source (π y)
  have hsrc : d₁.val (π y) ∈ (chartTransition d₁ d).source := by
    simpa [chartTransition, OpenPartialHomeomorph.trans_source, d₁.val.left_inv hyd₁] using
      ⟨d₁.val.map_source hyd₁, hyd⟩
  have hTy : T (d₁.val (π y)) ≠ 0 := complexJacobian_chartTransition_ne_zero d₁ d hsrc
  have hqy : 0 < q y := by
    have h1 : 0 < Complex.normSq (T (d₁.val (π y))) := Complex.normSq_pos.mpr hTy
    have h2 : 0 < Complex.normSq (uu y) := Complex.normSq_pos.mpr (hune y hyV₀)
    exact div_pos h1 (mul_pos h2 (Real.exp_pos _))
  have hqc : ContinuousAt q y := by
    have hTc : ContinuousAt T (d₁.val (π y)) :=
      continuousAt_complexJacobian (chartTransition_contDiffAt d₁ d hsrc)
    have h0 : ContinuousAt (fun t => d₁.val (π t)) y :=
      (d₁.val.continuousAt hyd₁).comp hπ.1.continuous.continuousAt
    have h1 : ContinuousAt (fun t => T (d₁.val (π t))) y :=
      ContinuousAt.comp (f := fun t => d₁.val (π t)) hTc h0
    have h2 : ContinuousAt uu y := (huhol y hyV₀).continuousAt
    have h3 : ContinuousAt h' y := hh'c.continuousAt (hVR.mem_nhds hyVR)
    have h4 : Complex.normSq (uu y) * Real.exp (h' y) ≠ 0 :=
      (mul_pos (Complex.normSq_pos.mpr (hune y hyV₀)) (Real.exp_pos _)).ne'
    exact (Complex.continuous_normSq.continuousAt.comp h1).div
      ((Complex.continuous_normSq.continuousAt.comp h2).mul
        (Real.continuous_exp.continuousAt.comp h3)) h4
  have hev : ∀ᶠ t in 𝓝 y, q y / 2 < q t ∧ q t < 2 * q y :=
    (hqc.eventually (Ioo_mem_nhds (by linarith) (by linarith)))
  obtain ⟨N₀, hN₀sub, hN₀o, hyN₀⟩ := _root_.mem_nhds_iff.mp hev
  set N : Set Z := N₀ ∩ V₀ ∩ U₁ ∩ π ⁻¹' d.val.source with hN
  have hNo : IsOpen N :=
    ((hN₀o.inter hV₀).inter hU₁o).inter (d.val.open_source.preimage hπ.1.continuous)
  set O : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' N with hO
  have hOo : IsOpen O := e.val.isOpen_inter_preimage_symm hNo
  refine ⟨O, hOo, ⟨e.val.map_source hya, ?_⟩, fun w hw => ⟨hw.1, hw.2.2⟩, q y / 2, 2 * q y,
    by positivity, ?_⟩
  · rw [mem_preimage, e.val.left_inv hya]
    exact ⟨⟨⟨hyN₀, hyV₀⟩, hyU₁⟩, hyd⟩
  intro w hwO hJw
  set t := e.val.symm w with ht
  have htN : t ∈ N := hwO.2
  have hwt : w ∈ e.val.target := hwO.1
  have hte : e.val t = w := e.val.right_inv hwt
  have hdom₁ : w ∈ coordinateDomain π e d₁ := ⟨hwt, htN.1.2.2⟩
  have hdom : w ∈ coordinateDomain π e d := ⟨hwt, htN.2⟩
  have hchain := complexJacobian_coordinateMap_change_target hπ.1 e d₁ d hdom₁ hdom
  have hF₁ : coordinateMap π e d₁ w = d₁.val (π t) := rfl
  have hJt : J t = complexJacobian (coordinateMap π e d₁) w := by
    show complexJacobian (coordinateMap π e d₁) (e.val t) = _
    rw [hte]
  rw [hF₁, ← hJt] at hchain
  have hJt0 : J t ≠ 0 := by
    intro h0
    apply hJw
    rw [hchain, h0, mul_zero]
  have hgRt : gR t = uu t * J t := hgeq t htN.1.1.2
  have hgR0 : gR t ≠ 0 := by rw [hgRt]; exact mul_ne_zero (hune t htN.1.1.2) hJt0
  have hwt' : ER.weight t = ((Real.log (‖gR t‖ ^ 2) + h' t : ℝ) : EReal) := by
    rw [hw t (hV₀sub htN.1.1.2).2, generatorLog_eq_log_sum]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [ENNReal.log_ofReal_of_pos (by positivity), ← EReal.coe_add]
  have hkey : Complex.normSq (complexJacobian (coordinateMap π e d) w) *
      Real.exp (-(ER.weight t).toReal) = q t := by
    have hX : 0 < ‖gR t‖ ^ 2 := by
      have := norm_pos_iff.mpr hgR0
      positivity
    have hexp : Real.exp (-(Real.log (‖gR t‖ ^ 2) + h' t)) =
        (‖gR t‖ ^ 2)⁻¹ * (Real.exp (h' t))⁻¹ := by
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hX]
    have hnorm : ‖gR t‖ ^ 2 = Complex.normSq (uu t) * Complex.normSq (J t) := by
      rw [hgRt, norm_mul, mul_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    rw [hwt', EReal.toReal_coe, hchain, hexp, hnorm, hq]
    simp only
    rw [Complex.normSq_mul]
    have h1 : Complex.normSq (J t) ≠ 0 := (Complex.normSq_pos.mpr hJt0).ne'
    have h2 : Complex.normSq (uu t) ≠ 0 := (Complex.normSq_pos.mpr (hune t htN.1.1.2)).ne'
    field_simp
    rfl
  have hqt := hN₀sub htN.1.1.1
  refine ⟨by rw [hwt']; exact EReal.coe_ne_bot _, ?_, ?_⟩
  · rw [hkey]; exact hqt.1.le
  · rw [hkey]; exact hqt.2.le

/-- **The relative Jacobian weight is finite off the exceptional set.** -/
theorem relJacobianWeight_ne_bot {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {ER : MeteredEffectiveQDivisor n Z}
    (hER : DivisorMetric.IsDivisorMetric (actualRelativeJacobianDivisor (n := n) hπ) ER)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hBc : IsClosed B)
    (hpre : π ⁻¹' B = A)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hleft : ∀ y ∉ A, s (π y) = y) {t : Z} (htA : t ∉ A) : ER.weight t ≠ ⊥ := by
  set e := complexChartAt (n := n) t
  set d := complexChartAt (n := n) (π t)
  have hte : t ∈ e.val.source := mem_complexChartAt_source t
  have htd : π t ∈ d.val.source := mem_complexChartAt_source (π t)
  obtain ⟨O, -, htO, -, c, C, -, hb⟩ := exists_jacobian_weight_bounds hπ hER t d hte htd
  have hJ := complexJacobian_coordinateMap_ne_zero hπ.1 hAc hBc hpre hs hleft e d hte htd htA
  have := (hb _ htO hJ).1
  rwa [e.val.left_inv hte] at this

end Modification

end SGPT.Okounkov.TranscendentalL2

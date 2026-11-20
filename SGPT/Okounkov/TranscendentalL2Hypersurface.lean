import SGPT.Okounkov.TranscendentalL2Weight
import SGPT.Okounkov.TranscendentalLiftingExtension
import SGPT.Okounkov.TranscendentalLiftingIntegral
import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Okounkov.MultiplierCancellation
import SGPT.Okounkov.TranscendentalRelGenGeneration
import SGPT.Okounkov.TranscendentalRelGenDivisibility
import SGPT.Foundations.Analysis.Pending.OhsawaTakegoshiPoint
import SGPT.Foundations.Analysis.Pending.HolomorphicAnalytic
import SGPT.Foundations.Analysis.Pending.LocalPotentials

/-!
# A hypersurface containing the image of the divisor and of the exceptional set

Plan `tok/RELGEN3` step P7 (blueprint `l2:hypersurface`, chapter `claude-tok-l2`).

In the setting of `ModificationL2GenerationStatement`, let `z ∈ V = π⁻¹(d⁻¹ B(p, r))` and
`x₀ = d(π z)`. There are a ball `B(x₀, r₁)` with closure in `B(p, r)` and `k` holomorphic on it,
vanishing identically near no point, with `k(d(π y)) = 0` whenever `π y` lies in the exceptional
set `B_X` of the base or `ψ_E(y) = -∞` (`exists_hypersurface`).

Proof (blueprint): `u = c ψ_E + h` is `π^*θ`-psh (`β + c Θ_E = π^*θ + dd^c h`), so `u = φ_X ∘ π`
with `φ_X` `θ`-psh (LIFT `exists_descent`), and `Φ_X = ρ + φ_X ∘ d⁻¹` is psh on `B(p, r)`.
Ohsawa–Takegoshi from a point (TN `OhsawaTakegoshiPoint.exists_extension_from_point`) gives `k₁`
with `k₁(x₁) = 1` and `∫ |k₁|² e^{-Φ_X/c} < ∞`. Near a point `y ∉ A` with `ψ_E(y) = -∞`, the
change of variables along `d ∘ π` (`lintegral_multiplierDensity_coordinateMap_le`) gives
`∫ |k₁ ∘ F|² |g|^{-2} < ∞` (`g` a local equation of `D`, the Jacobian is bounded below), so
`k₁ ∘ F` is divisible by `g` (`L²` divisibility) and vanishes at `y`. Then `k = k₁ h_B` with
`h_B` a local generator of the analytic set `B_X` not vanishing identically.
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
open SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
open SGPT.Okounkov.TranscendentalRelGen

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-! ### The potential `c ψ_E + h` and its descent -/

/-- **`c ψ_E + h` is `π^*θ`-psh**: `π^*θ + dd^c (c ψ_E + h) = c [E] + β`. -/
theorem isThetaPshPotential_pullback_weight [CompactSpace Z] {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z) (hβ : β.val.IsKahler)
    (E : MeteredEffectiveQDivisor n Z) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hheq : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ θ).val
      (fun y => (c : EReal) * E.weight y + (h y : EReal)) := by
  have hE1 := TranscendentalLifting.isThetaPshPotential_weight E
  have hE2 := TranscendentalCore.isThetaPshPotential_nonneg_smul hE1 hc.le
  set τ : ClosedRealOneOneForm n Z := ClosedRealOneOneForm.pullback hπ θ - c • E.curvature
    with hτ
  have hH : IsThetaPshPotential τ.val (fun y => (h y : EReal)) := by
    refine ⟨(LocalPotentials.thetaPlurisubharmonic_smooth_iff τ h hh).mpr ?_,
      fun x U _ hxU => ⟨x, hxU, EReal.coe_ne_bot _⟩⟩
    intro e z hz v
    have h1 := hheq e z hz
    have h2 : τ.val.coeff e z + smoothDDC (fun y => h (e.val.symm y)) z = β.val.coeff e z := by
      rw [hτ, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
        add_assoc, add_comm (-_) _, ← add_assoc, ← h1, ClosedRealOneOneForm.coeff_add]
      abel
    have h3 : 0 ≤ β.val.coeff e z ![v, Complex.I • v] := by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact ((hβ.1 e z hz).2 v hv).le
    rw [← ContinuousAlternatingMap.add_apply, h2]
    exact h3
  have hsum := isThetaPshPotential_add_from_positive_sum hE2 hH
  have heq : c • E.curvature + τ = ClosedRealOneOneForm.pullback hπ θ := by
    rw [hτ]; abel
  rwa [heq] at hsum

/-- **The local potential on the base is psh**: if `φ_X` is `θ`-psh and `ρ` is a smooth local
potential of `θ` on `W` in the chart `d`, then `ρ + φ_X ∘ d⁻¹` is psh on `W`. -/
theorem plurisubharmonicOn_localPotential_add {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (d : ComplexChart n X) {W : Set (ComplexModel n)}
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ.val d W ρ) :
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

/-! ### Divisibility by a local equation of `D` -/

/-- **The extension vanishes on `D` off the exceptional set** (blueprint `l2:hypersurface`): if
`∫_Ω |k₁|² e^{-Φ_X / c} < ∞` with `Φ_X ∘ d ∘ π = ρ ∘ d ∘ π + c ψ_E + h`, then `k₁(d(π y)) = 0` at
every `y ∉ A` with `ψ_E(y) = -∞`. -/
theorem eq_zero_of_lintegral_multiplierDensity_ne_top {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hBc : IsClosed B)
    (hpre : π ⁻¹' B = A) (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hleft : ∀ y ∉ A, s (π y) = y)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h) (d : ComplexChart n X) {φX : X → EReal}
    (hφX : ∀ y, φX (π y) = (c : EReal) * E.weight y + (h y : EReal))
    {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {ρ : ComplexModel n → ℝ} (hρ : ContinuousOn ρ Ω)
    {k₁ : ComplexModel n → ℂ} (hk₁ : DifferentiableOn ℂ k₁ Ω)
    (hfin : ∫⁻ x in Ω, multiplierDensity (fun x => (ρ x : EReal) + φX (d.val.symm x)) (1 / c)
      k₁ x ≠ ⊤)
    {y : Z} (hyd : π y ∈ d.val.source) (hyΩ : d.val (π y) ∈ Ω) (hyA : y ∉ A)
    (hyE : E.weight y = ⊥) : k₁ (d.val (π y)) = 0 := by
  set e := complexChartAt (n := n) y with he
  set F := coordinateMap π e d with hF
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  set w₀ := e.val y with hw₀
  have hw₀t : w₀ ∈ e.val.target := e.val.map_source hye
  have hw₀d : w₀ ∈ coordinateDomain π e d := mem_coordinateDomain hye hyd
  have hFw₀ : F w₀ = d.val (π y) := coordinateMap_at hye
  obtain ⟨V, hV, hyV, g, hg, h', hh'c, hwE⟩ := exists_localEquation_of_isDivisorMetric hE y
  have hgy : g y = 0 := by
    by_contra hgy
    apply (EReal.coe_ne_bot (Real.log (‖g y‖ ^ 2) + h' y))
    rw [← hyE, hwE y hyV, generatorLog_eq_log_sum]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [ENNReal.log_ofReal_of_pos (by positivity), ← EReal.coe_add]
  -- the Jacobian
  set J := complexJacobian F with hJ
  have hJ0 : J w₀ ≠ 0 :=
    complexJacobian_coordinateMap_ne_zero hπ.1 hAc hBc hpre hs hleft e d hye hyd hyA
  have hFc : ContDiffAt ℂ ∞ F w₀ := coordinateMap_contDiffAt hπ.1 e d hw₀d
  have hJc : ContinuousAt J w₀ := continuousAt_complexJacobian hFc
  -- the domain
  have hdomo : IsOpen (coordinateDomain π e d) := coordinateDomain_isOpen hπ.1 e d
  have hFcont : ContinuousOn F (coordinateDomain π e d) :=
    (coordinateMap_contDiffOn hπ.1 e d).continuousOn
  set U₀ : Set (ComplexModel n) :=
    (coordinateDomain π e d ∩ F ⁻¹' Ω) ∩ (e.val.target ∩ e.val.symm ⁻¹' V) with hU₀
  have hU₀o : IsOpen U₀ :=
    (hFcont.isOpen_inter_preimage hdomo hΩ).inter (e.val.isOpen_inter_preimage_symm hV)
  have hw₀U₀ : w₀ ∈ U₀ :=
    ⟨⟨hw₀d, by rw [mem_preimage, hFw₀]; exact hyΩ⟩, hw₀t, by rw [mem_preimage, e.val.left_inv hye]; exact hyV⟩
  -- the bounded part of the weight
  set b : ComplexModel n → ℝ := fun w => (ρ (F w) + c * h' (e.val.symm w) + h (e.val.symm w)) / c
    with hb
  have hbc : ContinuousAt b w₀ := by
    have h1 : ContinuousAt (fun w => ρ (F w)) w₀ :=
      (hρ.continuousAt (hΩ.mem_nhds (by rw [hFw₀]; exact hyΩ))).comp hFc.continuousAt
    have hsy : ContinuousAt e.val.symm w₀ := e.val.continuousAt_symm hw₀t
    have hsy' : e.val.symm w₀ = y := e.val.left_inv hye
    have h2 : ContinuousAt (fun w => h' (e.val.symm w)) w₀ := by
      refine ContinuousAt.comp (f := e.val.symm) ?_ hsy
      rw [hsy']; exact hh'c.continuousAt (hV.mem_nhds hyV)
    have h3 : ContinuousAt (fun w => h (e.val.symm w)) w₀ :=
      ((hh e).continuousOn.continuousAt (e.val.open_target.mem_nhds hw₀t))
    exact ((h1.add (continuousAt_const.mul h2)).add h3).div_const c
  have hJpos : 0 < ‖J w₀‖ ^ 2 := by
    have := norm_pos_iff.mpr hJ0
    positivity
  have hev : ∀ᶠ w in 𝓝 w₀, w ∈ U₀ ∧ ‖J w₀‖ ^ 2 / 2 < ‖J w‖ ^ 2 ∧ b w < b w₀ + 1 := by
    have h1' : ∀ᶠ w in 𝓝 w₀, ‖J w₀‖ ^ 2 / 2 < ‖J w‖ ^ 2 :=
      (((continuous_norm.continuousAt.comp hJc).pow 2).eventually
        (Ioi_mem_nhds (by linarith : ‖J w₀‖ ^ 2 / 2 < ‖J w₀‖ ^ 2)))
    have h2 : ∀ᶠ w in 𝓝 w₀, b w < b w₀ + 1 :=
      hbc.eventually (Iio_mem_nhds (lt_add_one _))
    filter_upwards [hU₀o.mem_nhds hw₀U₀, h1', h2] with w hw1 hw2 hw3
    exact ⟨hw1, hw2, hw3⟩
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.eventually_nhds_iff_ball.mp hev
  -- the local equation in the chart
  set G : ComplexModel n → ℂ := fun w => g (e.val.symm w) with hG
  have hGd : DifferentiableOn ℂ G (e.val.target ∩ e.val.symm ⁻¹' V) :=
    MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg.1
  have hGfreq := frequently_ne_zero_comp_symm hg.2.1 e (e.val.isOpen_inter_preimage_symm hV)
    subset_rfl
  have hballU : ball w₀ r₀ ⊆ U₀ := fun w hw => (hr₀s w hw).1
  have hae : ∀ᵐ w ∂(volume.restrict (ball w₀ r₀)), G w ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun w hw => (hballU hw).2)
      (LelongPoincareDivisor.ae_ne_zero (e.val.isOpen_inter_preimage_symm hV) hGd hGfreq)
  -- the change of variables
  have hcov := lintegral_multiplierDensity_coordinateMap_le hπ e d isOpen_ball
    (fun w hw => (hballU hw).1.1) (fun x => (ρ x : EReal) + φX (d.val.symm x)) (1 / c) k₁
  have hFball : F '' ball w₀ r₀ ⊆ Ω := by
    rintro _ ⟨w, hw, rfl⟩; exact (hballU hw).1.2
  have hfin' : ∫⁻ w in ball w₀ r₀, multiplierDensity
      (fun w => (ρ (F w) : EReal) + φX (d.val.symm (F w))) (1 / c)
      (fun w => k₁ (F w) * complexJacobian F w) w < ⊤ :=
    lt_of_le_of_lt (hcov.trans (lintegral_mono_set hFball)) (lt_top_iff_ne_top.mpr hfin)
  set K : ℝ := 2 * Real.exp (b w₀ + 1) / ‖J w₀‖ ^ 2 with hK
  have hpt : ∀ᵐ w ∂(volume.restrict (ball w₀ r₀)),
      ENNReal.ofReal (‖k₁ (F w)‖ ^ 2) / ENNReal.ofReal (‖G w‖ ^ (2 * 1)) ≤
        ENNReal.ofReal K * multiplierDensity
          (fun w => (ρ (F w) : EReal) + φX (d.val.symm (F w))) (1 / c)
          (fun w => k₁ (F w) * complexJacobian F w) w := by
    filter_upwards [hae, ae_restrict_mem measurableSet_ball] with w hGw hw
    obtain ⟨hwU, hJw, hbw⟩ := hr₀s w hw
    have hwd : w ∈ coordinateDomain π e d := hwU.1.1
    have hwV : e.val.symm w ∈ V := hwU.2.2
    have hdF : d.val.symm (F w) = π (e.val.symm w) := d.val.left_inv hwd.2
    have hGpos : 0 < ‖G w‖ ^ 2 := by
      have := norm_pos_iff.mpr hGw
      positivity
    have hweight : (ρ (F w) : EReal) + φX (d.val.symm (F w)) =
        ((ρ (F w) + c * (Real.log (‖G w‖ ^ 2) + h' (e.val.symm w)) + h (e.val.symm w) : ℝ) :
          EReal) := by
      rw [hdF, hφX, hwE _ hwV, generatorLog_eq_log_sum]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [ENNReal.log_ofReal_of_pos hGpos, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add,
        ← EReal.coe_add, add_assoc]
    have hexp : Real.exp (-(1 / c * (ρ (F w) + c * (Real.log (‖G w‖ ^ 2) + h' (e.val.symm w)) +
        h (e.val.symm w)))) = Real.exp (-b w) / ‖G w‖ ^ 2 := by
      have : -(1 / c * (ρ (F w) + c * (Real.log (‖G w‖ ^ 2) + h' (e.val.symm w)) +
          h (e.val.symm w))) = -b w + -Real.log (‖G w‖ ^ 2) := by
        rw [hb]; field_simp; ring
      rw [this, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hGpos, div_eq_mul_inv]
    simp only [multiplierDensity]
    rw [hweight, multiplierWeight_coe, hexp, ← ENNReal.ofReal_div_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, mul_pow]
    have hkey : Real.exp (b w₀ + 1) * Real.exp (-b w) ≥ 1 := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have hJw' : ‖J w₀‖ ^ 2 ≤ 2 * ‖complexJacobian F w‖ ^ 2 := by
      have : ‖J w₀‖ ^ 2 / 2 < ‖J w‖ ^ 2 := hJw
      linarith
    have hk2 : 0 ≤ ‖k₁ (F w)‖ ^ 2 := sq_nonneg _
    rw [show 2 * 1 = 2 from rfl, hK]
    have hq : 0 ≤ ‖k₁ (F w)‖ ^ 2 / ‖G w‖ ^ 2 := by positivity
    calc ‖k₁ (F w)‖ ^ 2 / ‖G w‖ ^ 2
        ≤ (Real.exp (b w₀ + 1) * Real.exp (-b w)) *
            (2 * ‖complexJacobian F w‖ ^ 2 / ‖J w₀‖ ^ 2) * (‖k₁ (F w)‖ ^ 2 / ‖G w‖ ^ 2) := by
          have h2 : 1 ≤ 2 * ‖complexJacobian F w‖ ^ 2 / ‖J w₀‖ ^ 2 := by
            rw [le_div_iff₀ hJpos]; linarith
          have h3 : 1 ≤ (Real.exp (b w₀ + 1) * Real.exp (-b w)) *
              (2 * ‖complexJacobian F w‖ ^ 2 / ‖J w₀‖ ^ 2) := by nlinarith
          nlinarith
      _ = 2 * Real.exp (b w₀ + 1) / ‖J w₀‖ ^ 2 *
            (‖k₁ (F w)‖ ^ 2 * ‖complexJacobian F w‖ ^ 2 * (Real.exp (-b w) / ‖G w‖ ^ 2)) := by
          field_simp
  have hquot : (∫⁻ w in ball w₀ r₀, ENNReal.ofReal (‖k₁ (F w)‖ ^ 2) /
      ENNReal.ofReal (‖G w‖ ^ (2 * 1))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hpt)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin'.ne
  -- `L²` divisibility
  have hkF : DifferentiableOn ℂ (fun w => k₁ (F w)) (ball w₀ r₀) :=
    hk₁.comp ((coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp) |>.mono
      fun w hw => (hballU hw).1.1) fun w hw => (hballU hw).1.2
  have hGd' : DifferentiableOn ℂ G (ball w₀ r₀) := hGd.mono fun w hw => (hballU hw).2
  have hGne : ¬ ∀ᶠ w in 𝓝 w₀, G w = 0 := fun hev' =>
    ((hGfreq w₀ (hballU (mem_ball_self hr₀)).2).and_eventually hev').exists.elim
      fun w hw => hw.1 hw.2
  obtain ⟨a, -, ha⟩ := l2DivisibilityStatement n w₀ r₀ hr₀ (fun w => k₁ (F w)) G hkF hGd' hGne 1
    hquot
  have h1 := ha.self_of_nhds
  simp only [hG, pow_one] at h1
  rw [← hFw₀, h1, hw₀, e.val.left_inv hye, hgy, mul_zero]

/-! ### Identity theorem on balls -/

/-- **Identity theorem on a ball**: a holomorphic function on a ball which vanishes identically
near some point of the ball vanishes identically near no point of it unless it is zero near
every point. In the form used here: if it does not vanish identically near `x₁`, it vanishes
identically near no point of the ball. -/
theorem not_eventually_zero_of_ball {k : ComplexModel n → ℂ} {x₀ : ComplexModel n} {r : ℝ}
    (hk : DifferentiableOn ℂ k (ball x₀ r)) {x₁ : ComplexModel n} (hx₁ : x₁ ∈ ball x₀ r)
    (hne : ¬ ∀ᶠ w in 𝓝 x₁, k w = 0) : ∀ x ∈ ball x₀ r, ¬ ∀ᶠ w in 𝓝 x, k w = 0 := by
  intro x hx hev
  have han := HolomorphicAnalytic.analyticOnNhd_of_differentiableOn isOpen_ball hk
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball x₀ r).isPreconnected
    hx hev
  apply hne
  filter_upwards [isOpen_ball.mem_nhds hx₁] with w hw
  exact h0 hw

/-- A product of two holomorphic functions vanishing identically near no point of an open set
vanishes identically near no point of it. -/
theorem not_eventually_mul_eq_zero {U : Set (ComplexModel n)} (hU : IsOpen U)
    {k₁ k₂ : ComplexModel n → ℂ} (hk₁ : DifferentiableOn ℂ k₁ U)
    (hne₁ : ∀ x ∈ U, ¬ ∀ᶠ w in 𝓝 x, k₁ w = 0) (hne₂ : ∀ x ∈ U, ¬ ∀ᶠ w in 𝓝 x, k₂ w = 0) :
    ∀ x ∈ U, ¬ ∀ᶠ w in 𝓝 x, k₁ w * k₂ w = 0 := by
  intro x hx hev
  have hfreq : ∃ᶠ w in 𝓝 x, k₁ w ≠ 0 := Filter.not_eventually.mp (hne₁ x hx)
  obtain ⟨x', hx', hx'ev⟩ := (hfreq.and_eventually
    ((hev.and (hU.mem_nhds hx)).eventually_nhds)).exists
  have hx'U : x' ∈ U := hx'ev.self_of_nhds.2
  have hc : ContinuousAt k₁ x' := (hk₁.differentiableAt (hU.mem_nhds hx'U)).continuousAt
  apply hne₂ x' hx'U
  filter_upwards [hc.eventually_ne hx', hx'ev] with w hw1 hw2
  exact (mul_eq_zero.mp hw2.1).resolve_left hw1

/-! ### A local equation of the exceptional set of the base -/

omit [IsComplexManifold n X] in
/-- **A local equation of a nowhere dense analytic set** in an arbitrary chart: near `d x` there
is a holomorphic `h_B`, not vanishing identically near `d x`, vanishing on `d(B)`. -/
theorem exists_local_equation_of_isComplexAnalyticSubset [IsComplexManifold n X] {B : Set X}
    (hBa : IsComplexAnalyticSubset (n := n) B) (hBi : interior B = ∅) (d : ComplexChart n X)
    {x : X} (hxd : x ∈ d.val.source) :
    ∃ r : ℝ, 0 < r ∧ ball (d.val x) r ⊆ d.val.target ∧ ∃ hB : ComplexModel n → ℂ,
      DifferentiableOn ℂ hB (ball (d.val x) r) ∧ (¬ ∀ᶠ w in 𝓝 (d.val x), hB w = 0) ∧
      ∀ t ∈ B, t ∈ d.val.source → d.val t ∈ ball (d.val x) r → hB (d.val t) = 0 := by
  classical
  obtain ⟨P⟩ := hBa x
  set d₀ := complexChartAt (n := n) x with hd₀
  have hxd₀ : x ∈ d₀.val.source := mem_complexChartAt_source x
  set N₀ := P.coordinateNeighborhood with hN₀
  have hN₀o : IsOpen N₀ := P.isOpen_coordinateNeighborhood
  have hxN₀ : d₀.val x ∈ N₀ := P.center_mem_coordinateNeighborhood
  -- some generator does not vanish identically near the centre
  obtain ⟨i, hi⟩ : ∃ i, ¬ ∀ᶠ w in 𝓝 (d₀.val x), P.generator i w = 0 := by
    by_contra hall
    push Not at hall
    have hev : ∀ᶠ w in 𝓝 (d₀.val x), w ∈ N₀ ∧ ∀ i, P.generator i w = 0 :=
      Filter.Eventually.and (hN₀o.mem_nhds hxN₀) (eventually_all.mpr hall)
    obtain ⟨S, hSsub, hSo, hxS⟩ := _root_.mem_nhds_iff.mp hev
    have hT : IsOpen (d₀.val.source ∩ d₀.val ⁻¹' S) := d₀.val.isOpen_inter_preimage hSo
    have hTB : d₀.val.source ∩ d₀.val ⁻¹' S ⊆ B := by
      intro t ht
      have h1 := hSsub ht.2
      exact (P.zeroLocus ht.1 h1.1).mpr h1.2
    have hxB : x ∈ interior B := interior_maximal hTB hT ⟨hxd₀, hxS⟩
    rw [hBi] at hxB
    exact hxB
  -- transport to the chart `d`
  set τ := chartTransition d d₀ with hτ
  have hxτ : d.val x ∈ τ.source := by
    simpa [hτ, chartTransition, OpenPartialHomeomorph.trans_source, d.val.left_inv hxd] using
      ⟨d.val.map_source hxd, hxd₀⟩
  have hτx : τ (d.val x) = d₀.val x := by
    simp [hτ, chartTransition, d.val.left_inv hxd]
  have hτc : ContinuousOn τ τ.source := τ.continuousOn
  have hO : IsOpen (τ.source ∩ τ ⁻¹' N₀) := hτc.isOpen_inter_preimage τ.open_source hN₀o
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO (d.val x) ⟨hxτ, by rw [mem_preimage, hτx]; exact hxN₀⟩
  have hτsrc : τ.source ⊆ d.val.target := by
    intro w hw
    have : w ∈ d.val.target ∧ d.val.symm w ∈ d₀.val.source := by
      simpa [hτ, chartTransition, OpenPartialHomeomorph.trans_source] using hw
    exact this.1
  refine ⟨r, hr, fun w hw => hτsrc (hrO hw).1, fun w => P.generator i (τ w), ?_, ?_, ?_⟩
  · intro w hw
    have hwτ := hrO hw
    have hτd : DifferentiableAt ℂ τ w :=
      (chartTransition_contDiffAt d d₀ hwτ.1).differentiableAt (by simp)
    have hgd : DifferentiableAt ℂ (P.generator i) (τ w) :=
      (P.generator_holomorphic i).differentiableAt (hN₀o.mem_nhds hwτ.2)
    exact (hgd.comp w hτd).differentiableWithinAt
  · intro hev
    apply hi
    set τ' := chartTransition d₀ d with hτ'
    have hx₀τ' : d₀.val x ∈ τ'.source := by
      simpa [hτ', chartTransition, OpenPartialHomeomorph.trans_source, d₀.val.left_inv hxd₀] using
        ⟨d₀.val.map_source hxd₀, hxd⟩
    have hτ'x : τ' (d₀.val x) = d.val x := by
      simp [hτ', chartTransition, d₀.val.left_inv hxd₀]
    have hτ'c : ContinuousAt τ' (d₀.val x) :=
      τ'.continuousAt hx₀τ'
    have hev' : ∀ᶠ w in 𝓝 (d₀.val x), P.generator i (τ (τ' w)) = 0 := by
      have := hτ'c.eventually (hτ'x ▸ hev)
      exact this
    filter_upwards [hev', τ'.open_source.mem_nhds hx₀τ'] with w hw hwτ'
    have hw' : w ∈ d₀.val.target ∧ d₀.val.symm w ∈ d.val.source := by
      simpa [hτ', chartTransition, OpenPartialHomeomorph.trans_source] using hwτ'
    have hid : τ (τ' w) = w := by
      simp only [hτ, hτ', chartTransition, OpenPartialHomeomorph.coe_trans,
        Function.comp_apply]
      rw [d.val.left_inv hw'.2, d₀.val.right_inv hw'.1]
    rwa [hid] at hw
  · intro t htB htd htball
    have h1 := hrO htball
    have hτt : τ (d.val t) = d₀.val t := by
      simp [hτ, chartTransition, d.val.left_inv htd]
    have htd₀ : t ∈ d₀.val.source := by
      have : d.val t ∈ d.val.target ∧ d.val.symm (d.val t) ∈ d₀.val.source := by
        simpa [hτ, chartTransition, OpenPartialHomeomorph.trans_source] using h1.1
      rw [d.val.left_inv htd] at this
      exact this.2
    have h2 : d₀.val t ∈ N₀ := by rw [← hτt]; exact h1.2
    have := (P.zeroLocus htd₀ h2).mp htB i
    simp only
    rw [hτt]
    exact this

/-! ### The hypersurface -/

omit [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] in
/-- Lebesgue integrals on `ℂⁿ` do not depend on the (equal) choice of Borel measurable space
structure; used to read TN's Ohsawa–Takegoshi theorem, stated for `borel`. -/
theorem lintegral_measurableSpace_congr (m₁ m₂ : MeasurableSpace (ComplexModel n))
    (hb₁ : @BorelSpace (ComplexModel n) _ m₁) (hb₂ : @BorelSpace (ComplexModel n) _ m₂)
    (hm : m₁ = m₂) (s : Set (ComplexModel n)) (f : ComplexModel n → ENNReal) :
    @lintegral (ComplexModel n) m₁ (@Measure.restrict _ m₁
      (@volume _ (@measureSpaceOfInnerProductSpace _ _ _ _ m₁ hb₁)) s) f =
    @lintegral (ComplexModel n) m₂ (@Measure.restrict _ m₂
      (@volume _ (@measureSpaceOfInnerProductSpace _ _ _ _ m₂ hb₂)) s) f := by
  subst hm
  rfl

omit [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] in
theorem lintegral_borel_eq (s : Set (ComplexModel n)) (f : ComplexModel n → ENNReal) :
    (by letI : MeasurableSpace (ComplexModel n) := borel _
        letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
        exact ∫⁻ x in s, f x) = ∫⁻ x in s, f x :=
  lintegral_measurableSpace_congr _ _ _ _ (BorelSpace.measurable_eq (α := ComplexModel n)).symm s f

/-- **The hypersurface** (blueprint `l2:hypersurface`): in the setting of
`ModificationL2GenerationStatement`, for `z ∈ V = π⁻¹(d⁻¹ B(p, r))` there are a ball
`B(x₀, r₁)` (`x₀ = d(π z)`) with closure in `B(p, r)` and `k` holomorphic on it, vanishing
identically near no point, with `k(d(π y)) = 0` whenever `π y ∈ B_X` or `ψ_E(y) = -∞`. -/
theorem exists_hypersurface [CompactSpace Z] {π : Z → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {A : Set Z} {B : Set X} {s : X → Z} (hAc : IsClosed A) (hBc : IsClosed B)
    (hBa : IsComplexAnalyticSubset (n := n) B) (hBi : interior B = ∅) (hpre : π ⁻¹' B = A)
    (hs : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s Bᶜ)
    (hleft : ∀ y ∉ A, s (π y) = y)
    (θ : ClosedRealOneOneForm n X) (β : ClosedRealOneOneForm n Z) (hβ : β.val.IsKahler)
    {D : EffectiveDivisor n Z} {E : MeteredEffectiveQDivisor n Z}
    (hE : DivisorMetric.IsDivisorMetric D E) {c : ℝ} (hc : 0 < c) {h : Z → ℝ}
    (hh : ChartSmooth (n := n) h)
    (hheq : ∀ (e : ComplexChart n Z) (z : ComplexModel n), z ∈ e.val.target →
      (β + c • E.curvature).val.coeff e z =
        (ClosedRealOneOneForm.pullback hπ.1 θ).val.coeff e z +
          smoothDDC (fun y => h (e.val.symm y)) z)
    (d : ComplexChart n X) {p : ComplexModel n} {r : ℝ} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val d (ball p r) ρ)
    {z : Z} (hz : z ∈ π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r)) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ closedBall (d.val (π z)) r₁ ⊆ ball p r ∧
      ∃ k : ComplexModel n → ℂ, DifferentiableOn ℂ k (ball (d.val (π z)) r₁) ∧
        (∀ x ∈ ball (d.val (π z)) r₁, ¬ ∀ᶠ w in 𝓝 x, k w = 0) ∧
        ∀ y : Z, π y ∈ d.val.source → d.val (π y) ∈ ball (d.val (π z)) r₁ →
          (π y ∈ B ∨ E.weight y = ⊥) → k (d.val (π y)) = 0 := by
  -- descent of `c ψ_E + h`
  have hu := isThetaPshPotential_pullback_weight hπ.1 θ β hβ E hc hh hheq
  obtain ⟨φX, hφX, hφXπ⟩ := TranscendentalLifting.exists_descent hπ θ hu
  have hpsh := plurisubharmonicOn_localPotential_add hφX d hρ
  set x₀ := d.val (π z) with hx₀
  have hx₀B : x₀ ∈ ball p r := hz.2
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp isOpen_ball x₀ hx₀B
  set r₂ := ε / 2 with hr₂
  have hr₂0 : 0 < r₂ := half_pos hε
  have hΩB : ball x₀ (2 * r₂) ⊆ ball p r := by
    rw [hr₂, mul_div_cancel₀ _ two_ne_zero]; exact hεB
  -- a point where `φ_X` is finite
  have hUo : IsOpen (d.val.source ∩ d.val ⁻¹' ball x₀ r₂) :=
    d.val.isOpen_inter_preimage isOpen_ball
  obtain ⟨t, ht, htφ⟩ := hφX.2 (π z) _ hUo ⟨hz.1, mem_ball_self hr₂0⟩
  set x₁ := d.val t with hx₁
  have hx₁Ω : x₁ ∈ ball x₀ (2 * r₂) := by
    have : dist x₁ x₀ < r₂ := ht.2
    rw [mem_ball]; linarith
  have hx₁sym : d.val.symm x₁ = t := d.val.left_inv ht.1
  -- Ohsawa–Takegoshi from the point `x₁`
  obtain ⟨C, hC, hOT⟩ := OhsawaTakegoshiPoint.exists_extension_from_point n
    (‖x₀‖ + 2 * r₂ + 1) (by positivity)
  have hbd : ∀ w ∈ ball x₀ (2 * r₂), ‖w‖ < ‖x₀‖ + 2 * r₂ + 1 := by
    intro w hw
    have h1 : ‖w - x₀‖ < 2 * r₂ := by rw [← dist_eq_norm]; exact hw
    have h2 := norm_le_norm_add_norm_sub' w x₀
    linarith
  obtain ⟨k₁, hk₁, hk₁x₁, hk₁int⟩ := hOT (ball x₀ (2 * r₂)) isOpen_ball (convex_ball _ _) hbd
    _ (hpsh.mono hΩB) (1 / c) (by positivity) x₁ hx₁Ω
  have hΦx₁ : (ρ x₁ : EReal) + φX (d.val.symm x₁) ≠ ⊥ := by
    rw [hx₁sym]
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, htφ⟩
  have hΦx₁' : (ρ x₁ : EReal) + φX (d.val.symm x₁) ≠ ⊤ := by
    rw [hx₁sym]
    have := hφX.quasiPshPotential.1.ne_top t
    exact EReal.add_ne_top_iff_ne_top₂ (EReal.coe_ne_bot _) (by simpa using htφ) |>.mpr
      ⟨EReal.coe_ne_top _, this⟩
  have hk₁int' : ∫⁻ x in ball x₀ (2 * r₂), multiplierDensity
      (fun x => (ρ x : EReal) + φX (d.val.symm x)) (1 / c) k₁ x ≤
        ENNReal.ofReal C * multiplierWeight (1 / c) ((ρ x₁ : EReal) + φX (d.val.symm x₁)) := by
    exact (lintegral_borel_eq _ _).symm.le.trans hk₁int
  have hfin : ∫⁻ x in ball x₀ (2 * r₂), multiplierDensity
      (fun x => (ρ x : EReal) + φX (d.val.symm x)) (1 / c) k₁ x ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) hk₁int'
    rw [← EReal.coe_toReal hΦx₁' hΦx₁, multiplierWeight_coe]
    exact ENNReal.ofReal_ne_top
  -- a local equation of `B_X`
  obtain ⟨r₃, hr₃, -, hB, hBd, hBne, hBzero⟩ :=
    exists_local_equation_of_isComplexAnalyticSubset hBa hBi d hz.1
  set r₁ := min r₂ r₃ with hr₁
  have hr₁0 : 0 < r₁ := lt_min hr₂0 hr₃
  have hr₁Ω : ball x₀ r₁ ⊆ ball x₀ (2 * r₂) :=
    ball_subset_ball ((min_le_left _ _).trans (by linarith))
  have hr₁B : ball x₀ r₁ ⊆ ball x₀ r₃ := ball_subset_ball (min_le_right _ _)
  refine ⟨r₁, hr₁0, ?_, fun w => k₁ w * hB w, ?_, ?_, ?_⟩
  · refine (closedBall_subset_ball ?_).trans hΩB
    exact (min_le_left _ _).trans_lt (by linarith)
  · exact (hk₁.mono hr₁Ω).mul (hBd.mono hr₁B)
  · have hne₁ := not_eventually_zero_of_ball hk₁ hx₁Ω (fun hev => by
      have := hev.self_of_nhds
      rw [hk₁x₁] at this
      exact one_ne_zero this)
    have hne₂ := not_eventually_zero_of_ball hBd (mem_ball_self hr₃) hBne
    exact not_eventually_mul_eq_zero isOpen_ball (hk₁.mono hr₁Ω)
      (fun x hx => hne₁ x (hr₁Ω hx)) (fun x hx => hne₂ x (hr₁B hx))
  · intro y hyd hyball hyBE
    by_cases hyB : π y ∈ B
    · simp only
      rw [hBzero (π y) hyB hyd (hr₁B hyball), mul_zero]
    · have hyE : E.weight y = ⊥ := hyBE.resolve_left hyB
      have hyA : y ∉ A := fun hyA => hyB (by rw [← hpre] at hyA; exact hyA)
      have h0 := eq_zero_of_lintegral_multiplierDensity_ne_top hπ hAc hBc hpre hs hleft hE hc hh d
        hφXπ isOpen_ball (hρ.2.2.1.continuousOn.mono hΩB) hk₁ hfin hyd (hr₁Ω hyball) hyA hyE
      simp only
      rw [h0, zero_mul]

end SGPT.Okounkov.TranscendentalL2

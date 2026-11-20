import SGPT.Okounkov.TranscendentalCore2Siu
import SGPT.Okounkov.TranscendentalPartialStatement
import SGPT.Okounkov.TranscendentalLiftingIntegral
import SGPT.Okounkov.EffectiveDivisorMetricGeneric
import SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient
import SGPT.Foundations.Analysis.Pending.ResidualNef

/-!
# Subtracting a dominated divisor from a current with analytic singularities

Source: the case of blueprint node `tok:siu-analytic` (DRWNXZ = Darvas--Reboulet--Witt
Nyström--Xia--Zhang, *Transcendental Okounkov bodies*, Lemma 2.3) used by `tok:partial-birational`
(DRWNXZ Lemma 5.5): sub-lemmas `tok-partial:division`, `tok-partial:residual-local`,
`tok-partial:residual` of `claude-tok-partial.tex`.

Let `E` be a metered effective `ℚ`-divisor (weight `ψ_E`, curvature `Θ_E`) on a compact complex
manifold and `u ∈ 𝒜(θ)` with `u ⪯ ψ_E`. Then `u = ψ_E + W` with `W ∈ 𝒜(θ - Θ_E)`
(`divisorResidual_mem_analyticCurrents`, which proves the published `DivisorResidualStatement`).
DRWNXZ obtain this from Siu's decomposition (the generic Lelong numbers along the components of
`E` dominate the coefficients); here the domination `u ≤ ψ_E + C` is used directly, and `E` may
have several (singular) components.

## The route

Write `q E` as the metric of an integral divisor (`exists_integralModel`): near a point of a
chart, `q ψ_E = log |G|² + h'` with `G` holomorphic and `h'` smooth. Let
`u = c' log ∑ |f_i|² + O(1)` and write `(1/q)/c' = k/L`; with the power family
`F_β = ∏_{j < L} f_{β j}`, `u = (c'/L) log ∑ |F_β|² + O(1)` and `(c'/L) k = 1/q`. The domination
gives `|F_β| ≤ C |G|^k` (at zeros of `G`, `u = -∞`, so all `f_i` vanish), and the bounded
quotient `F_β / G^k` extends holomorphically (Riemann extension, TN `HolomorphicBoundedQuotient`):
`F_β = G^k H_β` (`exists_eq_mul_of_norm_le`). Off `Supp E`,
`u - ψ_E = (c'/L) log ∑ |H_β|² + O(1)`, and the same two-sided bound holds for the upper
regularization across `Supp E` (CB2's `le_uscRegularization_cut`, `uscRegularization_cut_le`), so
the extension has analytic singularities (`hasAnalyticSingularityTypeAt_divisorResidual`); it is
`(θ - Θ_E)`-psh by the removable singularity theorem (`Supp E` is analytic and `u - ψ_E` is
bounded above).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPartial

open Set Filter
open scoped Topology Manifold ContDiff ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
open SGPT.Okounkov.TranscendentalCore2

/-! ### Division by a dominating holomorphic function -/

section Division

variable {n : ℕ}

/-- **Division by a dominating function** (blueprint `tok-partial:division`, the Riemann
extension theorem): if `F` and `G` are holomorphic near `z`, the zero set of `G` has empty
interior and `‖F‖ ≤ C ‖G‖` near `z`, then `F = H G` near `z` with `H` holomorphic. -/
theorem exists_eq_mul_of_norm_le {F G : ComplexModel n → ℂ} {z : ComplexModel n}
    (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w) (hG : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w)
    (hnd : ∀ᶠ w in 𝓝 z, ∀ U ∈ 𝓝 w, ∃ w' ∈ U, G w' ≠ 0)
    (hbdd : ∃ C : ℝ, ∀ᶠ w in 𝓝 z, ‖F w‖ ≤ C * ‖G w‖) :
    ∃ H : ComplexModel n → ℂ, (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ H w) ∧
      F =ᶠ[𝓝 z] fun w => H w * G w := by
  obtain ⟨O, hOsub, hO, hzO⟩ := _root_.mem_nhds_iff.mp hnd
  have hgne : ∀ W : Set (ComplexModel n), IsOpen W → W ⊆ O → W.Nonempty →
      ∃ y ∈ W, G y ≠ 0 := by
    rintro W hW hWO ⟨w, hw⟩
    exact hOsub (hWO hw) W (hW.mem_nhds hw)
  have hFh : HolomorphicAt n F z :=
    hF.mono fun w hw => mdifferentiableAt_iff_differentiableAt.mpr hw
  have hGh : HolomorphicAt n G z :=
    hG.mono fun w hw => mdifferentiableAt_iff_differentiableAt.mpr hw
  obtain ⟨H, hH, hFH⟩ :=
    HolomorphicBoundedQuotient.exists_holomorphicAt_eventuallyEq_mul hO hzO hFh hGh hgne hbdd
  exact ⟨H, hH.mono fun w hw => mdifferentiableAt_iff_differentiableAt.mp hw, hFH⟩

end Division

/-! ### Chart data of an integral divisor metric -/

section Chart

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Local data of a divisor metric in a chart**: near every point `z` of a chart, the weight is
`log |G|² + h'` with `G` holomorphic and `h'` continuous, `Supp E` is the zero set of `G`, and the
zero set of `G` has empty interior (CB2's `exists_chart_divisor_data` without primality). -/
theorem exists_chart_metric_data (D : EffectiveDivisor n M) (E : MeteredEffectiveQDivisor n M)
    (hE : DivisorMetric.IsDivisorMetric D E) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    ∃ (G : ComplexModel n → ℂ) (h' : ComplexModel n → ℝ),
      (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w) ∧ ContinuousAt h' z ∧
      (∀ᶠ w in 𝓝 z, E.weight (e.val.symm w) =
        ENNReal.log (ENNReal.ofReal (‖G w‖ ^ 2)) + (h' w : EReal)) ∧
      (∀ᶠ w in 𝓝 z, (e.val.symm w ∈ E.support ↔ G w = 0)) ∧
      (∀ᶠ w in 𝓝 z, ∀ U ∈ 𝓝 w, ∃ w' ∈ U, G w' ≠ 0) := by
  have hy0 : e.val.symm z ∈ e.val.source := e.val.map_target hz
  obtain ⟨V', hV', hy0V', g, hg, -, h, hh, hwV⟩ := hE (e.val.symm z)
  have hdom : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V') := e.val.isOpen_inter_preimage_symm hV'
  have hzdom : z ∈ e.val.target ∩ e.val.symm ⁻¹' V' := ⟨hz, hy0V'⟩
  have hdomN : e.val.target ∩ e.val.symm ⁻¹' V' ∈ 𝓝 z := hdom.mem_nhds hzdom
  have hGd : DifferentiableOn ℂ (fun w => g (e.val.symm w)) (e.val.target ∩ e.val.symm ⁻¹' V') :=
    MeteredDivisorPositivity.differentiableOn_comp_chartSymm e hg
  have hwt : ∀ w ∈ e.val.target ∩ e.val.symm ⁻¹' V', E.weight (e.val.symm w) =
      ENNReal.log (ENNReal.ofReal (‖g (e.val.symm w)‖ ^ 2)) + (h (e.val.symm w) : EReal) :=
    fun w hw => by rw [hwV _ hw.2, TranscendentalCore.generatorLog_single]
  have hsupp : ∀ w ∈ e.val.target ∩ e.val.symm ⁻¹' V',
      (e.val.symm w ∈ E.support ↔ g (e.val.symm w) = 0) := by
    intro w hw
    change E.weight (e.val.symm w) = ⊥ ↔ _
    rw [hwt w hw]
    constructor
    · intro hbot
      rcases EReal.add_eq_bot_iff.mp hbot with h1 | h1
      · rw [ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero] at h1
        have h2 : ‖g (e.val.symm w)‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
        exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
      · exact absurd h1 (EReal.coe_ne_bot _)
    · intro h0
      rw [h0, norm_zero]
      simp
  have hw := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric D E hE
  refine ⟨fun w => g (e.val.symm w), fun w => h (e.val.symm w), ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hdomN] with w hw'
    exact hGd.differentiableAt (hdom.mem_nhds hw')
  · exact ((hh e).continuousOn.continuousAt hdomN)
  · filter_upwards [hdomN] with w hw'
    exact hwt w hw'
  · filter_upwards [hdomN] with w hw'
    exact hsupp w hw'
  · -- the zero set of `G` has empty interior
    filter_upwards [hdomN] with w hw' U hU
    have hsw : e.val.symm w ∈ e.val.source := e.val.map_target hw'.1
    have hOpen : IsOpen (e.val.source ∩ e.val ⁻¹' (interior U ∩ (e.val.target ∩
        e.val.symm ⁻¹' V'))) :=
      e.val.continuousOn.isOpen_inter_preimage e.val.open_source (isOpen_interior.inter hdom)
    have hmem : e.val.symm w ∈ e.val.source ∩ e.val ⁻¹' (interior U ∩ (e.val.target ∩
        e.val.symm ⁻¹' V')) := by
      refine ⟨hsw, ?_⟩
      simp only [mem_preimage, e.val.right_inv hw'.1]
      exact ⟨mem_interior_iff_mem_nhds.mpr hU, hw'⟩
    obtain ⟨y, ⟨hys, hyU, hydom⟩, hy⟩ := hw.2 _ _ hOpen hmem
    refine ⟨e.val y, interior_subset hyU, fun h0 => hy ?_⟩
    have := (hsupp _ hydom).mpr h0
    rw [e.val.left_inv hys] at this
    exact this

end Chart

/-! ### The local analytic type of the residual -/

section Local

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The residual has analytic singularities where the potential has**
(blueprint `tok-partial:residual-local`): let `E` be the metric of an integral divisor, `a ∈ ℚ_{>0}`
and `u ≤ a ψ_E + C₀` everywhere. If `u` has analytic singularity type at the point `z` of the chart
`e`, then so has the extension `W` of `u - a ψ_E` across `Supp E`: near `z`,
`W = (c'/L) log ∑ |H_β|² + O(1)`. -/
theorem hasAnalyticSingularityTypeAt_divisorResidual {u : M → EReal}
    (D : EffectiveDivisor n M) (E : MeteredEffectiveQDivisor n M)
    (hE : DivisorMetric.IsDivisorMetric D E) {a : ℚ} (ha : 0 < a) {C₀ : ℝ}
    (hle : ∀ x, u x ≤ ((a : ℝ) : EReal) * E.weight x + (C₀ : EReal))
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hAz : HasAnalyticSingularityTypeAt (chartFunction u e) z) :
    HasAnalyticSingularityTypeAt
      (chartFunction (extensionAcross E.support (SGPT.Okounkov.smoothDivisorOffResidual E a u)) e)
        z := by
  classical
  obtain ⟨G, h', hGd, hh', hwt, hsupp, hnd⟩ := exists_chart_metric_data D E hE e hz
  obtain ⟨c', K, f, hc'pos, ⟨Of, hOf, hzOf, hfd⟩, b, ⟨Bb, hBb0, hBb⟩, heq⟩ := hAz
  have hc'Q : (0 : ℚ) < c' := by exact_mod_cast hc'pos
  have haR0 : (0 : ℝ) ≤ a := by exact_mod_cast ha.le
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  -- `a / c' = k / L`
  set t : ℚ := a / c' with ht
  have ht0 : 0 ≤ t := div_nonneg ha.le hc'Q.le
  set k : ℕ := t.num.toNat with hk
  set L : ℕ := t.den with hL
  have hLpos : 0 < L := t.den_pos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hkLQ : a * (L : ℚ) = c' * (k : ℚ) := by
    have hk' : (k : ℚ) = (t.num : ℚ) := by
      simp only [hk]
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr ht0)
    rw [hk', ← Rat.mul_den_eq_num t, hL, ht]
    field_simp
  have hkL : (a : ℝ) * L = (c' : ℝ) * k := by exact_mod_cast hkLQ
  -- the power family `F_β = ∏_j f_{β j}`
  have hfc : ∀ i, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (f i) w := fun i => by
    filter_upwards [hOf.mem_nhds hzOf] with w hw
    exact (hfd i).differentiableAt (hOf.mem_nhds hw)
  have hPd : ∀ i, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (powerFamily L f i) w := by
    intro i
    filter_upwards [eventually_all.mpr hfc] with w hw
    unfold powerFamily
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun j _ => (hw _).hasFDerivAt).differentiableAt
  obtain ⟨Bh, hBh0, hBh⟩ := boundedRealGermAt_of_continuousAt hh'
  -- the factorization `F_β = G^k H_β`
  have hfact : ∀ i, ∃ H : ComplexModel n → ℂ, (∀ᶠ w in 𝓝 z, DifferentiableAt ℂ H w) ∧
      powerFamily L f i =ᶠ[𝓝 z] fun w => G w ^ k * H w := by
    intro i
    set B : ℝ := (L : ℝ) * (C₀ + Bb + a * Bh) / c' with hB
    have hbound : ∀ᶠ w in 𝓝 z, ‖powerFamily L f i w‖ ≤ Real.exp (B / 2) * ‖G w ^ k‖ := by
      filter_upwards [heq, hwt, hsupp, hBb, hBh] with w hweq hwtw hsuppw hbw hhw
      have hu' : u (e.val.symm w) = ((c' : ℝ) : EReal) * generatorLog f w + (b w : EReal) := by
        have h1 := hweq
        simp only [chartFunction] at h1
        exact h1
      by_cases hGw : G w = 0
      · -- `u = -∞` at the zeros of `G`, so every `f_j` vanishes there
        have hyD : E.weight (e.val.symm w) = ⊥ := hsuppw.mpr hGw
        have hubot : u (e.val.symm w) = ⊥ := by
          have h := hle (e.val.symm w)
          rw [hyD, EReal.coe_mul_bot_of_pos haR, EReal.bot_add] at h
          exact le_bot_iff.mp h
        rw [hu'] at hubot
        have hglog : generatorLog f w = ⊥ := by
          rcases EReal.add_eq_bot_iff.mp hubot with h | h
          · rw [EReal.mul_eq_bot] at h
            rcases h with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h3, -⟩ | ⟨h4, -⟩
            · exact absurd h1 (EReal.coe_ne_bot _)
            · exact h2
            · exact absurd h3 (EReal.coe_ne_top _)
            · exact absurd (EReal.coe_lt_coe_iff.mp (h4.trans_eq EReal.coe_zero.symm))
                hc'pos.not_gt
          · exact absurd h (EReal.coe_ne_bot _)
        have hS0 : ∑ j, ‖f j w‖ ^ 2 = 0 := by
          rw [generatorLog_eq_log_sum, ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero] at hglog
          exact le_antisymm hglog (Finset.sum_nonneg fun j _ => by positivity)
        have hP0 : ‖powerFamily L f i w‖ ^ 2 = 0 := by
          have hPle := norm_sq_powerFamily_le L f w i
          rw [hS0, zero_pow hLpos.ne'] at hPle
          exact le_antisymm hPle (sq_nonneg _)
        have hP0' : ‖powerFamily L f i w‖ = 0 := pow_eq_zero_iff (by norm_num) |>.mp hP0
        rw [hP0']
        positivity
      · by_cases hPw : powerFamily L f i w = 0
        · rw [hPw, norm_zero]
          positivity
        have hGpos : 0 < ‖G w‖ ^ 2 := by positivity
        have hwt' : E.weight (e.val.symm w) = ((Real.log (‖G w‖ ^ 2) + h' w : ℝ) : EReal) := by
          rw [hwtw, ENNReal.log_ofReal_of_pos hGpos, EReal.coe_add]
        have hPle := norm_sq_powerFamily_le L f w i
        have hPpos : 0 < ‖powerFamily L f i w‖ ^ 2 := by positivity
        have hSpos : 0 < ∑ j, ‖f j w‖ ^ 2 := by
          by_contra hS0
          push Not at hS0
          have h0 : ∑ j, ‖f j w‖ ^ 2 = 0 :=
            le_antisymm hS0 (Finset.sum_nonneg fun j _ => by positivity)
          rw [h0, zero_pow hLpos.ne'] at hPle
          linarith
        have hgl : generatorLog f w = ((Real.log (∑ j, ‖f j w‖ ^ 2) : ℝ) : EReal) := by
          rw [generatorLog_eq_log_sum, ENNReal.log_ofReal_of_pos hSpos]
        have hineq := hle (e.val.symm w)
        rw [hu', hgl, hwt', ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add,
          EReal.coe_le_coe_iff] at hineq
        have hlogP : Real.log (‖powerFamily L f i w‖ ^ 2) ≤
            L * Real.log (∑ j, ‖f j w‖ ^ 2) := by
          rw [← Real.log_pow]
          exact Real.log_le_log hPpos hPle
        have h1 := (abs_le.mp hbw).1
        have h2 : (a : ℝ) * h' w ≤ a * Bh := mul_le_mul_of_nonneg_left (abs_le.mp hhw).2 haR0
        have hlogS : Real.log (∑ j, ‖f j w‖ ^ 2) ≤
            (C₀ + Bb + a * Bh + a * Real.log (‖G w‖ ^ 2)) / c' := by
          rw [le_div_iff₀ hc'pos]
          nlinarith
        have hlogF : Real.log (‖powerFamily L f i w‖ ^ 2) ≤
            (k : ℝ) * Real.log (‖G w‖ ^ 2) + B := by
          calc Real.log (‖powerFamily L f i w‖ ^ 2) ≤ L * Real.log (∑ j, ‖f j w‖ ^ 2) := hlogP
            _ ≤ L * ((C₀ + Bb + a * Bh + a * Real.log (‖G w‖ ^ 2)) / c') :=
              mul_le_mul_of_nonneg_left hlogS hLR.le
            _ = ((L : ℝ) * a / c') * Real.log (‖G w‖ ^ 2) + B := by
              rw [hB]
              field_simp
              ring
            _ = (k : ℝ) * Real.log (‖G w‖ ^ 2) + B := by
              congr 2
              rw [mul_comm (L : ℝ), hkL]
              field_simp
        -- exponentiate
        have hsq : ‖powerFamily L f i w‖ ^ 2 ≤ (Real.exp (B / 2) * ‖G w ^ k‖) ^ 2 := by
          have h3 : ‖powerFamily L f i w‖ ^ 2 ≤ Real.exp ((k : ℝ) * Real.log (‖G w‖ ^ 2) + B) := by
            rw [← Real.exp_log hPpos]
            exact Real.exp_le_exp.mpr hlogF
          have h4 : Real.exp ((k : ℝ) * Real.log (‖G w‖ ^ 2) + B) =
              (Real.exp (B / 2) * ‖G w ^ k‖) ^ 2 := by
            rw [Real.exp_add, ← Real.log_pow, Real.exp_log (pow_pos hGpos k), mul_pow, norm_pow,
              ← Real.exp_nat_mul]
            ring_nf
          rw [← h4]
          exact h3
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq
    have hGk : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w => G w ^ k) w :=
      hGd.mono fun w hw => hw.pow k
    have hndk : ∀ᶠ w in 𝓝 z, ∀ U ∈ 𝓝 w, ∃ w' ∈ U, G w' ^ k ≠ 0 := by
      filter_upwards [hnd] with w hw U hU
      obtain ⟨w', hw'U, hw'⟩ := hw U hU
      exact ⟨w', hw'U, pow_ne_zero k hw'⟩
    obtain ⟨H, hH, hFH⟩ := exists_eq_mul_of_norm_le (hPd i) hGk hndk ⟨_, hbound⟩
    exact ⟨H, hH, hFH.mono fun w hw => by rw [hw]; ring⟩
  choose H hHd hPH using hfact
  -- the residual off `Supp E`
  set A : ComplexModel n → EReal :=
    fun w => (((c' : ℝ) / L : ℝ) : EReal) * generatorLog H w with hA
  set R : ComplexModel n → ℝ := fun w => b w - (a : ℝ) * h' w with hR
  set B : ℝ := Bb + (a : ℝ) * Bh with hB
  have hB0 : 0 ≤ B := by positivity
  have hrep : ∀ᶠ w in 𝓝 z, G w ≠ 0 →
      chartFunction (SGPT.Okounkov.smoothDivisorOffResidual E a u) e w = A w + (R w : EReal) := by
    filter_upwards [heq, hwt, hsupp, eventually_all.mpr hPH] with w hweq hwtw hsuppw hPHw hGw
    have hyD : e.val.symm w ∉ E.support := fun h => hGw (hsuppw.mp h)
    have hGpos : 0 < ‖G w‖ ^ 2 := by positivity
    have hlogG : ENNReal.log (ENNReal.ofReal (‖G w‖ ^ 2)) =
        ((Real.log (‖G w‖ ^ 2) : ℝ) : EReal) := ENNReal.log_ofReal_of_pos hGpos
    have hgP : generatorLog (powerFamily L f) w =
        ((k : ℝ) : EReal) * ((Real.log (‖G w‖ ^ 2) : ℝ) : EReal) + generatorLog H w := by
      have : generatorLog (powerFamily L f) w = generatorLog (fun i w => G w ^ k * H i w) w := by
        rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by rw [hPHw i]
      rw [this, TranscendentalCore.generatorLog_pow_mul, hlogG]
    have hu' : u (e.val.symm w) =
        (((c' : ℝ) / L : ℝ) : EReal) * generatorLog (powerFamily L f) w + (b w : EReal) := by
      have h1 := hweq
      simp only [chartFunction] at h1
      rw [h1, generatorLog_powerFamily, ← mul_assoc, ← EReal.coe_mul, div_mul_cancel₀ _ hLR.ne']
    simp only [chartFunction, SGPT.Okounkov.smoothDivisorOffResidual, if_neg hyD]
    rw [hu', hgP, hwtw, hlogG,
      TranscendentalCore.ereal_residual_identity (div_pos hc'pos hLR) (k : ℝ)
        (Real.log (‖G w‖ ^ 2)) (b w) (a : ℝ) (h' w)]
    have hzero : (c' : ℝ) / L * k - (a : ℝ) = 0 := by
      field_simp
      linarith [hkL]
    rw [hzero, EReal.coe_zero, zero_mul, add_zero]
  -- a neighbourhood of `z` where all the local data hold
  obtain ⟨O, hOsub, hO, hzO⟩ := _root_.mem_nhds_iff.mp (hrep.and (hsupp.and (hnd.and
    ((eventually_all.mpr hHd).and (hBb.and (hBh.and (e.val.open_target.mem_nhds hz)))))))
  have hAc : ∀ w ∈ O, ContinuousAt A w := fun w hw =>
    continuousAt_coe_mul_generatorLog (div_pos hc'pos hLR).ne'
      (fun i => ((hOsub hw).2.2.2.1 i).continuousAt)
  have hRB : ∀ w ∈ O, |R w| ≤ B := by
    intro w hw
    have h1 := (hOsub hw).2.2.2.2.1
    have h2 := (hOsub hw).2.2.2.2.2.1
    calc |R w| ≤ |b w| + |(a : ℝ) * h' w| := abs_sub _ _
      _ = |b w| + (a : ℝ) * |h' w| := by rw [abs_mul, abs_of_nonneg haR0]
      _ ≤ Bb + (a : ℝ) * Bh := add_le_add h1 (mul_le_mul_of_nonneg_left h2 haR0)
  have hbounds : ∀ w ∈ O,
      A w + ((-B : ℝ) : EReal) ≤
        chartFunction (extensionAcross E.support (SGPT.Okounkov.smoothDivisorOffResidual E a u))
          e w ∧
      chartFunction (extensionAcross E.support (SGPT.Okounkov.smoothDivisorOffResidual E a u))
          e w ≤ A w + (B : EReal) := by
    intro w hw
    have hwt' : w ∈ e.val.target := (hOsub hw).2.2.2.2.2.2
    rw [chartFunction_extensionAcross_eq_extension_preimage hwt']
    constructor
    · refine le_uscRegularization_cut ?_ (continuousAt_add_coe (hAc w hw) _) ?_
      · intro V hV
        obtain ⟨w', hw'V, hGw'⟩ := (hOsub hw).2.2.1 (V ∩ O) (inter_mem hV (hO.mem_nhds hw))
        exact ⟨w', hw'V.1, fun hK => hGw' (((hOsub hw'V.2).2.1).mp hK)⟩
      · filter_upwards [hO.mem_nhds hw] with w' hw'O hw'K
        have hGw' : G w' ≠ 0 := fun h0 => hw'K (((hOsub hw'O).2.1).mpr h0)
        rw [(hOsub hw'O).1 hGw']
        exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp (hRB w' hw'O)).1)
    · refine uscRegularization_cut_le (continuousAt_add_coe (hAc w hw) _).upperSemicontinuousAt ?_
      filter_upwards [hO.mem_nhds hw] with w' hw'O hw'K
      have hGw' : G w' ≠ 0 := fun h0 => hw'K (((hOsub hw'O).2.1).mpr h0)
      rw [(hOsub hw'O).1 hGw']
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp (hRB w' hw'O)).2)
  have hAtop : ∀ w, A w ≠ ⊤ := fun w =>
    TranscendentalCore.ereal_coe_mul_ne_top (div_pos hc'pos hLR).le
      (TranscendentalCore.generatorLog_ne_top H w)
  have hex : ∀ w ∈ O, ∃ r : ℝ, |r| ≤ B ∧
      chartFunction (extensionAcross E.support (SGPT.Okounkov.smoothDivisorOffResidual E a u))
        e w = A w + (r : EReal) := fun w hw =>
    TranscendentalCore.exists_remainder_of_bounds hB0 (hAtop w) (hbounds w hw).1 (hbounds w hw).2
  choose! r hr hrW using hex
  have hAtype : HasAnalyticSingularityTypeAt A z := by
    have h := TranscendentalCore.hasAnalyticSingularityTypeAt_generatorLog (H := H) hHd
      (c := c' / L) (div_pos hc'Q (by exact_mod_cast hLpos))
    have hcast : (((c' / L : ℚ) : ℝ)) = (c' : ℝ) / L := by push_cast; rfl
    rw [hcast] at h
    exact h
  refine DemaillyAnalyticType.HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded hAtype
    (b := r) ⟨B, hB0, ?_⟩ ?_
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact hr w hw
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact hrW w hw

end Local

/-! ### The global statement -/

section Global

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- **`tok-partial:residual`** (the divisor case of `tok:siu-analytic`; DRWNXZ Lemma 2.3 as used
in Lemma 5.5): on a compact complex manifold, if `u ∈ 𝒜(θ)` and `u ⪯ ψ_E` for a metered effective
`ℚ`-divisor `E`, then `u = ψ_E + W` with `W ∈ 𝒜(θ - Θ_E)`. -/
theorem divisorResidual_mem_analyticCurrents {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : u ∈ TranscendentalCore.analyticCurrents θ) (E : MeteredEffectiveQDivisor n M)
    (hle : SGPT.PSH.SingularityLE u E.weight) :
    ∃ W ∈ TranscendentalCore.analyticCurrents (θ - E.curvature), ∀ x, u x = E.weight x + W x := by
  classical
  obtain ⟨C₀, hC₀⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hle
  -- an integral model `E' = q E`
  obtain ⟨q, hq, D, hD⟩ := TranscendentalLifting.exists_integralModel E
  have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  set E' := MeteredDivisorScaling.smul hq0 E with hE'
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  set a : ℚ := (q : ℚ)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.mpr hqQ
  have haq : (a : ℝ) * (q : ℝ) = 1 := by
    rw [ha]
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast hq.ne')
  have hEsupp : E'.support = E.support := MeteredDivisorScaling.smul_support hq0 hqQ.ne' E
  have hwE : IsThetaPshPotential E.curvature.val E.weight := TranscendentalLifting.isThetaPshPotential_weight E
  have hwE' : IsThetaPshPotential E'.curvature.val E'.weight :=
    SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric D E' hD
  -- `a ψ_{E'} = ψ_E`
  have hweight : ∀ x, ((a : ℝ) : EReal) * E'.weight x = E.weight x := by
    intro x
    rw [MeteredDivisorScaling.weight_smul, ← mul_assoc, ← EReal.coe_mul, Rat.cast_natCast, haq,
      EReal.coe_one, one_mul]
  have hcurv : θ - (a : ℝ) • E'.curvature = θ - E.curvature := by
    rw [MeteredDivisorScaling.curvature_smul, smul_smul, Rat.cast_natCast, haq, one_smul]
  have hle' : ∀ x, u x ≤ ((a : ℝ) : EReal) * E'.weight x + (C₀ : EReal) := fun x => by
    rw [hweight]; exact hC₀ x
  set W := extensionAcross E'.support (SGPT.Okounkov.smoothDivisorOffResidual E' a u) with hW
  have htype : HasManifoldAnalyticSingularityType (n := n) W :=
    fun e z hz => hasAnalyticSingularityTypeAt_divisorResidual D E' hD ha0 hle' e hz (hu.2 e z hz)
  have hEclosed : IsClosed E'.support :=
    (ResidualNef.isComplexAnalyticSubset_support E').isClosed
  have hoff : ThetaPshOff (θ - (a : ℝ) • E'.curvature).val E'.support
      (SGPT.Okounkov.smoothDivisorOffResidual E' a u) :=
    SGPT.Okounkov.thetaPshOff_smoothDivisorOffResidual hu.1 E' (a : ℝ)
  have hWeq : ∀ y, y ∉ E'.support →
      W y = SGPT.Okounkov.smoothDivisorOffResidual E' a u y :=
    fun y hy => extensionAcross_eq_of_notMem hEclosed hoff hy
  -- locally bounded above off `Supp E`
  have hbound : LocallyBoundedAboveOff E'.support
      (SGPT.Okounkov.smoothDivisorOffResidual E' a u) := by
    intro x
    have hxs := mem_complexChartAt_source (n := n) x
    obtain ⟨C, hC⟩ := exists_eventually_le_of_hasAnalyticSingularityTypeAt
      (htype (complexChartAt (n := n) x) _ ((complexChartAt (n := n) x).val.map_source hxs))
    have hcont : Tendsto (complexChartAt (n := n) x).val (𝓝 x)
        (𝓝 ((complexChartAt (n := n) x).val x)) :=
      ((complexChartAt (n := n) x).val.continuousAt hxs).tendsto
    refine ⟨_, (hcont.eventually hC).and
      ((complexChartAt (n := n) x).val.open_source.mem_nhds hxs), C, fun y hy hyD => ?_⟩
    obtain ⟨hy1, hys⟩ := hy
    rw [← hWeq y hyD]
    simpa only [chartFunction, (complexChartAt (n := n) x).val.left_inv hys] using hy1
  -- plurisubharmonic across `Supp E` (removable singularities)
  have hAan : IsComplexAnalyticSubset (n := n) E'.support :=
    ResidualNef.isComplexAnalyticSubset_support E'
  have hAne : E'.support ≠ univ ∨ IsEmpty M := by
    by_cases hM : Nonempty M
    · left
      obtain ⟨x⟩ := hM
      obtain ⟨y, -, hy⟩ := hwE'.2 x univ isOpen_univ trivial
      intro hA
      have hyA : y ∈ E'.support := by rw [hA]; trivial
      exact hy hyA
    · right
      exact not_nonempty_iff.mp hM
  have hWpsh : ThetaPlurisubharmonic (θ - (a : ℝ) • E'.curvature).val W := by
    rcases hAne with hAne | hempty
    · have hclosure := PshAnalyticRemovable.analyticRemovableThetaPsh_of_closed
        (θ - (a : ℝ) • E'.curvature) E'.support (SGPT.Okounkov.smoothDivisorOffResidual E' a u)
        hAan hAne hoff hbound
      exact thetaPlurisubharmonic_extensionAcross_of_localClosure hEclosed hoff hclosure
    · intro e z hz
      exact (hempty.false (e.val.symm z)).elim
  -- the identity `u = ψ_E + W`
  have hid : ∀ x, u x = E.weight x + W x := by
    intro x
    by_cases hx : x ∈ E'.support
    · have hEx : E.weight x = ⊥ := by rw [hEsupp] at hx; exact hx
      have hux : u x = ⊥ := by
        have h := hC₀ x
        rw [hEx, EReal.bot_add] at h
        exact le_bot_iff.mp h
      rw [hux, hEx, EReal.bot_add]
    · rw [hWeq x hx]
      simp only [SGPT.Okounkov.smoothDivisorOffResidual, if_neg hx, hweight]
      have hEx : E.weight x ≠ ⊥ := fun h => hx (by rw [hEsupp]; exact h)
      have hEtop : E.weight x ≠ ⊤ := hwE.1.quasiPlurisubharmonic.ne_top _
      obtain ⟨r, hr⟩ : ∃ r : ℝ, E.weight x = r := ⟨_, (EReal.coe_toReal hEtop hEx).symm⟩
      rw [hr]
      induction u x using EReal.rec with
      | bot => simp
      | top => simp
      | coe s => rw [← EReal.coe_sub, ← EReal.coe_add]; congr 1; ring
  -- locally nondegenerate
  have hWnd : LocallyNondegenerate W := by
    intro x U hU hxU
    obtain ⟨y0, hy0U, hy0⟩ := hwE'.2 x U hU hxU
    obtain ⟨y, hyU, hy⟩ := hu.1.2 y0 (U ∩ E'.supportᶜ) (hU.inter hEclosed.isOpen_compl)
      ⟨hy0U, hy0⟩
    refine ⟨y, hyU.1, fun hWy => hy ?_⟩
    rw [hid y, hWy, EReal.add_bot]
  refine ⟨W, ⟨⟨?_, hWnd⟩, htype⟩, hid⟩
  rw [← hcurv]
  exact hWpsh

/-- **`DivisorResidualStatement`** (the divisor case of `tok:siu-analytic`, published in
`TranscendentalPartialStatement`) holds. -/
theorem divisorResidualStatement : DivisorResidualStatement.{u} :=
  fun _ _ _ _ _ _ θ D _ hv hle => divisorResidual_mem_analyticCurrents (θ := θ) hv D hle

end Global

end SGPT.Okounkov.TranscendentalPartial

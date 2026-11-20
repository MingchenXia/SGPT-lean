import SGPT.PSH.LelongBallLimit
import SGPT.PSH.Supremum
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous
import SGPT.PSH.VariableLelong

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SquaredLogLelongSourceNormalization
open scoped Topology ENNReal NNReal

/-- The actual source slope controls every fixed endpoint, which makes the
logarithmic comparison constant uniform across a locally bounded family. -/
theorem PSHOn.logBallSup_le_endpoint_of_source_lelong {n : ℕ} (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : PSHOn u (ball 0 1))
    {a t : ℝ} (ha : a < 0) (ht : t < a) :
    logBallSup u 0 t ≤ logBallSup u 0 a +
      (2 * (squaredLogLelongNumber (n := n) u 0).toReal) * (t - a) := by
  obtain ⟨s, hs, hsource, hlim, _hpoint⟩ := hu.exists_lelongBall_slope hn
  have hdiv (A : ℝ) : Tendsto (fun b : ℝ => A / b) atBot (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atBot (𝓝 A)).mul
        tendsto_inv_atBot_zero
  have hratio := ((hdiv (logBallSup u 0 a)).sub hlim).div
    ((hdiv a).sub tendsto_const_nhds) (by norm_num : (0 - 1 : ℝ) ≠ 0)
  have hchord : Tendsto
      (ConvexSlopeAtBot.chordSlope (logBallSup u 0) a) atBot (𝓝 s) := by
    have heq : (fun b : ℝ =>
        (logBallSup u 0 a / b - logBallSup u 0 b / b) / (a / b - 1)) =ᶠ[atBot]
        ConvexSlopeAtBot.chordSlope (logBallSup u 0) a := by
      filter_upwards [eventually_lt_atBot 0, eventually_lt_atBot a] with b hb hba
      dsimp [ConvexSlopeAtBot.chordSlope]
      have hden : a / b - 1 ≠ 0 := by
        intro h
        have hab : a = 1 * b := (div_eq_iff hb.ne).mp (sub_eq_zero.mp h)
        linarith
      field_simp [hb.ne, sub_ne_zero.mpr hba.ne', hden]
    simpa using hratio.congr' heq
  have hsle : s ≤ ConvexSlopeAtBot.chordSlope (logBallSup u 0) a t := by
    apply le_of_tendsto hchord
    filter_upwards [eventually_lt_atBot t] with b hb
    apply ConvexSlopeAtBot.chordSlope_mono (T := 0) _ ha hb ht
    intro x y z hxy hyz hz
    exact hu.logBallSup_chord (by norm_num) hxy hyz (by simpa using hz)
  rw [ConvexSlopeAtBot.chordSlope, le_div_iff₀ (by linarith : 0 < a - t)] at hsle
  have hnorm : 2 * (squaredLogLelongNumber (n := n) u 0).toReal = s := by
    rw [hsource, ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hnorm]
  linarith

/-- A genuine common bound at one actual radius produces ONE logarithmic
constant for every member of an arbitrary nonempty original PSH family. -/
theorem family_uniform_lelong_logarithmic_bound {n : ℕ} (hn : 0 < n)
    {I : Type*} [Nonempty I] {u : I → ComplexModel n → EReal}
    (hu : ∀ i, PSHOn (u i) (ball 0 1)) {a M : ℝ} (ha : a < 0)
    (hM : ∀ i z, z ∈ ball (0 : ComplexModel n) (Real.exp a) → u i z ≤ (M : EReal)) :
    (⨅ i, squaredLogLelongNumber (n := n) (u i) 0) ≠ ⊤ ∧
    ∃ C : ℝ, ∀ i z, 0 < ‖z‖ → ‖z‖ < Real.exp a / 2 →
      u i z ≤ ((2 * (⨅ j, squaredLogLelongNumber (n := n) (u j) 0).toReal *
        Real.log ‖z‖ + C : ℝ) : EReal) := by
  let ν : I → ℝ≥0∞ := fun i => squaredLogLelongNumber (n := n) (u i) 0
  have hfinite (i : I) : ν i ≠ ⊤ := by
    obtain ⟨s, _, hsource, _, _⟩ := (hu i).exists_lelongBall_slope hn
    change squaredLogLelongNumber (n := n) (u i) 0 ≠ ⊤
    rw [hsource]
    exact ENNReal.ofReal_ne_top
  let i₀ : I := Classical.choice inferInstance
  refine ⟨ne_top_of_le_ne_top (hfinite i₀) (iInf_le ν i₀), ?_⟩
  let m : ℝ := (⨅ i, ν i).toReal
  refine ⟨M + 2 * m * (Real.log 2 - a), ?_⟩
  intro i z hz hza
  have htwo : 0 < 2 * ‖z‖ := by positivity
  have ht : Real.log (2 * ‖z‖) < a := by
    apply (Real.log_lt_iff_lt_exp htwo).mpr
    linarith
  have hta : Real.log (2 * ‖z‖) < Real.log 1 := by simpa using ht.trans ha
  have hcoe := (hu i).coe_logBallSup (by norm_num : (0 : ℝ) < 1) hta
  have hzball : z ∈ ball (0 : ComplexModel n) (Real.exp (Real.log (2 * ‖z‖))) := by
    rw [Real.exp_log htwo]
    simp only [mem_ball, dist_zero_right]
    linarith
  have hpoint : u i z ≤ (logBallSup (u i) 0 (Real.log (2 * ‖z‖)) : EReal) :=
    (le_iSup₂ (f := fun w (_ : w ∈ ball 0 (Real.exp (Real.log (2 * ‖z‖)))) => u i w)
      z hzball).trans_eq hcoe.symm
  have haM : logBallSup (u i) 0 a ≤ M := by
    apply EReal.coe_le_coe_iff.mp
    rw [(hu i).coe_logBallSup (by norm_num : (0 : ℝ) < 1) (by simpa using ha)]
    exact iSup_le fun w => iSup_le fun hw => hM i w hw
  have hmi : m ≤ (ν i).toReal := ENNReal.toReal_mono (hfinite i) (iInf_le ν i)
  have hendpoint := (hu i).logBallSup_le_endpoint_of_source_lelong hn ha ht
  have hcoeff := mul_le_mul_of_nonpos_right hmi (sub_nonpos.mpr ht.le)
  refine hpoint.trans (EReal.coe_le_coe_iff.mpr ?_)
  change logBallSup (u i) 0 (Real.log (2 * ‖z‖)) ≤
    2 * m * Real.log ‖z‖ + (M + 2 * m * (Real.log 2 - a))
  change logBallSup (u i) 0 (Real.log (2 * ‖z‖)) ≤
    logBallSup (u i) 0 a + 2 * (ν i).toReal * (Real.log (2 * ‖z‖) - a) at hendpoint
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne'] at hendpoint hcoeff ⊢
  nlinarith

/-- The actual neighborhood regularization retains the genuinely uniform
family logarithmic bound at every point of the punctured open ball. -/
theorem family_uniform_lelong_logarithmic_bound_uscSup {n : ℕ} (hn : 0 < n)
    {I : Type*} [Nonempty I] {u : I → ComplexModel n → EReal}
    (hu : ∀ i, PSHOn (u i) (ball 0 1)) {a M : ℝ} (ha : a < 0)
    (hM : ∀ i z, z ∈ ball (0 : ComplexModel n) (Real.exp a) → u i z ≤ (M : EReal)) :
    (⨅ i, squaredLogLelongNumber (n := n) (u i) 0) ≠ ⊤ ∧
    ∃ C : ℝ, ∀ z, 0 < ‖z‖ → ‖z‖ < Real.exp a / 2 →
      uscSup u z ≤ ((2 * (⨅ j, squaredLogLelongNumber (n := n) (u j) 0).toReal *
        Real.log ‖z‖ + C : ℝ) : EReal) := by
  obtain ⟨hfinite, C, hC⟩ := family_uniform_lelong_logarithmic_bound hn hu ha hM
  refine ⟨hfinite, C, ?_⟩
  intro z hz hza
  let m : ℝ := (⨅ i, squaredLogLelongNumber (n := n) (u i) 0).toReal
  have hlog : ContinuousAt (fun w : ComplexModel n => Real.log ‖w‖) z :=
    (Real.continuousAt_log hz.ne').comp continuous_norm.continuousAt
  have hg : ContinuousAt
      (fun w : ComplexModel n => ((2 * m * Real.log ‖w‖ + C : ℝ) : EReal)) z :=
    continuous_coe_real_ereal.continuousAt.comp
      ((continuousAt_const.mul hlog).add continuousAt_const)
  change uscRegularization (fun w => ⨆ i, u i w) z ≤ _
  apply uscRegularization_le_of_eventually_le hg.upperSemicontinuousAt
  have hp : ∀ᶠ w in 𝓝 z, 0 < ‖w‖ :=
    continuous_norm.continuousAt.eventually (Ioi_mem_nhds hz)
  have hr : ∀ᶠ w in 𝓝 z, ‖w‖ < Real.exp a / 2 :=
    continuous_norm.continuousAt.eventually (Iio_mem_nhds hza)
  filter_upwards [hp, hr] with w hw hwr
  exact iSup_le fun i => hC i w hw hwr

/-- The actual source growth reader of the unchanged regularized supremum
is the infimum of the original readers, for every model dimension. -/
theorem squaredLogLelongNumber_uscSup_eq_iInf_on_unit_ball {n : ℕ}
    {I : Type*} [Nonempty I] {u : I → ComplexModel n → EReal}
    (hu : ∀ i, PSHOn (u i) (ball 0 1)) {a M : ℝ} (ha : a < 0)
    (hM : ∀ i z, z ∈ ball (0 : ComplexModel n) (Real.exp a) → u i z ≤ (M : EReal)) :
    squaredLogLelongNumber (n := n) (uscSup u) 0 =
      ⨅ i, squaredLogLelongNumber (n := n) (u i) 0 := by
  by_cases hn : n = 0
  · simp [squaredLogLelongNumber, hn]
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨hfinite, C, hC⟩ :=
    family_uniform_lelong_logarithmic_bound_uscSup hpos hu ha hM
  let μ : ℝ≥0∞ := ⨅ i, squaredLogLelongNumber (n := n) (u i) 0
  apply le_antisymm
  · apply le_iInf
    intro i
    rw [squaredLogLelongNumber, if_neg hn]
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨D, hD⟩ := hγ
    rw [squaredLogLelongNumber, if_neg hn]
    apply le_iSup₂_of_le (f := fun (δ : ℝ≥0) (_ : ∃ D : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ComplexModel n),
      u i z ≤ (((δ : ℝ) * Real.log
        (‖(complexChartAt (n := n) (0 : ComplexModel n)).val z -
          (complexChartAt (n := n) (0 : ComplexModel n)).val 0‖ ^ 2) + D : ℝ) : EReal)) =>
      (δ : ℝ≥0∞)) γ ⟨D, ?_⟩ le_rfl
    filter_upwards [hD] with z hz
    exact (le_uscSup u i z).trans hz
  · change μ ≤ squaredLogLelongNumber (n := n) (uscSup u) 0
    rw [squaredLogLelongNumber, if_neg hn]
    let γ : ℝ≥0 := μ.toNNReal
    have hcast : (γ : ℝ≥0∞) = μ := ENNReal.coe_toNNReal hfinite
    rw [← hcast]
    apply le_iSup₂_of_le (f := fun (δ : ℝ≥0) (_ : ∃ D : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ComplexModel n),
      uscSup u z ≤ (((δ : ℝ) * Real.log
        (‖(complexChartAt (n := n) (0 : ComplexModel n)).val z -
          (complexChartAt (n := n) (0 : ComplexModel n)).val 0‖ ^ 2) + D : ℝ) : EReal)) =>
      (δ : ℝ≥0∞)) γ ⟨C, ?_⟩ le_rfl
    rw [eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds (0 : ComplexModel n) (by positivity : 0 < Real.exp a / 2)]
      with z hz hz0
    have h := hC z (norm_pos_iff.mpr hz0)
      (by simpa only [mem_ball, dist_zero_right] using hz)
    simpa only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      id_eq, sub_zero, Real.log_pow, Nat.cast_ofNat, γ, ENNReal.coe_toNNReal, μ,
      ENNReal.coe_toNNReal_eq_toReal, mul_comm, mul_left_comm, mul_assoc] using h

/-- Genuine affine localization transports the complete source formula to
every actual ball, retaining the original model and its independent reader. -/
theorem squaredLogLelongNumber_uscSup_eq_iInf_of_ball_family {n : ℕ}
    {I : Type*} [Nonempty I] {u : I → ComplexModel n → EReal} {U : Set (ComplexModel n)}
    (hu : ∀ i, DiscPshOn (u i) U) {b : ComplexModel n} {r M : ℝ} (hr : 0 < r)
    (hB : ball b r ⊆ U) (hnd : ∀ i, ∃ z ∈ ball b r, u i z ≠ ⊥)
    (hM : ∀ i z, z ∈ ball b r → u i z ≤ (M : EReal)) :
    squaredLogLelongNumber (n := n) (uscSup u) b =
      ⨅ i, squaredLogLelongNumber (n := n) (u i) b := by
  let H : ComplexModel n ≃ₜ ComplexModel n :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addRight b)
  have hH (w : ComplexModel n) : H w = r • w + b := rfl
  have hHinv (z : ComplexModel n) : H.symm z = r⁻¹ • (z - b) := rfl
  have hH0 : H 0 = b := by rw [hH]; simp
  have hinvb : H.symm b = 0 := by rw [← hH0, H.symm_apply_apply]
  have hnorm (w : ComplexModel n) : dist (H w) b = r * ‖w‖ := by
    rw [hH, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hmap : MapsTo H (ball (0 : ComplexModel n) 1) (ball b r) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    change dist (H w) b < r
    rw [hnorm]
    nlinarith
  have hdiffH : Differentiable ℂ H := by
    change Differentiable ℂ (fun w : ComplexModel n => r • w + b)
    exact (differentiable_id.const_smul r).add_const b
  have hdiffInv : Differentiable ℂ H.symm := by
    change Differentiable ℂ (fun z : ComplexModel n => r⁻¹ • (z - b))
    exact (differentiable_id.sub_const b).const_smul r⁻¹
  let Φ : LocalHolomorphicEquivAt (n := n) b := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ b
    toFun := H.symm
    invFun := H
    toFun_holomorphic := hdiffInv.differentiableOn
    invFun_holomorphic := hdiffH.differentiableOn
    mapsTo_toFun := fun _ _ => mem_univ _
    mapsTo_invFun := fun _ _ => mem_univ _
    left_inv := fun z _ => H.apply_symm_apply z
    right_inv := fun w _ => H.symm_apply_apply w }
  have hcov (f : ComplexModel n → EReal) :
      squaredLogLelongNumber (n := n) (f ∘ H) 0 = squaredLogLelongNumber (n := n) f b := by
    change squaredLogLelongNumber (n := n) (fun z => f (H z)) 0 = _
    simpa only [Φ, hinvb, Function.comp_apply] using
      VariableComplexAtlas.squaredLogLelongNumber_comp_inv_eq Φ (mem_univ b) f
  let v : I → ComplexModel n → EReal := fun i w => u i (H w)
  have hv (i : I) : PSHOn (v i) (ball 0 1) := by
    have hdisc : DiscPshOn (v i) (H ⁻¹' U) := by
      have hp := (hu i).comp_affine (r • ContinuousLinearMap.id ℂ (ComplexModel n)) b
      have heq : (fun w => b + (r • ContinuousLinearMap.id ℂ (ComplexModel n)) w) = H := by
        funext w
        change b + r • w = H w
        rw [hH, add_comm]
      change DiscPshOn ((u i) ∘ (fun w => b +
        (r • ContinuousLinearMap.id ℂ (ComplexModel n)) w))
        ((fun w => b + (r • ContinuousLinearMap.id ℂ (ComplexModel n)) w) ⁻¹' U) at hp
      rw [heq] at hp
      exact hp
    refine ⟨hdisc.mono (fun w hw => hB (hmap hw)), ?_⟩
    obtain ⟨z, hz, hzn⟩ := hnd i
    have hh := hnorm (H.symm z)
    rw [H.apply_symm_apply] at hh
    have hw : ‖H.symm z‖ < 1 := by
      have hz' : dist z b < r := hz
      nlinarith
    exact ⟨H.symm z, by simpa only [mem_ball, dist_zero_right] using hw,
      by simpa only [v, H.apply_symm_apply] using hzn⟩
  have hm : ∀ i w, w ∈ ball (0 : ComplexModel n) (Real.exp (-1)) → v i w ≤ (M : EReal) := by
    intro i w hw
    exact hM i (H w) (hmap ((ball_subset_ball
      (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)).le) hw))
  have hformula := squaredLogLelongNumber_uscSup_eq_iInf_on_unit_ball hv
    (by norm_num : (-1 : ℝ) < 0) hm
  have hreg : uscSup v = (uscSup u) ∘ H := by
    funext w
    exact uscRegularization_comp_homeomorph_apply (fun z => ⨆ i, u i z) H w
  rw [hreg] at hformula
  change squaredLogLelongNumber (n := n) ((uscSup u) ∘ H) 0 =
    ⨅ i, squaredLogLelongNumber (n := n) (u i ∘ H) 0 at hformula
  simpa only [hcov] using hformula

namespace VariableComplexAtlas

/-- The complete original arbitrary-family Lelong corollary, with actual
local uniform bounds and genuine variable-dimensional source PSH data. -/
theorem sourceLelong_uscSup_eq_iInf {X : Type*} [TopologicalSpace X]
    (A : VariableComplexAtlas X) {I : Type*} [Nonempty I] {u : I → X → EReal}
    (hu : ∀ i, A.IsPSH (u i))
    (hb : SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove
      (Set.range u) univ) (x : X) :
    A.sourceLelong (uscSup u) x = ⨅ i, A.sourceLelong (u i) x := by
  classical
  obtain ⟨i, hi⟩ := A.cover x
  let e := A.chart i
  let b := e x
  have hbt : b ∈ e.target := e.map_source hi
  obtain ⟨V, hV, M, hM⟩ := A.locallyBounded_coordinateFamily hb i b hbt
  rw [nhdsWithin_eq_nhds.mpr (e.open_target.mem_nhds hbt)] at hV
  have hnbhd : V ∩ e.target ∈ 𝓝 b := inter_mem hV (e.open_target.mem_nhds hbt)
  obtain ⟨r, hr, hBr⟩ := Metric.mem_nhds_iff.mp hnbhd
  have hB : ball b r ⊆ e.target := fun z hz => (hBr hz).2
  have hnd (j : I) : ∃ z ∈ ball b r, A.coordinate (u j) i z ≠ ⊥ :=
    LocallyNondegenerate.exists_coordinate_ne_bot (hu j).locallyNondegenerate e
      isOpen_ball hB (mem_ball_self hr)
  have hformula := squaredLogLelongNumber_uscSup_eq_iInf_of_ball_family
    (fun j => ((hu j).chartPlurisubharmonic i).discPshOn) hr hB hnd
    (fun j z hz => hM j z (hBr hz))
  have hgerm : uscSup (fun j => A.coordinate (u j) i) =ᶠ[𝓝 b]
      A.coordinate (uscSup u) i := by
    filter_upwards [e.open_target.mem_nhds hbt] with z hz
    exact A.uscSup_coordinateFamily u i hz
  have hcongr := squaredLogLelongNumber_congr hgerm
  simp_rw [A.sourceLelong_eq_chart _ x i hi]
  exact hcongr.symm.trans hformula

end VariableComplexAtlas
end SGPT.PSH

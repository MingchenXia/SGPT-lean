import SGPT.NPP.SourceEnvelopeComplexRadius

/-!
# Joint continuity of the actual radial integral

Complete blueprint: `blueprint/src/dnt-big-joint-radial-continuity.tex`,
written first. A local compact cutoff and an actual integrable dominating
function prove joint continuity in the base point and positive radius. The
literal source envelope supplies its own local L¹ input from big-class data.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ}

/-- Actual local domination proves joint continuity of an actual radial
pairing with an integrable function; the radius remains positive. -/
theorem continuousAt_integrable_jointRadialPairing {ρ : ComplexModel n → ℝ}
    (hρ : IsRadialKernel ρ) {f : ComplexModel n → ℝ} (hf : Integrable f)
    {p : ComplexModel n × ℝ} (hr : 0 < p.2) :
    ContinuousAt (fun q : ComplexModel n × ℝ =>
      ∫ x, f x * scaledKernel ρ q.2 (x - q.1)) p := by
  let d := Module.finrank ℝ (ComplexModel n)
  have hcoef : ContinuousAt (fun q : ComplexModel n × ℝ => (q.2 ^ d)⁻¹) p :=
    (continuous_snd.continuousAt.pow d).inv₀ (pow_ne_zero d hr.ne')
  obtain ⟨M, hM⟩ := hρ.hasCompactSupport.exists_bound_of_continuous hρ.continuous
  let B : ℝ := max M 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ x, ‖ρ x‖ ≤ B := fun x => (hM x).trans (le_max_left _ _)
  let A : ℝ := ‖(p.2 ^ d)⁻¹‖ + 1
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hcoefBd : ∀ᶠ q in 𝓝 p, ‖(q.2 ^ d)⁻¹‖ ≤ A := by
    filter_upwards [hcoef.norm.eventually (gt_mem_nhds (lt_add_one ‖(p.2 ^ d)⁻¹‖))] with q hq
    exact hq.le
  have hmeas : ∀ᶠ q in 𝓝 p,
      AEStronglyMeasurable (fun x => f x * scaledKernel ρ q.2 (x - q.1)) volume := by
    exact Eventually.of_forall fun q => hf.aestronglyMeasurable.mul
      (((contDiff_scaledKernel hρ q.2).continuous.comp
        (continuous_id.sub continuous_const)).aestronglyMeasurable)
  have hbound : ∀ᶠ q in 𝓝 p, ∀ᵐ x ∂volume,
      ‖f x * scaledKernel ρ q.2 (x - q.1)‖ ≤ (A * B) * ‖f x‖ := by
    filter_upwards [hcoefBd] with q hq
    exact Eventually.of_forall fun x => by
      simp only [scaledKernel, norm_mul]
      have hk : ‖(q.2 ^ d)⁻¹‖ * ‖ρ (q.2⁻¹ • (x - q.1))‖ ≤ A * B :=
        mul_le_mul hq (hB _) (norm_nonneg _) hA0
      calc
        ‖f x‖ * (‖(q.2 ^ Module.finrank ℝ (ComplexModel n))⁻¹‖ *
            ‖ρ (q.2⁻¹ • (x - q.1))‖) ≤ ‖f x‖ * (A * B) :=
          mul_le_mul_of_nonneg_left hk (norm_nonneg _)
        _ = (A * B) * ‖f x‖ := mul_comm _ _
  apply continuousAt_of_dominated hmeas hbound (hf.norm.const_mul (A * B))
  exact Eventually.of_forall fun x => by
    have hi : ContinuousAt (fun q : ComplexModel n × ℝ => q.2⁻¹) p :=
      continuous_snd.continuousAt.inv₀ hr.ne'
    have harg : ContinuousAt (fun q : ComplexModel n × ℝ => q.2⁻¹ • (x - q.1)) p :=
      hi.smul (continuous_const.sub continuous_fst).continuousAt
    exact continuousAt_const.mul (hcoef.mul (hρ.continuous.continuousAt.comp harg))

/-- Actual compact localization extends joint radial continuity to every
locally integrable real representative, without continuity of that function. -/
theorem continuousAt_radialRegularization_joint {ρ : ComplexModel n → ℝ}
    (hρ : IsRadialKernel ρ) {u : ComplexModel n → EReal} {W : Set (ComplexModel n)}
    (huL : LocallyIntegrableOn (fun x => (u x).toReal) W volume)
    {p : ComplexModel n × ℝ} (hr : 0 < p.2) (hp : p.1 ∈ innerDomain W p.2) :
    ContinuousAt (fun q : ComplexModel n × ℝ => radialRegularization ρ u q.2 q.1) p := by
  obtain ⟨d, hrd, hdW⟩ := hp
  let ε : ℝ := (d - p.2) / 4
  have hε : 0 < ε := by dsimp only [ε]; linarith
  let R : ℝ := (p.2 + d) / 2
  let K : Set (ComplexModel n) := closedBall p.1 R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKW : K ⊆ W := (closedBall_subset_ball (by dsimp only [R]; linarith)).trans hdW
  let f : ComplexModel n → ℝ := K.indicator (fun x => (u x).toReal)
  have hf : Integrable f := ((huL.mono_set hKW).integrableOn_isCompact hK).integrable_indicator
    hK.measurableSet
  have hnear₁ : ∀ᶠ q : ComplexModel n × ℝ in 𝓝 p, dist q.1 p.1 < ε :=
    (continuous_fst.tendsto p).eventually (Metric.ball_mem_nhds _ hε)
  have hnear₂ : ∀ᶠ q : ComplexModel n × ℝ in 𝓝 p, dist q.2 p.2 < ε :=
    (continuous_snd.tendsto p).eventually (Metric.ball_mem_nhds _ hε)
  have hpos : ∀ᶠ q : ComplexModel n × ℝ in 𝓝 p, 0 < q.2 :=
    continuous_snd.continuousAt.eventually (lt_mem_nhds hr)
  have heq : (fun q : ComplexModel n × ℝ => radialRegularization ρ u q.2 q.1) =ᶠ[𝓝 p]
      (fun q : ComplexModel n × ℝ => ∫ x, f x * scaledKernel ρ q.2 (x - q.1)) := by
    filter_upwards [hnear₁, hnear₂, hpos] with q hq₁ hq₂ hqpos
    have hq₂' : q.2 - p.2 < ε := by
      rw [Real.dist_eq] at hq₂
      exact (abs_lt.mp hq₂).2
    have hsupp : tsupport (fun x => scaledKernel ρ q.2 (x - q.1)) ⊆ K := by
      intro x hx
      have hxb : dist x q.1 ≤ q.2 := tsupport_scaledKernel_translate_subset hρ hqpos q.1 hx
      change dist x p.1 ≤ R
      have ht := dist_triangle x q.1 p.1
      dsimp only [R, ε] at *
      linarith
    rw [radialRegularization_eq_translationPairing hρ]
    change (∫ x, (u x).toReal * scaledKernel ρ q.2 (x - q.1)) =
      ∫ x, f x * scaledKernel ρ q.2 (x - q.1)
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (u x).toReal * scaledKernel ρ q.2 (x - q.1) =
        f x * scaledKernel ρ q.2 (x - q.1)
      by_cases hxK : x ∈ K
      · simp only [f, indicator_of_mem hxK]
      · have hxκ : x ∉ tsupport (fun x => scaledKernel ρ q.2 (x - q.1)) :=
          fun h => hxK (hsupp h)
        rw [image_eq_zero_of_notMem_tsupport hxκ, mul_zero, mul_zero]
  exact (continuousAt_congr heq).mpr (continuousAt_integrable_jointRadialPairing hρ hf hr)

/-- Joint continuity of the same literal source-envelope smoothing in base
and logarithmic radius, derived from actual local L¹ rather than assumed. -/
theorem sourceChartRadialSmoothing_joint_continuousOn {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    (w : KahlerBackground n Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : Continuous g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    (hWc : IsPreconnected W) {x₀ : ComplexModel n} (hx₀ : x₀ ∈ W)
    {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ) :
    ContinuousOn (fun p : ComplexModel n × ℂ =>
      sourceChartRadialSmoothing ρ θ g e ψ (Real.exp p.2.re) p.1 + ψ p.1)
      (radialJointDomain W) := by
  obtain ⟨φ, hφ⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  have hPn := SGPT.Okounkov.TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous
    w (atlasClosedFormToNative θ) hg hφ
  have hP : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))) := by
    rw [sourceObstacleEnvelope_eq_native]
    exact hPn
  have hp : PlurisubharmonicOn (sourceEnvelopeChartPotential θ g e ψ) W := by
    change PlurisubharmonicOn
      (fun z => chartFunction (sourceRelativeEnvelope θ (fun _ => ⊤)
        (fun x => (g x : EReal))) e z + (ψ z : EReal)) W
    exact ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hP.1 e hψ
  obtain ⟨z₀, hzW, hzne⟩ := hP.quasiPshPotential.2.exists_chart_ne_bot e hψ.1 hψ.2.1 hx₀
  have hne : ∃ z ∈ W, sourceEnvelopeChartPotential θ g e ψ z ≠ ⊥ :=
    ⟨z₀, hzW, EReal.add_ne_bot_iff.mpr ⟨hzne, EReal.coe_ne_bot _⟩⟩
  have huL := hp.locallyIntegrableOn_toReal volume hWc hne
  intro p hp
  have hinner : p.1 ∈ innerDomain W (Real.exp p.2.re) := hp
  have hloc := continuousAt_radialRegularization_joint (p := (p.1, Real.exp p.2.re))
    hρ huL (Real.exp_pos p.2.re) hinner
  have hmap : ContinuousAt
      (fun q : ComplexModel n × ℂ => (q.1, Real.exp q.2.re)) p := by fun_prop
  have hcomp := ContinuousAt.comp'
    (f := fun q : ComplexModel n × ℂ => (q.1, Real.exp q.2.re)) hloc hmap
  simpa only [sourceChartRadialSmoothing, sub_add_cancel] using hcomp.continuousWithinAt

end SGPT.NPP.DNTBig

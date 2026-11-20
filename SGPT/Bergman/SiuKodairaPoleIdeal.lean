import SGPT.Bergman.SiuKodairaRadialIdeal
import SGPT.Bergman.SiuUniformGenerationGeometry
import SGPT.PSH.BookMultiplierSections
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison

/-!
# The actual isolated pole has the original point ideal

Native preferred-chart multiplier membership is transported to the actual
fixed pole chart.  The cutoff logarithmic profile is proved from the
original pole function, and its critical coefficient is the dimension.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:pole-ideal`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The exact preferred-chart multiplier ideal is the actual maximal point
ideal when one actual chart has the critical radial logarithmic profile. -/
theorem multiplierIdeal_mem_iff_vanish_of_criticalChart (hn : 0 < n)
    {θ : SmoothRealForm n X 2} {φ : X → EReal} (hφ : ThetaPlurisubharmonic θ φ)
    (e : ComplexChart n X) {x : X} (hx : x ∈ e.val.source)
    (hprofile : chartFunction φ e =ᶠ[𝓝 (e.val x)] criticalPole n (e.val x))
    (g : X → ℂ) :
    (multiplierIdeal (n := n) 1 φ).mem x g ↔ HolomorphicAt n g x ∧ g x = 0 := by
  let c := complexChartAt (n := n) x
  have hxc : x ∈ c.val.source := mem_complexChartAt_source x
  have husce : UpperSemicontinuousOn (chartFunction φ e) (ChartWeightedL2.overlapDomain e c) :=
    (hφ.quasiPlurisubharmonic e).upperSemicontinuousOn.mono fun _ hz => hz.1
  have huscc : UpperSemicontinuousOn (chartFunction φ c) (ChartWeightedL2.overlapDomain c e) :=
    (hφ.quasiPlurisubharmonic c).upperSemicontinuousOn.mono fun _ hz => hz.1
  constructor
  · intro hg
    have hchart := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      e c hx hxc husce (by norm_num : (1 : ℝ) ≠ 0) hg.2
    have hrad := hchart.congr hprofile (EventuallyEq.refl _ _)
    have hzero := eq_zero_of_multiplierIntegrableAt_criticalPole hn hrad
    exact ⟨hg.1, by simpa only [e.val.left_inv hx] using hzero⟩
  · rintro ⟨hg, hg0⟩
    obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hg
    let W := e.val.target ∩ e.val.symm ⁻¹' V
    have hW : IsOpen W := e.val.isOpen_inter_preimage_symm hV
    have hxW : e.val x ∈ W := ⟨e.val.map_source hx, by rw [mem_preimage, e.val.left_inv hx]; exact hxV⟩
    have hgd : DifferentiableOn ℂ (fun z => g (e.val.symm z)) W := by
      intro z hz
      exact (SGPT.PSH.differentiableAt_comp_chart_symm e hz.1 (hVsub hz.2)).differentiableWithinAt
    have hrad := (multiplierIntegrableAt_criticalPole_iff hn hW hxW hgd).mpr
      (by simpa only [e.val.left_inv hx] using hg0)
    have hchart := hrad.congr hprofile.symm (EventuallyEq.refl _ _)
    exact ⟨hg, ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      c e hxc hx huscc (by norm_num : (1 : ℝ) ≠ 0) hchart⟩

/-- A genuinely continuous finite potential has the unit multiplier germ.
The actual Lebesgue mass and original preferred chart are used directly. -/
theorem one_mem_multiplierIdeal_of_continuousAt_finite
    {θ : SmoothRealForm n X 2} {φ : X → EReal} (hφ : ThetaPlurisubharmonic θ φ)
    {x : X} (hcont : ContinuousAt φ x) (hbot : φ x ≠ ⊥) :
    (multiplierIdeal (n := n) 1 φ).mem x (fun _ => 1) := by
  let e := complexChartAt (n := n) x
  let p := e.val x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hpt : p ∈ e.val.target := e.val.map_source hx
  let a : ℝ := (φ x).toReal
  have hax : (a : EReal) = φ x := EReal.coe_toReal (hφ.quasiPlurisubharmonic.ne_top x) hbot
  have hcontc : ContinuousAt (chartFunction φ e) p := by
    have hs : e.val.symm p = x := e.val.left_inv hx
    have hcont' : ContinuousAt φ (e.val.symm p) := hs.symm ▸ hcont
    exact hcont'.comp (e.val.continuousAt_symm hpt)
  have hlow : ∀ᶠ z in 𝓝 p, ((a - 1 : ℝ) : EReal) ≤ chartFunction φ e z :=
    hcontc.eventually (eventually_ge_nhds (by
      change ((a - 1 : ℝ) : EReal) < φ (e.val.symm p)
      rw [e.val.left_inv hx, ← hax]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)))
  obtain ⟨R, hR, hBR⟩ := Metric.mem_nhds_iff.mp
    ((show ∀ᶠ z in 𝓝 p, z ∈ e.val.target from e.val.open_target.mem_nhds hpt).and hlow)
  have hwm : AEMeasurable (fun z => multiplierWeight 1 (chartFunction φ e z))
      (volume.restrict (ball p R)) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      ((hφ.quasiPlurisubharmonic e).upperSemicontinuousOn.mono fun z hz => (hBR hz).1)
      (by norm_num : (1 : ℝ) ≠ 0)
  have hbound : ∀ z ∈ ball p R, multiplierWeight 1 (chartFunction φ e z) ≤
      ENNReal.ofReal (Real.exp (-(a - 1))) := by
    intro z hz
    simpa only [multiplierWeight_coe, one_mul] using
      multiplierWeight_antitone (by norm_num : (0 : ℝ) ≤ 1) (hBR hz).2
  have hfin : (∫⁻ z in ball p R, multiplierWeight 1 (chartFunction φ e z)) < ⊤ := by
    calc _ ≤ ∫⁻ z in ball p R, ENNReal.ofReal (Real.exp (-(a - 1))) :=
        setLIntegral_mono' measurableSet_ball hbound
      _ = ENNReal.ofReal (Real.exp (-(a - 1))) * volume (ball p R) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  refine ⟨Eventually.of_forall fun _ => mdifferentiableAt_const, one_pos,
    ball p R, isOpen_ball, mem_ball_self hR, differentiableOn_const _, ?_⟩
  change WeightedL2On (chartFunction φ e) 1 (fun _ => 1) (ball p R) volume
  unfold WeightedL2On
  have hdens : multiplierDensity (chartFunction φ e) 1 (fun _ => 1) =
      fun z => multiplierWeight 1 (chartFunction φ e z) := by
    funext z
    simp only [multiplierDensity, norm_one, one_pow, ENNReal.ofReal_one, one_mul]
  rw [hdens]
  exact ⟨hwm, hfin⟩

variable [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {G : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- The actual critical cutoff pole, from the fixed positive-geometric chart. -/
def criticalPointWeight (D : SiuCover μ G G) (a : Fin D.m) (x₀ : X) (x : X) : EReal :=
  ((n : ℝ) : EReal) * poleFun (D.chartX a) ((D.chartX a).val x₀)
    (D.R a / 2) (Real.log (D.siuPoleR a ^ 2)) x

/-- The original cutoff pole has exactly the critical radial germ. -/
theorem criticalPointWeight_profile (D : SiuCover μ G G) (a : Fin D.m) {x₀ : X}
    (hp : (D.chartX a).val x₀ ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) :
    chartFunction (criticalPointWeight D a x₀) (D.chartX a) =ᶠ[𝓝 ((D.chartX a).val x₀)]
      criticalPole n ((D.chartX a).val x₀) := by
  let p := (D.chartX a).val x₀
  have hP := D.siuPoleRadii a hp
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hP.r_pos)] with z hz
  have hzR : z ∈ ball p (D.R a / 2) :=
    ball_subset_ball (by have := hP.four_r_le; have := hP.r_pos; linarith) hz
  have hzt := hP.ball_subset_target hzR
  change ((n : ℝ) : EReal) * poleFun (D.chartX a) p (D.R a / 2)
    (Real.log (D.siuPoleR a ^ 2)) ((D.chartX a).val.symm z) = criticalPole n p z
  rw [poleFun_of_mem ((D.chartX a).val.map_target hzt)
      (by rw [(D.chartX a).val.right_inv hzt]; exact hzR),
    (D.chartX a).val.right_inv hzt,
    poleChart_eq_logNormSq (by simpa only [← dist_eq_norm] using hz.le)]
  rfl

/-- One geometric lower-curvature constant gives genuine original potentials
for every point pole. -/
theorem isThetaPshPotential_criticalPointWeight (hn : 0 < n)
    (D : SiuCover μ G G) {θG : ClosedRealOneOneForm n X} (hKah : θG.val.IsKahler)
    {B : ℝ} (hB0 : 0 < B) (a : Fin D.m) {mω : ℝ}
    (hmω : ∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
      mω * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v])
    (hBm : 2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * mω)
    {x₀ : X} (hx₀ : x₀ ∈ (D.chartX a).val.source)
    (hp : (D.chartX a).val x₀ ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4)) :
    IsThetaPshPotential (((n : ℝ) * B) • θG).val (criticalPointWeight D a x₀) := by
  let ωb : KahlerBackground n X := ⟨θG, hKah⟩
  have hP := D.siuPoleRadii a hp
  have hbase : IsThetaPshPotential (B • θG).val
      (poleFun (D.chartX a) ((D.chartX a).val x₀) (D.R a / 2)
        (Real.log (D.siuPoleR a ^ 2))) := by
    refine ⟨thetaPlurisubharmonic_poleFun ωb hP
      (fun w hw v => hmω w (D.closedBall_subset_of_mem hp (by linarith [D.R_pos a]) hw) v)
      hB0.le hBm, ?_⟩
    exact locallyNondegenerate_poleFun hn fun y hy h => (D.chartX a).val.injOn hy hx₀ h
  have hscaled := RestrictedApproximantComparison.isThetaPshPotential_smul hbase
    (show (0 : ℝ) < n by exact_mod_cast hn)
  change IsThetaPshPotential (((n : ℝ) * B) • θG).val
    (fun x => ((n : ℝ) : EReal) * poleFun (D.chartX a) ((D.chartX a).val x₀)
      (D.R a / 2) (Real.log (D.siuPoleR a ^ 2)) x)
  simpa only [smul_smul] using hscaled

/-- The original germ ideal of the actual cutoff pole is the maximal ideal
at its original point, with all holomorphic representatives admitted. -/
theorem multiplierIdeal_criticalPointWeight_mem_iff (hn : 0 < n)
    (D : SiuCover μ G G) {θG : ClosedRealOneOneForm n X} (hKah : θG.val.IsKahler)
    {B : ℝ} (hB0 : 0 < B) (a : Fin D.m) {mω : ℝ}
    (hmω : ∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
      mω * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v])
    (hBm : 2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * mω)
    {x₀ : X} (hx₀ : x₀ ∈ (D.chartX a).val.source)
    (hp : (D.chartX a).val x₀ ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4))
    (g : X → ℂ) :
    (multiplierIdeal (n := n) 1 (criticalPointWeight D a x₀)).mem x₀ g ↔
      HolomorphicAt n g x₀ ∧ g x₀ = 0 :=
  multiplierIdeal_mem_iff_vanish_of_criticalChart hn
    (isThetaPshPotential_criticalPointWeight hn D hKah hB0 a hmω hBm hx₀ hp).1
    (D.chartX a) hx₀ (criticalPointWeight_profile D a hp) g

/-- The original critical point weight is continuous at every other point. -/
theorem criticalPointWeight_continuousAt (hn : 0 < n) (D : SiuCover μ G G)
    (a : Fin D.m) {x₀ q : X} (hx₀ : x₀ ∈ (D.chartX a).val.source)
    (hp : (D.chartX a).val x₀ ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4))
    (hqx : q ≠ x₀) : ContinuousAt (criticalPointWeight D a x₀) q := by
  have hc : ContinuousAt (poleFun (D.chartX a) ((D.chartX a).val x₀) (D.R a / 2)
      (Real.log (D.siuPoleR a ^ 2))) q :=
    continuousAt_poleFun (D.siuPoleRadii a hp) fun hq h => hqx ((D.chartX a).val.injOn hq hx₀ h)
  have hn0 : ((n : ℝ) : EReal) ≠ 0 := by
    intro h
    have := EReal.coe_eq_zero.mp h
    exact (ne_of_gt (show (0 : ℝ) < n by exact_mod_cast hn)) this
  exact (EReal.continuousAt_mul (Or.inl hn0) (Or.inl hn0)
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).comp
      (continuousAt_const.prodMk hc)

omit [BorelSpace X] in
/-- Every point away from the actual pole has a finite original weight. -/
theorem criticalPointWeight_ne_bot (hn : 0 < n) (D : SiuCover μ G G)
    (a : Fin D.m) {x₀ q : X} (hx₀ : x₀ ∈ (D.chartX a).val.source)
    (hqx : q ≠ x₀) : criticalPointWeight D a x₀ q ≠ ⊥ := by
  have hbase : poleFun (D.chartX a) ((D.chartX a).val x₀) (D.R a / 2)
      (Real.log (D.siuPoleR a ^ 2)) q ≠ ⊥ :=
    poleFun_ne_bot fun hq h => hqx ((D.chartX a).val.injOn hq hx₀ h)
  unfold criticalPointWeight
  induction h : poleFun (D.chartX a) ((D.chartX a).val x₀) (D.R a / 2)
      (Real.log (D.siuPoleR a ^ 2)) q using EReal.rec with
  | bot => exact absurd h hbase
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
  | top => rw [EReal.coe_mul_top_of_pos (by exact_mod_cast hn)]; exact top_ne_bot

/-- Away from the original pole, the actual multiplier ideal is the full
original holomorphic germ ring. -/
theorem multiplierIdeal_criticalPointWeight_mem_iff_of_ne (hn : 0 < n)
    (D : SiuCover μ G G) {θG : ClosedRealOneOneForm n X} (hKah : θG.val.IsKahler)
    {B : ℝ} (hB0 : 0 < B) (a : Fin D.m) {mω : ℝ}
    (hmω : ∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
      mω * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v])
    (hBm : 2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * mω)
    {x₀ q : X} (hx₀ : x₀ ∈ (D.chartX a).val.source)
    (hp : (D.chartX a).val x₀ ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4))
    (hqx : q ≠ x₀) (g : X → ℂ) :
    (multiplierIdeal (n := n) 1 (criticalPointWeight D a x₀)).mem q g ↔ HolomorphicAt n g q := by
  refine ⟨fun hg => hg.1, fun hg => ?_⟩
  have hφ := isThetaPshPotential_criticalPointWeight hn D hKah hB0 a hmω hBm hx₀ hp
  have hunit := one_mem_multiplierIdeal_of_continuousAt_finite hφ.1
    (criticalPointWeight_continuousAt hn D a hx₀ hp hqx) (criticalPointWeight_ne_bot hn D a hx₀ hqx)
  simpa only [mul_one] using MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul hg hunit

end SGPT.Bergman.SiuKodaira

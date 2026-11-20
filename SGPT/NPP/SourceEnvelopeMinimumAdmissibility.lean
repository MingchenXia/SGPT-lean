import SGPT.NPP.SourceEnvelopeObstacleMean
import SGPT.Foundations.Analysis.Pending.ActualAnalyticFactorResidualPsh

/-!
# Actual normalized source radius minima and obstacle admissibility

Complete blueprint: `blueprint/src/dnt-big-source-minimum-admissibility.tex`,
written first. The same actual radius minimum is normalized by its actual
holomorphic divisor logarithm. A genuine half-radius test and the proved
same-kernel weak-obstacle mean bound give its actual obstacle domination.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization
open SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.DNTC11

variable {n : ℕ}

/-- The literal numerical normalization is the logarithm of the actual
admissible half radius; no convention at a divisor zero is used. -/
theorem divisorHalfRadius_log_normalization {δ : ℝ} (hδ : 0 < δ)
    {b : ℂ} (hb : b ≠ 0) (a c : ℝ) :
    c * Real.log (δ / 2) + c * a * Real.log ‖b‖ =
      c * Real.log (δ * ‖b‖ ^ a / 2) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  rw [show δ * ‖b‖ ^ a / 2 = (δ / 2) * ‖b‖ ^ a by ring,
    Real.log_mul hδ2.ne' (Real.rpow_pos_of_pos hbpos a).ne', Real.log_rpow hbpos]
  ring

variable {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The actual corrected source minimum plus its actual half-radius
holomorphic-logarithmic normalization. -/
def normalizedSourceDivisorMinimum (ρ : ComplexModel n → ℝ)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)) (g : Y → ℝ)
    (e : ComplexChart n Y) (ψ : ComplexModel n → ℝ) (s : ComplexModel n → ℂ)
    (δ a K c : ℝ) (y : ComplexModel n) : EReal :=
  penalizedDivisorRadiusMinimum
    (fun p : ComplexModel n × ℂ =>
      ((sourceChartRadialSmoothing ρ θ g e ψ (Real.exp p.2.re) p.1 + ψ p.1 : ℝ) : EReal))
    s δ a K c y + ((c * Real.log (δ / 2) + c * a * Real.log ‖s y‖ : ℝ) : EReal)

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- Actual local normalized source minima are PSH, using the actual
holomorphic divisor logarithm rather than an assigned PSH correction. -/
theorem normalizedSourceDivisorMinimum_locally_plurisubharmonicOn
    (w : KahlerBackground n Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : Continuous g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {s : ComplexModel n → ℂ} (hs : DifferentiableOn ℂ s W)
    {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) (c : ℝ)
    {z : ComplexModel n} (hz : z ∈ W)
    (hzN : e.val.symm z ∉ sourceNonKahlerLocus
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ z ∈ U ∧ U ⊆ W ∧
      ∃ δ : ℝ, 0 < δ ∧ PlurisubharmonicOn
        (normalizedSourceDivisorMinimum ρ θ g e ψ s δ a K c) {y | y ∈ U ∧ s y ≠ 0} := by
  obtain ⟨U, hU, hzU, hUW, δ, hδ, hmin⟩ :=
    sourceChartRadialSmoothing_locally_penalizedDivisorMinimum
      w θ hbig hg e hψ hρ hs ha hK c hz hzN
  have hlog := ActualAnalyticFactorResidualPsh.plurisubharmonicOn_real_log_normSq_off_zeros
    hU (hs.mono hUW) (c * a / 2)
  have hlog' : PlurisubharmonicOn (fun y => ((c * a * Real.log ‖s y‖ : ℝ) : EReal))
      {y | y ∈ U ∧ s y ≠ 0} := by
    convert hlog using 1
    · funext y
      rw [Complex.normSq_eq_norm_sq, Real.log_pow]
      congr 1
      ring
    · ext y
      rfl
  have hconst : PlurisubharmonicOn (fun _ : ComplexModel n =>
      ((c * Real.log (δ / 2) : ℝ) : EReal)) {y | y ∈ U ∧ s y ≠ 0} :=
    (discPshOn_const _ (EReal.coe_ne_top _) _).plurisubharmonicOn
      ((hs.mono hUW).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton)
  refine ⟨U, hU, hzU, hUW, δ, hδ, ?_⟩
  convert hmin.add (hconst.add hlog') using 1
  funext y
  simp only [normalizedSourceDivisorMinimum, EReal.coe_add]

/-- A genuine actual half-radius test plus the proved same-kernel source
obstacle mean bound establishes local obstacle domination of the same actual
normalized minimum; no bound on the output minimum is an input. -/
theorem normalizedSourceDivisorMinimum_locally_le_obstacle
    (w : KahlerBackground n Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : HasBoundedComplexHessian (n := n) g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {z : ComplexModel n} (hz : z ∈ W)
    (hzN : e.val.symm z ∉ sourceNonKahlerLocus
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ (s : ComplexModel n → ℂ) (δ : ℝ), 0 < δ → ∀ a K c : ℝ,
      ∀ y ∈ ball z (2 * r₀), s y ≠ 0 → δ * ‖s y‖ ^ a / 2 < r₀ →
      normalizedSourceDivisorMinimum ρ θ g e ψ s δ a K c y ≤
        ((g (e.val.symm y) + ψ y + (M + K) * (δ * ‖s y‖ ^ a / 2) ^ 2 : ℝ) : EReal) := by
  obtain ⟨r₀, hr₀, _, M, hM0, hM⟩ :=
    sourceChartRadialSmoothing_locally_le_obstacle_quadratic w θ hbig hg e hψ hρ hz hzN
  refine ⟨r₀, hr₀, M, hM0, ?_⟩
  intro s δ hδ a K c y hy hsy hrsmall
  let r : ℝ := δ * ‖s y‖ ^ a / 2
  have hR : 0 < δ * ‖s y‖ ^ a :=
    mul_pos hδ (Real.rpow_pos_of_pos (norm_pos_iff.mpr hsy) a)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : r < δ * ‖s y‖ ^ a := by dsimp only [r]; linarith
  let N : ℝ := c * Real.log (δ / 2) + c * a * Real.log ‖s y‖
  have hN : N = c * Real.log r := divisorHalfRadius_log_normalization hδ hsy a c
  have htrial : penalizedDivisorRadiusMinimum
      (fun p : ComplexModel n × ℂ =>
        ((sourceChartRadialSmoothing ρ θ g e ψ (Real.exp p.2.re) p.1 + ψ p.1 : ℝ) : EReal))
      s δ a K c y ≤
      ((sourceChartRadialSmoothing ρ θ g e ψ r y + ψ y : ℝ) : EReal) +
        ((K * r ^ 2 - c * Real.log r : ℝ) : EReal) := by
    have hh := iInf_le
      (fun t : ↥(Ioo (0 : ℝ) (δ * ‖s y‖ ^ a)) =>
        ((sourceChartRadialSmoothing ρ θ g e ψ (Real.exp (Complex.ofReal (Real.log (t : ℝ))).re) y +
          ψ y : ℝ) : EReal) + ((K * (t : ℝ) ^ 2 - c * Real.log (t : ℝ) : ℝ) : EReal))
      ⟨r, hr, hrR⟩
    simpa only [penalizedDivisorRadiusMinimum, Complex.ofReal_re, Real.exp_log hr] using hh
  have hh := add_le_add htrial (le_refl (N : EReal))
  have hright :
      (((sourceChartRadialSmoothing ρ θ g e ψ r y + ψ y : ℝ) : EReal) +
        ((K * r ^ 2 - c * Real.log r : ℝ) : EReal)) + (N : EReal) =
      ((sourceChartRadialSmoothing ρ θ g e ψ r y + ψ y + K * r ^ 2 : ℝ) : EReal) := by
    rw [← EReal.coe_add, ← EReal.coe_add]
    congr 1
    rw [hN]
    ring
  rw [hright] at hh
  have hmean := hM y hy r hr hrsmall
  exact hh.trans (EReal.coe_le_coe_iff.mpr (by dsimp only [r] at *; nlinarith))

end SGPT.NPP.DNTBig

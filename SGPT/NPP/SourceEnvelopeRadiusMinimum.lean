import SGPT.NPP.SourceEnvelopeJointRadialPsh
import SGPT.NPP.PenalizedRadiusMinimum

/-!
# Actual local divisor-radius source-envelope minima

Complete blueprint: `blueprint/src/dnt-big-source-radius-minimum.tex`,
written first. A genuine numerical radius-buffer estimate supplies the
admissible logarithmic domain. The actual source convolution's joint PSH
is produced from big-class data before taking its literal penalized minimum.
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

variable {n : ℕ}

/-- A genuine numerical chart buffer dominates the actual varying divisor
radius; the logarithm is used only at actual nonzero divisor values. -/
theorem exists_local_divisorRadiusDomain_subset_radialJointDomain
    {V : Set (ComplexModel n)} (hV : IsOpen V) {z : ComplexModel n} (hz : z ∈ V)
    {s : ComplexModel n → ℂ} (hs : ContinuousAt s z) {a : ℝ} (ha : 0 ≤ a) :
    ∃ U : Set (ComplexModel n), IsOpen U ∧ z ∈ U ∧ U ⊆ V ∧
      ∃ δ : ℝ, 0 < δ ∧ divisorRadiusDomain U s δ a ⊆ radialJointDomain V := by
  obtain ⟨d, hd, hdV⟩ := Metric.isOpen_iff.mp hV z hz
  let R : ℝ := d / 3
  have hR : 0 < R := by dsimp only [R]; positivity
  let M : ℝ := ‖s z‖ + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hsnear : ∀ᶠ y in 𝓝 z, ‖s y‖ ≤ M := by
    filter_upwards [hs.norm.eventually (gt_mem_nhds (lt_add_one ‖s z‖))] with y hy
    exact hy.le
  have hnear : ∀ᶠ y in 𝓝 z, y ∈ ball z R ∧ ‖s y‖ ≤ M := by
    filter_upwards [ball_mem_nhds z hR, hsnear] with y hy hsy
    exact ⟨hy, hsy⟩
  obtain ⟨U, hUsub, hU, hzU⟩ := _root_.mem_nhds_iff.mp hnear
  have hUV : U ⊆ V := by
    intro y hy
    apply hdV
    exact (ball_subset_ball (by dsimp only [R]; linarith)) (hUsub hy).1
  have hbuffer : ∀ y ∈ U, ball y R ⊆ V := by
    intro y hy x hx
    apply hdV
    have hyz := (hUsub hy).1
    rw [mem_ball] at hyz hx ⊢
    have ht := dist_triangle x y z
    dsimp only [R] at *
    linarith
  let A : ℝ := M ^ a
  have hA : 0 ≤ A := Real.rpow_nonneg hM.le a
  let δ : ℝ := R / (A + 1)
  have hδ : 0 < δ := div_pos hR (by positivity)
  have hδA : δ * A < R := by
    have heq : δ * (A + 1) = R := div_mul_cancel₀ R (by positivity)
    nlinarith
  refine ⟨U, hU, hzU, hUV, δ, hδ, ?_⟩
  intro p hp
  have hpow : ‖s p.1‖ ^ a ≤ A := Real.rpow_le_rpow (norm_nonneg _) (hUsub hp.1).2 ha
  have hexp : Real.exp p.2.re < δ * ‖s p.1‖ ^ a := by
    have hh := Real.exp_lt_exp.mpr hp.2.2
    rw [Real.exp_add, Real.exp_log hδ,
      show a * Real.log ‖s p.1‖ = Real.log ‖s p.1‖ * a by ring,
      ← Real.rpow_def_of_pos (norm_pos_iff.mpr hp.2.1)] at hh
    exact hh
  exact ⟨R, hexp.trans ((mul_le_mul_of_nonneg_left hpow hδ.le).trans_lt hδA),
    hbuffer p.1 hp.1⟩

variable {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- Actual local penalized divisor-radius minima of the same source-envelope
convolution are PSH; all joint PSH and domain admissibility are produced. -/
theorem sourceChartRadialSmoothing_locally_penalizedDivisorMinimum
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
        (penalizedDivisorRadiusMinimum
          (fun p : ComplexModel n × ℂ =>
            ((sourceChartRadialSmoothing ρ θ g e ψ (Real.exp p.2.re) p.1 + ψ p.1 : ℝ) : EReal))
          s δ a K c) {y | y ∈ U ∧ s y ≠ 0} := by
  obtain ⟨V, hV, hzV, hVW, hΦ⟩ :=
    sourceChartRadialSmoothing_locally_joint_plurisubharmonicOn w θ hbig hg e hψ hρ hz hzN
  have hsc : ContinuousAt s z := hs.continuousOn.continuousAt (hψ.1.mem_nhds hz)
  obtain ⟨U, hU, hzU, hUV, δ, hδ, hdomain⟩ :=
    exists_local_divisorRadiusDomain_subset_radialJointDomain hV hzV hsc ha
  refine ⟨U, hU, hzU, hUV.trans hVW, δ, hδ, ?_⟩
  apply plurisubharmonicOn_penalizedDivisorRadiusMinimum hU (hs.mono (hUV.trans hVW)) hδ a
    (hΦ.mono hdomain) _ hK c
  intro y τ σ hτσ
  simp only [hτσ]

end SGPT.NPP.DNTBig

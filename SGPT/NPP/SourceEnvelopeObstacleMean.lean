import SGPT.NPP.ArbitraryKernelObstacleMean

/-!
# Actual source convolution domination by the weak-Hessian obstacle

Complete blueprint: `blueprint/src/dnt-big-source-obstacle-mean.tex`, written
first. The finite patch, actual corrected source PSH, actual weak obstacle
Hessian and actual pointwise envelope comparison are produced from big-class
source data. The same arbitrary radial kernel is retained throughout.
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

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- Actual local source convolution is dominated quadratically by its same
weak-Hessian obstacle, using finite patch bounds manufactured off the original
source locus and retaining the same arbitrary actual radial kernel. -/
theorem sourceChartRadialSmoothing_locally_le_obstacle_quadratic
    (w : KahlerBackground n Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : HasBoundedComplexHessian (n := n) g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {z : ComplexModel n} (hz : z ∈ W)
    (hzN : e.val.symm z ∉ sourceNonKahlerLocus
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ a : ℝ, 0 < a ∧ closedBall z (4 * a) ⊆ W ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ y ∈ ball z (2 * a), ∀ r : ℝ, 0 < r → r < a →
        sourceChartRadialSmoothing ρ θ g e ψ r y ≤ g (e.val.symm y) + M * r ^ 2 := by
  obtain ⟨V, hV, hzV, hVW, C, _, huV⟩ :=
    sourceEnvelopeChartPotential_locally_bounded w θ hbig hg.1 e hψ hz hzN
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV z hzV
  let a : ℝ := ε / 8
  have ha : 0 < a := by dsimp only [a]; positivity
  have hballV : closedBall z (4 * a) ⊆ V :=
    (closedBall_subset_ball (by dsimp only [a]; linarith)).trans hεV
  obtain ⟨H, hHg⟩ := hg.2 e
  have hq := (hHg.mono hV (hVW.trans hψ.2.1)).add_contDiffOn (hψ.2.2.1.mono hVW)
  obtain ⟨φ, hφ⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  have hPn := SGPT.Okounkov.TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous
    w (atlasClosedFormToNative θ) hg.1 hφ
  have hP : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))) := by
    rw [sourceObstacleEnvelope_eq_native]
    exact hPn
  have hp : PlurisubharmonicOn (sourceEnvelopeChartPotential θ g e ψ) W := by
    change PlurisubharmonicOn
      (fun y => chartFunction (sourceRelativeEnvelope θ (fun _ => ⊤)
        (fun x => (g x : EReal))) e y + (ψ y : EReal)) W
    exact ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hP.1 e hψ
  have huf : ∀ y ∈ V, sourceEnvelopeChartPotential θ g e ψ y ≠ ⊥ := fun y hy =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-C)) (huV y hy).1
  have hsourcele (y : Y) : sourceRelativeEnvelope θ (fun _ => ⊤)
      (fun x => (g x : EReal)) y ≤ (g y : EReal) := by
    rw [sourceObstacleEnvelope_eq_native]
    exact SGPT.Okounkov.TranscendentalWNReg.rooftopEnvelope_le_of_isThetaPshPotential hg.1 hPn y
  have huq : ∀ y ∈ V, sourceEnvelopeChartPotential θ g e ψ y ≤
      ((g (e.val.symm y) + ψ y : ℝ) : EReal) := by
    intro y _
    rw [EReal.coe_add]
    exact add_le_add (hsourcele (e.val.symm y)) le_rfl
  obtain ⟨M, hM0, hM⟩ := radialRegularization_le_obstacle_of_boundedDensity hρ hq
    (hp.mono hVW) huf huq ha hballV
  refine ⟨a, ha, hballV.trans hVW, M, hM0, ?_⟩
  intro y hy r hr hra
  have hh := hM y hy r hr hra
  dsimp only [sourceChartRadialSmoothing]
  linarith

end SGPT.NPP.DNTBig

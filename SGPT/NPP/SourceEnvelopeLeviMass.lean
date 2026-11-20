import SGPT.NPP.ActualDirectionalLeviMass
import SGPT.NPP.SourceEnvelopeJointRadialPsh

/-!
# Actual directional Levi mass of the same corrected source envelope

Complete blueprint: `blueprint/src/dnt-big-actual-levi-mass.tex`, written
first. Bigness, the same arbitrary continuous obstacle, and the original
source non-Kähler-locus exclusion manufacture the actual finite PSH patch.
Its actual positive directional Levi measures and crude ball-mass bound are
then derived, with no envelope regularity or assigned measure as input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- The actual corrected source envelope produces its own local positive
Levi measures and actual crude radius-mass bound off the ORIGINAL source
non-Kähler locus, with no assumed Hessian or mass certificate. -/
theorem sourceEnvelopeChartPotential_locally_directionalLeviMass_bound
    (w : KahlerBackground n Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : Continuous g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    {z : ComplexModel n} (hz : z ∈ W)
    (hzN : e.val.symm z ∉ sourceNonKahlerLocus
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ (V : Set (ComplexModel n)) (hV : IsOpen V), z ∈ V ∧ V ⊆ W ∧
      ∃ a : ℝ, 0 < a ∧ closedBall z (4 * a) ⊆ V ∧
      ∃ hL : LocallyIntegrableOn
          (fun x => (sourceEnvelopeChartPotential θ g e ψ x).toReal) V volume,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ComplexModel n, ∃ ν : Measure (⟨V, hV⟩ : Opens (ComplexModel n)),
        ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
        (∀ φ : 𝓓((⟨V, hV⟩ : Opens (ComplexModel n)), ℝ),
          (∫ x : (⟨V, hV⟩ : Opens (ComplexModel n)), φ x ∂ν) =
            distributionalLeviCLM v (regularDistribution volume
              (fun x => (sourceEnvelopeChartPotential θ g e ψ x).toReal) hL) φ) ∧
        ∀ y ∈ ball z (2 * a), ∀ r : ℝ, 0 < r → r < a →
          ν {x : (⟨V, hV⟩ : Opens (ComplexModel n)) | x.val ∈ ball y r} ≤
            ENNReal.ofReal (C * ‖v‖ ^ 2 * (r ^ Module.finrank ℝ (ComplexModel n) / r ^ 2)) := by
  obtain ⟨V, hV, hzV, hVW, B, hB0, hub⟩ :=
    sourceEnvelopeChartPotential_locally_bounded w θ hbig hg e hψ hz hzN
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV z hzV
  let a : ℝ := ε / 8
  have ha : 0 < a := by dsimp only [a]; positivity
  have hballV : closedBall z (4 * a) ⊆ V :=
    (closedBall_subset_ball (by dsimp only [a]; linarith)).trans hεV
  obtain ⟨φ, hφ⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  have hPn := SGPT.Okounkov.TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous
    w (atlasClosedFormToNative θ) hg hφ
  have hP : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))) := by
    rw [sourceObstacleEnvelope_eq_native]
    exact hPn
  have hp : PlurisubharmonicOn (sourceEnvelopeChartPotential θ g e ψ) W := by
    change PlurisubharmonicOn
      (fun y => chartFunction (sourceRelativeEnvelope θ (fun _ => ⊤)
        (fun x => (g x : EReal))) e y + (ψ y : EReal)) W
    exact ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hP.1 e hψ
  have hcoe (x : ComplexModel n) (hx : x ∈ V) :
      ((sourceEnvelopeChartPotential θ g e ψ x).toReal : EReal) =
        sourceEnvelopeChartPotential θ g e ψ x :=
    EReal.coe_toReal (hp x (hVW hx)).ne_top
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-B)) (hub x hx).1)
  have hrealpsh : PlurisubharmonicOn
      (fun x => ((sourceEnvelopeChartPotential θ g e ψ x).toReal : EReal)) V := by
    intro x hx
    apply (hp x (hVW hx)).congr
    filter_upwards [hV.mem_nhds hx] with y hy
    exact (hcoe y hy).symm
  have hbound : ∀ x ∈ V, |(sourceEnvelopeChartPotential θ g e ψ x).toReal| ≤ B := by
    intro x hx
    have hh := hub x hx
    rw [← hcoe x hx, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff] at hh
    exact abs_le.mpr hh
  let Ω : Opens (ComplexModel n) := ⟨V, hV⟩
  let hL := locallyIntegrableOn_of_plurisubharmonicOn_real (Ω := Ω) hrealpsh
  obtain ⟨C, hC0, hC⟩ := exists_directionalLeviMeasures_ball_bound_of_boundedPsh
    (Ω := Ω) hrealpsh hB0 hbound ha hballV
  exact ⟨V, hV, hzV, hVW, a, ha, hballV, hL, C, hC0, hC⟩

end SGPT.NPP.DNTBig

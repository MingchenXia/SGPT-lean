import SGPT.NPP.DNTBigReduction
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

/-!
# Actual radial smoothing of the literal source envelope

Complete blueprint: `blueprint/src/dnt-big-source-radial-family.tex`, written
before this file. Every smoothing is the actual radial convolution of the
same actual source envelope plus the same actual local background potential.
The source envelope's PSH property and noncollapse are derived from bigness
and the continuous obstacle, with no envelope regularity hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The actual source obstacle envelope corrected by the actual local
potential. Genuine extended-real poles remain poles. -/
def sourceEnvelopeChartPotential (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (g : Y → ℝ) (e : ComplexChart n Y) (ψ : ComplexModel n → ℝ)
    (z : ComplexModel n) : EReal :=
  sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal)) (e.val.symm z) + (ψ z : EReal)

/-- The actual radial integral, with the same smooth background potential
subtracted. It is an explicit function rather than assigned smoothing data. -/
def sourceChartRadialSmoothing (ρ : ComplexModel n → ℝ)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)) (g : Y → ℝ)
    (e : ComplexChart n Y) (ψ : ComplexModel n → ℝ) (r : ℝ) (z : ComplexModel n) : ℝ :=
  radialRegularization ρ (sourceEnvelopeChartPotential θ g e ψ) r z - ψ z

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

private theorem sourceEnvelopeChartPotential_data (w : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : Continuous g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    {x₀ : ComplexModel n} (hx₀ : x₀ ∈ W) :
    PlurisubharmonicOn (sourceEnvelopeChartPotential θ g e ψ) W ∧
      ∃ z ∈ W, sourceEnvelopeChartPotential θ g e ψ z ≠ ⊥ := by
  obtain ⟨φ, hφ⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  have hPn := SGPT.Okounkov.TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous
    w (atlasClosedFormToNative θ) hg hφ
  have hP : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))) := by
    rw [sourceObstacleEnvelope_eq_native]
    exact hPn
  have hp := ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
    hP.1 e hψ
  obtain ⟨z, hzW, hzne⟩ := hP.quasiPshPotential.2.exists_chart_ne_bot e hψ.1 hψ.2.1 hx₀
  refine ⟨?_, z, hzW, ?_⟩
  · change PlurisubharmonicOn
      (fun z => chartFunction (sourceRelativeEnvelope θ (fun _ => ⊤)
        (fun x => (g x : EReal))) e z + (ψ z : EReal)) W
    exact hp
  · exact EReal.add_ne_bot_iff.mpr ⟨hzne, EReal.coe_ne_bot _⟩

variable (w : KahlerBackground n Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
  (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
  {g : Y → ℝ} (hg : Continuous g) (e : ComplexChart n Y)
  {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
  (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
  (hWc : IsPreconnected W) {x₀ : ComplexModel n} (hx₀ : x₀ ∈ W)
  {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)

include w hbig hg hψ hWc hx₀ hρ

/-- Fixed-radius smoothness of the actual source-envelope radial integral. -/
theorem sourceChartRadialSmoothing_contDiffOn {r : ℝ} (hr : 0 < r) :
    ContDiffOn ℝ ∞ (sourceChartRadialSmoothing ρ θ g e ψ r) (innerDomain W r) := by
  obtain ⟨hp, hne⟩ := sourceEnvelopeChartPotential_data w θ hbig hg e hψ hx₀
  exact (contDiffOn_radialRegularization hρ hψ.1 hWc hp hne hr).sub
    (hψ.2.2.1.mono (innerDomain_subset hr.le))

/-- The smoothed function has the actual corrected PSH property for the
same actual local background potential. -/
theorem sourceChartRadialSmoothing_corrected_plurisubharmonicOn {r : ℝ} (hr : 0 < r) :
    PlurisubharmonicOn
      (fun z => ((sourceChartRadialSmoothing ρ θ g e ψ r z + ψ z : ℝ) : EReal))
      (innerDomain W r) := by
  obtain ⟨hp, hne⟩ := sourceEnvelopeChartPotential_data w θ hbig hg e hψ hx₀
  have h := plurisubharmonicOn_radialRegularization hρ hψ.1 hWc hp hne hr
  convert h using 1
  funext z
  simp only [sourceChartRadialSmoothing, sub_add_cancel]

/-- The actual singular radial submean inequality for the actual source
envelope; no real-valuedness of a pole is inferred. -/
theorem sourceChartRadialSmoothing_corrected_ge {r : ℝ} (hr : 0 < r)
    {z : ComplexModel n} (hz : z ∈ innerDomain W r) :
    sourceEnvelopeChartPotential θ g e ψ z ≤
      ((sourceChartRadialSmoothing ρ θ g e ψ r z + ψ z : ℝ) : EReal) := by
  obtain ⟨hp, hne⟩ := sourceEnvelopeChartPotential_data w θ hbig hg e hψ hx₀
  simpa only [sourceChartRadialSmoothing, sub_add_cancel] using
    le_radialRegularization hρ hψ.1 hWc hp hne hr hz

/-- Radius monotonicity of the same actual source-envelope smoothing. -/
theorem sourceChartRadialSmoothing_mono_radius {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {z : ComplexModel n} (hz : z ∈ innerDomain W R) :
    sourceChartRadialSmoothing ρ θ g e ψ r z ≤ sourceChartRadialSmoothing ρ θ g e ψ R z := by
  obtain ⟨hp, hne⟩ := sourceEnvelopeChartPotential_data w θ hbig hg e hψ hx₀
  exact sub_le_sub_right (radialRegularization_mono hρ hψ.1 hWc hp hne hr hrR hz) (ψ z)

/-- Pointwise convergence to the literal actual source envelope, including
its genuine extended-real poles, after adding back the same background. -/
theorem sourceChartRadialSmoothing_corrected_tendsto {z : ComplexModel n} (hz : z ∈ W) :
    Tendsto (fun r => ((sourceChartRadialSmoothing ρ θ g e ψ r z + ψ z : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 (sourceEnvelopeChartPotential θ g e ψ z)) := by
  obtain ⟨hp, hne⟩ := sourceEnvelopeChartPotential_data w θ hbig hg e hψ hx₀
  simpa only [sourceChartRadialSmoothing, sub_add_cancel] using
    tendsto_radialRegularization hρ hψ.1 hWc hp hne hz

end SGPT.NPP.DNTBig

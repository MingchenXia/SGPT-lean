import SGPT.NPP.BoundedJointRadialPsh
import SGPT.PSH.SourceLscFreeEnvelope

/-!
# Actual joint radial source-envelope PSH off the original source locus

Complete blueprint: `blueprint/src/dnt-big-source-joint-radial.tex`, written
first. Finite local bounds are manufactured for the literal source envelope
from bigness and the existing original-source local bound theorem. The actual
bounded-patch disc/Fubini proof then yields joint PSH for the same convolution.
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

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

private theorem sourceEnvelope_nativePotential_of_big (w : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : Continuous g) :
    IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal))) := by
  obtain ⟨φ, hφ⟩ := SGPT.Okounkov.TranscendentalWN.exists_isThetaPshPotential_of_isBigClass hbig
  rw [sourceObstacleEnvelope_eq_native]
  exact SGPT.Okounkov.TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous
    w (atlasClosedFormToNative θ) hg hφ

/-- Bigness and the original source non-Kähler-locus bound theorem produce
actual finite bounds on the actual corrected envelope near the chosen point. -/
theorem sourceEnvelopeChartPotential_locally_bounded (w : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : Continuous g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    {z : ComplexModel n} (hz : z ∈ W)
    (hzN : e.val.symm z ∉ sourceNonKahlerLocus
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ V : Set (ComplexModel n), IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ V,
        ((-C : ℝ) : EReal) ≤ sourceEnvelopeChartPotential θ g e ψ y ∧
        sourceEnvelopeChartPotential θ g e ψ y ≤ (C : EReal) := by
  have hP := sourceEnvelope_nativePotential_of_big w θ hbig hg
  obtain ⟨D, hD⟩ := hP.exists_global_upper_bound
  have hnt : sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (g x : EReal)) ≠
      fun _ => ⊤ := by
    intro heq
    have ht : (⊤ : EReal) ≤ (D : EReal) := by simpa only [heq] using hD (e.val.symm z)
    exact (EReal.coe_lt_top D).not_ge ht
  obtain ⟨U, hU, hzU, a, b, hab⟩ := sourceLscObstacleEnvelope_locallyBounded
    w θ hbig g hg.lowerSemicontinuous hnt (e.val.symm z) hzN
  let B : ℝ := |ψ z| + 1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hUnear : ∀ᶠ y in 𝓝 z, e.val.symm y ∈ U :=
    (e.val.continuousAt_symm (hψ.2.1 hz)).eventually (hU.mem_nhds hzU)
  have hψcont : ContinuousAt ψ z := hψ.2.2.1.continuousOn.continuousAt (hψ.1.mem_nhds hz)
  have hψnear : ∀ᶠ y in 𝓝 z, |ψ y| ≤ B := by
    filter_upwards [hψcont.abs.eventually (gt_mem_nhds (lt_add_one |ψ z|))] with y hy
    exact hy.le
  have hnear : ∀ᶠ y in 𝓝 z, y ∈ W ∧ e.val.symm y ∈ U ∧ |ψ y| ≤ B := by
    filter_upwards [hψ.1.mem_nhds hz, hUnear, hψnear] with y hyW hyU hyψ
    exact ⟨hyW, hyU, hyψ⟩
  obtain ⟨V, hVsub, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  let C : ℝ := |a| + |b| + B
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨V, hV, hzV, fun y hy => (hVsub hy).1, C, hC, ?_⟩
  intro y hy
  have hyU := (hVsub hy).2.1
  have hψb : -B ≤ ψ y ∧ ψ y ≤ B := abs_le.mp ((hVsub hy).2.2)
  have hPy := hab (e.val.symm y) hyU
  constructor
  · calc
      ((-C : ℝ) : EReal) ≤ ((a + -B : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by
        dsimp only [C]
        linarith [neg_abs_le a, abs_nonneg b])
      _ = (a : EReal) + ((-B : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ sourceEnvelopeChartPotential θ g e ψ y :=
        add_le_add hPy.1 (EReal.coe_le_coe_iff.mpr hψb.1)
  · calc
      sourceEnvelopeChartPotential θ g e ψ y ≤ (b : EReal) + (B : EReal) :=
        add_le_add hPy.2 (EReal.coe_le_coe_iff.mpr hψb.2)
      _ = ((b + B : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ (C : EReal) := EReal.coe_le_coe_iff.mpr (by
        dsimp only [C]
        linarith [le_abs_self b, abs_nonneg a])

/-- The actual source smoothing is jointly PSH on a genuinely produced native
patch around each point outside the original source non-Kähler locus. -/
theorem sourceChartRadialSmoothing_locally_joint_plurisubharmonicOn
    (w : KahlerBackground n Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {g : Y → ℝ} (hg : Continuous g) (e : ComplexChart n Y)
    {W : Set (ComplexModel n)} {ψ : ComplexModel n → ℝ}
    (hψ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ψ)
    {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {z : ComplexModel n} (hz : z ∈ W)
    (hzN : e.val.symm z ∉ sourceNonKahlerLocus
      (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ V : Set (ComplexModel n), IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      PlurisubharmonicOn
        (fun p : ComplexModel n × ℂ =>
          ((sourceChartRadialSmoothing ρ θ g e ψ (Real.exp p.2.re) p.1 + ψ p.1 : ℝ) : EReal))
        (radialJointDomain V) := by
  obtain ⟨V, hV, hzV, hVW, C, hC, huV⟩ :=
    sourceEnvelopeChartPotential_locally_bounded w θ hbig hg e hψ hz hzN
  have hP := sourceEnvelope_nativePotential_of_big w θ hbig hg
  have hp : PlurisubharmonicOn (sourceEnvelopeChartPotential θ g e ψ) W := by
    change PlurisubharmonicOn
      (fun y => chartFunction (sourceRelativeEnvelope θ (fun _ => ⊤)
        (fun x => (g x : EReal))) e y + (ψ y : EReal)) W
    exact ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hP.1 e hψ
  refine ⟨V, hV, hzV, hVW, ?_⟩
  simpa only [sourceChartRadialSmoothing, sub_add_cancel] using
    plurisubharmonicOn_boundedJointRadialRegularization hρ hV (hp.mono hVW) hC huV

end SGPT.NPP.DNTBig

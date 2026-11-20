import SGPT.NAPotential.DHCont
import SGPT.NAPotential.DHIntrinsicCore

/-! # Intrinsic Duistermaat--Heckman measure

The Lebesgue--Stieltjes measure of
minus the actual slice-mass function makes the flag-free measure directly in
all dimensions. At the cutoff the zero extension can have a jump, hence an
atom there is allowed. This module applies the continuity criterion.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.NAPotential.DH

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M] {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

theorem naIntrinsicDuistermaatHeckman_hasDHTails (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) :
    HasDHTails (naIntrinsicDuistermaatHeckman omega Γ) Γ where
  isFiniteMeasure := naIntrinsicDuistermaatHeckman_finite omega Γ
  Ici_eq := naIntrinsicDuistermaatHeckman_Ici omega Γ
  Ioi_max_eq := naIntrinsicDuistermaatHeckman_Ioi_max omega Γ
  univ_eq := naIntrinsicDuistermaatHeckman_univ omega Γ

def naIntrinsicFiniteDuistermaatHeckman (omega : KahlerBackground n M)
    (Γ : SourcePositiveIModelTestCurve θ) : FiniteMeasure ℝ :=
  ⟨naIntrinsicDuistermaatHeckman omega Γ, naIntrinsicDuistermaatHeckman_finite omega Γ⟩

theorem naIntrinsicDuistermaatHeckman_independent_background
    (omega eta : KahlerBackground n M) (Γ : SourcePositiveIModelTestCurve θ) :
    naIntrinsicDuistermaatHeckman omega Γ = naIntrinsicDuistermaatHeckman eta Γ :=
  (naIntrinsicDuistermaatHeckman_hasDHTails omega Γ).unique
    (naIntrinsicDuistermaatHeckman_hasDHTails eta Γ)

theorem naIntrinsicDuistermaatHeckman_tendsto_of_decreasingInf
    (omega : KahlerBackground n M) (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j →
      SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j)) (sourcePositiveTestCurveToNA (Γs i)))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))))
    (hΓ : sourcePositiveTestCurveToNA Γ =
      SourceNAPotential.decreasingInf omega (fun i => sourcePositiveTestCurveToNA (Γs i)) ha hb)
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ)))) :
    Tendsto (fun i => naIntrinsicFiniteDuistermaatHeckman omega (Γs i)) atTop
      (𝓝 (naIntrinsicFiniteDuistermaatHeckman omega Γ)) :=
  tendsto_of_hasDHTails_of_toNA_eq_decreasingInf omega Γs Γ ha hb hΓ hvol
    (fun i => naIntrinsicDuistermaatHeckman_hasDHTails omega (Γs i))
    (naIntrinsicDuistermaatHeckman_hasDHTails omega Γ)

theorem naIntrinsicDuistermaatHeckman_tendsto_of_uscSup
    (omega : KahlerBackground n M) (Γs : ℕ → SourcePositiveIModelTestCurve θ)
    (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j →
      SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) (sourcePositiveTestCurveToNA (Γs j)))
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))))
    (hΓ : sourcePositiveTestCurveToNA Γ =
      SourceNAPotential.uscSup omega (fun i => sourcePositiveTestCurveToNA (Γs i)) hb) :
    Tendsto (fun i => naIntrinsicFiniteDuistermaatHeckman omega (Γs i)) atTop
      (𝓝 (naIntrinsicFiniteDuistermaatHeckman omega Γ)) :=
  tendsto_of_hasDHTails_of_toNA_eq_uscSup omega Γs Γ hmono hb hΓ
    (fun i => naIntrinsicDuistermaatHeckman_hasDHTails omega (Γs i))
    (naIntrinsicDuistermaatHeckman_hasDHTails omega Γ)

end SGPT.NAPotential.DH

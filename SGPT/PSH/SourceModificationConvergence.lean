import SGPT.PSH.SourceSingularityDistance
import SGPT.PSH.NativeQPSHPullback
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Okounkov.ModificationNativeConvergence
import SGPT.Okounkov.NativeFlagBaseGeometry

set_option autoImplicit false
noncomputable section

/-! # Whole original general bimeromorphic singularity convergence

The complete source-first proofs are in `source-modification-convergence.tex`.
All analytic modification, mass and native convergence results below already
exist; this module retains their exact original functions, forms and topology.
-/

universe u
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Actual pullback on the ENTIRE original PSH class, including exceptional
points and poles. Local nondegeneracy is produced by genuine geometry. -/
def sourceModificationPullback {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : SourceThetaPotentialL1 θ) :
    SourceThetaPotentialL1 (θ.nativeHolomorphicPullback hπ.1) :=
  ⟨u.val ∘ π, u.property.comp_native_analyticModification hπ⟩

/-- The same original function is retained pointwise, with no normalization. -/
theorem sourceModificationPullback_val {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u : SourceThetaPotentialL1 θ) :
    (sourceModificationPullback hπ θ u).val = u.val ∘ π := rfl

/-- The whole original pulled tensor is exactly the existing native one. -/
theorem sourceModificationPullback_background {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) :
    atlasClosedFormToNative (θ.nativeHolomorphicPullback hπ.1) =
      ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative θ) :=
  sourceNativeAtlasForm_roundTrip _

/-- Pullback preserves the actual source maximum on the full PSH carrier. -/
theorem sourceModificationPullback_maximum {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (u v : SourceThetaPotentialL1 θ) :
    sourceModificationPullback hπ θ (sourceThetaPotentialMaximum u v) =
      sourceThetaPotentialMaximum (sourceModificationPullback hπ θ u)
        (sourceModificationPullback hπ θ v) := Subtype.ext rfl

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Genuine original geometry and original bigness produce the actual big
upstairs background; upstairs compactness and connectedness are internal. -/
theorem sourceModificationPullback_big {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative (θ.nativeHolomorphicPullback hπ.1))) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  rw [sourceModificationPullback_background hπ θ]
  exact SGPT.Okounkov.isBigClass_modification_pullback hπ ωX ωY (atlasClosedFormToNative θ) hbig

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- Literal minimal-envelope equality, without additive shifts, follows
from the existing genuine full modification descent theorem. -/
theorem sourceMinimalEnvelope_modification_pullback {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) (ωX : KahlerBackground n X)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    sourceMinimalEnvelope (θ.nativeHolomorphicPullback hπ.1) =
      sourceMinimalEnvelope θ ∘ π := by
  simp only [sourceMinimalEnvelope_eq_native]
  funext y
  exact AnalyticModificationMinimalMixedPullback.thetaPshSupremum_pullback_eq hπ
    (atlasClosedFormToNative θ)
    ⟨sourceMinimalEnvelope θ, (isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourceMinimalEnvelope_thetaPSH ωX θ hbig)⟩ y

/-- Every actual original extended endpoint mass is preserved, including
zero mass, dimension zero and the same literal minimal reference. -/
theorem sourceMinimalMixedMass_modification_pullback {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) (j : Fin (n + 1)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    let β := θ.nativeHolomorphicPullback hπ.1
    let hβ := sourceModificationPullback_big hπ ωX ωY θ hbig
    sourceMinimalMixedMass ωY β hβ (sourceModificationPullback hπ θ u).val
      (sourceModificationPullback hπ θ u).property j =
      sourceMinimalMixedMass ωX θ hbig u.val u.property j := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  dsimp only
  rw [sourceMinimalMixedMass_eq_native, sourceMinimalMixedMass_eq_native]
  have h := SGPT.Okounkov.minimalEndpointMixedMass_modification_pullback hπ ωX ωY
    (atlasClosedFormToNative θ) hbig ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property) j
  simpa only [sourceModificationPullback_background hπ θ, sourceModificationPullback] using h

/-- Exactly the original finite mixed-mass middle expression is invariant.
This makes no assertion of numerical equality of the two pseudometrics. -/
theorem sourceSingularityMassJoinGap_modification_pullback {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    let β := θ.nativeHolomorphicPullback hπ.1
    let hβ := sourceModificationPullback_big hπ ωX ωY θ hbig
    sourceSingularityMassJoinGap ωY β hβ (sourceModificationPullback hπ θ u)
      (sourceModificationPullback hπ θ v) = sourceSingularityMassJoinGap ωX θ hbig u v := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  dsimp only
  simp only [sourceSingularityMassJoinGap, ← sourceModificationPullback_maximum hπ θ,
    sourceMinimalMixedMass_modification_pullback hπ ωX ωY θ hbig]

/-- WHOLE original cor:dSconv_bimero for EVERY filter and every original
PSH family/target. The topology is explicitly the actual dS topology on BOTH
carriers. All upstairs geometric/big hypotheses are internally manufactured. -/
theorem tendsto_sourceSingularityTopology_modification_pullback_iff {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    let β := θ.nativeHolomorphicPullback hπ.1
    let hβ := sourceModificationPullback_big hπ ωX ωY θ hbig
    Tendsto w F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ωX θ hbig) v) ↔
      Tendsto (fun i => sourceModificationPullback hπ θ (w i)) F
        (@nhds (SourceThetaPotentialL1 β) (sourceSingularityTopology ωY β hβ)
          (sourceModificationPullback hπ θ v)) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  dsimp only
  let β := θ.nativeHolomorphicPullback hπ.1
  let hβ := sourceModificationPullback_big hπ ωX ωY θ hbig
  have hX := tendsto_sourceSingularityTopology_iff_mixedMass ωX θ hbig F w v
  have hY := tendsto_sourceSingularityTopology_iff_mixedMass ωY β hβ F
    (fun i => sourceModificationPullback hπ θ (w i)) (sourceModificationPullback hπ θ v)
  refine hX.trans (Iff.trans ?_ hY.symm)
  apply forall_congr'
  intro j
  simp only [β, ← sourceModificationPullback_maximum hπ θ,
    sourceMinimalMixedMass_modification_pullback hπ ωX ωY θ hbig]

end SGPT.PSH.VariableComplexAtlas

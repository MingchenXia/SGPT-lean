import SGPT.Envelopes.SourceRelativeEnergy
import SGPT.PSH.GlobalPComparison
import SGPT.Foundations.Analysis.Pending.SingularMinimalGlobalPMassCriterion

/-! # Whole original P-equivalence mass characterization

The literal original minimal envelope and endpoint measures are retained.
The genuine native criterion handles zero original masses. Only the separate
diagonal branch requires both positive original masses. The complete source
route is in `source-p-mass-characterization.tex`.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending DiagonalMass GlobalNonPluripolar GlobalDiagonalScaling RelativeEnergy

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Original bigness produces the model fields for the literal minimal envelope. -/
theorem sourceMinimalEnvelope_model (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    SourceModelPotential θ (sourceMinimalEnvelope θ) := by
  apply (sourceModelPotential_iff_native θ _).mpr
  rw [sourceMinimalEnvelope_eq_native]
  exact SingularMinimalCanonicalRay.isModelPotential_thetaPshSupremum ω
    (atlasClosedFormToNative θ) hbig

/-- Original theta-PSH regularity of V_theta is internally produced. -/
theorem sourceMinimalEnvelope_thetaPSH (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    (ofFixedModel n M).IsThetaPSH θ (sourceMinimalEnvelope θ) :=
  (sourceMinimalEnvelope_model ω θ hbig).thetaPSH

/-- Exactly j original input slots and n-j literal minimal-envelope slots. -/
def sourceMinimalMixedMass (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (j : Fin (n + 1)) : ℝ≥0∞ :=
  sourceEndpointMixedMeasure θ (sourceMinimalEnvelope θ) u
    (sourceMinimalEnvelope_thetaPSH ω θ hbig) hu j univ

/-- The same tuple, forms and whole-space value give the existing native mass. -/
theorem sourceMinimalMixedMass_eq_native (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (j : Fin (n + 1)) :
    sourceMinimalMixedMass ω θ hbig u hu j =
      endpointMixedMass (atlasClosedFormToNative θ)
        (thetaPshSupremum (atlasClosedFormToNative θ).val) u
        (SingularMinimalCanonicalRay.isModelPotential_thetaPshSupremum ω
          (atlasClosedFormToNative θ) hbig).plurisubharmonic
        ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) j := by
  unfold sourceMinimalMixedMass
  rw [sourceEndpointMixedMeasure_eq_native]
  change endpointMixedMass (atlasClosedFormToNative θ) (sourceMinimalEnvelope θ) u _ _ j = _
  simp only [sourceMinimalEnvelope_eq_native]

/-- Actual compact mixed-measure finiteness precedes any real encoding. -/
theorem sourceMinimalMixedMass_lt_top (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (j : Fin (n + 1)) : sourceMinimalMixedMass ω θ hbig u hu j < ⊤ := by
  unfold sourceMinimalMixedMass sourceEndpointMixedMeasure
  exact globalMixedMeasure_apply_lt_top ω
    (endpointMixedPotential_thetaPlurisubharmonic (atlasClosedFormToNative θ) j u
      (sourceMinimalEnvelope θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp
        (sourceMinimalEnvelope_thetaPSH ω θ hbig))) univ

omit [BorelSpace M] [ConnectedSpace M] in
/-- The last endpoint selects the entire input in every slot, including n=0. -/
theorem sourceEndpointMixedMeasure_last
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (p u : M → EReal)
    (hp : (ofFixedModel n M).IsThetaPSH θ p) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceEndpointMixedMeasure θ p u hp hu (Fin.last n) =
      sourcePotentialNonPluripolarMeasure θ u hu := by
  unfold sourceEndpointMixedMeasure sourcePotentialNonPluripolarMeasure diagonalPotentialMeasure
  exact globalMixedMeasure_congr rfl (by
    funext i
    simp only [Fin.val_last, if_pos i.isLt]) _ _

/-- The final original mixed mass is the unchanged original diagonal mass. -/
theorem sourceMinimalMixedMass_last (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceMinimalMixedMass ω θ hbig u hu (Fin.last n) =
      sourcePotentialNonPluripolarMeasure θ u hu univ := by
  unfold sourceMinimalMixedMass
  rw [sourceEndpointMixedMeasure_last]

/-- The whole mixed-mass equivalence allows either original mass to vanish. -/
theorem sourcePEquivalent_iff_minimalMixedMass_eq (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : GlobalPComparison.sourcePOrder (n := n) u v) :
    GlobalPComparison.sourcePEquivalent (n := n) u v ↔
      ∀ j : Fin (n + 1), sourceMinimalMixedMass ω θ hbig u hu j =
        sourceMinimalMixedMass ω θ hbig v hv j := by
  simpa only [sourceMinimalMixedMass_eq_native] using
    SingularMinimalGlobalPMassCriterion.sourcePEquivalent_iff_minimal_endpointMixedMass_eq
      ω (atlasClosedFormToNative θ) hbig
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) huv

/-- Only this additional diagonal branch requires both original positive masses. -/
theorem sourcePEquivalent_iff_diagonalMass_eq_of_positive (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (huv : GlobalPComparison.sourcePOrder (n := n) u v) :
    GlobalPComparison.sourcePEquivalent (n := n) u v ↔
      sourcePotentialNonPluripolarMeasure θ u hu univ =
        sourcePotentialNonPluripolarMeasure θ v hv univ :=
  SingularGlobalPOrder.sourcePEquivalent_iff_diagonalPotentialMass_eq_of_sourcePOrder
    ω (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) hupos hvpos huv

/-- Entire original prop:Pequivchar2, general and extra positive branches together. -/
theorem sourcePEquivalent_mass_characterization (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : GlobalPComparison.sourcePOrder (n := n) u v) :
    (GlobalPComparison.sourcePEquivalent (n := n) u v ↔
      ∀ j : Fin (n + 1), sourceMinimalMixedMass ω θ hbig u hu j =
        sourceMinimalMixedMass ω θ hbig v hv j) ∧
    ((0 < sourcePotentialNonPluripolarMeasure θ u hu univ ∧
      0 < sourcePotentialNonPluripolarMeasure θ v hv univ) →
      (GlobalPComparison.sourcePEquivalent (n := n) u v ↔
        sourcePotentialNonPluripolarMeasure θ u hu univ =
          sourcePotentialNonPluripolarMeasure θ v hv univ)) :=
  ⟨sourcePEquivalent_iff_minimalMixedMass_eq ω θ hbig hu hv huv,
    fun hpos => sourcePEquivalent_iff_diagonalMass_eq_of_positive ω hu hv hpos.1 hpos.2 huv⟩

end SGPT.PSH.VariableComplexAtlas

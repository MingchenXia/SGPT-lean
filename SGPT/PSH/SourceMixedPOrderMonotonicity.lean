import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.PSH.GlobalPComparison
import SGPT.Foundations.Analysis.Pending.ActualMixedMassGlobalPMonotone

/-! Whole original `prop:mono2`: actual source mixed masses for the genuine
global P-preorder, retaining independent backgrounds, zero masses and n=0. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Whole original `prop:mono2` on the unchanged source mixed product and genuine global P-order. -/
theorem sourceMixedNonPluripolarMass_mono_of_sourcePOrder (ω : KahlerBackground n M)
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (huv : ∀ i, GlobalPComparison.sourcePOrder (n := n) (u i) (v i)) :
    sourceMixedNonPluripolarMass θ u hu ≤ sourceMixedNonPluripolarMass θ v hv :=
  ActualMixedMassGlobalPMonotone.globalMixedMass_mono_of_sourcePOrder ω
    (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i))
    (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (v i)).mp (hv i)) huv

/-- The same whole original inequality displayed on the literal actual measures evaluated on X. -/
theorem sourceMixedNonPluripolarMeasure_univ_mono_of_sourcePOrder (ω : KahlerBackground n M)
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (huv : ∀ i, GlobalPComparison.sourcePOrder (n := n) (u i) (v i)) :
    sourceMixedNonPluripolarMeasure θ u hu univ ≤
      sourceMixedNonPluripolarMeasure θ v hv univ :=
  sourceMixedNonPluripolarMass_mono_of_sourcePOrder ω hu hv huv

/-- Actual Kähler finiteness is produced before transporting global P-monotonicity to real masses. -/
theorem sourceMixedNonPluripolarMassReal_mono_of_sourcePOrder (ω : KahlerBackground n M)
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (huv : ∀ i, GlobalPComparison.sourcePOrder (n := n) (u i) (v i)) :
    (sourceMixedNonPluripolarMass θ u hu).toReal ≤
      (sourceMixedNonPluripolarMass θ v hv).toReal :=
  ENNReal.toReal_mono (sourceMixedNonPluripolarMass_lt_top ω θ v hv).ne
    (sourceMixedNonPluripolarMass_mono_of_sourcePOrder ω hu hv huv)

/-- Both actual global orders preserve the same independent original mixed mass, including zero. -/
theorem sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent (ω : KahlerBackground n M)
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (huv : ∀ i, GlobalPComparison.sourcePEquivalent (n := n) (u i) (v i)) :
    sourceMixedNonPluripolarMass θ u hu = sourceMixedNonPluripolarMass θ v hv :=
  le_antisymm
    (sourceMixedNonPluripolarMass_mono_of_sourcePOrder ω hu hv (fun i => (huv i).1))
    (sourceMixedNonPluripolarMass_mono_of_sourcePOrder ω hv hu (fun i => (huv i).2))

end SGPT.PSH.VariableComplexAtlas

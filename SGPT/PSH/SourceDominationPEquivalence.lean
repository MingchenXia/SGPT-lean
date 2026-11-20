import SGPT.Envelopes.SourceDominationPrinciple
import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import SGPT.PSH.SourcePMassCharacterization

/-! # Whole global P-equivalence clause of original rmk:npp:L982

Pinned author/chapter_npp.tex:1097--1101, with the original common-witness
condition eq:varphipsiPequiv at1088--1090. The original positive masses are
retained. The common source witness is produced from the actual original
ordinary envelope, with unchanged functions, background and actual measures.
The already checked sourceRelativeFullMass_domination covers the remark's
first, model-relative clause.
-/

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
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}

/-- The exact original existential common full-mass upper witness is
equivalent to TRUE background-independent source P-equivalence. -/
theorem sourcePEquivalent_iff_commonFullMassUpper (omega : KahlerBackground n M)
    (hu : IsThetaPSH θ u) (hv : IsThetaPSH θ v)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ) :
    GlobalPComparison.sourcePEquivalent (n := n) u v ↔
      ∃ w : M → EReal, ∃ hw : IsThetaPSH θ w,
        SGPT.PSH.SingularityLE u w ∧ SGPT.PSH.SingularityLE v w ∧
        sourcePotentialNonPluripolarMeasure θ u hu univ =
          sourcePotentialNonPluripolarMeasure θ w hw univ ∧
        sourcePotentialNonPluripolarMeasure θ v hv univ =
          sourcePotentialNonPluripolarMeasure θ w hw univ := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  constructor
  · intro hP
    have hfixed := (SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith omega
      (atlasClosedFormToNative θ) hun hvn hupos hvpos).mp hP
    have henv : sourceSingularityEnvelope θ u = sourceSingularityEnvelope θ v := by
      simpa only [sourceSingularityEnvelope_eq_native] using
        POrder.pEquivalentWith_iff_envelope_eq.mp hfixed
    let w := sourceSingularityEnvelope θ u
    have hw : IsThetaPSH θ w := sourceOrdinaryEnvelope_genuine hu
    have huw : SGPT.PSH.SingularityLE u w := by
      simpa only [w, SGPT.PSH.SingularityLE, sourceSingularityEnvelope_eq_native] using
        moreSingularOn_singularityEnvelope hun
    have hvw : SGPT.PSH.SingularityLE v w := by
      dsimp only [w]
      rw [henv]
      simpa only [SGPT.PSH.SingularityLE, sourceSingularityEnvelope_eq_native] using
        moreSingularOn_singularityEnvelope hvn
    have hwmass := sourceOrdinaryEnvelope_diagonalMass_eq omega hu
    have hmass := (sourcePEquivalent_iff_diagonalMass_eq_of_positive
      omega hu hv hupos hvpos hP.1).mp hP
    exact ⟨w, hw, huw, hvw, hwmass.symm, hmass.symm.trans hwmass.symm⟩
  · rintro ⟨w, hw, huw, hvw, humass, hvmass⟩
    have hwn := (isThetaPSH_iff_nativeThetaPotential θ w).mp hw
    have hwpos : 0 < sourcePotentialNonPluripolarMeasure θ w hw univ := by
      rw [← humass]
      exact hupos
    have huwP := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega
      (atlasClosedFormToNative θ) (atlasClosedFormToNative θ) hun hwn huw
    have hvwP := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega
      (atlasClosedFormToNative θ) (atlasClosedFormToNative θ) hvn hwn hvw
    have huwE := (sourcePEquivalent_iff_diagonalMass_eq_of_positive
      omega hu hw hupos hwpos huwP).mpr humass
    have hvwE := (sourcePEquivalent_iff_diagonalMass_eq_of_positive
      omega hv hw hvpos hwpos hvwP).mpr hvmass
    exact ⟨GlobalPComparison.sourcePOrder_trans omega huwE.1 hvwE.2,
      GlobalPComparison.sourcePOrder_trans omega hvwE.1 huwE.2⟩

/-- Original domination reformulated with global source P-equivalence;
the actual existential common witness is manufactured by the preceding theorem. -/
theorem sourceDomination_of_sourcePEquivalent (omega : KahlerBackground n M)
    (hu : IsThetaPSH θ u) (hv : IsThetaPSH θ v)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (hP : GlobalPComparison.sourcePEquivalent (n := n) u v)
    (hzero : sourcePotentialNonPluripolarMeasure θ u hu {x | u x < v x} = 0) :
    v ≤ u :=
  sourceDomination omega hu hv hupos hvpos
    ((sourcePEquivalent_iff_commonFullMassUpper omega hu hv hupos hvpos).mp hP) hzero

end SGPT.PSH.VariableComplexAtlas

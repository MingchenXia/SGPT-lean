import SGPT.Envelopes.SourcePositiveAffineEnvelopes
import SGPT.Foundations.Analysis.Pending.DominationPrinciple

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v φ : M → EReal}

/-- The WHOLE original domination principle with its actual arbitrary common
witness displayed: unchanged source functions/form, actual measures and additive
singularity order. No model, normalization or pointwise order is inserted. -/
theorem sourceDomination_of_common_witness (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (huφ : SGPT.PSH.SingularityLE u φ) (hvφ : SGPT.PSH.SingularityLE v φ)
    (humass : sourcePotentialNonPluripolarMeasure θ u hu univ =
      sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hvmass : sourcePotentialNonPluripolarMeasure θ v hv univ =
      sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hzero : sourcePotentialNonPluripolarMeasure θ u hu {x | u x < v x} = 0) :
    v ≤ u :=
  DominationPrinciple.le_of_diagonalPotentialMeasure_lt_eq_zero ω (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv)
    ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
    hupos hvpos huφ hvφ humass hvmass hzero

/-- WHOLE original thm:dom_prin_1, with the literal EXISTENTIAL common genuine
source witness of the SAME actual mass. The nullity locus and conclusion are
at every original point; all analytic barrier and nondegeneracy stages are internal. -/
theorem sourceDomination (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ)
    (hcommon : ∃ φ : M → EReal, ∃ hφ : (ofFixedModel n M).IsThetaPSH θ φ,
      SGPT.PSH.SingularityLE u φ ∧ SGPT.PSH.SingularityLE v φ ∧
        sourcePotentialNonPluripolarMeasure θ u hu univ =
          sourcePotentialNonPluripolarMeasure θ φ hφ univ ∧
        sourcePotentialNonPluripolarMeasure θ v hv univ =
          sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hzero : sourcePotentialNonPluripolarMeasure θ u hu {x | u x < v x} = 0) :
    v ≤ u := by
  obtain ⟨φ, hφ, huφ, hvφ, humass, hvmass⟩ := hcommon
  exact sourceDomination_of_common_witness ω hu hv hφ hupos hvpos huφ hvφ humass hvmass hzero

/-- FIRST original model-relative remark only: the ENTIRE existing source
additive-preceq full-mass class supplies the actual witness and positive masses.
The separate global P-equivalence characterization is not asserted here. -/
theorem sourceRelativeFullMass_domination (ω : KahlerBackground n M)
    {hφ : SourceModelPotential θ φ}
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ)
    (hzero : sourcePotentialNonPluripolarMeasure θ u hu.choose {x | u x < v x} = 0) :
    v ≤ u := by
  have hupos : 0 < sourcePotentialNonPluripolarMeasure θ u hu.choose univ := by
    rw [hu.choose_spec.2]
    exact hφ.choose_spec.2
  have hvpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv.choose univ := by
    rw [hv.choose_spec.2]
    exact hφ.choose_spec.2
  exact sourceDomination_of_common_witness ω hu.choose hv.choose hφ.thetaPSH
    hupos hvpos hu.choose_spec.1 hv.choose_spec.1 hu.choose_spec.2 hv.choose_spec.2 hzero

end SGPT.PSH.VariableComplexAtlas

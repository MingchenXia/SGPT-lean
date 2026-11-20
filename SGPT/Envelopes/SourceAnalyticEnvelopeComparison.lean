import SGPT.Envelopes.SourceMinimalEnvelopeLocalBounds
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.PSH.SourcePIComparison
import SGPT.PSH.AnalyticTypeSingularityEquivalence
import SGPT.Foundations.Analysis.Pending.ActualAnalyticReferenceFixedEnvelopeEquality

/-! # The original analytic P/I comparison, including zero mass and dimension zero

The source hypothesis is the original connected-neighborhood rational
logarithmic presentation with bounded remainder. No goodness, mass,
strict positivity, or output envelope certificate is supplied.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Full original ideal order against an original rational analytic reference
produces one global additive constant, with independent original backgrounds. -/
theorem sourceIOrder_singularityLE_of_analytic {u v : M → EReal}
    (hI : sourceIOrder (ofFixedModel n M) u v)
    (hA : (ofFixedModel n M).HasRationalAnalyticType v) :
    SGPT.PSH.SingularityLE u v := by
  obtain ⟨θ, hu⟩ := hI.1
  obtain ⟨ζ, hv⟩ := hI.2.1
  exact ActualAnalyticReferenceFixedEnvelopeEquality.moreSingularOn_of_iOrder_analytic_reference
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential ζ v).mp hv)
    ((sourceRationalAnalyticType_iff_native v).mp hA)
    ((sourceIOrder_iff_native hI.1 hI.2.1).mp hI)

variable [Nonempty M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}

/-- Literal envelope equality and BOTH printed source additive equivalences.
No positivity of the original background or mass is assumed. -/
theorem sourceAnalytic_envelope_comparison
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hA : (ofFixedModel n M).HasRationalAnalyticType φ) :
    sourceSingularityEnvelope θ φ = sourceIEnvelope θ φ ∧
      SGPT.PSH.SingularityEquiv φ (sourceSingularityEnvelope θ φ) ∧
      SGPT.PSH.SingularityEquiv (sourceSingularityEnvelope θ φ) (sourceIEnvelope θ φ) := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have heq : sourceSingularityEnvelope θ φ = sourceIEnvelope θ φ := by
    rw [sourceSingularityEnvelope_eq_native, sourceIEnvelope_eq_native θ φ hφ]
    exact ActualAnalyticReferenceFixedEnvelopeEquality.singularityEnvelope_eq_iSingularityEnvelope_of_analytic_reference
        (atlasClosedFormToNative θ) hn ((sourceRationalAnalyticType_iff_native φ).mp hA)
  have hback : SGPT.PSH.SingularityLE (sourceIEnvelope θ φ) φ :=
    sourceIOrder_singularityLE_of_analytic (sourceIEquivalent_iEnvelope hφ).2 hA
  have hfront : SGPT.PSH.SingularityLE φ (sourceIEnvelope θ φ) := by
    rw [sourceIEnvelope_eq_native θ φ hφ]
    exact moreSingularOn_iSingularityEnvelope hn
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    exact ⟨hfront, hback⟩
  · rw [heq]
    exact SGPT.PSH.singularityEquiv_refl _

/-- Both actual envelope functions retain connected-neighborhood rational
analytic presentations; their bounded remainders are internally manufactured. -/
theorem sourceAnalytic_envelopes_hasRationalAnalyticType
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hA : (ofFixedModel n M).HasRationalAnalyticType φ) :
    (ofFixedModel n M).HasRationalAnalyticType (sourceSingularityEnvelope θ φ) ∧
      (ofFixedModel n M).HasRationalAnalyticType (sourceIEnvelope θ φ) := by
  have hcomp := sourceAnalytic_envelope_comparison hφ hA
  have hP := hA.of_singularityEquiv hφ.1
    (isThetaPSH_sourceSingularityEnvelope hφ).1 hcomp.2.1
  refine ⟨hP, ?_⟩
  exact hP.of_singularityEquiv (isThetaPSH_sourceSingularityEnvelope hφ).1
    (isThetaPSH_sourceIEnvelope hφ).1 hcomp.2.2

variable [MeasurableSpace M] [BorelSpace M]

/-- The printed original mass--volume identity includes vanishing original
mass and dimension zero, using the SAME background and actual source measures. -/
theorem sourceAnalytic_mass_eq_iVolume (ω : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hA : (ofFixedModel n M).HasRationalAnalyticType φ) :
    sourcePotentialNonPluripolarMeasure θ φ hφ univ = sourceIVolume θ φ hφ := by
  have hcomp := sourceAnalytic_envelope_comparison hφ hA
  have hI := SGPT.PSH.singularityEquiv_trans hcomp.2.1 hcomp.2.2
  change sourcePotentialNonPluripolarMeasure θ φ hφ univ =
    sourcePotentialNonPluripolarMeasure θ (sourceIEnvelope θ φ)
      (isThetaPSH_sourceIEnvelope hφ) univ
  exact le_antisymm
    (sourcePotentialNonPluripolarMass_mono ω hφ (isThetaPSH_sourceIEnvelope hφ) hI.1)
    (sourcePotentialNonPluripolarMass_mono ω (isThetaPSH_sourceIEnvelope hφ) hφ hI.2)

/-- WHOLE `prop:analysingcompPandPI`: the two original singularity
equivalences, both original analytic types, and the actual mass--volume identity. -/
theorem sourceAnalytic_whole_envelope_comparison (ω : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hA : (ofFixedModel n M).HasRationalAnalyticType φ) :
    (SGPT.PSH.SingularityEquiv φ (sourceSingularityEnvelope θ φ) ∧
      SGPT.PSH.SingularityEquiv (sourceSingularityEnvelope θ φ) (sourceIEnvelope θ φ)) ∧
      ((ofFixedModel n M).HasRationalAnalyticType (sourceSingularityEnvelope θ φ) ∧
        (ofFixedModel n M).HasRationalAnalyticType (sourceIEnvelope θ φ)) ∧
      sourcePotentialNonPluripolarMeasure θ φ hφ univ = sourceIVolume θ φ hφ :=
  ⟨(sourceAnalytic_envelope_comparison hφ hA).2,
    sourceAnalytic_envelopes_hasRationalAnalyticType hφ hA,
    sourceAnalytic_mass_eq_iVolume ω hφ hA⟩

end SGPT.PSH.VariableComplexAtlas

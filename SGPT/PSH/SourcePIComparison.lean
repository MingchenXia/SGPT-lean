import SGPT.PSH.SourceIVolumeGoodness
import SGPT.Foundations.Analysis.Pending.IGoodMassReduction
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

/-! # Original ordinary and I-envelope comparisons

All original source competitors, positive real exponents, actual measures
and unchanged backgrounds are retained. The native analytic and total mixed
mass monotonicity theorems are reused, including dimension zero.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.MixedMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}

/-- The entire original ordinary envelope is a genuine source potential;
local potentials of the original background are internally produced. -/
theorem isThetaPSH_sourceSingularityEnvelope
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceSingularityEnvelope θ φ) := by
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  rw [sourceSingularityEnvelope_eq_native]
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  exact SGPT.Foundations.Analysis.Pending.singularityEnvelope_isThetaPshPotential
    (atlasClosedFormToNative θ).val θ.closed θ.typeOneOne
    hn.1.hasSmoothLocalPotentials φ hn

/-- Source multiplier equivalence with the ordinary envelope at every
positive real exponent, obtained from the actual proved strong-openness route. -/
theorem sourceIEquivalent_pEnvelope
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIEquivalent (ofFixedModel n M) φ (sourceSingularityEnvelope θ φ) := by
  have hP := isThetaPSH_sourceSingularityEnvelope hφ
  apply (sourceIEquivalent_iff_native ⟨θ, hφ⟩ ⟨θ, hP⟩).mpr
  rw [sourceSingularityEnvelope_eq_native]
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  exact iEquivalent_singularityEnvelope (atlasClosedFormToNative θ).val
    θ.closed θ.typeOneOne hn.1.hasSmoothLocalPotentials φ hn

theorem sourcePEnvelope_le_IEnvelope
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceSingularityEnvelope θ φ ≤ sourceIEnvelope θ φ :=
  le_sourceIEnvelope (isThetaPSH_sourceSingularityEnvelope hφ)
    (sourceSingularityEnvelope_le_zero θ φ)
    (sourceIEquivalent_symm (sourceIEquivalent_pEnvelope hφ))

theorem sourceIEnvelope_pEnvelope
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIEnvelope θ (sourceSingularityEnvelope θ φ) = sourceIEnvelope θ φ :=
  (sourceIEnvelope_eq_of_equivalent (sourceIEquivalent_pEnvelope hφ)).symm

theorem sourcePEnvelope_iEnvelope
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceSingularityEnvelope θ (sourceIEnvelope θ φ) = sourceIEnvelope θ φ := by
  rw [sourceSingularityEnvelope_eq_native, sourceIEnvelope_eq_native θ φ hφ]
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  exact singularityEnvelope_iSingularityEnvelope (atlasClosedFormToNative θ).val
    θ.closed θ.typeOneOne hn.1.hasSmoothLocalPotentials φ hn

/-- Whole `prop:PandPI` and its composition identity, plus the actual
ordinary fixed-point identity for the original I-envelope. -/
theorem sourcePI_comparison
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceSingularityEnvelope θ φ ≤ sourceIEnvelope θ φ ∧
      sourceIEquivalent (ofFixedModel n M) φ (sourceSingularityEnvelope θ φ) ∧
      sourceIEnvelope θ (sourceSingularityEnvelope θ φ) = sourceIEnvelope θ φ ∧
      sourceSingularityEnvelope θ (sourceIEnvelope θ φ) = sourceIEnvelope θ φ :=
  ⟨sourcePEnvelope_le_IEnvelope hφ, sourceIEquivalent_pEnvelope hφ,
    sourceIEnvelope_pEnvelope hφ, sourcePEnvelope_iEnvelope hφ⟩

variable [MeasurableSpace M] [BorelSpace M]

/-- Whole `cor:compnppmassandvol`: actual original mass is at most actual
I-volume, with the original Kähler standing background and no positivity,
bigness or positive-dimension condition. -/
theorem sourceMass_le_iVolume (ω : KahlerBackground n M)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourcePotentialNonPluripolarMeasure θ φ hφ univ ≤ sourceIVolume θ φ hφ := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have hI := (isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_sourceIEnvelope hφ)
  have horder : MoreSingularOn φ (sourceIEnvelope θ φ) univ := by
    rw [sourceIEnvelope_eq_native θ φ hφ]
    exact moreSingularOn_iSingularityEnvelope hn
  exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential
    (θ := fun _ : Fin n => atlasClosedFormToNative θ)
    (u := fun _ => φ) (v := fun _ => sourceIEnvelope θ φ)
    ω (fun _ => hn) (fun _ => hI) (fun _ => horder)

end SGPT.PSH.VariableComplexAtlas

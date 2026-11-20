import SGPT.Envelopes.SourceRooftopMassCalculus
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The literal entire-space mass of the unchanged original mixed product. -/
def sourceMixedNonPluripolarMass
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) : ℝ≥0∞ :=
  sourceMixedNonPluripolarMeasure θ u hu univ

omit [BorelSpace M] in
/-- No object replacement: source total mass is exactly the actual native total mass. -/
theorem sourceMixedNonPluripolarMass_eq_native
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceMixedNonPluripolarMass θ u hu = MixedMass.globalMixedMass
      (fun i => atlasClosedFormToNative (θ i)) u
      (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)).1) := rfl

/-- Actual finiteness is produced before any real mass readback. -/
theorem sourceMixedNonPluripolarMass_lt_top (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) :
    sourceMixedNonPluripolarMass θ u hu < ⊤ :=
  MixedMass.globalMixedMass_lt_top ω
    (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)).1)

omit [BorelSpace M] in
/-- The constant original tuple gives the same original diagonal mass. -/
theorem sourceMixedNonPluripolarMass_diagonal
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceMixedNonPluripolarMass (fun _ => θ) (fun _ => u) (fun _ => hu) =
      sourcePotentialNonPluripolarMeasure θ u hu univ :=
  congrArg (fun μ : Measure M => μ univ) (sourceMixedNonPluripolarMeasure_diagonal θ u hu)

/-- WHOLE original mixed monotonicity: more singular in every independent
slot gives less mass, including dimension zero and zero masses. -/
theorem sourceMixedNonPluripolarMass_mono (ω : KahlerBackground n M)
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (huv : ∀ i, SGPT.PSH.SingularityLE (u i) (v i)) :
    sourceMixedNonPluripolarMass θ u hu ≤ sourceMixedNonPluripolarMass θ v hv :=
  GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential ω
    (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i))
    (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (v i)).mp (hv i)) huv

/-- The whole printed diagonal consequence has the same additive source order. -/
theorem sourcePotentialNonPluripolarMass_mono (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : SGPT.PSH.SingularityLE u v) :
    sourcePotentialNonPluripolarMeasure θ u hu univ ≤
      sourcePotentialNonPluripolarMeasure θ v hv univ := by
  simpa only [sourceMixedNonPluripolarMass_diagonal] using
    (sourceMixedNonPluripolarMass_mono ω (fun _ : Fin n => hu)
      (fun _ => hv) (fun _ => huv))

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}

/-- The actual maximum estimate on every Borel set, with ties assigned to u. -/
theorem sourcePotentialNonPluripolarMeasure_max_apply (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    {E : Set M} (hE : MeasurableSet E) :
    sourcePotentialNonPluripolarMeasure θ u hu (E ∩ {x | v x ≤ u x}) +
        sourcePotentialNonPluripolarMeasure θ v hv (E ∩ {x | u x < v x}) ≤
      sourcePotentialNonPluripolarMeasure θ (fun x => max (u x) (v x))
        (sourceThetaMaximum_genuine hu hv) E :=
  MaxMassDecomposition.measure_max_ge' ω
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceThetaMaximum_genuine hu hv)) hE

/-- WHOLE original measure inequality, with the actual contact piece retained. -/
theorem sourcePotentialNonPluripolarMeasure_max (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | v x ≤ u x} +
        (sourcePotentialNonPluripolarMeasure θ v hv).restrict {x | u x < v x} ≤
      sourcePotentialNonPluripolarMeasure θ (fun x => max (u x) (v x))
        (sourceThetaMaximum_genuine hu hv) := by
  apply Measure.le_iff.mpr
  intro E hE
  simpa only [Measure.add_apply, Measure.restrict_apply hE] using
    sourcePotentialNonPluripolarMeasure_max_apply ω hu hv hE

/-- Actual contact comparison on every Borel set, under only original pointwise order. -/
theorem sourcePotentialNonPluripolarMeasure_contact_apply (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : u ≤ v) {E : Set M} (hE : MeasurableSet E) :
    sourcePotentialNonPluripolarMeasure θ u hu (E ∩ {x | u x = v x}) ≤
      sourcePotentialNonPluripolarMeasure θ v hv (E ∩ {x | u x = v x}) :=
  MaxMassDecomposition.contact_measure_le ω
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) huv hE

/-- WHOLE printed contact-set consequence, as an actual inequality of measures. -/
theorem sourcePotentialNonPluripolarMeasure_contact (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (huv : u ≤ v) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | u x = v x} ≤
      (sourcePotentialNonPluripolarMeasure θ v hv).restrict {x | u x = v x} := by
  apply Measure.le_iff.mpr
  intro E hE
  simpa only [Measure.restrict_apply hE] using
    sourcePotentialNonPluripolarMeasure_contact_apply ω hu hv huv hE

end SGPT.PSH.VariableComplexAtlas

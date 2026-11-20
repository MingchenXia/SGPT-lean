import SGPT.Envelopes.SourceInterpolatedEnvelope
import SGPT.Envelopes.SourceNonPluripolarMassOrder

/-! Genuine mass order for the unchanged original interpolating envelope. -/
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
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {u v : M → EReal}

/-- The SAME original interpolated mixed mass is monotone under the original
additive singularity comparison; no mass or I-envelope comparison is assumed. -/
theorem sourceInterpolatedMass_mono_of_singularityLE (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (huv : SGPT.PSH.SingularityLE u v) :
    sourceInterpolatedMass θ j u hu ≤ sourceInterpolatedMass θ j v hv := by
  have hI := sourceIEnvelope_mono_of_singularityLE hu hv huv
  let U : Fin n → M → EReal := fun i => if i.val < j.val then u else sourceIEnvelope θ u
  let V : Fin n → M → EReal := fun i => if i.val < j.val then v else sourceIEnvelope θ v
  have hU (i : Fin n) : IsThetaPshPotential (atlasClosedFormToNative θ).val (U i) := by
    dsimp only [U]
    split_ifs with hi
    · exact (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
    · exact (isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_sourceIEnvelope hu)
  have hV (i : Fin n) : IsThetaPshPotential (atlasClosedFormToNative θ).val (V i) := by
    dsimp only [V]
    split_ifs with hi
    · exact (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
    · exact (isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_sourceIEnvelope hv)
  exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential ω hU hV (fun i => by
    dsimp only [U, V]
    split_ifs with hi
    · exact huv
    · exact MoreSingularOn.of_le (fun x _ => hI x))

/-- Equivalent original singularity types preserve the actual interpolated mass. -/
theorem sourceInterpolatedMass_eq_of_singularityEquiv (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (huv : SGPT.PSH.SingularityEquiv u v) :
    sourceInterpolatedMass θ j u hu = sourceInterpolatedMass θ j v hv :=
  le_antisymm (sourceInterpolatedMass_mono_of_singularityLE ω j hu hv huv.1)
    (sourceInterpolatedMass_mono_of_singularityLE ω j hv hu huv.2)

/-- Normalize the original datum internally; no candidate or finite bound
is supplied by the caller. -/
theorem sourceInterpolatedEnvelopeCompetitors_nonempty (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    Nonempty (sourceInterpolatedEnvelopeCompetitors θ j u hu) := by
  obtain ⟨C, hC⟩ := ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).exists_global_upper_bound
  let s : M → EReal := fun x => u x + ((-C : ℝ) : EReal)
  have hs : (ofFixedModel n M).IsThetaPSH θ s := sourceThetaPSH_add_const hu (-C)
  have hs0 : s ≤ 0 := by
    intro x
    change u x + ((-C : ℝ) : EReal) ≤ (0 : EReal)
    have h := add_le_add (hC x) (le_refl ((-C : ℝ) : EReal))
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h
  have hus : SGPT.PSH.SingularityLE u s := by
    apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    refine ⟨C, fun x => ?_⟩
    change u x ≤ (u x + ((-C : ℝ) : EReal)) + (C : EReal)
    have hcancel : (u x + ((-C : ℝ) : EReal)) + (C : EReal) = u x := by
      simpa only [neg_neg] using RelativePreceqClasses.add_coe_add_coe_neg (u x) (-C)
    exact hcancel.symm.le
  have hsu : SGPT.PSH.SingularityLE s u :=
    (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨-C, fun _ => le_rfl⟩
  exact ⟨⟨s, hs, hs0, hus, sourceInterpolatedMass_eq_of_singularityEquiv ω j hu hs ⟨hus, hsu⟩⟩⟩

/-- The whole actual original interpolating envelope is genuinely theta-PSH. -/
theorem isThetaPSH_sourceInterpolatedEnvelope (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (ofFixedModel n M).IsThetaPSH θ (sourceInterpolatedEnvelope θ j u hu) := by
  let : Nonempty (sourceInterpolatedEnvelopeCompetitors θ j u hu) :=
    sourceInterpolatedEnvelopeCompetitors_nonempty ω j hu
  apply isThetaPSH_uscSup_of_majorant
    (w := fun _ => (0 : EReal)) (fun v => v.2.choose)
    continuous_const.upperSemicontinuous (fun _ => EReal.coe_ne_top (0 : ℝ))
  intro v
  exact v.2.choose_spec.1

omit [BorelSpace M] in
/-- Every original competitor is nonpositive, hence so is the actual envelope. -/
theorem sourceInterpolatedEnvelope_le_zero (j : Fin (n + 1))
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceInterpolatedEnvelope θ j u hu ≤ 0 := by
  apply uscRegularization_le continuous_const.upperSemicontinuous
  intro x
  exact iSup_le fun v => v.2.choose_spec.1 x

/-- The original datum is more singular than the produced original envelope. -/
theorem singularityLE_sourceInterpolatedEnvelope (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    SGPT.PSH.SingularityLE u (sourceInterpolatedEnvelope θ j u hu) := by
  let v := Classical.choice (sourceInterpolatedEnvelopeCompetitors_nonempty ω j hu)
  have hvP : v.1 ≤ sourceInterpolatedEnvelope θ j u hu := by
    intro x
    exact (le_iSup (fun a : sourceInterpolatedEnvelopeCompetitors θ j u hu => a.1 x) v).trans
      (le_uscRegularization
        (fun y => ⨆ a : sourceInterpolatedEnvelopeCompetitors θ j u hu, a.1 y) x)
  exact SGPT.PSH.singularityLE_trans v.2.choose_spec.2.1
    (MoreSingularOn.of_le fun x _ => hvP x)

/-- Actual diagonal mass cannot decrease under the original interpolating envelope. -/
theorem sourceInterpolatedEnvelope_mass_ge (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ u hu univ ≤
      sourcePotentialNonPluripolarMeasure θ (sourceInterpolatedEnvelope θ j u hu)
        (isThetaPSH_sourceInterpolatedEnvelope ω j hu) univ :=
  sourcePotentialNonPluripolarMass_mono ω hu
    (isThetaPSH_sourceInterpolatedEnvelope ω j hu)
    (singularityLE_sourceInterpolatedEnvelope ω j hu)

/-- Positive actual source mass gives positive output mass, without an
idempotence or interpolated-mass-preservation premise. -/
theorem sourceInterpolatedEnvelope_positive (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    0 < sourcePotentialNonPluripolarMeasure θ (sourceInterpolatedEnvelope θ j u hu)
      (isThetaPSH_sourceInterpolatedEnvelope ω j hu) univ :=
  lt_of_lt_of_le hpos (sourceInterpolatedEnvelope_mass_ge ω j hu)

/-- Actual interpolated mass is finite before real encoding or limit arguments. -/
theorem sourceInterpolatedMass_lt_top (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceInterpolatedMass θ j u hu < ⊤ := by
  unfold sourceInterpolatedMass sourceEndpointMixedMeasure
  exact GlobalNonPluripolar.globalMixedMeasure_apply_lt_top ω
    (RelativeEnergy.endpointMixedPotential_thetaPlurisubharmonic
      (atlasClosedFormToNative θ) j u (sourceIEnvelope θ u)
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_sourceIEnvelope hu))) univ

/-- The actual mixed mass has the lower half of the preservation comparison.
The reverse inequality is a separate remaining mathematical obligation. -/
theorem sourceInterpolatedMass_le_envelope (ω : KahlerBackground n M)
    (j : Fin (n + 1)) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceInterpolatedMass θ j u hu ≤
      sourceInterpolatedMass θ j (sourceInterpolatedEnvelope θ j u hu)
        (isThetaPSH_sourceInterpolatedEnvelope ω j hu) :=
  sourceInterpolatedMass_mono_of_singularityLE ω j hu
    (isThetaPSH_sourceInterpolatedEnvelope ω j hu)
    (singularityLE_sourceInterpolatedEnvelope ω j hu)

end SGPT.PSH.VariableComplexAtlas

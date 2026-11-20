import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.ShiftedRooftopContactProof

/-! # Whole original rooftop and relative-envelope contact measures

The source raw rooftop and generalized relative envelope are unchanged.
The only missing object link is the entire source relative competitor family
and native shifted limit. Original nonbottom produces genuineness internally;
individual early shifted roofs may be bottom. All analytic contact, tail,
increasing-limit and measure-regularity results are existing native proofs.
The complete source-first route is `source-rooftop-contact-measures.tex`.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass ShiftedRooftopLimit

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}

/-- Original nonbottom forces the entire competitor family nonempty; the
existing genuine-obstacle supremum producer then supplies the output. -/
theorem sourceRelativeEnvelope_genuine_of_ne_bot
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hne : sourceRelativeEnvelope θ u v ≠ ⊥) :
    (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ u v) := by
  classical
  have hn : Nonempty (sourceRelativeEnvelopeCompetitors θ u v) := by
    by_contra h
    have : IsEmpty (sourceRelativeEnvelopeCompetitors θ u v) := not_nonempty_iff.mp h
    apply hne
    change uscRegularization (fun x => ⨆ a : sourceRelativeEnvelopeCompetitors θ u v, a.1 x) = ⊥
    have hraw : (fun x => ⨆ a : sourceRelativeEnvelopeCompetitors θ u v, a.1 x) =
        (⊥ : M → EReal) := by funext x; simp
    rw [hraw]
    exact uscRegularization_const ⊥
  let := hn
  exact isThetaPSH_uscSup_of_majorant (fun a => a.2.1) hv.upperSemicontinuous hv.1
    (fun a => ((sourceRelativeEnvelopeCompetitors_iff hv).mp a.2).2.1)

/-- BOTH ALL-competitor directions give the actual native shifted limit.
Its first argument is the unshifted obstacle v; no intermediate roof regularity
or finite-energy/mass/model condition is assumed. -/
theorem sourceRelativeEnvelope_eq_nativeShiftedRooftopLimit
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hne : sourceRelativeEnvelope θ u v ≠ ⊥) :
    sourceRelativeEnvelope θ u v =
      shiftedRooftopLimit (atlasClosedFormToNative θ) v u := by
  have hη := sourceRelativeEnvelope_genuine_of_ne_bot hv hne
  have hnu := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hnv := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  apply le_antisymm
  · change uscRegularization (fun x => ⨆ a : sourceRelativeEnvelopeCompetitors θ u v, a.1 x) ≤ _
    apply uscRegularization_le (upperSemicontinuous_uscRegularization _)
    intro x
    apply iSup_le
    intro a
    have ha := (sourceRelativeEnvelopeCompetitors_iff hv).mp a.2
    obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp ha.2.2
    obtain ⟨j, hj⟩ := exists_nat_gt C
    have haj : a.1 ≤ shiftedRooftop (atlasClosedFormToNative θ) v u (j : ℝ) :=
      le_rooftopEnvelope ((isThetaPSH_iff_nativeThetaPotential θ a.1).mp ha.1)
        (quasiEverywhere_of_forall fun y => le_min (ha.2.1 y)
          ((hC y).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hj.le))))
    exact (haj x).trans (shiftedRooftop_le_shiftedRooftopLimit _ v u j x)
  · change uscRegularization (⨆ j : ℕ, shiftedRooftop (atlasClosedFormToNative θ) v u (j : ℝ)) ≤ _
    apply uscRegularization_le hη.upperSemicontinuous
    apply iSup_le
    intro j
    apply (rooftopEnvelope_le_iff hη.upperSemicontinuous).mpr
    intro a ha hqa
    have hav : a ≤ v := ha.1.le_of_quasiEverywhere_le hnv.1
      (hqa.mono fun y hy => hy.trans (min_le_left _ _))
    have hauj : a ≤ fun y => u y + ((j : ℝ) : EReal) :=
      ha.1.le_of_quasiEverywhere_le (hnu.add_const (j : ℝ)).1
        (hqa.mono fun y hy => hy.trans (min_le_right _ _))
    let b : sourceRelativeEnvelopeCompetitors θ u v :=
      ⟨a, (isThetaPSH_iff_nativeThetaPotential θ a).mpr ha,
        sourceQuasiEverywhere_of_forall hav,
        (singularityLE_iff_exists_real _ _).mpr ⟨(j : ℝ), hauj⟩⟩
    intro x
    change a x ≤ uscRegularization
      (fun y => ⨆ a : sourceRelativeEnvelopeCompetitors θ u v, a.1 y) x
    exact (le_iSup (fun a : sourceRelativeEnvelopeCompetitors θ u v => a.1 x) b).trans
      (le_uscRegularization (fun y => ⨆ a : sourceRelativeEnvelopeCompetitors θ u v, a.1 y) x)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] in
/-- Equality of WHOLE actual source/native rooftop measures, not just their
total masses. Native genuineness comes from the original genuine raw roof. -/
theorem sourceThetaRooftop_measure_eq_native
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v)) :
    sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr =
      diagonalPotentialMeasure (atlasClosedFormToNative θ)
        (RelativeDarvasDistance.rooftop (atlasClosedFormToNative θ) u v)
        (sourceThetaRooftop_native_genuine hu hv hr) :=
  MaxMassDecomposition.diagonalPotentialMeasure_congr
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp hr)
    (sourceThetaRooftop_native_genuine hu hv hr)
    (sourceThetaRooftop_eq_native hu hv (sourceThetaRooftop_native_genuine hu hv hr))

/-- The existing whole native inequality read on EVERY original set. -/
theorem sourceThetaRooftop_measure_le_apply (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v)) (E : Set M) :
    sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr E ≤
      sourcePotentialNonPluripolarMeasure θ u hu (E ∩ {x | thetaRooftop θ u v x = u x}) +
        sourcePotentialNonPluripolarMeasure θ v hv (E ∩ {x | thetaRooftop θ u v x = v x}) := by
  simpa only [sourcePotentialNonPluripolarMeasure,
    sourceThetaRooftop_eq_native hu hv (sourceThetaRooftop_native_genuine hu hv hr),
    RelativeDarvasDistance.rooftop] using
    RooftopMassDecomposition.diagonalPotentialMeasure_rooftopEnvelope_min_le ω
      (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv)
      (sourceThetaRooftop_native_genuine hu hv hr) E

/-- WHOLE original lma:rooftopMA as the actual inequality of measures. -/
theorem sourceThetaRooftop_measure_le (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v)) :
    sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr ≤
      (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | thetaRooftop θ u v x = u x} +
        (sourcePotentialNonPluripolarMeasure θ v hv).restrict {x | thetaRooftop θ u v x = v x} := by
  apply Measure.le_iff.mpr
  intro E hE
  simpa only [Measure.add_apply, Measure.restrict_apply hE] using
    sourceThetaRooftop_measure_le_apply ω hu hv hr E

/-- Both contact pieces vanish on the actual two-obstacle noncontact set. -/
theorem sourceThetaRooftop_noncontact_null (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v)) :
    sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr
      {x | thetaRooftop θ u v x ≠ u x ∧ thetaRooftop θ u v x ≠ v x} = 0 := by
  have h := sourceThetaRooftop_measure_le_apply ω hu hv hr
    {x | thetaRooftop θ u v x ≠ u x ∧ thetaRooftop θ u v x ≠ v x}
  have hleft : {x | thetaRooftop θ u v x ≠ u x ∧ thetaRooftop θ u v x ≠ v x} ∩
      {x | thetaRooftop θ u v x = u x} = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun x hx => hx.1.1 hx.2
  have hright : {x | thetaRooftop θ u v x ≠ u x ∧ thetaRooftop θ u v x ≠ v x} ∩
      {x | thetaRooftop θ u v x = v x} = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun x hx => hx.1.2 hx.2
  rw [hleft, hright, measure_empty, measure_empty, add_zero] at h
  exact le_antisymm h zero_le

/-- The original carried-by consequence holds for EVERY set, retaining the
actual union of contacts and making no topological-support claim. -/
theorem sourceThetaRooftop_measure_carried (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : (ofFixedModel n M).IsThetaPSH θ (thetaRooftop θ u v)) (E : Set M) :
    sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr E =
      sourcePotentialNonPluripolarMeasure θ (thetaRooftop θ u v) hr
        (E ∩ ({x | thetaRooftop θ u v x = u x} ∪ {x | thetaRooftop θ u v x = v x})) := by
  apply le_antisymm ?_ (measure_mono inter_subset_left)
  have hsub : E ⊆
      (E ∩ ({x | thetaRooftop θ u v x = u x} ∪ {x | thetaRooftop θ u v x = v x})) ∪
        {x | thetaRooftop θ u v x ≠ u x ∧ thetaRooftop θ u v x ≠ v x} := by
    intro x hx
    by_cases h1 : thetaRooftop θ u v x = u x
    · exact Or.inl ⟨hx, Or.inl h1⟩
    · by_cases h2 : thetaRooftop θ u v x = v x
      · exact Or.inl ⟨hx, Or.inr h2⟩
      · exact Or.inr ⟨h1, h2⟩
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans_eq
    (by rw [sourceThetaRooftop_noncontact_null ω hu hv hr, add_zero])

/-- ALL-set relative-envelope domination. Genuine eta is manufactured from
the ORIGINAL nonbottom condition before the actual native final theorem. -/
theorem sourceRelativeEnvelope_measure_le_apply (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hne : sourceRelativeEnvelope θ u v ≠ ⊥) (E : Set M) :
    sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ u v)
        (sourceRelativeEnvelope_genuine_of_ne_bot hv hne) E ≤
      sourcePotentialNonPluripolarMeasure θ v hv (E ∩ {x | sourceRelativeEnvelope θ u v x = v x}) := by
  have heq := sourceRelativeEnvelope_eq_nativeShiftedRooftopLimit hu hv hne
  have hnη : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (shiftedRooftopLimit (atlasClosedFormToNative θ) v u) := by
    rw [← heq]
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourceRelativeEnvelope_genuine_of_ne_bot hv hne)
  simpa only [sourcePotentialNonPluripolarMeasure, heq] using
    ShiftedRooftopContactProof.diagonalPotentialMeasure_shiftedRooftopLimit_le_contact_of_potential
      ω (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv)
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hnη E

/-- WHOLE original relative-envelope contact inequality of measures. -/
theorem sourceRelativeEnvelope_measure_le (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hne : sourceRelativeEnvelope θ u v ≠ ⊥) :
    sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ u v)
        (sourceRelativeEnvelope_genuine_of_ne_bot hv hne) ≤
      (sourcePotentialNonPluripolarMeasure θ v hv).restrict {x | sourceRelativeEnvelope θ u v x = v x} := by
  apply Measure.le_iff.mpr
  intro E hE
  simpa only [Measure.restrict_apply hE] using sourceRelativeEnvelope_measure_le_apply ω hu hv hne E

/-- The genuine relative-envelope measure gives no mass to noncontact points. -/
theorem sourceRelativeEnvelope_noncontact_null (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hne : sourceRelativeEnvelope θ u v ≠ ⊥) :
    sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ u v)
      (sourceRelativeEnvelope_genuine_of_ne_bot hv hne)
      {x | sourceRelativeEnvelope θ u v x ≠ v x} = 0 := by
  have h := sourceRelativeEnvelope_measure_le_apply ω hu hv hne
    {x | sourceRelativeEnvelope θ u v x ≠ v x}
  have hempty : {x | sourceRelativeEnvelope θ u v x ≠ v x} ∩
      {x | sourceRelativeEnvelope θ u v x = v x} = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun x hx => hx.1 hx.2
  rw [hempty, measure_empty] at h
  exact le_antisymm h zero_le

/-- Actual EVERY-set carried-by equality, after the full noncontact nullity. -/
theorem sourceRelativeEnvelope_measure_carried (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hne : sourceRelativeEnvelope θ u v ≠ ⊥) (E : Set M) :
    sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ u v)
        (sourceRelativeEnvelope_genuine_of_ne_bot hv hne) E =
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ u v)
        (sourceRelativeEnvelope_genuine_of_ne_bot hv hne)
        (E ∩ {x | sourceRelativeEnvelope θ u v x = v x}) := by
  apply le_antisymm ?_ (measure_mono inter_subset_left)
  have hsub : E ⊆ (E ∩ {x | sourceRelativeEnvelope θ u v x = v x}) ∪
      {x | sourceRelativeEnvelope θ u v x ≠ v x} := by
    intro x hx
    by_cases he : sourceRelativeEnvelope θ u v x = v x
    · exact Or.inl ⟨hx, he⟩
    · exact Or.inr he
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans_eq
    (by rw [sourceRelativeEnvelope_noncontact_null ω hu hv hne, add_zero])

/-- The WHOLE printed cor:Pvarphisupport at its literal positive-REAL raw
rooftop supremum; genuineness is produced, rather than supplied as input. -/
theorem sourcePositiveRooftopLimit_contact_measure (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hne : uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ (fun x => u x + (C.1 : EReal)) v) ≠ ⊥) :
    ∃ hη : (ofFixedModel n M).IsThetaPSH θ (uscSup (fun C : {C : ℝ // 0 < C} =>
        thetaRooftop θ (fun x => u x + (C.1 : EReal)) v)),
      sourcePotentialNonPluripolarMeasure θ (uscSup (fun C : {C : ℝ // 0 < C} =>
          thetaRooftop θ (fun x => u x + (C.1 : EReal)) v)) hη ≤
        (sourcePotentialNonPluripolarMeasure θ v hv).restrict
          {x | uscSup (fun C : {C : ℝ // 0 < C} =>
            thetaRooftop θ (fun y => u y + (C.1 : EReal)) v) x = v x} := by
  have heq := sourceRelativeEnvelope_eq_uscSup_positive_rooftop θ u v hv
  have hn : sourceRelativeEnvelope θ u v ≠ ⊥ := by rwa [heq]
  have hη := sourceRelativeEnvelope_genuine_of_ne_bot hv hn
  rw [heq] at hη
  refine ⟨hη, ?_⟩
  simpa only [heq] using sourceRelativeEnvelope_measure_le ω hu hv hn

end SGPT.PSH.VariableComplexAtlas

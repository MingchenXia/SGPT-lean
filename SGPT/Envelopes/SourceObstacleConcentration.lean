import SGPT.Envelopes.SourceRelativeEnvelopeExhaustion
import SGPT.PSH.SourceQuasiContinuity
import SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousEnvelopeContact

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

/-- The existing relative envelope's constant top reference excludes no function. -/
theorem sourceObstacle_topReference {M : Type*} (u : M → EReal) :
    SGPT.PSH.SingularityLE u (fun _ => ⊤) :=
  (singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => by simp⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {f : M → EReal}

/-- ALL ordinary source-QE competitors are exactly those of the existing
relative envelope with unconstrained top reference, without a new operation. -/
theorem sourceObstacle_competitors_iff (u : M → EReal) :
    ((ofFixedModel n M).IsThetaPSH θ u ∧
      SourceQuasiEverywhere (n := n) (fun x => u x ≤ f x) ∧
      SGPT.PSH.SingularityLE u (fun _ => ⊤)) ↔
    ((ofFixedModel n M).IsThetaPSH θ u ∧
      SourceQuasiEverywhere (n := n) (fun x => u x ≤ f x)) :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, sourceObstacle_topReference u⟩⟩

/-- The literal original P_theta(f) is the EXISTING generalized source envelope.
Both directions retain every genuine QE competitor, empty families and poles. -/
theorem sourceObstacleEnvelope_eq_native (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (f : M → EReal) :
    sourceRelativeEnvelope θ (fun _ => ⊤) f =
      rooftopEnvelope (atlasClosedFormToNative θ).val f := by
  apply congrArg uscRegularization
  funext x
  rw [rooftopSupremum_apply]
  apply le_antisymm
  · apply iSup_le
    intro u
    exact le_iSup_of_le u.1 (le_iSup_of_le
      ⟨(isThetaPSH_iff_nativeThetaPotential θ u.1).mp u.2.1,
        (sourceQuasiEverywhere_iff_native _).mp u.2.2.1⟩ le_rfl)
  · apply iSup_le
    intro u
    apply iSup_le
    intro hu
    exact le_iSup (fun a : sourceRelativeEnvelopeCompetitors θ (fun _ => ⊤) f => a.1 x)
      ⟨u, (isThetaPSH_iff_nativeThetaPotential θ u).mpr hu.1,
        (sourceQuasiEverywhere_iff_native _).mpr hu.2, sourceObstacle_topReference u⟩

/-- The ACTUAL source minimal potential of a genuine Kahler background is zero. -/
theorem sourceMinimalEnvelope_kahler_eq_zero (ω : KahlerBackground n M) :
    sourceMinimalEnvelope (nativeClosedFormToAtlas ω.form) = 0 := by
  apply le_antisymm (sourceMinimalEnvelope_le_zero _)
  intro x
  exact le_iSup
    (fun a : {a : M → EReal //
      (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas ω.form) a ∧ a ≤ 0} => a.1 x)
    ⟨0, sourceKahlerZero_thetaPSH ω, le_rfl⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- Exact original all-competitor Kahler capacity, with source coefficients
and actual diagonal measures preserved before the genuine zero-reference readback. -/
theorem sourceThetaCapacity_kahler_eq_native (ω : KahlerBackground n M) (E : Set M) :
    sourceThetaCapacity (nativeClosedFormToAtlas ω.form) E =
      ThetaCapacity.thetaCapacity ω.form (fun _ => 0) E := by
  rw [sourceThetaCapacity_eq_native]
  unfold ThetaCapacity.thetaCapacityV
  rw [← sourceMinimalEnvelope_eq_native, sourceMinimalEnvelope_kahler_eq_zero,
    sourceNativeAtlasForm_roundTrip]
  rfl

omit [BorelSpace M] in
/-- The EXPLICIT chosen original whole-domain Kahler QC convention supplies
native extended-real QC. Its original Borel and finite REAL-continuity clauses
are retained in the hypothesis; no reverse equivalence or capacity-change is claimed. -/
theorem sourceObstacleQuasiContinuous_to_native (ω : KahlerBackground n M)
    (hf : SourceQuasiContinuousOn (nativeClosedFormToAtlas ω.form) ⊤
      (fun x => f x.1)) :
    ActualExtendedObstacleQuasiContinuity.QuasiContinuousERealFor
      (ThetaCapacity.thetaCapacity ω.form (fun _ => 0)) f := by
  intro η hη
  obtain ⟨ε, _hε0, hεpos, hεη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
  obtain ⟨G, hGo, _hGX, hGc, hreal⟩ := hf.2 ε (ENNReal.ofReal_pos.mp hεpos)
  refine ⟨G, hGo, ?_, ?_⟩
  · rw [← sourceThetaCapacity_kahler_eq_native]
    exact hGc.trans_lt hεη
  · have hc := ((realContinuousOff_iff ⊤ (fun x => f x.1) G).mp hreal).2
    have hs : Continuous (fun x : M => (⟨x, mem_univ x⟩ : (⊤ : Opens M))) :=
      continuous_id.subtype_mk (fun x => mem_univ x)
    exact hc.comp hs.continuousOn (fun x hx => hx)

variable [ConnectedSpace M]

/-- Actual two-sided noncollapse alone manufactures the genuine source envelope;
no original obstacle regularity, family bound or output-PSH certificate is supplied. -/
theorem sourceObstacleEnvelope_genuine (ω : KahlerBackground n M)
    (hnb : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊥))
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊤)) :
    (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ (fun _ => ⊤) f) := by
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  rw [sourceObstacleEnvelope_eq_native]
  exact ActualNoncollapsedObstacleEnvelope.isThetaPshPotential_of_ne_infinities
    ω (atlasClosedFormToNative θ) (by rwa [← sourceObstacleEnvelope_eq_native])
    (by rwa [← sourceObstacleEnvelope_eq_native])

/-- The original noncollapsed envelope's finite bound is produced internally. -/
theorem sourceObstacleEnvelope_upper_bound (ω : KahlerBackground n M)
    (hnb : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊥))
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊤)) :
    ∃ C : ℝ, ∀ x, sourceRelativeEnvelope θ (fun _ => ⊤) f x ≤ (C : EReal) :=
  ((isThetaPSH_iff_nativeThetaPotential θ _).mp
    (sourceObstacleEnvelope_genuine ω hnb hnt)).exists_global_upper_bound

/-- The ACTUAL original quasi-everywhere obstacle bound, after genuineness
has been manufactured from exactly the two original noncollapse hypotheses. -/
theorem sourceObstacleEnvelope_le_qe (ω : KahlerBackground n M)
    (hnb : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊥))
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊤)) :
    SourceQuasiEverywhere (n := n)
      (fun x => sourceRelativeEnvelope θ (fun _ => ⊤) f x ≤ f x) := by
  apply (sourceQuasiEverywhere_iff_native _).mpr
  have hP := (isThetaPSH_iff_nativeThetaPotential θ _).mp
    (sourceObstacleEnvelope_genuine ω hnb hnt)
  rw [sourceObstacleEnvelope_eq_native] at hP ⊢
  exact PolydiskPatchBalayageContactQE.rooftopEnvelope_le_quasiEverywhere_of_kahler
    ω (atlasClosedFormToNative θ) hP

/-- WHOLE original arbitrary-obstacle concentration, with its chosen ACTUAL
source Kahler-QC convention and both original noncollapse hypotheses.
Unbounded obstacles, nonbig theta, zero mass and dimension zero are retained. -/
theorem sourceObstacleEnvelope_concentration (ω : KahlerBackground n M)
    (hf : SourceQuasiContinuousOn (nativeClosedFormToAtlas ω.form) ⊤ (fun x => f x.1))
    (hnb : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊥))
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊤)) :
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ (fun _ => ⊤) f),
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ (fun _ => ⊤) f) hP
        {x | sourceRelativeEnvelope θ (fun _ => ⊤) f x < f x} = 0 ∧
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ (fun _ => ⊤) f) hP
        {x | sourceRelativeEnvelope θ (fun _ => ⊤) f x ≠ f x} = 0 := by
  obtain ⟨hP, hstrict, hneq⟩ :=
    ActualQuasiContinuousEnvelopeContact.exists_genuine_envelope_and_contact
      ω (atlasClosedFormToNative θ) (sourceObstacleQuasiContinuous_to_native ω hf)
      (by rwa [← sourceObstacleEnvelope_eq_native])
      (by rwa [← sourceObstacleEnvelope_eq_native])
  refine ⟨sourceObstacleEnvelope_genuine ω hnb hnt, ?_, ?_⟩
  · simpa only [sourceObstacleEnvelope_eq_native, sourcePotentialNonPluripolarMeasure] using hstrict
  · simpa only [sourceObstacleEnvelope_eq_native, sourcePotentialNonPluripolarMeasure] using hneq

/-- The printed strict noncontact nullity, with genuine PSH produced before its measure. -/
theorem sourceObstacleEnvelope_strict_null (ω : KahlerBackground n M)
    (hf : SourceQuasiContinuousOn (nativeClosedFormToAtlas ω.form) ⊤ (fun x => f x.1))
    (hnb : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊥))
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊤)) :
    sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ (fun _ => ⊤) f)
      (sourceObstacleEnvelope_genuine ω hnb hnt)
      {x | sourceRelativeEnvelope θ (fun _ => ⊤) f x < f x} = 0 := by
  obtain ⟨_hP, hstrict, _hneq⟩ := sourceObstacleEnvelope_concentration ω hf hnb hnt
  exact hstrict

/-- The whole actual complement of the contact set is null, rather than only a strict set. -/
theorem sourceObstacleEnvelope_ne_null (ω : KahlerBackground n M)
    (hf : SourceQuasiContinuousOn (nativeClosedFormToAtlas ω.form) ⊤ (fun x => f x.1))
    (hnb : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊥))
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊤)) :
    sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ (fun _ => ⊤) f)
      (sourceObstacleEnvelope_genuine ω hnb hnt)
      {x | sourceRelativeEnvelope θ (fun _ => ⊤) f x ≠ f x} = 0 := by
  obtain ⟨_hP, _hstrict, hneq⟩ := sourceObstacleEnvelope_concentration ω hf hnb hnt
  exact hneq

/-- The actual source measure is carried by the original contact set, for EVERY
set. No topological support containment or unnecessary measurability is claimed. -/
theorem sourceObstacleEnvelope_measure_carried (ω : KahlerBackground n M)
    (hf : SourceQuasiContinuousOn (nativeClosedFormToAtlas ω.form) ⊤ (fun x => f x.1))
    (hnb : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊥))
    (hnt : sourceRelativeEnvelope θ (fun _ => ⊤) f ≠ (fun _ => ⊤)) (E : Set M) :
    sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ (fun _ => ⊤) f)
      (sourceObstacleEnvelope_genuine ω hnb hnt) E =
    sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ (fun _ => ⊤) f)
      (sourceObstacleEnvelope_genuine ω hnb hnt)
      (E ∩ {x | sourceRelativeEnvelope θ (fun _ => ⊤) f x = f x}) := by
  apply le_antisymm ?_ (measure_mono inter_subset_left)
  have hsub : E ⊆ (E ∩ {x | sourceRelativeEnvelope θ (fun _ => ⊤) f x = f x}) ∪
      {x | sourceRelativeEnvelope θ (fun _ => ⊤) f x ≠ f x} := by
    intro x hx
    by_cases he : sourceRelativeEnvelope θ (fun _ => ⊤) f x = f x
    · exact Or.inl ⟨hx, he⟩
    · exact Or.inr he
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans_eq
    (by rw [sourceObstacleEnvelope_ne_null ω hf hnb hnt, add_zero])

end SGPT.PSH.VariableComplexAtlas

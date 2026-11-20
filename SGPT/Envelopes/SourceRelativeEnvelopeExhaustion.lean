import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.PSH.CountablePluripolar
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyShiftedRooftopContinuity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original failure set has actual local source PSH pole witnesses. -/
def SourceQuasiEverywhere (P : M → Prop) : Prop :=
  (ofFixedModel n M).LocallyPluripolar {x | ¬ P x}

/-- Actual source neighborhoods and actual native chart witnesses give the
same quasi-everywhere predicate, without choosing a measure. -/
theorem sourceQuasiEverywhere_iff_native (P : M → Prop) :
    SourceQuasiEverywhere (n := n) P ↔ QuasiEverywhere (n := n) P := by
  constructor
  · intro h e
    exact h.in_chart e
  · intro h
    exact locallyPluripolar_of_in_chart h

/-- The actual zero pole witness for an empty failure set is transported back
to original source neighborhoods by the full dictionary. -/
theorem sourceQuasiEverywhere_of_forall {P : M → Prop} (h : ∀ x, P x) :
    SourceQuasiEverywhere (n := n) P :=
  (sourceQuasiEverywhere_iff_native P).mpr (quasiEverywhere_of_forall h)

/-- Quasi-everywhere may be replaced by everywhere ONLY with a genuine
theta-PSH obstacle; no such assertion is made for arbitrary obstacles. -/
theorem sourceQuasiEverywhere_le_iff
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {a b : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a)
    (hb : (ofFixedModel n M).IsThetaPSH θ b) :
    SourceQuasiEverywhere (n := n) (fun x => a x ≤ b x) ↔ a ≤ b := by
  constructor
  · intro h
    exact ((isThetaPSH_iff_nativeThetaPotential θ a).mp ha).1.le_of_quasiEverywhere_le
      ((isThetaPSH_iff_nativeThetaPotential θ b).mp hb).1
      ((sourceQuasiEverywhere_iff_native _).mp h)
  · exact sourceQuasiEverywhere_of_forall

/-- ALL original generalized relative-envelope competitors, retaining actual
quasi-everywhere comparison for an arbitrary original obstacle. -/
def sourceRelativeEnvelopeCompetitors
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u f : M → EReal) :=
  {a : M → EReal // (ofFixedModel n M).IsThetaPSH θ a ∧
    SourceQuasiEverywhere (n := n) (fun x => a x ≤ f x) ∧ SGPT.PSH.SingularityLE a u}

/-- Literal original generalized envelope, including empty competitor families
and the original neighborhood upper regularization. -/
def sourceRelativeEnvelope (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u f : M → EReal) : M → EReal :=
  uscSup (fun a : sourceRelativeEnvelopeCompetitors θ u f => a.1)

/-- The whole actual original competitor family has a pointwise description
when its obstacle is genuine. -/
theorem sourceRelativeEnvelopeCompetitors_iff
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v a : M → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    ((ofFixedModel n M).IsThetaPSH θ a ∧
      SourceQuasiEverywhere (n := n) (fun x => a x ≤ v x) ∧ SGPT.PSH.SingularityLE a u) ↔
      (ofFixedModel n M).IsThetaPSH θ a ∧ a ≤ v ∧ SGPT.PSH.SingularityLE a u := by
  constructor
  · rintro ⟨ha, hle, hau⟩
    exact ⟨ha, (sourceQuasiEverywhere_le_iff ha hv).mp hle, hau⟩
  · rintro ⟨ha, hle, hau⟩
    exact ⟨ha, sourceQuasiEverywhere_of_forall hle, hau⟩

/-- Both directions reindex ALL original actual competitors before upper
regularization; no rooftop genuineness or nonempty family is assumed. -/
theorem sourceRelativeEnvelope_eq_uscSup_rooftop
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u v : M → EReal)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    sourceRelativeEnvelope θ u v =
      uscSup (fun C : ℝ => thetaRooftop θ (fun x => u x + (C : EReal)) v) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro a
    have ha := (sourceRelativeEnvelopeCompetitors_iff hv).mp a.2
    obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp ha.2.2
    exact (le_thetaRooftop ha.1 hC ha.2.1 x).trans
      (le_iSup (fun C : ℝ => thetaRooftop θ (fun x => u x + (C : EReal)) v x) C)
  · apply iSup_le
    intro C
    apply iSup_le
    intro a
    exact le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ u v => b.1 x)
      ⟨a.1, a.2.1, sourceQuasiEverywhere_of_forall a.2.2.2,
        (singularityLE_iff_exists_real _ _).mpr ⟨C, a.2.2.1⟩⟩

/-- Positive real shifts are genuinely cofinal, even for raw source rooftops
with empty competitor families or extended-real poles. -/
theorem sourceRooftop_realSup_eq_positiveSup
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u v : M → EReal) :
    uscSup (fun C : ℝ => thetaRooftop θ (fun x => u x + (C : EReal)) v) =
      uscSup (fun C : {C : ℝ // 0 < C} =>
        thetaRooftop θ (fun x => u x + (C.1 : EReal)) v) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro C
    let D : {C : ℝ // 0 < C} := ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _)⟩
    apply le_trans _ (le_iSup
      (fun D : {C : ℝ // 0 < C} => thetaRooftop θ (fun x => u x + (D.1 : EReal)) v x) D)
    apply iSup_le
    intro a
    apply le_thetaRooftop a.2.1 _ a.2.2.2 x
    intro y
    exact (a.2.2.1 y).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left C 1)))
  · apply iSup_le
    intro C
    exact le_iSup (fun D : ℝ => thetaRooftop θ (fun x => u x + (D : EReal)) v x) C.1

/-- The first original equality has exactly the printed positive-real index. -/
theorem sourceRelativeEnvelope_eq_uscSup_positive_rooftop
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u v : M → EReal)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    sourceRelativeEnvelope θ u v = uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ (fun x => u x + (C.1 : EReal)) v) :=
  (sourceRelativeEnvelope_eq_uscSup_rooftop θ u v hv).trans
    (sourceRooftop_realSup_eq_positiveSup θ u v)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u v : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Actual full-mass closure manufactures the genuine native rooftop required
by the existing all-minorant dictionary; source symmetry fixes the input order. -/
theorem sourceFullMass_shiftedRooftop_eq_native (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) (C : ℝ) :
    thetaRooftop θ (fun x => u x + (C : EReal)) v =
      RelativeDarvasDistance.rooftop (atlasClosedFormToNative θ) v
        (fun x => u x + (C : EReal)) := by
  have hnu := (sourceRelativeFullMass_iff_native θ φ u hφ).mp hu
  have hnv := (sourceRelativeFullMass_iff_native θ φ v hφ).mp hv
  have hr := RelativePreceqClasses.relativeFullMassPreceq_rooftop ω hnv (hnu.add_const C)
  rw [thetaRooftop_comm]
  exact sourceThetaRooftop_eq_native hv.choose
    ((isThetaPSH_iff_nativeThetaPotential θ _).mpr (hnu.plurisubharmonic.add_const C))
    hr.plurisubharmonic

/-- Whole source full-preceq exhaustion, with the exact original positive-real
index and no normalization, order, bounded model or finite-energy input. -/
theorem sourceFullMass_rooftop_exhaustion (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ (fun x => u x + (C.1 : EReal)) v) = v := by
  rw [← sourceRooftop_realSup_eq_positiveSup, sourceUscSup_eq_native]
  simp_rw [sourceFullMass_shiftedRooftop_eq_native ω hu hv]
  exact SingularModelEnergyShiftedRooftopContinuity.uscRegularization_iSup_rooftop_add_const_eq ω
    ((sourceRelativeFullMass_iff_native θ φ v hφ).mp hv)
    ((sourceRelativeFullMass_iff_native θ φ u hφ).mp hu)

/-- Both equalities in the whole original full-mass relative-envelope
assertion, using its literal original quasi-everywhere competitor definition. -/
theorem sourceRelativeEnvelope_fullMass (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    sourceRelativeEnvelope θ u v = uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ (fun x => u x + (C.1 : EReal)) v) ∧
    uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ (fun x => u x + (C.1 : EReal)) v) = v :=
  ⟨sourceRelativeEnvelope_eq_uscSup_positive_rooftop θ u v hv.choose,
    sourceFullMass_rooftop_exhaustion ω hu hv⟩

end SGPT.PSH.VariableComplexAtlas

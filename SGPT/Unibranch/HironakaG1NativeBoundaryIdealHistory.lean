import SGPT.Unibranch.HironakaG1CanonicalOldBoundarySuccessor
import SGPT.Unibranch.HironakaG1FiniteNativeHistoryComparison

/-!
# Actual full chronological native boundary-ideal histories from E=[]

Every old ideal is the genuine global epsilon-split successor of its
preceding actual ideal; the literal last slot is the actual pulled centre
ideal. Exact full native window readouts are constructed from Fin0 along
the SAME existing actual finite native history, never supplied as a future
compatibility or alignment field.

Blueprint FIRST: `hironaka-g1-native-boundary-ideal-history.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite Classical
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1NativeBoundaryIdealHistory

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  HironakaG1CanonicalStageSuccessor HironakaG1CanonicalStageBoundaryIncidence
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaSmoothCentreRealDomainActualSheafStalk
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (K : ∀ i, Set (w i).ambient)
  (hCover : ∀ i (c : (w i).carrier), c.val ∈ (M i).cosupp →
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ K j ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  (hEmpty : ∀ i, (M i).E = [])
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)

include hEmpty in
private theorem boundaryLength (i : ι) : (currentBoundary w M B s i).length = m := by
  change (geoTransformAlong (M i) (s.T i).2).E.length = m
  rw [length_E_geoTransformAlong, hEmpty i, List.length_nil, zero_add, s.length i]

/-- The genuine entire current boundary is indexed by the literal clock. -/
def chronologicalLabel (i : ι) (j : Fin m) : Fin (currentBoundary w M B s i).length :=
  Fin.cast (boundaryLength w M B hEmpty s i).symm j

/-- Actual original native ideals for EVERY retained chronological label.
The full scalar maps and all whole native Cartier IMAGE readouts are fields. -/
structure BoundaryIdealEntry (j : Fin m) where
  ideal : SheafOfModules.{0} (forgetRing xs.Y.obj.left.toSheafedSpace.sheaf)
  inclusion : ideal ⟶ SheafOfModules.unit _
  mono : Mono inclusion
  readout : ∀ i
    (p : (ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left),
    nativePulledIdealStalkIdeal (xs.map i).hom.left ideal inclusion p =
      actualLabelledBoundaryTraceIdeal (xs.carrier i) (currentBoundary w M B s i)
        (chronologicalLabel w M B hEmpty s i j) p

/-- The whole literal chronological family; no label is filtered out. -/
structure BoundaryIdealState where
  entry : ∀ j : Fin m, BoundaryIdealEntry w M B hEmpty s xs j

/-- The empty original boundary has its genuine Fin0 native ideal-state. -/
def zeroState : BoundaryIdealState w M B hEmpty
    (GStage.zero B.toResolutionInvariant M (mapAdm w)) (XStage.zero w) where
  entry j := j.elim0

variable [Finite ι] (hK : ∀ i, IsCompact (K i))
  (a : Successor w M B hD hClass H hState K hCover s xs hK)

omit [Finite ι] in
private theorem next_old_member (i : ι) (j : Fin m) :
    (currentBoundary w M B (nextStage w M B hD hClass H hState K hCover s) i).get
      (chronologicalLabel w M B hEmpty (nextStage w M B hD hClass H hState K hCover s) i j.castSucc) =
    BlowupStrictSubmanifold.geoStrictTransform
      (nextProjection w M B hD hClass H hState K hCover s i)
      (gcentre B.toResolutionInvariant M K s.T i)
      ((currentBoundary w M B s i).get (chronologicalLabel w M B hEmpty s i j)) := by
  have hj : j.val < (currentBoundary w M B s i).length := by
    rw [boundaryLength w M B hEmpty s i]
    exact j.isLt
  change (((currentBoundary w M B s i).map
    (BlowupStrictSubmanifold.geoStrictTransform
      (nextProjection w M B hD hClass H hState K hCover s i)
      (gcentre B.toResolutionInvariant M K s.T i)) ++
    [(nextProjection w M B hD hClass H hState K hCover s i) ⁻¹'
      gcentre B.toResolutionInvariant M K s.T i]).get ⟨j.val, by
        simpa only [List.length_append, List.length_map, List.length_singleton]
          using Nat.lt_succ_of_lt hj⟩) = _
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left
    (as := (currentBoundary w M B s i).map
      (BlowupStrictSubmanifold.geoStrictTransform
        (nextProjection w M B hD hClass H hState K hCover s i)
        (gcentre B.toResolutionInvariant M K s.T i)))
    (by simpa only [List.length_map] using hj), List.getElem_map]
  rfl

omit [Finite ι] in
private theorem next_born_label (i : ι) :
    chronologicalLabel w M B hEmpty (nextStage w M B hD hClass H hState K hCover s) i (Fin.last m) =
      HironakaG1CanonicalBornBoundaryIdeal.bornLabel
        w M B hD hClass H hState K hCover s i := by
  apply Fin.ext
  change m = (currentBoundary w M B s i).length
  exact (boundaryLength w M B hEmpty s i).symm

/-- Every old slot is its actual global successor ideal, and the literal
last slot is the ACTUAL native pulled centre ideal with its inclusion. -/
def successorState (u : BoundaryIdealState w M B hEmpty s xs) :
    BoundaryIdealState w M B hEmpty
      (nextStage w M B hD hClass H hState K hCover s) a.toXStage := by
  let C := support w M B hD hClass H hState K hCover s xs
  let J := intrinsicReducedCentreIdealModule xs.Y.obj.left C
  let bJ := intrinsicReducedCentreIdealInclusion xs.Y.obj.left C
  let born := nativePulledIdealModule a.p.hom.left J bJ
  let bBorn := nativePulledIdealInclusion a.p.hom.left J bJ
  refine ⟨fun j => ?_⟩
  refine Fin.lastCases ?_ (fun q => ?_) j
  · refine ⟨born, bBorn, inferInstance, ?_⟩
    intro i p
    rw [next_born_label w M B hD hClass H hState K hCover hEmpty s i]
    exact HironakaG1CanonicalBornBoundaryIdeal.window_stalkIdeal_eq_born
      w M B hD hClass H hState K hCover s xs hK a i p
  · let old := HironakaG1CanonicalOldBoundarySuccessor.successorIdealModule
      w M B hD hClass H hState K hCover s xs hK a (u.entry q).ideal (u.entry q).inclusion
    let bOld := HironakaG1CanonicalOldBoundarySuccessor.successorIdealInclusion
      w M B hD hClass H hState K hCover s xs hK a (u.entry q).ideal (u.entry q).inclusion
    refine ⟨old, bOld, ?_, ?_⟩
    · change Mono (HironakaG1NativeStalkIdealSheaf.idealInclusion _)
      infer_instance
    · intro i p
      rw [actualLabelledBoundaryTraceIdeal,
        next_old_member w M B hD hClass H hState K hCover hEmpty s i q]
      exact HironakaG1CanonicalOldBoundarySuccessor.window_stalkIdeal_eq_strictOld
        w M B hD hClass H hState K hCover s xs hK a (u.entry q).ideal (u.entry q).inclusion
        (fun i => chronologicalLabel w M B hEmpty s i q)
        (fun i p => (u.entry q).readout i p) i p

open HironakaG1FiniteNativeHistoryComparison (ambientStage History)

/-- ACTUAL labelled ideal-history construction cases, indexed by their
literal states. There is no future-alignment or comparison field. -/
inductive IdealHistory : (n : ℕ) →
    (ys : XStage w (ambientStage w M B hD hClass H hState K hCover n).T) →
    BoundaryIdealState w M B hEmpty (ambientStage w M B hD hClass H hState K hCover n) ys → Prop
  | zero : IdealHistory 0 (XStage.zero w) (zeroState w M B hEmpty)
  | step {n : ℕ}
      {ys : XStage w (ambientStage w M B hD hClass H hState K hCover n).T}
      {u : BoundaryIdealState w M B hEmpty (ambientStage w M B hD hClass H hState K hCover n) ys}
      (hu : IdealHistory n ys u)
      (b : Successor w M B hD hClass H hState K hCover
        (ambientStage w M B hD hClass H hState K hCover n) ys hK) :
      IdealHistory (n + 1) b.toXStage
        (successorState w M B hD hClass H hState K hCover hEmpty
          (ambientStage w M B hD hClass H hState K hCover n) ys hK b u)

/-- The SAME given actual native history acquires a constructed complete
ideal history by induction from the literal empty original state. -/
theorem exists_idealHistory_of_nativeHistory {n : ℕ}
    {ys : XStage w (ambientStage w M B hD hClass H hState K hCover n).T}
    (hy : History w M B hD hClass H hState K hCover hK n ys) :
    ∃ u, IdealHistory w M B hD hClass H hState K hCover hEmpty hK n ys u := by
  induction hy with
  | zero => exact ⟨zeroState w M B hEmpty, IdealHistory.zero⟩
  | @step n ys hy b ih =>
    obtain ⟨u, hu⟩ := ih
    exact ⟨successorState w M B hD hClass H hState K hCover hEmpty
      (ambientStage w M B hD hClass H hState K hCover n) ys hK b u, IdealHistory.step hu b⟩

/-- Every finite clock has an ACTUAL native geometric history and its
entire labelled global ideal history from ordinary initial data alone. -/
theorem exists_native_boundary_ideal_history (n : ℕ) :
    ∃ ys, ∃ u, IdealHistory w M B hD hClass H hState K hCover hEmpty hK n ys u := by
  obtain ⟨ys, hy⟩ := HironakaG1FiniteNativeHistoryComparison.exists_history
    w M B hD hClass H hState K hCover hK n
  obtain ⟨u, hu⟩ := exists_idealHistory_of_nativeHistory
    w M B hD hClass H hState K hCover hEmpty hK hy
  exact ⟨ys, u, hu⟩

end
end SGPT.Unibranch.HironakaG1NativeBoundaryIdealHistory

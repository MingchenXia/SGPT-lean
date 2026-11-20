import SGPT.Unibranch.HironakaG1NativeBoundaryIdealHistory
import SGPT.Unibranch.HironakaG1CanonicalOldBoundaryNaturality

/-!
# Whole chronological native ideal naturality from the actual empty history

Two actual labelled ideal histories on independent ordinary footprint
choices of the SAME original atlas are compared from zero. CURRENT old
transport is derived by induction, never supplied as future alignment.
All literal old/born slots and the full original unit inclusions remain.
Blueprint FIRST: `hironaka-g1-native-boundary-history-naturality.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite Classical
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1NativeBoundaryHistoryNaturality

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  HironakaG1CanonicalStageSuccessor HironakaG1CanonicalStageBoundaryIncidence
  HironakaG1IndependentFootprintDrivers HironakaG1IndependentNativeHistories
  HironakaG1NativeBoundaryIdealHistory
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealStalk HironakaSingularModuleSheafStalk
  HironakaActualIntrinsicLabelledBoundaryIdeals
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (hEmpty : ∀ i, (M i).E = []) [Finite ι]

/-- Forget only the extra ideal-state fields, preserving the SAME actual
zero/successor native history and all its full native maps. -/
theorem nativeHistory_of_idealHistory (P : FootprintCover w M) {n : ℕ}
    {xs : XStage w (stage w M B hD hClass H hState P n).T}
    {u : BoundaryIdealState w M B hEmpty (stage w M B hD hClass H hState P n) xs}
    (hu : IdealHistory w M B hD hClass H hState P.K P.cover hEmpty P.compact n xs u) :
    NativeHistory w M B hD hClass H hState P n xs := by
  induction hu with
  | zero => exact HironakaG1FiniteNativeHistoryComparison.History.zero
  | step hu b ih => exact HironakaG1FiniteNativeHistoryComparison.History.step ih b

private def entryImage {m : ℕ}
    {s : GStage B.toResolutionInvariant M (mapAdm w) m} {xs : XStage w s.T} {j : Fin m}
    (t : BoundaryIdealEntry w M B hEmpty s xs j) (z : xs.Y.obj.left) :
    Ideal (xs.Y.obj.left.presheaf.stalk z).carrier :=
  LinearMap.range (stalkInclusionLinearMap xs.Y.obj.left.toSheafedSpace.sheaf
    t.ideal t.inclusion z)

section Successor

variable (P Q : FootprintCover w M) (n : ℕ)
  (xs : XStage w (stage w M B hD hClass H hState P n).T)
  (ys : XStage w (stage w M B hD hClass H hState Q n).T)
  (u : BoundaryIdealState w M B hEmpty (stage w M B hD hClass H hState P n) xs)
  (v : BoundaryIdealState w M B hEmpty (stage w M B hD hClass H hState Q n) ys)
  (e : ys.Y ≅ xs.Y) (he : e.hom ≫ xs.q = ys.q)
  (hI : ∀ j (z : ys.Y.obj.left), nativePulledIdealStalkIdeal e.hom.hom.left
    (u.entry j).ideal (u.entry j).inclusion z =
      LinearMap.range (stalkInclusionLinearMap ys.Y.obj.left.toSheafedSpace.sheaf
        (v.entry j).ideal (v.entry j).inclusion z))
  (a : Successor w M B hD hClass H hState P.K P.cover
    (stage w M B hD hClass H hState P n) xs P.compact)
  (b : Successor w M B hD hClass H hState Q.K Q.cover
    (stage w M B hD hClass H hState Q n) ys Q.compact)

local notation "F" => successorIso w M B hD hClass H hState P Q n xs ys e he a b
local notation "uNext" => successorState w M B hD hClass H hState P.K P.cover hEmpty
  (stage w M B hD hClass H hState P n) xs P.compact a u
local notation "vNext" => successorState w M B hD hClass H hState Q.K Q.cover hEmpty
  (stage w M B hD hClass H hState Q n) ys Q.compact b v

include hI in
private theorem successor_entries_map (j : Fin (n + 1)) (z : b.Y.obj.left) :
    nativePulledIdealStalkIdeal ((F).hom.hom.left)
      ((uNext).entry j).ideal ((uNext).entry j).inclusion z =
        LinearMap.range (stalkInclusionLinearMap b.Y.obj.left.toSheafedSpace.sheaf
          ((vNext).entry j).ideal ((vNext).entry j).inclusion z) := by
  change Ideal.map (((F).hom.hom.left).stalkMap z).hom
    (entryImage w M B hEmpty ((uNext).entry j) (((F).hom.hom.left).base z)) =
      entryImage w M B hEmpty ((vNext).entry j) z
  refine Fin.lastCases ?_ (fun q => ?_) j
  · dsimp only [successorState]
    rw [Fin.lastCases_last, Fin.lastCases_last]
    change Ideal.map (((F).hom.hom.left).stalkMap z).hom
      (LinearMap.range (nativePulledIdealStalkInclusion a.p.hom.left
        (intrinsicReducedCentreIdealModule xs.Y.obj.left
          (actualCentre w M B hD hClass H hState P n xs))
        (intrinsicReducedCentreIdealInclusion xs.Y.obj.left
          (actualCentre w M B hD hClass H hState P n xs))
        (((F).hom.hom.left).base z))) =
      LinearMap.range (nativePulledIdealStalkInclusion b.p.hom.left
        (intrinsicReducedCentreIdealModule ys.Y.obj.left
          (actualCentre w M B hD hClass H hState Q n ys))
        (intrinsicReducedCentreIdealInclusion ys.Y.obj.left
          (actualCentre w M B hD hClass H hState Q n ys)) z)
    rw [nativePulledIdealStalkInclusion_range, nativePulledIdealStalkInclusion_range]
    exact HironakaG1CanonicalOldBoundaryNaturality.successor_totalImage_map
      w M B hD hClass H hState P Q n xs ys e he a b _ _ _ _
      (wholeCentreStalkIdeal_eq w M B hD hClass H hState P Q n xs ys e he) z
  · dsimp only [successorState]
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
    dsimp only [entryImage]
    change Ideal.map (((F).hom.hom.left).stalkMap z).hom
      (LinearMap.range (stalkInclusionLinearMap _
        (HironakaG1CanonicalOldBoundarySuccessor.successorIdealModule
          w M B hD hClass H hState P.K P.cover (stage w M B hD hClass H hState P n)
          xs P.compact a (u.entry q).ideal (u.entry q).inclusion)
        (HironakaG1CanonicalOldBoundarySuccessor.successorIdealInclusion
          w M B hD hClass H hState P.K P.cover (stage w M B hD hClass H hState P n)
          xs P.compact a (u.entry q).ideal (u.entry q).inclusion)
        (((F).hom.hom.left).base z))) =
      LinearMap.range (stalkInclusionLinearMap b.Y.obj.left.toSheafedSpace.sheaf
        (HironakaG1CanonicalOldBoundarySuccessor.successorIdealModule
          w M B hD hClass H hState Q.K Q.cover (stage w M B hD hClass H hState Q n)
          ys Q.compact b (v.entry q).ideal (v.entry q).inclusion)
        (HironakaG1CanonicalOldBoundarySuccessor.successorIdealInclusion
          w M B hD hClass H hState Q.K Q.cover (stage w M B hD hClass H hState Q n)
          ys Q.compact b (v.entry q).ideal (v.entry q).inclusion) z)
    rw [HironakaG1CanonicalOldBoundarySuccessor.successorIdeal_stalkRange
      w M B hD hClass H hState P.K P.cover (stage w M B hD hClass H hState P n)
      xs P.compact a (u.entry q).ideal (u.entry q).inclusion
      (fun i => chronologicalLabel w M B hEmpty (stage w M B hD hClass H hState P n) i q)
      (fun i p => (u.entry q).readout i p)]
    rw [HironakaG1CanonicalOldBoundarySuccessor.successorIdeal_stalkRange
      w M B hD hClass H hState Q.K Q.cover (stage w M B hD hClass H hState Q n)
      ys Q.compact b (v.entry q).ideal (v.entry q).inclusion
      (fun i => chronologicalLabel w M B hEmpty (stage w M B hD hClass H hState Q n) i q)
      (fun i p => (v.entry q).readout i p)]
    exact HironakaG1CanonicalOldBoundaryNaturality.successorStalkIdeal_map
      w M B hD hClass H hState P Q n xs ys e he a b
      (u.entry q).ideal (u.entry q).inclusion (v.entry q).ideal (v.entry q).inclusion (hI q) z

end Successor

variable (P Q : FootprintCover w M)

private theorem exists_labelled_comparison {n : ℕ}
    {xs : XStage w (stage w M B hD hClass H hState P n).T}
    {ys : XStage w (stage w M B hD hClass H hState Q n).T}
    {u : BoundaryIdealState w M B hEmpty (stage w M B hD hClass H hState P n) xs}
    {v : BoundaryIdealState w M B hEmpty (stage w M B hD hClass H hState Q n) ys}
    (hu : IdealHistory w M B hD hClass H hState P.K P.cover hEmpty P.compact n xs u)
    (hv : IdealHistory w M B hD hClass H hState Q.K Q.cover hEmpty Q.compact n ys v) :
    ∃ e : ys.Y ≅ xs.Y, e.hom ≫ xs.q = ys.q ∧
      ∀ j (z : ys.Y.obj.left), nativePulledIdealStalkIdeal e.hom.hom.left
        (u.entry j).ideal (u.entry j).inclusion z =
          LinearMap.range (stalkInclusionLinearMap ys.Y.obj.left.toSheafedSpace.sheaf
            (v.entry j).ideal (v.entry j).inclusion z) := by
  induction hu with
  | zero =>
    cases hv
    refine ⟨Iso.refl X, Category.id_comp _, ?_⟩
    intro j
    exact j.elim0
  | @step n xs u hu a ih =>
    cases hv with
    | @step _ ys v hv b =>
      obtain ⟨e, he, hI⟩ := ih hv
      refine ⟨successorIso w M B hD hClass H hState P Q n xs ys e he a b,
        successorIso_original_projection w M B hD hClass H hState P Q n xs ys e he a b, ?_⟩
      exact successor_entries_map w M B hD hClass H hState hEmpty P Q n xs ys u v e he hI a b

variable {n : ℕ}
  {xs : XStage w (stage w M B hD hClass H hState P n).T}
  {ys : XStage w (stage w M B hD hClass H hState Q n).T}
  {u : BoundaryIdealState w M B hEmpty (stage w M B hD hClass H hState P n) xs}
  {v : BoundaryIdealState w M B hEmpty (stage w M B hD hClass H hState Q n) ys}
  (hu : IdealHistory w M B hD hClass H hState P.K P.cover hEmpty P.compact n xs u)
  (hv : IdealHistory w M B hD hClass H hState Q.K Q.cover hEmpty Q.compact n ys v)

local notation "E" => globalHistoryIso w M B hD hClass H hState P Q
  (nativeHistory_of_idealHistory w M B hD hClass H hState hEmpty P hu)
  (nativeHistory_of_idealHistory w M B hD hClass H hState hEmpty Q hv)

/-- ENTIRE chronological labelled ideal transport under the ACTUAL
from-zero independent native history comparison, with no alignment input. -/
theorem labelledIdeal_map (j : Fin n) (z : ys.Y.obj.left) :
    nativePulledIdealStalkIdeal ((E).hom.hom.left)
      (u.entry j).ideal (u.entry j).inclusion z =
        LinearMap.range (stalkInclusionLinearMap ys.Y.obj.left.toSheafedSpace.sheaf
          (v.entry j).ideal (v.entry j).inclusion z) := by
  obtain ⟨e, he, hI⟩ := exists_labelled_comparison w M B hD hClass H hState hEmpty P Q hu hv
  have heq : e.hom = (E).hom := globalHistoryHom_unique w M B hD hClass H hState P Q
    (nativeHistory_of_idealHistory w M B hD hClass H hState hEmpty P hu)
    (nativeHistory_of_idealHistory w M B hD hClass H hState hEmpty Q hv) e.hom he
  rw [← heq]
  exact hI j z

omit [Finite ι] in
private theorem entry_inclusion_injective (j : Fin n) (U : Opens ys.Y.obj.left.toTopCat) :
    Function.Injective ((v.entry j).inclusion.val.app (op U)) := by
  let : Mono (v.entry j).inclusion := (v.entry j).mono
  apply (ModuleCat.mono_iff_injective _).mp
  change Mono ((SheafOfModules.evaluation _ (op U)).map (v.entry j).inclusion)
  infer_instance

/-- UNIQUE full original native module comparison for EVERY literal label,
preserving the SAME original unit inclusion, derived from zero. -/
theorem existsUnique_labelledIdealIso (j : Fin n) :
    ∃! L : nativePulledIdealModule ((E).hom.hom.left)
        (u.entry j).ideal (u.entry j).inclusion ≅ (v.entry j).ideal,
      L.hom ≫ (v.entry j).inclusion = nativePulledIdealInclusion ((E).hom.hom.left)
        (u.entry j).ideal (u.entry j).inclusion := by
  let Pz (z : ys.Y.obj.left) := LinearMap.range
    (stalkInclusionLinearMap ys.Y.obj.left.toSheafedSpace.sheaf
      (v.entry j).ideal (v.entry j).inclusion z)
  let L := nativePulledIdealModule ((E).hom.hom.left) (u.entry j).ideal (u.entry j).inclusion
  let bL := nativePulledIdealInclusion ((E).hom.hom.left) (u.entry j).ideal (u.entry j).inclusion
  have hL (z : ys.Y.obj.left) :
      LinearMap.range (stalkInclusionLinearMap ys.Y.obj.left.toSheafedSpace.sheaf L bL z) = Pz z := by
    change LinearMap.range (nativePulledIdealStalkInclusion ((E).hom.hom.left)
      (u.entry j).ideal (u.entry j).inclusion z) = _
    rw [nativePulledIdealStalkInclusion_range]
    exact labelledIdeal_map w M B hD hClass H hState hEmpty P Q hu hv j z
  obtain ⟨eL, heL, _⟩ := HironakaG1NativeStalkIdealSheaf.existsUnique_idealIso Pz L bL
    (fun _ => Subtype.val_injective) hL
  obtain ⟨eQ, heQ, _⟩ := HironakaG1NativeStalkIdealSheaf.existsUnique_idealIso Pz
    (v.entry j).ideal (v.entry j).inclusion
    (entry_inclusion_injective w M B hD hClass H hState hEmpty Q j) (fun _ => rfl)
  have hQinv : eQ.inv ≫ (v.entry j).inclusion = HironakaG1NativeStalkIdealSheaf.idealInclusion Pz := by
    rw [← heQ, ← Category.assoc, eQ.inv_hom_id, Category.id_comp]
  have hcomm : (eL.trans eQ.symm).hom ≫ (v.entry j).inclusion = bL := by
    change (eL.hom ≫ eQ.inv) ≫ (v.entry j).inclusion = bL
    rw [Category.assoc, hQinv, heL]
  refine ⟨eL.trans eQ.symm, hcomm, ?_⟩
  intro f hf
  let : Mono (v.entry j).inclusion := (v.entry j).mono
  apply Iso.ext
  apply (cancel_mono (v.entry j).inclusion).mp
  exact hf.trans hcomm.symm

end
end SGPT.Unibranch.HironakaG1NativeBoundaryHistoryNaturality

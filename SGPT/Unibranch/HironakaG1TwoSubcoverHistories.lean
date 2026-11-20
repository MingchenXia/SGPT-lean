import SGPT.Unibranch.HironakaG1AtlasPermutation

/-!
# Honest two-sided original-subcover native history independence

An actual sumComm permutation compares the independent reindexed drivers.
Every intermediate native history is constructed from ordinary initial data.
Whole native maps/centres/ideals are compared through the actual union;
no positive-prefix iso or centre packet is assumed. Blueprint FIRST:
`hironaka-g1-two-subcover-histories.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1TwoSubcoverHistories

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG11PresLineState
  HironakaG1CanonicalStageCentreIdeal HironakaG1IndependentFootprintDrivers
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11SingularCentreModification SmoothCentreModification
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

private theorem iso_isOpen {A A' : SourceReducedComplexSpace} (E : A ≅ A') :
    LocallyRingedSpace.IsOpenImmersion E.hom.hom.left := by
  have : IsIso E.hom.hom.left := by
    change IsIso (isoLeft E).hom
    infer_instance
  infer_instance

private theorem nativeLift_eq {A Y X : SourceReducedComplexSpace} {p : Y ⟶ X}
    (hp : IsSingularCentreModification p) (F G : A ⟶ Y)
    (hG : LocallyRingedSpace.IsOpenImmersion G.hom.left) (hFG : F ≫ p = G ≫ p) : F = G := by
  apply morphism_eq_of_pointwise_eq
  have hint : interior (p.hom.left.base ⁻¹' (intrinsicRegularLocus X.obj)ᶜ) = ∅ :=
    hp.interior_preimage_intrinsicSingularLocus
  have h := HironakaG11LiftUniqueness.eq_of_comp_eq_of_isOpenMap
    hp.isIsoOver_intrinsicRegularLocus hint F.hom.left.base.hom.continuous
    G.hom.left.base.hom.continuous hG.base_open.isOpenMap
    (fun z => congrArg (fun t => t.hom.left.base z) hFG)
  exact fun z => congrFun h z

private theorem inv_projection {A B X : SourceReducedComplexSpace}
    (E : A ≅ B) (a : A ⟶ X) (b : B ⟶ X) (h : E.hom ≫ b = a) : E.inv ≫ a = b := by
  rw [← h, ← Category.assoc, E.inv_hom_id, Category.id_comp]

private theorem inv_centre {A B : SourceReducedComplexSpace} (E : A ≅ B)
    (CA : Set A.obj.left) (CB : Set B.obj.left) (h : E.hom.hom.left.base ⁻¹' CB = CA) :
    E.inv.hom.left.base ⁻¹' CA = CB := by
  ext b
  rw [← h]
  change E.hom.hom.left.base (E.inv.hom.left.base b) ∈ CB ↔ b ∈ CB
  have hb := congrArg (fun t => t.hom.left.base b) E.inv_hom_id
  change E.hom.hom.left.base (E.inv.hom.left.base b) = b at hb
  rw [hb]

private theorem comp_centre {A B C : SourceReducedComplexSpace} (E : A ≅ B) (F : B ≅ C)
    (CA : Set A.obj.left) (CB : Set B.obj.left) (CC : Set C.obj.left)
    (hE : E.hom.hom.left.base ⁻¹' CB = CA) (hF : F.hom.hom.left.base ⁻¹' CC = CB) :
    (E ≪≫ F).hom.hom.left.base ⁻¹' CC = CA := by
  change E.hom.hom.left.base ⁻¹' (F.hom.hom.left.base ⁻¹' CC) = CA
  rw [hF, hE]

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {κ ν : Type*} (w : κ ⊕ ν → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))

/-- The ACTUAL swapped original atlas; no identification of index orders is made. -/
abbrev swappedWindows := HironakaG1AtlasPermutation.permutedWindows w (Equiv.sumComm ν κ)

abbrev swappedRecords := HironakaG1AtlasPermutation.permutedRecords w M (Equiv.sumComm ν κ)

/-- Ordinary RIGHT compact footprint coverage, expressed in its actual swapped atlas. -/
abbrev RightFootprints := HironakaG1UnionAtlasReindex.SelectedFootprints (swappedWindows w) (swappedRecords w M)

/-- Literal empty-left, active-right ordinary full union cover. -/
def rightUnionCover (Q : RightFootprints w M) : FootprintCover w M where
  K a := match a with
    | Sum.inl _ => ∅
    | Sum.inr j => Q.K j
  cover a c hc := by
    cases a with
    | inl i =>
      obtain ⟨j, z, hz, hzc⟩ := Q.cover (Sum.inr i) c hc
      exact ⟨Sum.inr j, z, hz, hzc⟩
    | inr i =>
      obtain ⟨j, z, hz, hzc⟩ := Q.cover (Sum.inl i) c hc
      exact ⟨Sum.inr j, z, hz, hzc⟩
  compact a := by
    cases a with
    | inl _ => exact isCompact_empty
    | inr j => exact Q.compact j

/-- PROVED equality of the ordinary covers under the actual sum permutation. -/
theorem swapped_rightUnionCover (Q : RightFootprints w M) :
    HironakaG1AtlasPermutation.permutedCover w M (Equiv.sumComm ν κ) (rightUnionCover w M Q) =
      HironakaG1UnionAtlasReindex.unionCover (swappedWindows w) (swappedRecords w M) Q := by
  have hK : (HironakaG1AtlasPermutation.permutedCover w M (Equiv.sumComm ν κ) (rightUnionCover w M Q)).K =
      (HironakaG1UnionAtlasReindex.unionCover (swappedWindows w) (swappedRecords w M) Q).K := by
    funext i
    cases i <;> rfl
  generalize HironakaG1AtlasPermutation.permutedCover w M (Equiv.sumComm ν κ) (rightUnionCover w M Q) = A at hK ⊢
  generalize HironakaG1UnionAtlasReindex.unionCover (swappedWindows w) (swappedRecords w M) Q = A' at hK ⊢
  cases A
  cases A'
  cases hK
  rfl

variable (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : (κ ⊕ ν) → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (P : HironakaG1UnionAtlasReindex.SelectedFootprints w M) (Q : RightFootprints w M)

local notation "SW" => swappedWindows w
local notation "SM" => swappedRecords w M
local notation "SD" => (fun i => hD ((Equiv.sumComm ν κ) i))
local notation "SC" => HironakaG1AtlasPermutation.permutedClass w M hClass (Equiv.sumComm ν κ)
local notation "SH" => (fun i => H ((Equiv.sumComm ν κ) i))
local notation "SN" => (fun i => hState ((Equiv.sumComm ν κ) i))
local notation "LC" => HironakaG1UnionAtlasReindex.unionCover w M P
local notation "RC" => rightUnionCover w M Q
local notation "QC" => HironakaG1UnionAtlasReindex.unionCover SW SM Q
local notation "PC" => HironakaG1AtlasPermutation.permutedCover w M (Equiv.sumComm ν κ) RC

abbrev leftStage (n : ℕ) := HironakaG1UnionAtlasReindex.selectedStage w M B hD hClass H hState P n
abbrev rightStage (n : ℕ) := HironakaG1UnionAtlasReindex.selectedStage SW SM B SD SC SH SN Q n

abbrev leftCentre (n : ℕ) (xs : XStage (HironakaG1UnionAtlasReindex.selectedWindows w)
    (leftStage w M B hD hClass H hState P n).T) : Set xs.Y.obj.left :=
  HironakaG1UnionNativeHistories.selectedCentre w M B hD hClass H hState P n xs

abbrev rightCentre (n : ℕ) (ys : XStage (HironakaG1UnionAtlasReindex.selectedWindows SW)
    (rightStage w M B hD hClass H hState Q n).T) : Set ys.Y.obj.left :=
  HironakaG1UnionNativeHistories.selectedCentre SW SM B SD SC SH SN Q n ys

variable [Finite κ]

abbrev LeftHistory (n : ℕ) (xs : XStage (HironakaG1UnionAtlasReindex.selectedWindows w)
    (leftStage w M B hD hClass H hState P n).T) : Prop :=
  HironakaG1UnionNativeHistories.SelectedHistory w M B hD hClass H hState P n xs

variable [Finite ν]

abbrev RightHistory (n : ℕ) (ys : XStage (HironakaG1UnionAtlasReindex.selectedWindows SW)
    (rightStage w M B hD hClass H hState Q n).T) : Prop :=
  HironakaG1UnionNativeHistories.SelectedHistory SW SM B SD SC SH SN Q n ys

/-- The TWO selected histories exist from ordinary original data alone. -/
theorem exists_native_histories (n : ℕ) : ∃ xs ys,
    LeftHistory w M B hD hClass H hState P n xs ∧ RightHistory w M B hD hClass H hState Q n ys := by
  obtain ⟨xs, _, hx, _⟩ := HironakaG1UnionNativeHistories.exists_native_histories w M B hD hClass H hState P n
  obtain ⟨ys, _, hy, _⟩ := HironakaG1UnionNativeHistories.exists_native_histories SW SM B SD SC SH SN Q n
  exact ⟨xs, ys, hx, hy⟩

/-- Actual two-sided comparison, produced through independently constructed
union/permuted histories; no positive-prefix comparison packet is supplied. -/
theorem exists_global_history_iso {n : ℕ}
    {xs : XStage (HironakaG1UnionAtlasReindex.selectedWindows w) (leftStage w M B hD hClass H hState P n).T}
    {ys : XStage (HironakaG1UnionAtlasReindex.selectedWindows SW) (rightStage w M B hD hClass H hState Q n).T}
    (hx : LeftHistory w M B hD hClass H hState P n xs)
    (hy : RightHistory w M B hD hClass H hState Q n ys) :
    ∃ E : ys.Y ≅ xs.Y, E.hom ≫ xs.q = ys.q ∧
      E.hom.hom.left.base ⁻¹' leftCentre w M B hD hClass H hState P n xs =
        rightCentre w M B hD hClass H hState Q n ys := by
  obtain ⟨us, hu⟩ := HironakaG1IndependentNativeHistories.exists_native_history w M B hD hClass H hState LC n
  obtain ⟨rs, vs, hr, hv⟩ := HironakaG1AtlasPermutation.exists_native_histories w M B hD hClass H hState
    (Equiv.sumComm ν κ) RC n
  obtain ⟨ds, hd⟩ := HironakaG1IndependentNativeHistories.exists_native_history SW SM B SD SC SH SN QC n
  let L := HironakaG1UnionNativeHistories.globalHistoryIso w M B hD hClass H hState P hx hu
  let D := HironakaG1IndependentNativeHistories.globalHistoryIso w M B hD hClass H hState LC RC hu hv
  let A := HironakaG1AtlasPermutation.globalHistoryIso w M B hD hClass H hState (Equiv.sumComm ν κ) RC hr hv
  let T := HironakaG1IndependentNativeHistories.globalHistoryIso SW SM B SD SC SH SN QC PC hd hr
  let R := HironakaG1UnionNativeHistories.globalHistoryIso SW SM B SD SC SH SN Q hy hd
  have hL : L.hom ≫ xs.q = us.q :=
    HironakaG1UnionNativeHistories.globalHistoryIso_projection w M B hD hClass H hState P hx hu
  have hD' : D.hom ≫ us.q = vs.q :=
    HironakaG1IndependentNativeHistories.globalHistoryIso_projection w M B hD hClass H hState LC RC hu hv
  have hA : A.hom ≫ rs.q = vs.q :=
    HironakaG1AtlasPermutation.globalHistoryIso_projection w M B hD hClass H hState (Equiv.sumComm ν κ) RC hr hv
  have hT : T.hom ≫ ds.q = rs.q :=
    HironakaG1IndependentNativeHistories.globalHistoryIso_projection SW SM B SD SC SH SN QC PC hd hr
  have hR : R.hom ≫ ys.q = ds.q :=
    HironakaG1UnionNativeHistories.globalHistoryIso_projection SW SM B SD SC SH SN Q hy hd
  have hAi := inv_projection A vs.q rs.q hA
  have hTi := inv_projection T rs.q ds.q hT
  have hRi := inv_projection R ds.q ys.q hR
  let G := R.symm ≪≫ T.symm ≪≫ A.symm ≪≫ D ≪≫ L
  refine ⟨G, ?_, ?_⟩
  · simp only [G, Iso.trans_hom, Iso.symm_hom, Category.assoc, hL, hD', hAi, hTi, hRi]
  · have cL := HironakaG1UnionNativeHistories.globalHistoryIso_centre_preimage_eq
      w M B hD hClass H hState P hx hu
    have cD := HironakaG1IndependentNativeHistories.globalHistoryIso_centre_preimage_eq
      w M B hD hClass H hState LC RC hu hv
    have cA := HironakaG1AtlasPermutation.globalHistoryIso_centre_preimage_eq
      w M B hD hClass H hState (Equiv.sumComm ν κ) RC hr hv
    have cT := HironakaG1IndependentNativeHistories.globalHistoryIso_centre_preimage_eq
      SW SM B SD SC SH SN QC PC hd hr
    have cR := HironakaG1UnionNativeHistories.globalHistoryIso_centre_preimage_eq
      SW SM B SD SC SH SN Q hy hd
    have ciA := inv_centre A _ _ cA
    have ciT := inv_centre T _ _ cT
    have ciR := inv_centre R _ _ cR
    have cRT := comp_centre R.symm T.symm _ _ _ ciR ciT
    have cRTA := comp_centre (R.symm ≪≫ T.symm) A.symm _ _ _ cRT ciA
    have cRTAD := comp_centre (R.symm ≪≫ T.symm ≪≫ A.symm) D _ _ _ cRTA cD
    exact comp_centre (R.symm ≪≫ T.symm ≪≫ A.symm ≪≫ D) L _ _ _ cRTAD cL

variable {n : ℕ}
  {xs : XStage (HironakaG1UnionAtlasReindex.selectedWindows w) (leftStage w M B hD hClass H hState P n).T}
  {ys : XStage (HironakaG1UnionAtlasReindex.selectedWindows (swappedWindows w)) (rightStage w M B hD hClass H hState Q n).T}
  (hx : LeftHistory w M B hD hClass H hState P n xs)
  (hy : RightHistory w M B hD hClass H hState Q n ys)

/-- The actual two-sided full native comparison, with its genuine typed maps. -/
def globalHistoryIso : ys.Y ≅ xs.Y :=
  (exists_global_history_iso w M B hD hClass H hState P Q hx hy).choose

theorem globalHistoryIso_projection :
    (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom ≫ xs.q = ys.q :=
  (exists_global_history_iso w M B hD hClass H hState P Q hx hy).choose_spec.1

theorem globalHistoryIso_centre_preimage_eq :
    (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom.hom.left.base ⁻¹'
        leftCentre w M B hD hClass H hState P n xs = rightCentre w M B hD hClass H hState Q n ys :=
  (exists_global_history_iso w M B hD hClass H hState P Q hx hy).choose_spec.2

/-- Entire native over-original uniqueness removes all intermediate history choices. -/
theorem globalHistoryHom_unique (t : ys.Y ⟶ xs.Y) (ht : t ≫ xs.q = ys.q) :
    t = (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom := by
  apply nativeLift_eq xs.isSingularCentreModification _ _
    (iso_isOpen (globalHistoryIso w M B hD hClass H hState P Q hx hy))
  exact ht.trans (globalHistoryIso_projection w M B hD hClass H hState P Q hx hy).symm

/-- Whole original centre ideal image in the ACTUAL native scalar sheaf. -/
theorem globalHistoryIso_wholeCentreSubmodule_eq :
    nativePulledIdealSubmodule (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom.hom.left
        (intrinsicReducedCentreIdealModule xs.Y.obj.left (leftCentre w M B hD hClass H hState P n xs))
        (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (leftCentre w M B hD hClass H hState P n xs)) =
      intrinsicReducedCentreSubmodule ys.Y.obj.left (rightCentre w M B hD hClass H hState Q n ys) := by
  have := iso_isOpen (globalHistoryIso w M B hD hClass H hState P Q hx hy)
  rw [openImmersion_pulled_submodule_eq]
  exact congrArg (intrinsicReducedCentreSubmodule ys.Y.obj.left)
    (globalHistoryIso_centre_preimage_eq w M B hD hClass H hState P Q hx hy)

/-- Entire centre ideal at EVERY actual right native stalk. -/
theorem globalHistoryIso_wholeCentreStalkIdeal_eq (y : ys.Y.obj.left) :
    nativePulledIdealStalkIdeal (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom.hom.left
        (intrinsicReducedCentreIdealModule xs.Y.obj.left (leftCentre w M B hD hClass H hState P n xs))
        (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (leftCentre w M B hD hClass H hState P n xs)) y =
      intrinsicCentreStalkRange ys.Y.obj.left (rightCentre w M B hD hClass H hState Q n ys) y := by
  have := iso_isOpen (globalHistoryIso w M B hD hClass H hState P Q hx hy)
  rw [openImmersion_pulled_stalkIdeal_eq]
  exact congrArg (fun C => intrinsicCentreStalkRange ys.Y.obj.left C y)
    (globalHistoryIso_centre_preimage_eq w M B hD hClass H hState P Q hx hy)

end
end SGPT.Unibranch.HironakaG1TwoSubcoverHistories

import SGPT.Unibranch.HironakaG1UnionAtlasReindex
import SGPT.Unibranch.HironakaG1IndependentNativeHistories

/-!
# Global native histories of a selected original subcover and union extension

The index types differ. Actual selected window isos and the proved selected
GLOBAL centre image cover derive centre/whole ideal transport. Whole UP gives
the actual global successor iso; the final theorem inducts TWO finite native
histories from initial identity, not an all-prefix comparison packet.

Blueprint FIRST: `hironaka-g1-union-native-histories.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1UnionNativeHistories

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG11PresLineState
  HironakaG1CanonicalStageCentreIdeal HironakaG1IndependentFootprintDrivers HironakaG1UnionAtlasReindex
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11SingularCentreModification SmoothCentreModification
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk HironakaG11NativeTowerRepresentation
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
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

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {κ ν : Type*} (w : κ ⊕ ν → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : (κ ⊕ ν) → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (P : SelectedFootprints w M)

local notation "WS" => selectedWindows w
local notation "MS" => selectedRecords w M
local notation "DS" => (fun i => hD (Sum.inl i))
local notation "CS" => selectedClass w M hClass
local notation "HS" => (fun i => H (Sum.inl i))
local notation "NS" => (fun i => hState (Sum.inl i))
local notation "PS" => selectedCover w M P
local notation "PU" => unionCover w M P
local notation "SS" => selectedStage w M B hD hClass H hState P
local notation "SU" => unionStage w M B hD hClass H hState P
local notation "jS" => HironakaG1IndependentNativeHistories.windowMap WS MS B DS CS HS NS PS
local notation "jU" => HironakaG1IndependentNativeHistories.windowMap w M B hD hClass H hState PU

private theorem carrier_comparison (n : ℕ) (i : κ) :
    strictCarrier w M B hD hClass H hState PU n (Sum.inl i) =
      selectedAmbientIso w M B hD hClass H hState P n i ⁻¹' strictCarrier WS MS B DS CS HS NS PS n i := by
  have h := (selectedAmbientIso_isTowerIso w M B hD hClass H hState P n i).strictAlong_eq
    (w (Sum.inl i)).carrier
  change strictCarrier w M B hD hClass H hState PU n (Sum.inl i) =
    selectedAmbientIso w M B hD hClass H hState P n i ⁻¹' strictCarrier WS MS B DS CS HS NS PS n i at h
  exact h

/-- The ACTUAL native quotient-window iso induced by the produced selected prefix lift. -/
def selectedWindowIso (n : ℕ) (i : κ) : nativeWindow w M B hD hClass H hState PU n (Sum.inl i) ≅
    nativeWindow WS MS B DS CS HS NS PS n i := by
  let hC := fun z => Set.ext_iff.mp (carrier_comparison w M B hD hClass H hState P n i) z
  let E := actualSubspaceBiholomorphicIso (selectedAmbientIso w M B hD hClass H hState P n i)
    (strictCarrier w M B hD hClass H hState PU n (Sum.inl i)) (strictCarrier WS MS B DS CS HS NS PS n i) hC
  exact ObjectProperty.isoMk _ (Over.isoMk E
    (actualSubspaceMap_point (selectedAmbientIso w M B hD hClass H hState P n i).contMDiff
      (fun z hz => (hC z).mp hz)))

theorem selectedWindowIso_point (n : ℕ) (i : κ)
    (z : strictCarrier w M B hD hClass H hState PU n (Sum.inl i)) :
    ((selectedWindowIso w M B hD hClass H hState P n i).hom.hom.left.base z).val =
      selectedAmbientIso w M B hD hClass H hState P n i z.val := rfl

theorem selected_nativeProjection_square (n : ℕ) (i : κ) :
    (selectedWindowIso w M B hD hClass H hState P n i).hom ≫ nativeProjection WS MS B DS CS HS NS PS n i =
      nativeProjection w M B hD hClass H hState PU n (Sum.inl i) := by
  apply morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  change ((SS n).T i).2.proj (selectedAmbientIso w M B hD hClass H hState P n i z.val) =
    ((SU n).T (Sum.inl i)).2.proj z.val
  exact ((selectedAmbientIso_isTowerIso w M B hD hClass H hState P n i).proj_comm z.val).symm

theorem selected_nativeCentre_preimage_eq (n : ℕ) (i : κ) :
    (selectedWindowIso w M B hD hClass H hState P n i).hom.hom.left.base ⁻¹'
        nativeCentreTrace WS MS B DS CS HS NS PS n i =
      nativeCentreTrace w M B hD hClass H hState PU n (Sum.inl i) := by
  ext z
  exact Set.ext_iff.mp (selected_centre_preimage_eq w M B hD hClass H hState P n i) z.val

/-- Actual selected current native window maps, reusing the full original normalizations. -/
abbrev selected_windowMap (n : ℕ) (xs : XStage WS (SS n).T) (i : κ) := jS n xs i

/-- Only actual SELECTED union windows are normalized; no whole-stage cover is assumed. -/
abbrev union_windowMap (n : ℕ) (ys : XStage w (SU n).T) (i : κ) := jU n ys (Sum.inl i)

abbrev selectedCentre (n : ℕ) (xs : XStage WS (SS n).T) : Set xs.Y.obj.left :=
  HironakaG1IndependentNativeHistories.actualCentre WS MS B DS CS HS NS PS n xs

abbrev unionCentre (n : ℕ) (ys : XStage w (SU n).T) : Set ys.Y.obj.left :=
  HironakaG1IndependentNativeHistories.actualCentre w M B hD hClass H hState PU n ys

/-- The selected-centre image cover is DERIVED for the entire actual union centre. -/
theorem union_centre_mem_iff_selected (n : ℕ) (ys : XStage w (SU n).T) (x : ys.Y.obj.left) :
    x ∈ unionCentre w M B hD hClass H hState P n ys ↔
      ∃ i : κ, ∃ z ∈ nativeCentreTrace w M B hD hClass H hState PU n (Sum.inl i),
        (jU n ys (Sum.inl i)).hom.left.base z = x := by
  constructor
  · intro hx
    change x ∈ HironakaG1CanonicalStageCentreIdeal.support w M B hD hClass H hState (unionCover w M P).K (unionCover w M P).cover (SU n) ys at hx
    rw [selected_centre_support_eq w M B hD hClass H hState P n ys] at hx
    obtain ⟨i, c, hc, hcx⟩ := mem_iUnion.mp hx
    let E := HironakaG1IndependentNativeHistories.windowModelIso w M B hD hClass H hState PU n ys (Sum.inl i)
    obtain ⟨z, hzc⟩ := (isoHomeomorph E).surjective c
    have hv : z.val = c.val :=
      (HironakaG1IndependentNativeHistories.windowModelIso_point w M B hD hClass H hState PU n ys
        (Sum.inl i) z).symm.trans (congrArg Subtype.val hzc)
    refine ⟨i, z, ?_, ?_⟩
    · change z.val ∈ gcentre B.toResolutionInvariant M (unionCover w M P).K (SU n).T (Sum.inl i)
      exact hv.symm ▸ hc
    · exact (congrArg (fun c => (ys.map (Sum.inl i)).hom.left.base c) hzc).trans hcx
  · rintro ⟨i, z, hz, hzx⟩
    exact (HironakaG1IndependentNativeHistories.actualCentre_mem_iff w M B hD hClass H hState PU n ys x).mpr
      ⟨Sum.inl i, z, hz, hzx⟩

section StageComparison

variable (n : ℕ)
  (xs : XStage (selectedWindows w) (selectedStage w M B hD hClass H hState P n).T)
  (ys : XStage w (unionStage w M B hD hClass H hState P n).T)
  (e : ys.Y ≅ xs.Y) (he : e.hom ≫ xs.q = ys.q)

include he in
/-- A preceding global iso is an induction field ONLY; the full selected
current-window agreement is derived on the same actual union window. -/
theorem current_window_square (i : κ) :
    jU n ys (Sum.inl i) ≫ e.hom = (selectedWindowIso w M B hD hClass H hState P n i).hom ≫ jS n xs i := by
  let E := selectedWindowIso w M B hD hClass H hState P n i
  have := iso_isOpen E
  have := HironakaG1IndependentNativeHistories.windowMap_isOpen WS MS B DS CS HS NS PS n xs i
  have hG : LocallyRingedSpace.IsOpenImmersion (E.hom ≫ jS n xs i).hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (E.hom.hom.left ≫ (jS n xs i).hom.left)
    infer_instance
  apply nativeLift_eq xs.isSingularCentreModification _ _ hG
  calc
    (jU n ys (Sum.inl i) ≫ e.hom) ≫ xs.q = jU n ys (Sum.inl i) ≫ ys.q := by rw [Category.assoc, he]
    _ = nativeProjection w M B hD hClass H hState PU n (Sum.inl i) ≫
        EmbeddedBlowupOverlap.chartMorphism (w (Sum.inl i)).toLocalEmbedding :=
      HironakaG1IndependentNativeHistories.windowMap_original_square w M B hD hClass H hState PU n ys (Sum.inl i)
    _ = E.hom ≫ (nativeProjection WS MS B DS CS HS NS PS n i ≫
        EmbeddedBlowupOverlap.chartMorphism (WS i).toLocalEmbedding) := by
      rw [← Category.assoc, selected_nativeProjection_square]
    _ = (E.hom ≫ jS n xs i) ≫ xs.q := by
      simpa only [Category.assoc] using (congrArg (fun t => E.hom ≫ t)
        (HironakaG1IndependentNativeHistories.windowMap_original_square WS MS B DS CS HS NS PS n xs i)).symm

include he in
theorem global_centre_preimage_eq :
    e.hom.hom.left.base ⁻¹' selectedCentre w M B hD hClass H hState P n xs =
      unionCentre w M B hD hClass H hState P n ys := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, zS, hzS, hSx⟩ :=
      (HironakaG1IndependentNativeHistories.actualCentre_mem_iff WS MS B DS CS HS NS PS n xs
        (e.hom.hom.left.base x)).mp hx
    let E := selectedWindowIso w M B hD hClass H hState P n i
    obtain ⟨zU, hU⟩ := (isoHomeomorph E).surjective zS
    have hzU : zU ∈ nativeCentreTrace w M B hD hClass H hState PU n (Sum.inl i) := by
      apply (Set.ext_iff.mp (selected_nativeCentre_preimage_eq w M B hD hClass H hState P n i) zU).mp
      change E.hom.hom.left.base zU ∈ nativeCentreTrace WS MS B DS CS HS NS PS n i
      exact hU.symm ▸ hzS
    apply (union_centre_mem_iff_selected w M B hD hClass H hState P n ys x).mpr
    refine ⟨i, zU, hzU, ?_⟩
    apply (isoHomeomorph e).injective
    exact (congrArg (fun t => t.hom.left.base zU)
      (current_window_square w M B hD hClass H hState P n xs ys e he i)).trans
      ((congrArg (fun z => (jS n xs i).hom.left.base z) hU).trans hSx)
  · intro hx
    obtain ⟨i, zU, hzU, hUx⟩ := (union_centre_mem_iff_selected w M B hD hClass H hState P n ys x).mp hx
    apply (HironakaG1IndependentNativeHistories.actualCentre_mem_iff WS MS B DS CS HS NS PS n xs
      (e.hom.hom.left.base x)).mpr
    refine ⟨i, (selectedWindowIso w M B hD hClass H hState P n i).hom.hom.left.base zU, ?_, ?_⟩
    · exact (Set.ext_iff.mp (selected_nativeCentre_preimage_eq w M B hD hClass H hState P n i) zU).mpr hzU
    · exact (congrArg (fun t => t.hom.left.base zU)
        (current_window_square w M B hD hClass H hState P n xs ys e he i)).symm.trans
          (congrArg e.hom.hom.left.base hUx)

local notation "CSEL" => selectedCentre w M B hD hClass H hState P n xs
local notation "CUNION" => unionCentre w M B hD hClass H hState P n ys

include he in
theorem wholeCentreSubmodule_eq : nativePulledIdealSubmodule e.hom.hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left CSEL)
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left CSEL) =
    intrinsicReducedCentreSubmodule ys.Y.obj.left CUNION := by
  have := iso_isOpen e
  rw [openImmersion_pulled_submodule_eq]
  exact congrArg (intrinsicReducedCentreSubmodule ys.Y.obj.left)
    (global_centre_preimage_eq w M B hD hClass H hState P n xs ys e he)

include he in
theorem wholeCentreStalkIdeal_eq (y : ys.Y.obj.left) : nativePulledIdealStalkIdeal e.hom.hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left CSEL)
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left CSEL) y =
    intrinsicCentreStalkRange ys.Y.obj.left CUNION y := by
  have := iso_isOpen e
  rw [openImmersion_pulled_stalkIdeal_eq]
  exact congrArg (fun C => intrinsicCentreStalkRange ys.Y.obj.left C y)
    (global_centre_preimage_eq w M B hD hClass H hState P n xs ys e he)

variable [Finite κ]
  (a : HironakaG1CanonicalStageSuccessor.Successor (selectedWindows w) (selectedRecords w M) B
    (fun i => hD (Sum.inl i)) (selectedClass w M hClass) (fun i => H (Sum.inl i))
    (fun i => hState (Sum.inl i)) (selectedCover w M P).K (selectedCover w M P).cover
    (selectedStage w M B hD hClass H hState P n) xs (selectedCover w M P).compact)

include he in
private theorem other_isIdealBlowup : IsIdealBlowup (a.p ≫ e.inv)
    (intrinsicReducedCentreIdealModule ys.Y.obj.left CUNION)
    (intrinsicReducedCentreIdealInclusion ys.Y.obj.left CUNION) := by
  have h := isIdealBlowup_comp_baseIso CSEL a.isIdealBlowup e
  rw [global_centre_preimage_eq w M B hD hClass H hState P n xs ys e he] at h
  exact h

variable [Finite ν]
  (b : HironakaG1CanonicalStageSuccessor.Successor w M B hD hClass H hState
    (unionCover w M P).K (unionCover w M P).cover (unionStage w M B hD hClass H hState P n) ys
    (unionCover w M P).compact)

include he in
private theorem successor_exists : ∃ E : b.Y ≅ a.Y,
    E.hom ≫ (a.p ≫ e.inv) = b.p ∧ ∀ t : b.Y ⟶ a.Y, t ≫ (a.p ≫ e.inv) = b.p → t = E.hom :=
  RIsoAModification.isIdealBlowup_exists_unique_iso b.isIdealBlowup
    (other_isIdealBlowup w M B hD hClass H hState P n xs ys e he a)

/-- The actual GLOBAL selected-subcover/union successor comparison. -/
def successorIso : b.Y ≅ a.Y :=
  (successor_exists w M B hD hClass H hState P n xs ys e he a b).choose

theorem successorIso_projection :
    (successorIso w M B hD hClass H hState P n xs ys e he a b).hom ≫ a.p = b.p ≫ e.hom := by
  have h := congrArg (fun t => t ≫ e.hom)
    (successor_exists w M B hD hClass H hState P n xs ys e he a b).choose_spec.1
  simpa only [successorIso, Category.assoc, e.inv_hom_id, Category.comp_id] using h

theorem successorIso_original_projection :
    (successorIso w M B hD hClass H hState P n xs ys e he a b).hom ≫ a.toXStage.q = b.toXStage.q := by
  change _ ≫ (a.p ≫ xs.q) = b.p ≫ ys.q
  rw [← Category.assoc, successorIso_projection, Category.assoc, he]

end StageComparison

section Histories

variable [Finite κ]

/-- The existing ACTUAL finite native histories on the selected original atlas. -/
abbrev SelectedHistory (n : ℕ) (xs : XStage WS (SS n).T) : Prop :=
  HironakaG1IndependentNativeHistories.NativeHistory WS MS B DS CS HS NS PS n xs

variable [Finite ν]

/-- The existing ACTUAL finite native histories on the full inactive union extension. -/
abbrev UnionHistory (n : ℕ) (ys : XStage w (SU n).T) : Prop :=
  HironakaG1IndependentNativeHistories.NativeHistory w M B hD hClass H hState PU n ys

/-- Both genuine native constructions exist from the ordinary INITIAL data alone. -/
theorem exists_native_histories (n : ℕ) : ∃ xs ys,
    SelectedHistory w M B hD hClass H hState P n xs ∧ UnionHistory w M B hD hClass H hState P n ys := by
  obtain ⟨xs, hx⟩ := HironakaG1IndependentNativeHistories.exists_native_history WS MS B DS CS HS NS PS n
  obtain ⟨ys, hy⟩ := HironakaG1IndependentNativeHistories.exists_native_history w M B hD hClass H hState PU n
  exact ⟨xs, ys, hx, hy⟩

/-- Genuine induction of TWO actual finite histories with DIFFERENT index types;
the global comparison is produced from original identity, not an input packet. -/
theorem exists_global_history_iso {n : ℕ} {xs : XStage WS (SS n).T} {ys : XStage w (SU n).T}
    (hx : SelectedHistory w M B hD hClass H hState P n xs)
    (hy : UnionHistory w M B hD hClass H hState P n ys) :
    ∃ E : ys.Y ≅ xs.Y, E.hom ≫ xs.q = ys.q := by
  induction hx with
  | zero =>
    cases hy
    exact ⟨Iso.refl X, Category.id_comp _⟩
  | @step n xs hx a ih =>
    cases hy with
    | @step _ ys hy b =>
      obtain ⟨e, he⟩ := ih hy
      exact ⟨successorIso w M B hD hClass H hState P n xs ys e he a b,
        successorIso_original_projection w M B hD hClass H hState P n xs ys e he a b⟩

variable {n : ℕ}
  {xs : XStage (selectedWindows w) (selectedStage w M B hD hClass H hState P n).T}
  {ys : XStage w (unionStage w M B hD hClass H hState P n).T}
  (hx : SelectedHistory w M B hD hClass H hState P n xs)
  (hy : UnionHistory w M B hD hClass H hState P n ys)

/-- The actual full GLOBAL native isomorphism produced by that finite induction. -/
def globalHistoryIso : ys.Y ≅ xs.Y :=
  (exists_global_history_iso w M B hD hClass H hState P hx hy).choose

theorem globalHistoryIso_projection :
    (globalHistoryIso w M B hD hClass H hState P hx hy).hom ≫ xs.q = ys.q :=
  (exists_global_history_iso w M B hD hClass H hState P hx hy).choose_spec

/-- Full native over-original uniqueness, with no selected whole-stage cover assumption. -/
theorem globalHistoryHom_unique (t : ys.Y ⟶ xs.Y) (ht : t ≫ xs.q = ys.q) :
    t = (globalHistoryIso w M B hD hClass H hState P hx hy).hom := by
  apply nativeLift_eq xs.isSingularCentreModification _ _
    (iso_isOpen (globalHistoryIso w M B hD hClass H hState P hx hy))
  exact ht.trans (globalHistoryIso_projection w M B hD hClass H hState P hx hy).symm

theorem globalHistoryIso_window_square (i : κ) :
    jU n ys (Sum.inl i) ≫ (globalHistoryIso w M B hD hClass H hState P hx hy).hom =
      (selectedWindowIso w M B hD hClass H hState P n i).hom ≫ jS n xs i :=
  current_window_square w M B hD hClass H hState P n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState P hx hy) i

/-- Actual GLOBAL centre equality at the from-zero produced comparison. -/
theorem globalHistoryIso_centre_preimage_eq :
    (globalHistoryIso w M B hD hClass H hState P hx hy).hom.hom.left.base ⁻¹'
        selectedCentre w M B hD hClass H hState P n xs = unionCentre w M B hD hClass H hState P n ys :=
  global_centre_preimage_eq w M B hD hClass H hState P n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState P hx hy)

/-- ENTIRE global centre ideal transport in the actual original native scalars. -/
theorem globalHistoryIso_wholeCentreSubmodule_eq :
    nativePulledIdealSubmodule (globalHistoryIso w M B hD hClass H hState P hx hy).hom.hom.left
        (intrinsicReducedCentreIdealModule xs.Y.obj.left (selectedCentre w M B hD hClass H hState P n xs))
        (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (selectedCentre w M B hD hClass H hState P n xs)) =
      intrinsicReducedCentreSubmodule ys.Y.obj.left (unionCentre w M B hD hClass H hState P n ys) :=
  wholeCentreSubmodule_eq w M B hD hClass H hState P n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState P hx hy)

end Histories

end
end SGPT.Unibranch.HironakaG1UnionNativeHistories

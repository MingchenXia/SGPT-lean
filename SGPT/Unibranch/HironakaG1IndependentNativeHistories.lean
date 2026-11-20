import SGPT.Unibranch.HironakaG1IndependentFootprintDrivers
import SGPT.Unibranch.HironakaG1CanonicalSuccessorCover

/-!
# Actual global native comparisons of independent footprint histories

The previous native iso is only an INDUCTION field. The final finite-history
comparison starts at the actual initial identity. Current window maps, actual
centre image unions and whole ideals are derived, then native UP constructs
each global successor iso. No full XStage window cover is assumed.

Blueprint FIRST: `hironaka-g1-independent-native-histories.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1IndependentNativeHistories

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
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk HironakaG11NativeTowerRepresentation
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

private def equalModelIso {n : ℕ} {V : CMfd.{0} n} {A A' : Set V}
    (hA : IsComplexAnalyticSubset (n := n) A) (hA' : IsComplexAnalyticSubset (n := n) A')
    (h : A = A') : ofClosedAnalytic A hA ≅ ofClosedAnalytic A' hA' :=
  eqToIso (by cases h; rfl)

private theorem equalModelIso_point {n : ℕ} {V : CMfd.{0} n} {A A' : Set V}
    (hA : IsComplexAnalyticSubset (n := n) A) (hA' : IsComplexAnalyticSubset (n := n) A')
    (h : A = A') (z : A) : ((equalModelIso hA hA' h).hom.hom.left.base z).val = z.val := by
  cases h
  rfl

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
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))

/-- Literal quotient-model comparison, retaining the SAME actual ambient points. -/
def windowModelIso (P : FootprintCover w M) (n : ℕ)
    (xs : XStage w (stage w M B hD hClass H hState P n).T) (i : ι) :
    nativeWindow w M B hD hClass H hState P n i ≅ ofClosedAnalytic (xs.carrier i) (xs.analytic i) :=
  equalModelIso (strictCarrier_analytic w M B hD hClass H hState P n i)
    (xs.analytic i) (xs.carrier_eq i).symm

theorem windowModelIso_point (P : FootprintCover w M) (n : ℕ)
    (xs : XStage w (stage w M B hD hClass H hState P n).T) (i : ι)
    (z : strictCarrier w M B hD hClass H hState P n i) :
    ((windowModelIso w M B hD hClass H hState P n xs i).hom.hom.left.base z).val = z.val :=
  equalModelIso_point _ _ _ z

/-- The actual original current window map, with its entire original scalar action. -/
def windowMap (P : FootprintCover w M) (n : ℕ)
    (xs : XStage w (stage w M B hD hClass H hState P n).T) (i : ι) :
    nativeWindow w M B hD hClass H hState P n i ⟶ xs.Y :=
  (windowModelIso w M B hD hClass H hState P n xs i).hom ≫ xs.map i

theorem windowMap_isOpen (P : FootprintCover w M) (n : ℕ)
    (xs : XStage w (stage w M B hD hClass H hState P n).T) (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (windowMap w M B hD hClass H hState P n xs i).hom.left := by
  have := iso_isOpen (windowModelIso w M B hD hClass H hState P n xs i)
  have : LocallyRingedSpace.IsOpenImmersion (xs.map i).hom.left := xs.isOpenImmersion i
  change LocallyRingedSpace.IsOpenImmersion
    ((windowModelIso w M B hD hClass H hState P n xs i).hom.hom.left ≫ (xs.map i).hom.left)
  infer_instance

theorem windowMap_original_square (P : FootprintCover w M) (n : ℕ)
    (xs : XStage w (stage w M B hD hClass H hState P n).T) (i : ι) :
    windowMap w M B hD hClass H hState P n xs i ≫ xs.q =
      nativeProjection w M B hD hClass H hState P n i ≫
        EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding := by
  apply morphism_eq_of_pointwise_eq
  intro z
  let E := windowModelIso w M B hD hClass H hState P n xs i
  change xs.q.hom.left.base ((xs.map i).hom.left.base (E.hom.hom.left.base z)) = _
  rw [xs.square i (E.hom.hom.left.base z) (xs.proj_mem i (E.hom.hom.left.base z))]
  apply congrArg (w i).toLocalEmbedding.toPoint
  apply Subtype.ext
  change ((stage w M B hD hClass H hState P n).T i).2.proj (E.hom.hom.left.base z).val =
    ((stage w M B hD hClass H hState P n).T i).2.proj z.val
  exact congrArg ((stage w M B hD hClass H hState P n).T i).2.proj
    (windowModelIso_point w M B hD hClass H hState P n xs i z)

/-- The SAME internally constructed actual global centre of this actual stage. -/
abbrev actualCentre (P : FootprintCover w M) (n : ℕ)
    (xs : XStage w (stage w M B hD hClass H hState P n).T) : Set xs.Y.obj.left :=
  HironakaG1CanonicalStageCentreIdeal.support w M B hD hClass H hState P.K P.cover
    (stage w M B hD hClass H hState P n) xs

/-- The global centre is exactly its ACTUAL native centre-image union; no
full stage-cover assertion or alternative centre is introduced. -/
theorem actualCentre_mem_iff (P : FootprintCover w M) (n : ℕ)
    (xs : XStage w (stage w M B hD hClass H hState P n).T) (x : xs.Y.obj.left) :
    x ∈ actualCentre w M B hD hClass H hState P n xs ↔
      ∃ i, ∃ z ∈ nativeCentreTrace w M B hD hClass H hState P n i,
        (windowMap w M B hD hClass H hState P n xs i).hom.left.base z = x := by
  let F := HironakaG1CanonicalStageCentreIdeal.localCentres w M B hD hClass H hState P.K P.cover
    (stage w M B hD hClass H hState P n) xs
  constructor
  · intro hx
    obtain ⟨i, c, hc, hcx⟩ := F.mem_support.mp hx
    let E := windowModelIso w M B hD hClass H hState P n xs i
    obtain ⟨z, hzc⟩ := (isoHomeomorph E).surjective c
    have hv : z.val = c.val :=
      (windowModelIso_point w M B hD hClass H hState P n xs i z).symm.trans
        (congrArg Subtype.val hzc)
    refine ⟨i, z, ?_, ?_⟩
    · change z.val ∈ gcentre B.toResolutionInvariant M P.K (stage w M B hD hClass H hState P n).T i
      exact hv.symm ▸ hc
    · exact (congrArg (fun c => (xs.map i).hom.left.base c) hzc).trans hcx
  · rintro ⟨i, z, hz, hzx⟩
    refine F.mem_support.mpr ⟨i, (windowModelIso w M B hD hClass H hState P n xs i).hom.hom.left.base z,
      ?_, hzx⟩
    change ((windowModelIso w M B hD hClass H hState P n xs i).hom.hom.left.base z).val ∈
      gcentre B.toResolutionInvariant M P.K (stage w M B hD hClass H hState P n).T i
    exact (windowModelIso_point w M B hD hClass H hState P n xs i z).symm ▸ hz

section StageComparison

variable (P Q : FootprintCover w M) (n : ℕ)
  (xs : XStage w (stage w M B hD hClass H hState P n).T)
  (ys : XStage w (stage w M B hD hClass H hState Q n).T)
  (e : ys.Y ≅ xs.Y) (he : e.hom ≫ xs.q = ys.q)

include he in
/-- The previous global iso is an induction field only. The full current
window square is DERIVED from actual maps on the SAME current Q window. -/
theorem current_window_square (i : ι) :
    windowMap w M B hD hClass H hState Q n ys i ≫ e.hom =
      (nativeWindowIso w M B hD hClass H hState P Q n i).hom ≫
        windowMap w M B hD hClass H hState P n xs i := by
  let E := nativeWindowIso w M B hD hClass H hState P Q n i
  have := iso_isOpen E
  have := windowMap_isOpen w M B hD hClass H hState P n xs i
  have hG : LocallyRingedSpace.IsOpenImmersion
      (E.hom ≫ windowMap w M B hD hClass H hState P n xs i).hom.left := by
    change LocallyRingedSpace.IsOpenImmersion
      (E.hom.hom.left ≫ (windowMap w M B hD hClass H hState P n xs i).hom.left)
    infer_instance
  apply nativeLift_eq xs.isSingularCentreModification _ _ hG
  calc
    (windowMap w M B hD hClass H hState Q n ys i ≫ e.hom) ≫ xs.q =
        windowMap w M B hD hClass H hState Q n ys i ≫ ys.q := by rw [Category.assoc, he]
    _ = nativeProjection w M B hD hClass H hState Q n i ≫
        EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding :=
      windowMap_original_square w M B hD hClass H hState Q n ys i
    _ = E.hom ≫ (nativeProjection w M B hD hClass H hState P n i ≫
        EmbeddedBlowupOverlap.chartMorphism (w i).toLocalEmbedding) := by
      rw [← Category.assoc, nativeProjection_square]
    _ = (E.hom ≫ windowMap w M B hD hClass H hState P n xs i) ≫ xs.q := by
      simpa only [Category.assoc] using (congrArg (fun t => E.hom ≫ t)
        (windowMap_original_square w M B hD hClass H hState P n xs i)).symm

include he in
theorem centre_preimage_eq : e.hom.hom.left.base ⁻¹' actualCentre w M B hD hClass H hState P n xs =
    actualCentre w M B hD hClass H hState Q n ys := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, zP, hzP, hPx⟩ :=
      (actualCentre_mem_iff w M B hD hClass H hState P n xs (e.hom.hom.left.base x)).mp hx
    let E := nativeWindowIso w M B hD hClass H hState P Q n i
    obtain ⟨zQ, hQ⟩ := (isoHomeomorph E).surjective zP
    have hzQ : zQ ∈ nativeCentreTrace w M B hD hClass H hState Q n i := by
      apply (Set.ext_iff.mp (nativeCentre_preimage_eq w M B hD hClass H hState P Q n i) zQ).mp
      change E.hom.hom.left.base zQ ∈ nativeCentreTrace w M B hD hClass H hState P n i
      exact hQ.symm ▸ hzP
    apply (actualCentre_mem_iff w M B hD hClass H hState Q n ys x).mpr
    refine ⟨i, zQ, hzQ, ?_⟩
    apply (isoHomeomorph e).injective
    exact (congrArg (fun t => t.hom.left.base zQ)
      (current_window_square w M B hD hClass H hState P Q n xs ys e he i)).trans
      ((congrArg (fun z => (windowMap w M B hD hClass H hState P n xs i).hom.left.base z) hQ).trans hPx)
  · intro hx
    obtain ⟨i, zQ, hzQ, hQx⟩ := (actualCentre_mem_iff w M B hD hClass H hState Q n ys x).mp hx
    apply (actualCentre_mem_iff w M B hD hClass H hState P n xs (e.hom.hom.left.base x)).mpr
    refine ⟨i, (nativeWindowIso w M B hD hClass H hState P Q n i).hom.hom.left.base zQ, ?_, ?_⟩
    · exact (Set.ext_iff.mp (nativeCentre_preimage_eq w M B hD hClass H hState P Q n i) zQ).mpr hzQ
    · exact (congrArg (fun t => t.hom.left.base zQ)
        (current_window_square w M B hD hClass H hState P Q n xs ys e he i)).symm.trans
          (congrArg e.hom.hom.left.base hQx)

local notation "CP" => actualCentre w M B hD hClass H hState P n xs
local notation "CQ" => actualCentre w M B hD hClass H hState Q n ys

include he in
theorem wholeCentreSubmodule_eq : nativePulledIdealSubmodule e.hom.hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left CP)
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left CP) =
    intrinsicReducedCentreSubmodule ys.Y.obj.left CQ := by
  have := iso_isOpen e
  rw [openImmersion_pulled_submodule_eq]
  exact congrArg (intrinsicReducedCentreSubmodule ys.Y.obj.left)
    (centre_preimage_eq w M B hD hClass H hState P Q n xs ys e he)

include he in
theorem wholeCentreStalkIdeal_eq (y : ys.Y.obj.left) : nativePulledIdealStalkIdeal e.hom.hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left CP)
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left CP) y =
    intrinsicCentreStalkRange ys.Y.obj.left CQ y := by
  have := iso_isOpen e
  rw [openImmersion_pulled_stalkIdeal_eq]
  exact congrArg (fun C => intrinsicCentreStalkRange ys.Y.obj.left C y)
    (centre_preimage_eq w M B hD hClass H hState P Q n xs ys e he)

variable [Finite ι]
  (a : HironakaG1CanonicalStageSuccessor.Successor w M B hD hClass H hState P.K P.cover
    (stage w M B hD hClass H hState P n) xs P.compact)
  (b : HironakaG1CanonicalStageSuccessor.Successor w M B hD hClass H hState Q.K Q.cover
    (stage w M B hD hClass H hState Q n) ys Q.compact)

include he in
private theorem other_isIdealBlowup : IsIdealBlowup (a.p ≫ e.inv)
    (intrinsicReducedCentreIdealModule ys.Y.obj.left CQ)
    (intrinsicReducedCentreIdealInclusion ys.Y.obj.left CQ) := by
  have h := isIdealBlowup_comp_baseIso CP a.isIdealBlowup e
  rw [centre_preimage_eq w M B hD hClass H hState P Q n xs ys e he] at h
  exact h

include he in
private theorem successor_exists : ∃ E : b.Y ≅ a.Y,
    E.hom ≫ (a.p ≫ e.inv) = b.p ∧
      ∀ t : b.Y ⟶ a.Y, t ≫ (a.p ≫ e.inv) = b.p → t = E.hom :=
  RIsoAModification.isIdealBlowup_exists_unique_iso b.isIdealBlowup
    (other_isIdealBlowup w M B hD hClass H hState P Q n xs ys e he a)

/-- The ACTUAL global successor iso across independent footprint drivers. -/
def successorIso : b.Y ≅ a.Y :=
  (successor_exists w M B hD hClass H hState P Q n xs ys e he a b).choose

theorem successorIso_projection :
    (successorIso w M B hD hClass H hState P Q n xs ys e he a b).hom ≫ a.p = b.p ≫ e.hom := by
  have h := congrArg (fun t => t ≫ e.hom)
    (successor_exists w M B hD hClass H hState P Q n xs ys e he a b).choose_spec.1
  simpa only [successorIso, Category.assoc, e.inv_hom_id, Category.comp_id] using h

theorem successorIso_original_projection :
    (successorIso w M B hD hClass H hState P Q n xs ys e he a b).hom ≫ a.toXStage.q = b.toXStage.q := by
  change _ ≫ (a.p ≫ xs.q) = b.p ≫ ys.q
  rw [← Category.assoc, successorIso_projection, Category.assoc, he]

end StageComparison

section Histories

variable [Finite ι]

/-- Only the existing finite zero/actual-successor construction relation,
reindexed to this cover's OWN independently generated ambient driver. -/
abbrev NativeHistory (P : FootprintCover w M) (n : ℕ)
    (xs : XStage w (stage w M B hD hClass H hState P n).T) : Prop :=
  HironakaG1FiniteNativeHistoryComparison.History w M B hD hClass H hState P.K P.cover P.compact n xs

/-- Each native history is internally constructible from ordinary initial data. -/
theorem exists_native_history (P : FootprintCover w M) (n : ℕ) :
    ∃ xs, NativeHistory w M B hD hClass H hState P n xs :=
  HironakaG1FiniteNativeHistoryComparison.exists_history w M B hD hClass H hState P.K P.cover P.compact n

variable (P Q : FootprintCover w M)

/-- The genuine GLOBAL comparison is produced from actual initial identity
by induction on TWO actual independent native histories, with no iso packet. -/
theorem exists_global_history_iso {n : ℕ}
    {xs : XStage w (stage w M B hD hClass H hState P n).T}
    {ys : XStage w (stage w M B hD hClass H hState Q n).T}
    (hx : NativeHistory w M B hD hClass H hState P n xs)
    (hy : NativeHistory w M B hD hClass H hState Q n ys) :
    ∃ E : ys.Y ≅ xs.Y, E.hom ≫ xs.q = ys.q := by
  induction hx with
  | zero =>
    cases hy
    exact ⟨Iso.refl X, Category.id_comp _⟩
  | @step n xs hx a ih =>
    cases hy with
    | @step _ ys hy b =>
      obtain ⟨e, he⟩ := ih hy
      exact ⟨successorIso w M B hD hClass H hState P Q n xs ys e he a b,
        successorIso_original_projection w M B hD hClass H hState P Q n xs ys e he a b⟩

variable {n : ℕ}
  {xs : XStage w (stage w M B hD hClass H hState P n).T}
  {ys : XStage w (stage w M B hD hClass H hState Q n).T}
  (hx : NativeHistory w M B hD hClass H hState P n xs)
  (hy : NativeHistory w M B hD hClass H hState Q n ys)

/-- The actual full global native isomorphism produced by that finite induction. -/
def globalHistoryIso : ys.Y ≅ xs.Y :=
  (exists_global_history_iso w M B hD hClass H hState P Q hx hy).choose

theorem globalHistoryIso_projection :
    (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom ≫ xs.q = ys.q :=
  (exists_global_history_iso w M B hD hClass H hState P Q hx hy).choose_spec

/-- Uniqueness is for FULL original native morphisms over the original base. -/
theorem globalHistoryHom_unique (t : ys.Y ⟶ xs.Y) (ht : t ≫ xs.q = ys.q) :
    t = (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom := by
  apply nativeLift_eq xs.isSingularCentreModification _ _
    (iso_isOpen (globalHistoryIso w M B hD hClass H hState P Q hx hy))
  exact ht.trans (globalHistoryIso_projection w M B hD hClass H hState P Q hx hy).symm

/-- Every actual native independent window equation is DERIVED globally. -/
theorem globalHistoryIso_window_square (i : ι) :
    windowMap w M B hD hClass H hState Q n ys i ≫
        (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom =
      (nativeWindowIso w M B hD hClass H hState P Q n i).hom ≫
        windowMap w M B hD hClass H hState P n xs i :=
  current_window_square w M B hD hClass H hState P Q n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState P Q hx hy) i

/-- Actual global centre agreement at every produced comparison, with no
preceding/current global iso or centre equality supplied as an input. -/
theorem globalHistoryIso_centre_preimage_eq :
    (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom.hom.left.base ⁻¹'
        actualCentre w M B hD hClass H hState P n xs =
      actualCentre w M B hD hClass H hState Q n ys :=
  centre_preimage_eq w M B hD hClass H hState P Q n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState P Q hx hy)

/-- The ENTIRE global centre ideal and original scalar action agree under
the isomorphism actually constructed from initial identity. -/
theorem globalHistoryIso_wholeCentreSubmodule_eq :
    nativePulledIdealSubmodule
        (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom.hom.left
        (intrinsicReducedCentreIdealModule xs.Y.obj.left (actualCentre w M B hD hClass H hState P n xs))
        (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (actualCentre w M B hD hClass H hState P n xs)) =
      intrinsicReducedCentreSubmodule ys.Y.obj.left (actualCentre w M B hD hClass H hState Q n ys) :=
  wholeCentreSubmodule_eq w M B hD hClass H hState P Q n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState P Q hx hy)

/-- The actual global comparisons of THREE independent covers obey the cocycle. -/
theorem globalHistoryIso_cocycle (R : FootprintCover w M)
    {zs : XStage w (stage w M B hD hClass H hState R n).T}
    (hz : NativeHistory w M B hD hClass H hState R n zs) :
    (globalHistoryIso w M B hD hClass H hState Q R hy hz).trans
        (globalHistoryIso w M B hD hClass H hState P Q hx hy) =
      globalHistoryIso w M B hD hClass H hState P R hx hz := by
  apply Iso.ext
  apply globalHistoryHom_unique w M B hD hClass H hState P R hx hz
  change ((globalHistoryIso w M B hD hClass H hState Q R hy hz).hom ≫
    (globalHistoryIso w M B hD hClass H hState P Q hx hy).hom) ≫ xs.q = zs.q
  rw [Category.assoc, globalHistoryIso_projection]
  exact globalHistoryIso_projection w M B hD hClass H hState Q R hy hz

end Histories

end
end SGPT.Unibranch.HironakaG1IndependentNativeHistories

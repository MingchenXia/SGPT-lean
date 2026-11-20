import SGPT.Unibranch.HironakaG1CanonicalStageSuccessor
import SGPT.Unibranch.SourceMorphismExt
import SGPT.Unibranch.HironakaG11NativeTowerRepresentation

/-!
# The actual native one-step field for finite canonical-history comparison

Two original realisations of the SAME actual ambient prefix have their full
native window comparison DERIVED from an actual previous-stage iso. Its centre
and whole ideal transport then construct the genuine next-stage iso. No
current-window agreement or future compatible history is a caller premise.

Blueprint FIRST: `hironaka-g1-canonical-stage-iso-transport.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1CanonicalStageIsoTransport

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11SingularCentreModification SmoothCentreModification EmbeddedBlowup
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
  HironakaG11NativeTowerRepresentation

noncomputable section

private theorem model_eq {n : ℕ} {V : CMfd.{0} n} {A A' : Set V}
    (hA : IsComplexAnalyticSubset (n := n) A) (hA' : IsComplexAnalyticSubset (n := n) A')
    (h : A = A') : ofClosedAnalytic A hA = ofClosedAnalytic A' hA' := by
  cases h
  rfl

private def modelIso {n : ℕ} {V : CMfd.{0} n} {A A' : Set V}
    (hA : IsComplexAnalyticSubset (n := n) A) (hA' : IsComplexAnalyticSubset (n := n) A')
    (h : A = A') : ofClosedAnalytic A hA ≅ ofClosedAnalytic A' hA' :=
  eqToIso (model_eq hA hA' h)

private theorem modelIso_val {n : ℕ} {V : CMfd.{0} n} {A A' : Set V}
    (hA : IsComplexAnalyticSubset (n := n) A) (hA' : IsComplexAnalyticSubset (n := n) A')
    (h : A = A') (z : A) : ((modelIso hA hA' h).hom.hom.left.base z).val = z.val := by
  cases h
  rfl

private theorem iso_isOpen {A A' : SourceReducedComplexSpace} (e : A ≅ A') :
    LocallyRingedSpace.IsOpenImmersion e.hom.hom.left := by
  have : IsIso e.hom.hom.left := by
    change IsIso (isoLeft e).hom
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
  intro z
  exact congrFun h z

section Windows

variable {X : SourceReducedComplexSpace} {N : ℕ} {ι : Type*}
  (w : ι → DimEmbedding X N) (T : Towers w) (xs ys : XStage w T)

/-- Literal full native model comparison for the SAME actual strict carrier. -/
def windowIso (i : ι) : ofClosedAnalytic (xs.carrier i) (xs.analytic i) ≅
    ofClosedAnalytic (ys.carrier i) (ys.analytic i) :=
  modelIso (xs.analytic i) (ys.analytic i) ((xs.carrier_eq i).trans (ys.carrier_eq i).symm)

theorem windowIso_val (i : ι) (z : xs.carrier i) :
    ((windowIso w T xs ys i).hom.hom.left.base z).val = z.val :=
  modelIso_val _ _ _ z

/-- Native window agreement is DERIVED from the actual previous-stage iso;
it is not an inductive input or a future-history certificate. -/
theorem window_square (e : xs.Y ≅ ys.Y) (he : e.hom ≫ ys.q = xs.q) (i : ι) :
    xs.map i ≫ e.hom = (windowIso w T xs ys i).hom ≫ ys.map i := by
  let E := windowIso w T xs ys i
  have : LocallyRingedSpace.IsOpenImmersion E.hom.hom.left := iso_isOpen E
  have : LocallyRingedSpace.IsOpenImmersion (ys.map i).hom.left := ys.isOpenImmersion i
  have hG : LocallyRingedSpace.IsOpenImmersion (E.hom ≫ ys.map i).hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (E.hom.hom.left ≫ (ys.map i).hom.left)
    infer_instance
  apply nativeLift_eq ys.isSingularCentreModification _ _ hG
  apply morphism_eq_of_pointwise_eq
  intro z
  have h1 := congrArg (fun t => t.hom.left.base ((xs.map i).hom.left.base z)) he
  change ys.q.hom.left.base (e.hom.hom.left.base ((xs.map i).hom.left.base z)) =
    xs.q.hom.left.base ((xs.map i).hom.left.base z) at h1
  change ys.q.hom.left.base (e.hom.hom.left.base ((xs.map i).hom.left.base z)) =
    ys.q.hom.left.base ((ys.map i).hom.left.base (E.hom.hom.left.base z))
  rw [h1, xs.square i z (xs.proj_mem i z),
    ys.square i (E.hom.hom.left.base z) (ys.proj_mem i (E.hom.hom.left.base z))]
  apply congrArg (w i).toLocalEmbedding.toPoint
  apply Subtype.ext
  change (T i).2.proj z.val = (T i).2.proj (E.hom.hom.left.base z).val
  exact congrArg (T i).2.proj (windowIso_val w T xs ys i z).symm

end Windows

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, ResolutionInvariantSpec.IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (K : ∀ i, Set (w i).ambient)
  (hCover : ∀ i (c : (w i).carrier), c.val ∈ (M i).cosupp →
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ K j ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs ys : XStage w s.T)
  (e : xs.Y ≅ ys.Y) (he : e.hom ≫ ys.q = xs.q)

local notation "FX" => localCentres w M B hD hClass H hState K hCover s xs
local notation "FY" => localCentres w M B hD hClass H hState K hCover s ys
local notation "CX" => support w M B hD hClass H hState K hCover s xs
local notation "CY" => support w M B hD hClass H hState K hCover s ys
local notation "JX" => intrinsicReducedCentreIdealModule xs.Y.obj.left CX
local notation "JY" => intrinsicReducedCentreIdealModule ys.Y.obj.left CY
local notation "bX" => intrinsicReducedCentreIdealInclusion xs.Y.obj.left CX
local notation "bY" => intrinsicReducedCentreIdealInclusion ys.Y.obj.left CY

include he in
private theorem support_map_mem {x : xs.Y.obj.left} (hx : x ∈ CX) :
    e.hom.hom.left.base x ∈ CY := by
  obtain ⟨i, z, hz, rfl⟩ := (FX).mem_support.mp hx
  refine (FY).mem_support.mpr ⟨i, (windowIso w s.T xs ys i).hom.hom.left.base z, ?_, ?_⟩
  · change ((windowIso w s.T xs ys i).hom.hom.left.base z).val ∈
      gcentre B.toResolutionInvariant M K s.T i
    have hv := windowIso_val w s.T xs ys i z
    exact hv.symm ▸ hz
  · exact (congrArg (fun t => t.hom.left.base z) (window_square w s.T xs ys e he i)).symm

include he in
/-- The SAME entire constructed centre, transported by the actual native iso. -/
theorem support_preimage_eq : e.hom.hom.left.base ⁻¹' CY = CX := by
  ext x
  constructor
  · intro hx
    have he' : e.inv ≫ xs.q = ys.q := by
      rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    have h := support_map_mem w M B hD hClass H hState K hCover s ys xs e.symm he' hx
    have hc := congrArg (fun t => t.hom.left.base x) e.hom_inv_id
    change e.inv.hom.left.base (e.hom.hom.left.base x) = x at hc
    change e.inv.hom.left.base (e.hom.hom.left.base x) ∈ CX at h
    rwa [hc] at h
  · exact support_map_mem w M B hD hClass H hState K hCover s xs ys e he

include he in
/-- Whole native scalar-submodule pullback, with no support-only substitute. -/
theorem wholeSubmodule_eq : nativePulledIdealSubmodule e.hom.hom.left JY bY =
    intrinsicReducedCentreSubmodule xs.Y.obj.left CX := by
  have : LocallyRingedSpace.IsOpenImmersion e.hom.hom.left := iso_isOpen e
  rw [openImmersion_pulled_submodule_eq]
  exact congrArg (intrinsicReducedCentreSubmodule xs.Y.obj.left)
    (support_preimage_eq w M B hD hClass H hState K hCover s xs ys e he)

include he in
theorem wholeSectionIdeal_eq (V : Opens xs.Y.obj.left.toTopCat) :
    nativePulledIdealSectionIdeal e.hom.hom.left JY bY V =
      intrinsicReducedCentreSectionIdeal xs.Y.obj.left CX V := by
  have : LocallyRingedSpace.IsOpenImmersion e.hom.hom.left := iso_isOpen e
  rw [openImmersion_pulled_sectionIdeal_eq]
  exact congrArg (fun C => intrinsicReducedCentreSectionIdeal xs.Y.obj.left C V)
    (support_preimage_eq w M B hD hClass H hState K hCover s xs ys e he)

include he in
theorem wholeStalkIdeal_eq (x : xs.Y.obj.left) :
    nativePulledIdealStalkIdeal e.hom.hom.left JY bY x = intrinsicCentreStalkRange xs.Y.obj.left CX x := by
  have : LocallyRingedSpace.IsOpenImmersion e.hom.hom.left := iso_isOpen e
  rw [openImmersion_pulled_stalkIdeal_eq]
  exact congrArg (fun C => intrinsicCentreStalkRange xs.Y.obj.left C x)
    (support_preimage_eq w M B hD hClass H hState K hCover s xs ys e he)

local notation "NWX" => HironakaG1CanonicalStageSuccessor.nextWindow
  w M B hD hClass H hState K hCover s xs
local notation "NWY" => HironakaG1CanonicalStageSuccessor.nextWindow
  w M B hD hClass H hState K hCover s ys
local notation "PX" => HironakaG1CanonicalStageSuccessor.nextWindowProjection
  w M B hD hClass H hState K hCover s xs
local notation "PY" => HironakaG1CanonicalStageSuccessor.nextWindowProjection
  w M B hD hClass H hState K hCover s ys

/-- Actual model comparison after the SAME prescribed ambient canonical step. -/
def nextWindowIso (i : ι) : NWX i ≅ NWY i :=
  modelIso _ _ (congrArg
    (strictTransform N (HironakaG1CanonicalStageSuccessor.nextProjection
      w M B hD hClass H hState K hCover s i))
    ((xs.carrier_eq i).trans (ys.carrier_eq i).symm))

theorem nextWindowIso_val (i : ι) (z : (NWX i).obj.left) :
    ((nextWindowIso w M B hD hClass H hState K hCover s xs ys i).hom.hom.left.base z).val = z.val :=
  modelIso_val _ _ _ z

/-- The full native strict-projection triangle, not merely its support square. -/
theorem nextWindowProjection_square (i : ι) :
    (nextWindowIso w M B hD hClass H hState K hCover s xs ys i).hom ≫ PY i =
      PX i ≫ (windowIso w s.T xs ys i).hom := by
  apply morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  change HironakaG1CanonicalStageSuccessor.nextProjection w M B hD hClass H hState K hCover s i
      ((nextWindowIso w M B hD hClass H hState K hCover s xs ys i).hom.hom.left.base z).val =
    ((windowIso w s.T xs ys i).hom.hom.left.base ((PX i).hom.left.base z)).val
  calc
    _ = HironakaG1CanonicalStageSuccessor.nextProjection w M B hD hClass H hState K hCover s i z.val :=
      congrArg _ (nextWindowIso_val w M B hD hClass H hState K hCover s xs ys i z)
    _ = _ := (windowIso_val w s.T xs ys i ((PX i).hom.left.base z)).symm

variable [Finite ι] (hK : ∀ i, IsCompact (K i))
  (a : HironakaG1CanonicalStageSuccessor.Successor w M B hD hClass H hState K hCover s xs hK)
  (b : HironakaG1CanonicalStageSuccessor.Successor w M B hD hClass H hState K hCover s ys hK)

include he in
private theorem other_isIdealBlowup : IsIdealBlowup (b.p ≫ e.inv) JX bX := by
  have h := isIdealBlowup_comp_baseIso CY b.isIdealBlowup e
  rw [support_preimage_eq w M B hD hClass H hState K hCover s xs ys e he] at h
  exact h

include he in
private theorem comparison_exists : ∃ E : a.Y ≅ b.Y,
    E.hom ≫ (b.p ≫ e.inv) = a.p ∧
      ∀ t : a.Y ⟶ b.Y, t ≫ (b.p ≫ e.inv) = a.p → t = E.hom :=
  RIsoAModification.isIdealBlowup_exists_unique_iso a.isIdealBlowup
    (other_isIdealBlowup w M B hD hClass H hState K hCover s xs ys e he hK b)

/-- The actual successor comparison over the preceding native iso. -/
def successorIso : a.Y ≅ b.Y :=
  (comparison_exists w M B hD hClass H hState K hCover s xs ys e he hK a b).choose

theorem successorIso_projection :
    (successorIso w M B hD hClass H hState K hCover s xs ys e he hK a b).hom ≫ b.p = a.p ≫ e.hom := by
  have h := congrArg (fun t => t ≫ e.hom)
    (comparison_exists w M B hD hClass H hState K hCover s xs ys e he hK a b).choose_spec.1
  simpa only [successorIso, Category.assoc, e.inv_hom_id, Category.comp_id] using h

theorem successorHom_unique (t : a.Y ⟶ b.Y) (ht : t ≫ b.p = a.p ≫ e.hom) :
    t = (successorIso w M B hD hClass H hState K hCover s xs ys e he hK a b).hom := by
  apply (comparison_exists w M B hD hClass H hState K hCover s xs ys e he hK a b).choose_spec.2
  rw [← Category.assoc, ht, Category.assoc, e.hom_inv_id, Category.comp_id]

theorem successorIso_original_projection :
    (successorIso w M B hD hClass H hState K hCover s xs ys e he hK a b).hom ≫ b.toXStage.q =
      a.toXStage.q := by
  change _ ≫ (b.p ≫ ys.q) = a.p ≫ xs.q
  rw [← Category.assoc, successorIso_projection, Category.assoc, he]

/-- The genuine next native window comparison required for finite induction. -/
theorem successorIso_window_square (i : ι) :
    a.map i ≫ (successorIso w M B hD hClass H hState K hCover s xs ys e he hK a b).hom =
      (nextWindowIso w M B hD hClass H hState K hCover s xs ys i).hom ≫ b.map i := by
  let E := nextWindowIso w M B hD hClass H hState K hCover s xs ys i
  have : LocallyRingedSpace.IsOpenImmersion E.hom.hom.left := iso_isOpen E
  have : LocallyRingedSpace.IsOpenImmersion (b.map i).hom.left := b.isOpenImmersion i
  have hG : LocallyRingedSpace.IsOpenImmersion (E.hom ≫ b.map i).hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (E.hom.hom.left ≫ (b.map i).hom.left)
    infer_instance
  apply nativeLift_eq b.isSingularCentreStep.isSingularCentreModification _ _ hG
  calc
    (a.map i ≫ (successorIso w M B hD hClass H hState K hCover s xs ys e he hK a b).hom) ≫ b.p =
        a.map i ≫ (a.p ≫ e.hom) := by rw [Category.assoc, successorIso_projection]
    _ = (PX i ≫ xs.map i) ≫ e.hom := by rw [← Category.assoc, a.square i]
    _ = PX i ≫ ((windowIso w s.T xs ys i).hom ≫ ys.map i) := by
      rw [Category.assoc, window_square w s.T xs ys e he i]
    _ = (E.hom ≫ PY i) ≫ ys.map i := by
      rw [← Category.assoc, ← nextWindowProjection_square]
    _ = (E.hom ≫ b.map i) ≫ b.p := by
      simpa only [Category.assoc] using (congrArg (fun t => E.hom ≫ t) (b.square i)).symm

end
end SGPT.Unibranch.HironakaG1CanonicalStageIsoTransport

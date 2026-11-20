import SGPT.Unibranch.HironakaG1CanonicalOldBoundarySuccessor
import SGPT.Unibranch.HironakaG1IndependentNativeHistories

/-!
# One-successor naturality of the ACTUAL global native old ideal

The actual native successor isomorphism is constructed by the held whole
ideal-blowup universal property. CURRENT old-image transport is induction
data; current centre transport and the full successor square are derived.
Total/born images and true epsilon commute before the epsilon1 colon is
transported. E's full original-unit uniqueness gives actual sheaf transport.
No future ideal alignment, old regularity or support substitute is input.

Blueprint FIRST: `hironaka-g1-canonical-old-boundary-naturality.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry Opposite Classical
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1CanonicalOldBoundaryNaturality

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  HironakaG1CanonicalStageSuccessor HironakaG1CanonicalStageBoundaryIncidence
  HironakaG1IndependentFootprintDrivers
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
  HironakaSingularModuleSheafStalk HironakaG10ChowGermIdealDictionary
  HironakaActualIntrinsicLabelledBoundaryIdeals
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

section NativeAlgebra

private abbrev imageIdeal {X : LocallyRingedSpace.{0}}
    (D : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
    (bD : D ⟶ SheafOfModules.unit _) (x : X) : Ideal (X.presheaf.stalk x).carrier :=
  LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf D bD x)

private def splitIdeal {A X : LocallyRingedSpace.{0}} (p : A ⟶ X)
    (D J : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
    (bD : D ⟶ SheafOfModules.unit _) (bJ : J ⟶ SheafOfModules.unit _) (z : A) :
    Ideal (A.presheaf.stalk z).carrier :=
  if imageIdeal D bD (p.base z) ≤ imageIdeal J bJ (p.base z) then
    (nativePulledIdealStalkIdeal p D bD z).colon
      (nativePulledIdealStalkIdeal p J bJ z : Set _) else
    nativePulledIdealStalkIdeal p D bD z

private theorem map_colon_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I J : Ideal R) :
    Ideal.map e.toRingHom (I.colon (J : Set R)) =
      (Ideal.map e.toRingHom I).colon (Ideal.map e.toRingHom J : Set S) := by
  ext y
  constructor
  · intro hy
    have hy' := (Ideal.symm_apply_mem_of_equiv_iff
      (I := I.colon (J : Set R)) (f := e)).mpr hy
    apply Submodule.mem_colon.mpr
    intro s hs
    apply (Ideal.symm_apply_mem_of_equiv_iff (I := I) (f := e)).mp
    change e.symm (y * s) ∈ I
    rw [map_mul]
    exact (Submodule.mem_colon.mp hy') (e.symm s)
      ((Ideal.symm_apply_mem_of_equiv_iff (I := J) (f := e)).mpr hs)
  · intro hy
    apply (Ideal.symm_apply_mem_of_equiv_iff (I := I.colon (J : Set R)) (f := e)).mp
    apply Submodule.mem_colon.mpr
    intro s hs
    have hm := (Submodule.mem_colon.mp hy) (e s) (Ideal.mem_map_of_mem e.toRingHom hs)
    have hm' := (Ideal.symm_apply_mem_of_equiv_iff (I := I) (f := e)).mpr hm
    simpa only [smul_eq_mul, map_mul, e.symm_apply_apply] using hm'

private theorem total_map {A B X Y : LocallyRingedSpace.{0}}
    (p : A ⟶ X) (q : B ⟶ Y) (e : X ≅ Y) (F : A ≅ B)
    (hsq : F.hom ≫ q = p ≫ e.hom)
    (DY : SheafOfModules.{0} (forgetRing Y.toSheafedSpace.sheaf))
    (bDY : DY ⟶ SheafOfModules.unit _)
    (DX : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
    (bDX : DX ⟶ SheafOfModules.unit _)
    (hD : ∀ x : X, nativePulledIdealStalkIdeal e.hom DY bDY x = imageIdeal DX bDX x)
    (z : A) :
    Ideal.map (F.hom.stalkMap z).hom
      (nativePulledIdealStalkIdeal q DY bDY (F.hom.base z)) =
      nativePulledIdealStalkIdeal p DX bDX z := by
  rw [← nativePulledIdealStalkIdeal_comp, hsq, nativePulledIdealStalkIdeal_comp, hD]

private theorem split_map {A B X Y : LocallyRingedSpace.{0}}
    (p : A ⟶ X) (q : B ⟶ Y) (e : X ≅ Y) (F : A ≅ B)
    (hsq : F.hom ≫ q = p ≫ e.hom)
    (DY JY : SheafOfModules.{0} (forgetRing Y.toSheafedSpace.sheaf))
    (bDY : DY ⟶ SheafOfModules.unit _) (bJY : JY ⟶ SheafOfModules.unit _)
    (DX JX : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
    (bDX : DX ⟶ SheafOfModules.unit _) (bJX : JX ⟶ SheafOfModules.unit _)
    (hD : ∀ x : X, nativePulledIdealStalkIdeal e.hom DY bDY x = imageIdeal DX bDX x)
    (hJ : ∀ x : X, nativePulledIdealStalkIdeal e.hom JY bJY x = imageIdeal JX bJX x)
    (z : A) :
    Ideal.map (F.hom.stalkMap z).hom (splitIdeal q DY JY bDY bJY (F.hom.base z)) =
      splitIdeal p DX JX bDX bJX z := by
  have hp : q.base (F.hom.base z) = e.hom.base (p.base z) :=
    congrArg (fun f => f.base z) hsq
  have hc : (imageIdeal DY bDY (q.base (F.hom.base z)) ≤
      imageIdeal JY bJY (q.base (F.hom.base z))) ↔
      imageIdeal DX bDX (p.base z) ≤ imageIdeal JX bJX (p.base z) := by
    rw [hp, ← hD (p.base z), ← hJ (p.base z)]
    exact ((asIso (e.hom.stalkMap (p.base z))).commRingCatIsoToRingEquiv.idealComapOrderIso.symm).le_iff_le.symm
  have hT := total_map p q e F hsq DY bDY DX bDX hD z
  have hB := total_map p q e F hsq JY bJY JX bJX hJ z
  let eF := (asIso (F.hom.stalkMap z)).commRingCatIsoToRingEquiv
  have heF : eF.toRingHom = (F.hom.stalkMap z).hom := rfl
  rw [← heF] at hT hB
  change Ideal.map eF.toRingHom _ = _
  unfold splitIdeal
  rw [hc]
  by_cases h : imageIdeal DX bDX (p.base z) ≤ imageIdeal JX bJX (p.base z)
  · rw [if_pos h, if_pos h, map_colon_ringEquiv, hT, hB]
  · simpa only [if_neg h] using hT

end NativeAlgebra

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (P Q : FootprintCover w M) (n : ℕ)
  (xs : XStage w (stage w M B hD hClass H hState P n).T)
  (ys : XStage w (stage w M B hD hClass H hState Q n).T)
  (e : ys.Y ≅ xs.Y) (he : e.hom ≫ xs.q = ys.q)
  [Finite ι]
  (a : Successor w M B hD hClass H hState P.K P.cover
    (stage w M B hD hClass H hState P n) xs P.compact)
  (b : Successor w M B hD hClass H hState Q.K Q.cover
    (stage w M B hD hClass H hState Q n) ys Q.compact)
  (DP : SheafOfModules.{0} (forgetRing xs.Y.obj.left.toSheafedSpace.sheaf))
  (bDP : DP ⟶ SheafOfModules.unit _)
  (DQ : SheafOfModules.{0} (forgetRing ys.Y.obj.left.toSheafedSpace.sheaf))
  (bDQ : DQ ⟶ SheafOfModules.unit _)
  (hDI : ∀ y : ys.Y.obj.left, nativePulledIdealStalkIdeal e.hom.hom.left DP bDP y =
    LinearMap.range (stalkInclusionLinearMap ys.Y.obj.left.toSheafedSpace.sheaf DQ bDQ y))

local notation "F" => HironakaG1IndependentNativeHistories.successorIso
  w M B hD hClass H hState P Q n xs ys e he a b
local notation "JP" => intrinsicReducedCentreIdealModule xs.Y.obj.left
  (HironakaG1IndependentNativeHistories.actualCentre w M B hD hClass H hState P n xs)
local notation "bJP" => intrinsicReducedCentreIdealInclusion xs.Y.obj.left
  (HironakaG1IndependentNativeHistories.actualCentre w M B hD hClass H hState P n xs)
local notation "JQ" => intrinsicReducedCentreIdealModule ys.Y.obj.left
  (HironakaG1IndependentNativeHistories.actualCentre w M B hD hClass H hState Q n ys)
local notation "bJQ" => intrinsicReducedCentreIdealInclusion ys.Y.obj.left
  (HironakaG1IndependentNativeHistories.actualCentre w M B hD hClass H hState Q n ys)
local notation "PP" => HironakaG1CanonicalOldBoundarySuccessor.successorStalkIdeal
  w M B hD hClass H hState P.K P.cover (stage w M B hD hClass H hState P n) xs P.compact a DP bDP
local notation "PQ" => HironakaG1CanonicalOldBoundarySuccessor.successorStalkIdeal
  w M B hD hClass H hState Q.K Q.cover (stage w M B hD hClass H hState Q n) ys Q.compact b DQ bDQ
local notation "IP" => HironakaG1CanonicalOldBoundarySuccessor.successorIdealModule
  w M B hD hClass H hState P.K P.cover (stage w M B hD hClass H hState P n) xs P.compact a DP bDP
local notation "bIP" => HironakaG1CanonicalOldBoundarySuccessor.successorIdealInclusion
  w M B hD hClass H hState P.K P.cover (stage w M B hD hClass H hState P n) xs P.compact a DP bDP
local notation "IQ" => HironakaG1CanonicalOldBoundarySuccessor.successorIdealModule
  w M B hD hClass H hState Q.K Q.cover (stage w M B hD hClass H hState Q n) ys Q.compact b DQ bDQ
local notation "bIQ" => HironakaG1CanonicalOldBoundarySuccessor.successorIdealInclusion
  w M B hD hClass H hState Q.K Q.cover (stage w M B hD hClass H hState Q n) ys Q.compact b DQ bDQ

private theorem actual_square :
    (SourceReducedComplexSpace.isoLeft (F)).hom ≫ a.p.hom.left =
      b.p.hom.left ≫ (SourceReducedComplexSpace.isoLeft e).hom :=
  congrArg (fun t => t.hom.left)
    (HironakaG1IndependentNativeHistories.successorIso_projection
      w M B hD hClass H hState P Q n xs ys e he a b)

include hDI in
/-- ENTIRE actual native total pullback, derived from the held full square
and CURRENT old ideal transport. This also applies to the actual born J. -/
theorem successor_totalImage_map (z : b.Y.obj.left) :
    Ideal.map (((F).hom.hom.left).stalkMap z).hom
      (nativePulledIdealStalkIdeal a.p.hom.left DP bDP (((F).hom.hom.left).base z)) =
      nativePulledIdealStalkIdeal b.p.hom.left DQ bDQ z :=
  total_map b.p.hom.left a.p.hom.left (SourceReducedComplexSpace.isoLeft e)
    (SourceReducedComplexSpace.isoLeft (F))
    (actual_square w M B hD hClass H hState P Q n xs ys e he a b) DP bDP DQ bDQ hDI z

include hDI in
/-- True epsilon and the actual split successor ideal commute. Only the
epsilon1 branch transports colon; epsilon0 is the total identity above. -/
theorem successorStalkIdeal_map (z : b.Y.obj.left) :
    Ideal.map (((F).hom.hom.left).stalkMap z).hom (PP (((F).hom.hom.left).base z)) = PQ z := by
  have hJ : ∀ y : ys.Y.obj.left,
      nativePulledIdealStalkIdeal e.hom.hom.left JP bJP y = imageIdeal JQ bJQ y :=
    HironakaG1IndependentNativeHistories.wholeCentreStalkIdeal_eq
      w M B hD hClass H hState P Q n xs ys e he
  exact split_map b.p.hom.left a.p.hom.left (SourceReducedComplexSpace.isoLeft e)
    (SourceReducedComplexSpace.isoLeft (F))
    (actual_square w M B hD hClass H hState P Q n xs ys e he a b)
    DP JP bDP bJP DQ JQ bDQ bJQ hDI hJ z

variable
  (oldLabelP : ∀ i, Fin (currentBoundary w M B (stage w M B hD hClass H hState P n) i).length)
  (hOldP : ∀ i (p : (ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left),
    nativePulledIdealStalkIdeal (xs.map i).hom.left DP bDP p =
      actualLabelledBoundaryTraceIdeal (xs.carrier i)
        (currentBoundary w M B (stage w M B hD hClass H hState P n) i) (oldLabelP i) p)

include hDI hOldP in
/-- UNIQUE full native old-ideal transport, preserving the LITERAL
original unit inclusion. Every whole successor stalk identity is derived. -/
theorem existsUnique_successorIdealIso :
    ∃! E : nativePulledIdealModule ((F).hom.hom.left) IP bIP ≅ IQ,
      E.hom ≫ bIQ = nativePulledIdealInclusion ((F).hom.hom.left) IP bIP := by
  let L := nativePulledIdealModule ((F).hom.hom.left) IP bIP
  let bL := nativePulledIdealInclusion ((F).hom.hom.left) IP bIP
  have hRange (z : b.Y.obj.left) :
      LinearMap.range (stalkInclusionLinearMap b.Y.obj.left.toSheafedSpace.sheaf L bL z) = PQ z := by
    change LinearMap.range (nativePulledIdealStalkInclusion ((F).hom.hom.left) IP bIP z) = _
    rw [nativePulledIdealStalkInclusion_range]
    change Ideal.map (((F).hom.hom.left).stalkMap z).hom
      (LinearMap.range (stalkInclusionLinearMap _ IP bIP _)) = _
    rw [HironakaG1CanonicalOldBoundarySuccessor.successorIdeal_stalkRange
      w M B hD hClass H hState P.K P.cover (stage w M B hD hClass H hState P n)
      xs P.compact a DP bDP oldLabelP hOldP]
    exact successorStalkIdeal_map w M B hD hClass H hState P Q n xs ys e he a b DP bDP DQ bDQ hDI z
  exact HironakaG1NativeStalkIdealSheaf.existsUnique_idealIso (PQ) L bL
    (fun _ => Subtype.val_injective) hRange

end
end SGPT.Unibranch.HironakaG1CanonicalOldBoundaryNaturality

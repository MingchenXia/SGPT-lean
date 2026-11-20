import SGPT.Unibranch.HironakaG1CanonicalBornBoundaryIdeal
import SGPT.Unibranch.HironakaG1CanonicalStageBoundaryIncidence
import SGPT.Unibranch.HironakaG1CanonicalSuccessorCover
import SGPT.Unibranch.HironakaG11BlowupLocality
import SGPT.Foundations.Analysis.Pending.HironakaLegacyCoherentIdealSheaf
import SGPT.Foundations.Analysis.Pending.HironakaG1NativeStalkIdealSheaf
import Mathlib.RingTheory.Ideal.Colon

/-!
# One actual global old-ideal successor with its genuine incidence split

The true native total image is retained when epsilon is zero. In the
epsilon-one branch ONLY the actual regular born ideal on the FULL native
successor is cancelled. All current old labels and full native squares
are retained. Exact global stalks use genuine local ideal models.

Blueprint FIRST: `hironaka-g1-canonical-old-boundary-successor.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry Opposite Classical
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1CanonicalOldBoundarySuccessor

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  HironakaG1CanonicalStageSuccessor HironakaG1CanonicalStageBoundaryIncidence
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk HironakaNativePulledIdealComposition
  HironakaSingularModuleSheafStalk HironakaG10ChowGermIdealDictionary
  HironakaActualAnalyticSubspace HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaG1NativeOldBoundaryFactor
  HironakaG1QuotientLabelledBoundaryFrame BlowupFlatCoordinates NormalCrossings
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  HironakaLegacyCoherentIdealSheaf
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

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

private theorem colon_regular_principal_mul {R : Type*} [CommRing R]
    (b : R) (hb : IsRegular b) (S : Ideal R) :
    ((Ideal.span {b}) * S).colon (Ideal.span {b} : Set R) = S := by
  ext x
  rw [Submodule.mem_colon]
  simp only [smul_eq_mul]
  constructor
  · intro hx
    have hm := hx b (Ideal.mem_span_singleton_self b)
    change x * b ∈ Ideal.span {b} * S at hm
    rw [mul_comm (Ideal.span {b}) S, Ideal.mem_mul_span_singleton] at hm
    obtain ⟨s, hs, hse⟩ := hm
    have hxs : s = x := hb.right hse
    exact hxs ▸ hs
  · intro hx s hs
    change x * s ∈ Ideal.span {b} * S
    rw [mul_comm x s]
    exact Ideal.mul_mem_mul hs hx

private theorem whole_empty {n : ℕ} {Y : CMfd.{0} n} (y : Y) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (∅ : Set Y)) y = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← originalGerm_one y]
  exact Ideal.subset_span ⟨fun _ => (1 : ℂ), holomorphicAt_const 1,
    ⟨holomorphicAt_const 1, Eventually.of_forall fun _ h => h.elim⟩, rfl⟩

private theorem snc_member_empty_of_zero {n : ℕ} {Y : CMfd.{0} n}
    (hn : n = 0) {E : List (Set Y)} (hE : IsSNCDivisor n E) (i : Fin E.length) :
    E.get i = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨Φ, κ, _, _, _, hEq, _⟩ := exists_quotient_labelled_boundary_frame hE y
  obtain ⟨j, _, _⟩ := (hEq y (mem_flatDomain_self Φ) i).mp hy
  exact Fin.elim0 (Fin.cast hn j)

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (K : ∀ i, Set (w i).ambient)
  (hCover : ∀ i (c : (w i).carrier), c.val ∈ (M i).cosupp →
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ K j ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)
  [Finite ι] (hK : ∀ i, IsCompact (K i))
  (a : Successor w M B hD hClass H hState K hCover s xs hK)
  (D : SheafOfModules.{0} (forgetRing xs.Y.obj.left.toSheafedSpace.sheaf))
  (bD : D ⟶ SheafOfModules.unit _)

local notation "C" => support w M B hD hClass H hState K hCover s xs
local notation "J" => intrinsicReducedCentreIdealModule xs.Y.obj.left C
local notation "bJ" => intrinsicReducedCentreIdealInclusion xs.Y.obj.left C
local notation "π" => nextProjection w M B hD hClass H hState K hCover s
local notation "E" => currentBoundary w M B s

/-- The canonical WHOLE actual stalk ideal: epsilon0 retains total image;
epsilon1 is the colon by the actual native born ideal. -/
def successorStalkIdeal (y : a.Y.obj.left) : Ideal (a.Y.obj.left.presheaf.stalk y).carrier :=
  if LinearMap.range (stalkInclusionLinearMap xs.Y.obj.left.toSheafedSpace.sheaf
      D bD (a.p.hom.left.base y)) ≤
    LinearMap.range (stalkInclusionLinearMap xs.Y.obj.left.toSheafedSpace.sheaf
      J bJ (a.p.hom.left.base y)) then
    (nativePulledIdealStalkIdeal a.p.hom.left D bD y).colon
      (nativePulledIdealStalkIdeal a.p.hom.left J bJ y : Set _) else
    nativePulledIdealStalkIdeal a.p.hom.left D bD y

variable (oldLabel : ∀ i, Fin (currentBoundary w M B s i).length)
  (hOld : ∀ i (p : (ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left),
    nativePulledIdealStalkIdeal (xs.map i).hom.left D bD p =
      actualLabelledBoundaryTraceIdeal (xs.carrier i) (currentBoundary w M B s i) (oldLabel i) p)

omit [Finite ι] in
include hD in
private theorem current_snc (i : ι) : IsSNCDivisor N (E i) := by
  have ht := B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical
    (hD i) (s.T i).2 (s.canonical i)
  exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (hD i).isWellFormed (s.T i).2 ht).isSNCDivisor

omit [Finite ι] in
include hD hClass H hState hCover in
private theorem next_admissible (i : ι) :
    (geoTransformAlong (M i) (s.T i).2).IsAdmissibleCentre
      (gcentre B.toResolutionInvariant M K s.T i) := by
  exact (B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical (hD i)
    ((nextStage w M B hD hClass H hState K hCover s).T i).2
    ((nextStage w M B hD hClass H hState K hCover s).canonical i)).2

include hOld in
private theorem total_window_image (i : ι)
    (z : (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left) :
    Ideal.map ((a.map i).hom.left.stalkMap z).hom
      (nativePulledIdealStalkIdeal a.p.hom.left D bD ((a.map i).hom.left.base z)) =
    Ideal.map ((nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left.stalkMap z).hom
      (actualLabelledBoundaryTraceIdeal (xs.carrier i) (E i) (oldLabel i)
        ((nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left.base z)) := by
  have hsq : (a.map i).hom.left ≫ a.p.hom.left =
      (nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left ≫
        (xs.map i).hom.left := congrArg (fun f => f.hom.left) (a.square i)
  rw [← nativePulledIdealStalkIdeal_comp, hsq, nativePulledIdealStalkIdeal_comp, hOld i]

private theorem born_window_image (i : ι)
    (z : (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left) :
    Ideal.map ((a.map i).hom.left.stalkMap z).hom
      (nativePulledIdealStalkIdeal a.p.hom.left J bJ ((a.map i).hom.left.base z)) =
    actualLabelledBoundaryTraceIdeal (strictTransform N (π i) (xs.carrier i))
      [(π i) ⁻¹' gcentre B.toResolutionInvariant M K s.T i] 0 z := by
  have hb := HironakaG1CanonicalBornBoundaryIdeal.window_stalkIdeal_eq_born
    w M B hD hClass H hState K hCover s xs hK a i z
  rw [stalkIdeal_comp, nativePulledIdealStalkIdeal_comp] at hb
  rw [actualLabelledBoundaryTraceIdeal,
    HironakaG1CanonicalBornBoundaryIdeal.bornLabel_get] at hb
  exact hb

private theorem regular_born (y : a.Y.obj.left) :
    ∃ b : (a.Y.obj.left.presheaf.stalk y).carrier, IsRegular b ∧
      nativePulledIdealStalkIdeal a.p.hom.left J bJ y = Ideal.span {b} := by
  obtain ⟨U, hyU, t, ht⟩ := (HironakaG11BlowupLocality.hasRankOneData_iff
    a.p.hom.left J bJ).mp a.isIdealBlowup.1 y
  exact ⟨a.Y.obj.left.presheaf.germ U y hyU t, (ht y hyU).2, (ht y hyU).1⟩

include hOld in
/-- ENTIRE actual local comparison. Cancellation uses only the regular
born generator on the full actual successor; epsilon0 remains total. -/
theorem window_map_successorStalkIdeal (i : ι)
    (z : (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left) :
    Ideal.map ((a.map i).hom.left.stalkMap z).hom
      (successorStalkIdeal w M B hD hClass H hState K hCover s xs hK a D bD
        ((a.map i).hom.left.base z)) =
      actualLabelledBoundaryTraceIdeal (strictTransform N (π i) (xs.carrier i))
        [BlowupStrictSubmanifold.geoStrictTransform (π i)
          (gcentre B.toResolutionInvariant M K s.T i) ((E i).get (oldLabel i))] 0 z := by
  have : LocallyRingedSpace.IsOpenImmersion (a.map i).hom.left := a.isOpenImmersion i
  let e := (asIso ((a.map i).hom.left.stalkMap z)).commRingCatIsoToRingEquiv
  have heφ : e.toRingHom = ((a.map i).hom.left.stalkMap z).hom := rfl
  let T := nativePulledIdealStalkIdeal a.p.hom.left D bD ((a.map i).hom.left.base z)
  let Q := nativePulledIdealStalkIdeal a.p.hom.left J bJ ((a.map i).hom.left.base z)
  let old : Ideal ((nextWindow w M B hD hClass H hState K hCover s xs i).obj.left.presheaf.stalk z).carrier :=
    actualLabelledBoundaryTraceIdeal (strictTransform N (π i) (xs.carrier i))
    [BlowupStrictSubmanifold.geoStrictTransform (π i)
      (gcentre B.toResolutionInvariant M K s.T i) ((E i).get (oldLabel i))] 0 z
  have hTot := total_window_image w M B hD hClass H hState K hCover s xs hK a D bD oldLabel hOld i z
  have hBorn := born_window_image w M B hD hClass H hState K hCover s xs hK a i z
  rw [← heφ] at hTot hBorn
  change Ideal.map e.toRingHom _ = old
  have hSNC := current_snc w M B hD s i
  by_cases hn : 0 < N
  · have hf := native_old_boundary_factor hn
      (nextProjection_isBlowup w M B hD hClass H hState K hCover s i) hSNC
      (next_admissible w M B hD hClass H hState K hCover s i).2.2
      (xs.analytic i) (oldLabel i) z
    have hfactor : Ideal.map e.toRingHom T = (Ideal.map e.toRingHom Q) ^
        centreMemberExponent (gcentre B.toResolutionInvariant M K s.T i)
          ((E i).get (oldLabel i)) ((π i) z.val) * old :=
      hTot.trans (hf.trans (by rw [hBorn]))
    have heps := memberExponent_eq_global_ite w M B hD hClass H hState K hCover s xs D bD
      i (oldLabel i)
      ((nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left.base z)
      (hOld i _)
    have hpoint : (xs.map i).hom.left.base
        ((nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left.base z) =
      a.p.hom.left.base ((a.map i).hom.left.base z) :=
      (congrArg (fun f => f.hom.left.base z) (a.square i)).symm
    change centreMemberExponent _ _ ((π i) z.val) = _ at heps
    rw [hpoint] at heps
    unfold successorStalkIdeal
    split_ifs with hi
    · have he : centreMemberExponent (gcentre B.toResolutionInvariant M K s.T i)
          ((E i).get (oldLabel i)) ((π i) z.val) = 1 := by simpa only [if_pos hi] using heps
      rw [map_colon_ringEquiv e T Q]
      obtain ⟨b, hb, hQ⟩ := regular_born w M B hD hClass H hState K hCover s xs hK a
        ((a.map i).hom.left.base z)
      change Q = Ideal.span {b} at hQ
      have hreg := isRegular_map_ringEquiv e hb
      have hmapQ : Ideal.map e.toRingHom Q = Ideal.span {e b} := by
        rw [hQ, Ideal.map_span, Set.image_singleton]
        rfl
      rw [hfactor, he, pow_one, hmapQ, colon_regular_principal_mul (e b) hreg old]
    · have he : centreMemberExponent (gcentre B.toResolutionInvariant M K s.T i)
          ((E i).get (oldLabel i)) ((π i) z.val) = 0 := by simpa only [if_neg hi] using heps
      simpa only [he, pow_zero, one_mul] using hfactor
  · have hzero := Nat.eq_zero_of_not_pos hn
    have hEmpty := snc_member_empty_of_zero hzero hSNC (oldLabel i)
    have hOldTop : actualLabelledBoundaryTraceIdeal (xs.carrier i) (E i) (oldLabel i)
        ((nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left.base z) = ⊤ := by
      rw [actualLabelledBoundaryTraceIdeal, hEmpty, whole_empty, Ideal.map_top]
    have hTtop : Ideal.map e.toRingHom T = ⊤ := by
      simpa only [hOldTop, Ideal.map_top] using hTot
    have hOldTop' : old = ⊤ := by
      simp only [old, actualLabelledBoundaryTraceIdeal]
      change Ideal.map _ (actualWholeSheafStalkIdeal
        (vanishingIdeal (n := N) (BlowupStrictSubmanifold.geoStrictTransform (π i)
          (gcentre B.toResolutionInvariant M K s.T i) ((E i).get (oldLabel i)))) z.val) = ⊤
      rw [hEmpty]
      simp only [BlowupStrictSubmanifold.geoStrictTransform, empty_sdiff, preimage_empty,
        closure_empty, whole_empty, Ideal.map_top]
    unfold successorStalkIdeal
    split_ifs
    · rw [map_colon_ringEquiv e T Q, hTtop, Submodule.top_colon, hOldTop']
    · exact hTtop.trans hOldTop'.symm

omit [Finite ι] in
private theorem strict_member_coherent (i : ι) :
    (vanishingIdeal (n := N) (BlowupStrictSubmanifold.geoStrictTransform (π i)
      (gcentre B.toResolutionInvariant M K s.T i) ((E i).get (oldLabel i)))).IsCoherent := by
  by_cases hn : 0 < N
  · have ht := B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical
      (hD i) ((nextStage w M B hD hClass H hState K hCover s).T i).2
      ((nextStage w M B hD hClass H hState K hCover s).canonical i)
    have hSNC := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (hD i).isWellFormed ((nextStage w M B hD hClass H hState K hCover s).T i).2 ht).isSNCDivisor
    have hm : BlowupStrictSubmanifold.geoStrictTransform (π i)
        (gcentre B.toResolutionInvariant M K s.T i) ((E i).get (oldLabel i)) ∈
        (geoTransformAlong (M i) ((nextStage w M B hD hClass H hState K hCover s).T i).2).E := by
      rw [next_boundary_eq]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩)
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    have hr := MonomialPart.isClosedSubmanifold_get hn hSNC j
    rw [hj] at hr
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal hr
  · have he := snc_member_empty_of_zero (Nat.eq_zero_of_not_pos hn)
      (current_snc w M B hD s i) (oldLabel i)
    have hs : BlowupStrictSubmanifold.geoStrictTransform (π i)
        (gcentre B.toResolutionInvariant M K s.T i) ((E i).get (oldLabel i)) = ∅ := by
      rw [he]
      simp only [BlowupStrictSubmanifold.geoStrictTransform, empty_sdiff, preimage_empty, closure_empty]
    rw [hs]
    exact VanishingIdealCoherent.isCoherent_vanishingIdeal
      ⟨isClosed_empty, fun _ h => h.elim⟩

include hK in
private theorem centre_range_top_of_not_mem (x : xs.Y.obj.left) (hx : x ∉ C) :
    LinearMap.range (stalkInclusionLinearMap xs.Y.obj.left.toSheafedSpace.sheaf J bJ x) = ⊤ := by
  let U : Opens xs.Y.obj.left.toTopCat :=
    ⟨Cᶜ, (support_isClosed w M B hD hClass H hState K hCover s xs hK).isOpen_compl⟩
  let t : intrinsicReducedCentreSectionIdeal xs.Y.obj.left C U :=
    ⟨1, fun y hy hyC => (hy hyC).elim⟩
  apply (Ideal.eq_top_iff_one _).mpr
  refine ⟨TopCat.Presheaf.germ (J).val.presheaf U x hx t, ?_⟩
  change intrinsicReducedCentreStalkInclusion xs.Y.obj.left C x
    (TopCat.Presheaf.germ (J).val.presheaf U x hx t) = 1
  rw [intrinsicReducedCentreStalkInclusion_germ]
  exact map_one _

private theorem successorStalkIdeal_eq_total_offCentre (y : a.Y.obj.left)
    (hy : a.p.hom.left.base y ∉ C) :
    successorStalkIdeal w M B hD hClass H hState K hCover s xs hK a D bD y =
      nativePulledIdealStalkIdeal a.p.hom.left D bD y := by
  have ht := centre_range_top_of_not_mem w M B hD hClass H hState K hCover s xs hK
    (a.p.hom.left.base y) hy
  simp only [successorStalkIdeal, ht, le_top, ite_true, nativePulledIdealStalkIdeal,
    Ideal.map_top]
  change (nativePulledIdealStalkIdeal a.p.hom.left D bD y).colon Set.univ = _
  exact Submodule.colon_univ

include hOld in
private theorem successor_localModels (y : a.Y.obj.left) :
    HironakaG1NativeStalkIdealSheaf.LocalModelAt
      (successorStalkIdeal w M B hD hClass H hState K hCover s xs hK a D bD) y := by
  rcases HironakaG1CanonicalSuccessorCover.successor_window_or_offCentre
    w M B hD hClass H hState K hCover s xs hK a y with ⟨i, z, hz⟩ | hy
  · let L := (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left
    let j : L ⟶ ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel N)
        (nextAmbient w M B hD hClass H hState K hCover s i) :=
      actualSubspaceInclusion (n := N) (strictTransform N (π i) (xs.carrier i))
    let G := vanishingIdeal (n := N) (BlowupStrictSubmanifold.geoStrictTransform (π i)
      (gcentre B.toResolutionInvariant M K s.T i) ((E i).get (oldLabel i)))
    let A := nativePulledIdealModule j (actualIdealModuleSheaf G) (actualIdealModuleInclusion G)
    let bA := nativePulledIdealInclusion j (actualIdealModuleSheaf G) (actualIdealModuleInclusion G)
    refine ⟨L, (a.map i).hom.left, z, a.isOpenImmersion i, hz, A, bA, ?_⟩
    intro u
    have hcoh := strict_member_coherent w M B hD hClass H hState K hCover s oldLabel i
    change _ = LinearMap.range
      (nativePulledIdealStalkInclusion j (actualIdealModuleSheaf G) (actualIdealModuleInclusion G) u)
    rw [nativePulledIdealStalkInclusion_range]
    change _ = Ideal.map (j.stalkMap u).hom
      (LinearMap.range (stalkInclusionLinearMap _ (actualIdealModuleSheaf G)
        (actualIdealModuleInclusion G) u.val))
    rw [actualIdealModule_stalkRange G hcoh]
    exact window_map_successorStalkIdeal w M B hD hClass H hState K hCover s xs hK a D bD oldLabel hOld i u
  · let U : Opens a.Y.obj.left.toTopCat :=
      ⟨a.p.hom.left.base ⁻¹' Cᶜ,
        (support_isClosed w M B hD hClass H hState K hCover s xs hK).isOpen_compl.preimage
          a.p.hom.left.base.hom.continuous⟩
    let L := a.Y.obj.left.restrict U.isOpenEmbedding
    let f : L ⟶ a.Y.obj.left := a.Y.obj.left.ofRestrict U.isOpenEmbedding
    let T := nativePulledIdealModule a.p.hom.left D bD
    let bT := nativePulledIdealInclusion a.p.hom.left D bD
    let A := nativePulledIdealModule f T bT
    let bA := nativePulledIdealInclusion f T bT
    refine ⟨L, f, ⟨y, hy⟩, inferInstance, rfl, A, bA, ?_⟩
    intro u
    have hP := successorStalkIdeal_eq_total_offCentre w M B hD hClass H hState K hCover s xs hK
      a D bD (f.base u) u.property
    rw [hP]
    change _ = LinearMap.range (nativePulledIdealStalkInclusion f T bT u)
    rw [nativePulledIdealStalkInclusion_range]
    change _ = Ideal.map (f.stalkMap u).hom
      (LinearMap.range (nativePulledIdealStalkInclusion a.p.hom.left D bD (f.base u)))
    rw [nativePulledIdealStalkInclusion_range]

/-- The actual native global old-ideal subsheaf, with original sections,
scalar actions and inclusion. Exact stalks are proved separately below. -/
def successorIdealModule : SheafOfModules.{0} (forgetRing a.Y.obj.left.toSheafedSpace.sheaf) :=
  HironakaG1NativeStalkIdealSheaf.idealModule
    (successorStalkIdeal w M B hD hClass H hState K hCover s xs hK a D bD)

/-- The literal original structure-unit inclusion. -/
def successorIdealInclusion :
    successorIdealModule w M B hD hClass H hState K hCover s xs hK a D bD ⟶
      SheafOfModules.unit _ :=
  HironakaG1NativeStalkIdealSheaf.idealInclusion
    (successorStalkIdeal w M B hD hClass H hState K hCover s xs hK a D bD)

include hOld in
/-- Exact ENTIRE original stalk image, derived from the actual successor
window models and the genuine off-centre native restriction. -/
theorem successorIdeal_stalkRange (y : a.Y.obj.left) :
    LinearMap.range (stalkInclusionLinearMap a.Y.obj.left.toSheafedSpace.sheaf
      (successorIdealModule w M B hD hClass H hState K hCover s xs hK a D bD)
      (successorIdealInclusion w M B hD hClass H hState K hCover s xs hK a D bD) y) =
      successorStalkIdeal w M B hD hClass H hState K hCover s xs hK a D bD y :=
  HironakaG1NativeStalkIdealSheaf.stalkInclusion_range_of_localModels _
    (successor_localModels w M B hD hClass H hState K hCover s xs hK a D bD oldLabel hOld) y

include hOld in
/-- Every actual successor window reads the SAME global old ideal as its
ENTIRE actual strict-old Cartier image, preserving the original old slot. -/
theorem window_stalkIdeal_eq_strictOld (i : ι)
    (z : (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left) :
    nativePulledIdealStalkIdeal (a.map i).hom.left
      (successorIdealModule w M B hD hClass H hState K hCover s xs hK a D bD)
      (successorIdealInclusion w M B hD hClass H hState K hCover s xs hK a D bD) z =
      actualLabelledBoundaryTraceIdeal (strictTransform N (π i) (xs.carrier i))
        [BlowupStrictSubmanifold.geoStrictTransform (π i)
          (gcentre B.toResolutionInvariant M K s.T i) ((E i).get (oldLabel i))] 0 z := by
  change Ideal.map _ (LinearMap.range (stalkInclusionLinearMap _ _ _ _)) = _
  rw [successorIdeal_stalkRange w M B hD hClass H hState K hCover s xs hK a D bD oldLabel hOld]
  exact window_map_successorStalkIdeal w M B hD hClass H hState K hCover s xs hK a D bD oldLabel hOld i z

end
end SGPT.Unibranch.HironakaG1CanonicalOldBoundarySuccessor

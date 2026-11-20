import SGPT.Unibranch.HironakaG1FiniteNativeHistoryComparison
import SGPT.Foundations.Analysis.Pending.HironakaNormalCrossingsFirstStepChartHistory
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceMaps

/-!
# Genuine independent canonical drivers for different ordinary footprint covers

Two drivers on the SAME original atlas are separately computed. Their actual
prefix comparisons, footprint values and centres are constructed by induction
from zero, never supplied at positive clocks. Actual native strict windows and
whole centre ideals retain all original scalar and chronological step maps.

Blueprint FIRST: `hironaka-g1-independent-footprint-drivers.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1IndependentFootprintDrivers

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG11PresLineState
  HironakaG1CanonicalStageCentreIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq MarkedIdealBiholomorphism
  BlowupTowerIsomorphism HironakaNormalCrossingsFirstStepChartHistory
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
open ResolutionInvariantSpec (IsInvDomain)
open HomogenizedGlueingTower (strictAlong)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))

/-- Only ordinary initial footprint/coverage data. There is no stage,
invariant value, centre comparison or future-history field. -/
structure FootprintCover where
  K : ∀ i, Set (w i).ambient
  cover : ∀ i (c : (w i).carrier), c.val ∈ (M i).cosupp →
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ K j ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c
  compact : ∀ i, IsCompact (K i)

variable (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))

include hState in
private theorem initial_cosupp_subset (i : ι) : (M i).cosupp ⊆ (w i).carrier :=
  ((hState i).hsTowerState (BlowupTower.refl : BlowupTower (Amb w i) (Amb w i))
    (by trivial)).2.1

/-- Each ordinary cover computes its OWN actual canonical ambient driver. -/
abbrev stage (P : FootprintCover w M) (n : ℕ) : GStage B.toResolutionInvariant M (mapAdm w) n :=
  HironakaG1FiniteNativeHistoryComparison.ambientStage w M B hD hClass H hState P.K P.cover n

def footValues (P : FootprintCover w M) (n : ℕ) : Set Λ :=
  gfootValues B.toResolutionInvariant M P.K (stage w M B hD hClass H hState P n).T

private abbrev initialId (i : ι) := Diffeomorph.refl 𝓘(ℂ, ComplexModel N) (Amb w i) ∞

include hD in
private theorem pullback_initialId (i : ι) : MarkedIdeal.pullback (initialId w i) (M i) = M i := by
  change MarkedIdeal.pullback (id : Amb w i → Amb w i) (M i) = M i
  exact ContactCanonicalAlong.pullback_id _ (hD i).isWellFormed.isCoherent

variable (P Q : FootprintCover w M)

local notation "SP" => stage w M B hD hClass H hState P
local notation "SQ" => stage w M B hD hClass H hState Q
local notation "VP" => footValues w M B hD hClass H hState P
local notation "VQ" => footValues w M B hD hClass H hState Q

/-- This is produced recursively below; it is never a caller's all-prefix premise. -/
private structure Comparison (n : ℕ) where
  equiv : ∀ i, ((SQ n).T i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ ((SP n).T i).1
  towerIso : ∀ i, IsTowerIso (initialId w i) ((SQ n).T i).2 ((SP n).T i).2 (equiv i)

private theorem comparison_cosupp (n : ℕ)
    (A : Comparison w M B hD hClass H hState P Q n) (i : ι) :
    rcos M (SQ n).T i = A.equiv i ⁻¹' rcos M (SP n).T i := by
  have ht := B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical (hD i) _ ((SP n).canonical i)
  have h := IsTowerIso.cosupp_geoTransformAlong (initialId w i)
    (hD i).isWellFormed.isClosedSubmanifold_N (hD i).isWellFormed.isCoherent (A.towerIso i) ht
  rw [pullback_initialId w M hD i] at h
  exact h

private theorem comparison_value (n : ℕ)
    (A : Comparison w M B hD hClass H hState P Q n) (i : ι) (z : ((SQ n).T i).1)
    (hz : A.equiv i z ∈ rcos M (SP n).T i) :
    rvalue B.toResolutionInvariant M (SQ n).T i z =
      rvalue B.toResolutionInvariant M (SP n).T i (A.equiv i z) := by
  have h := B.toResolutionInvariant.isInvValue.towerIso (initialId w i) (M i) (hD i)
    ((SQ n).T i).2 ((SP n).T i).2 (A.equiv i) (A.towerIso i) ((SP n).canonical i) z hz
  simpa only [pullback_initialId w M hD i] using h

private theorem value_mem_footValues (P : FootprintCover w M) (n : ℕ) (i : ι)
    (z : ((stage w M B hD hClass H hState P n).T i).1)
    (hz : z ∈ rcos M (stage w M B hD hClass H hState P n).T i) :
    rvalue B.toResolutionInvariant M (stage w M B hD hClass H hState P n).T i z ∈
      footValues w M B hD hClass H hState P n :=
  rvalue_mem_gfootValues hD (initial_cosupp_subset w M H hState) P.cover (adm_exists_map w)
    (recordsTransport w M B hD hClass) (stage w M B hD hClass H hState P n) i z hz

private theorem comparison_footValues (n : ℕ)
    (A : Comparison w M B hD hClass H hState P Q n) : VP n = VQ n := by
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨i, y, ⟨hy, -⟩, rfl⟩ := mem_iUnion.mp hv
    let z := (A.equiv i).symm y
    have hzy : A.equiv i z = y := (A.equiv i).apply_symm_apply y
    have hz : z ∈ rcos M (SQ n).T i := by
      rw [comparison_cosupp w M B hD hClass H hState P Q n A i]
      change A.equiv i z ∈ rcos M (SP n).T i
      rwa [hzy]
    have hval := comparison_value w M B hD hClass H hState P Q n A i z (by rwa [hzy])
    have hm := value_mem_footValues w M B hD hClass H hState Q n i z hz
    rw [hval, hzy] at hm
    exact hm
  · intro v hv
    obtain ⟨i, z, ⟨hz, -⟩, rfl⟩ := mem_iUnion.mp hv
    have hy : A.equiv i z ∈ rcos M (SP n).T i := by
      rw [comparison_cosupp w M B hD hClass H hState P Q n A i] at hz
      exact hz
    have hm := value_mem_footValues w M B hD hClass H hState P n i (A.equiv i z) hy
    rw [← comparison_value w M B hD hClass H hState P Q n A i z hy] at hm
    exact hm

private theorem comparison_centre (n : ℕ)
    (A : Comparison w M B hD hClass H hState P Q n) (i : ι) :
    A.equiv i ⁻¹' gcentre B.toResolutionInvariant M P.K (SP n).T i =
      gcentre B.toResolutionInvariant M Q.K (SQ n).T i := by
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    have hcos : z ∈ rcos M (SQ n).T i := by
      rw [comparison_cosupp w M B hD hClass H hState P Q n A i]
      exact hz
    refine ⟨hcos, ?_⟩
    change rvalue B.toResolutionInvariant M (SQ n).T i z ∈ upperBounds (VQ n)
    rw [comparison_value w M B hD hClass H hState P Q n A i z hz,
      ← comparison_footValues w M B hD hClass H hState P Q n A]
    exact hmax
  · rintro ⟨hz, hmax⟩
    have hcos : A.equiv i z ∈ rcos M (SP n).T i := by
      rw [comparison_cosupp w M B hD hClass H hState P Q n A i] at hz
      exact hz
    refine ⟨hcos, ?_⟩
    change rvalue B.toResolutionInvariant M (SP n).T i (A.equiv i z) ∈ upperBounds (VP n)
    rw [← comparison_value w M B hD hClass H hState P Q n A i z hcos,
      comparison_footValues w M B hD hClass H hState P Q n A]
    exact hmax

abbrev ambientStepProjection (P : FootprintCover w M) (n : ℕ) (i : ι) :
    ((stage w M B hD hClass H hState P (n + 1)).T i).1 →
      ((stage w M B hD hClass H hState P n).T i).1 :=
  gnextMap hD (initial_cosupp_subset w M H hState) P.cover (adm_exists_map w)
    (recordsTransport w M B hD hClass) (stage w M B hD hClass H hState P n) i

theorem ambientStepProjection_isBlowup (P : FootprintCover w M) (n : ℕ) (i : ι) :
    IsBlowupAlong N (gcentre B.toResolutionInvariant M P.K (stage w M B hD hClass H hState P n).T i)
      (ambientStepProjection w M B hD hClass H hState P n i) :=
  gnextMap_isBlowup hD (initial_cosupp_subset w M H hState) P.cover (adm_exists_map w)
    (recordsTransport w M B hD hClass) (stage w M B hD hClass H hState P n) i

private theorem nextChoice (n : ℕ) (A : Comparison w M B hD hClass H hState P Q n) (i : ι) :
    ∃ E : ((SQ (n + 1)).T i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ ((SP (n + 1)).T i).1,
      IsTowerIso (A.equiv i)
        (.step .refl _ (ambientStepProjection w M B hD hClass H hState Q n i)
          (ambientStepProjection_isBlowup w M B hD hClass H hState Q n i))
        (.step .refl _ (ambientStepProjection w M B hD hClass H hState P n i)
          (ambientStepProjection_isBlowup w M B hD hClass H hState P n i)) E :=
  exists_oneStep_isTowerIso (A.equiv i)
    (ambientStepProjection_isBlowup w M B hD hClass H hState Q n i)
    (ambientStepProjection_isBlowup w M B hD hClass H hState P n i)
    (comparison_centre w M B hD hClass H hState P Q n A i)

private def nextComparison (n : ℕ) (A : Comparison w M B hD hClass H hState P Q n) :
    Comparison w M B hD hClass H hState P Q (n + 1) where
  equiv i := (nextChoice w M B hD hClass H hState P Q n A i).choose
  towerIso i := IsTowerIso.step (A.towerIso i)
    (ambientStepProjection_isBlowup w M B hD hClass H hState Q n i)
    (ambientStepProjection_isBlowup w M B hD hClass H hState P n i) _
    (fun z => ((nextChoice w M B hD hClass H hState P Q n A i).choose_spec.proj_comm z).symm)
    (comparison_centre w M B hD hClass H hState P Q n A i)

private def comparison : (n : ℕ) → Comparison w M B hD hClass H hState P Q n
  | 0 => ⟨initialId w, fun _ => IsTowerIso.refl⟩
  | n + 1 => nextComparison w M B hD hClass H hState P Q n (comparison n)

/-- Each actual positive-prefix comparison is CONSTRUCTED from clock zero. -/
def ambientIso (n : ℕ) (i : ι) : ((SQ n).T i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯
    ((SP n).T i).1 := (comparison w M B hD hClass H hState P Q n).equiv i

theorem ambientIso_isTowerIso (n : ℕ) (i : ι) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel N) (Amb w i) ∞) ((SQ n).T i).2 ((SP n).T i).2
      (ambientIso w M B hD hClass H hState P Q n i) :=
  (comparison w M B hD hClass H hState P Q n).towerIso i

theorem cosupp_preimage_eq (n : ℕ) (i : ι) : rcos M (SQ n).T i =
    ambientIso w M B hD hClass H hState P Q n i ⁻¹' rcos M (SP n).T i :=
  comparison_cosupp w M B hD hClass H hState P Q n (comparison w M B hD hClass H hState P Q n) i

theorem value_eq (n : ℕ) (i : ι) (z : ((SQ n).T i).1)
    (hz : ambientIso w M B hD hClass H hState P Q n i z ∈ rcos M (SP n).T i) :
    rvalue B.toResolutionInvariant M (SQ n).T i z = rvalue B.toResolutionInvariant M (SP n).T i
      (ambientIso w M B hD hClass H hState P Q n i z) :=
  comparison_value w M B hD hClass H hState P Q n (comparison w M B hD hClass H hState P Q n) i z hz

theorem footValues_eq (n : ℕ) : VP n = VQ n :=
  comparison_footValues w M B hD hClass H hState P Q n (comparison w M B hD hClass H hState P Q n)

theorem centre_preimage_eq (n : ℕ) (i : ι) :
    ambientIso w M B hD hClass H hState P Q n i ⁻¹' gcentre B.toResolutionInvariant M P.K (SP n).T i =
      gcentre B.toResolutionInvariant M Q.K (SQ n).T i :=
  comparison_centre w M B hD hClass H hState P Q n (comparison w M B hD hClass H hState P Q n) i

/-- Actual chronological successor square from the CHOSEN one-step UP lift. -/
theorem ambientIso_successor_square (n : ℕ) (i : ι) (z : ((SQ (n + 1)).T i).1) :
    ambientStepProjection w M B hD hClass H hState P n i (ambientIso w M B hD hClass H hState P Q (n + 1) i z) =
      ambientIso w M B hD hClass H hState P Q n i (ambientStepProjection w M B hD hClass H hState Q n i z) :=
  ((nextChoice w M B hD hClass H hState P Q n
    (comparison w M B hD hClass H hState P Q n) i).choose_spec.proj_comm z).symm

theorem all_cosupp_empty_iff (n : ℕ) :
    (∀ i, rcos M (SP n).T i = ∅) ↔ ∀ i, rcos M (SQ n).T i = ∅ := by
  constructor
  · intro h i
    rw [cosupp_preimage_eq w M B hD hClass H hState P Q n i, h i, preimage_empty]
  · intro h i
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    let z := (ambientIso w M B hD hClass H hState P Q n i).symm y
    have hz : z ∈ rcos M (SQ n).T i := by
      rw [cosupp_preimage_eq w M B hD hClass H hState P Q n i]
      change ambientIso w M B hD hClass H hState P Q n i z ∈ rcos M (SP n).T i
      simpa only [z, Diffeomorph.apply_symm_apply] using hy
    rw [h i] at hz
    exact hz

/-- The ACTUAL iterated strict carrier of the independently generated driver. -/
abbrev strictCarrier (P : FootprintCover w M) (n : ℕ) (i : ι) :
    Set ((stage w M B hD hClass H hState P n).T i).1 :=
  strictAlong ((stage w M B hD hClass H hState P n).T i).2 (w i).carrier

theorem strictCarrier_analytic (P : FootprintCover w M) (n : ℕ) (i : ι) :
    IsComplexAnalyticSubset (n := N) (strictCarrier w M B hD hClass H hState P n i) :=
  ((hState i).hsTowerState ((stage w M B hD hClass H hState P n).T i).2
    (B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical (hD i) _
      ((stage w M B hD hClass H hState P n).canonical i))).1

/-- Actual original native quotient model, including its entire scalar sheaf. -/
abbrev nativeWindow (P : FootprintCover w M) (n : ℕ) (i : ι) : SourceReducedComplexSpace :=
  ofClosedAnalytic (strictCarrier w M B hD hClass H hState P n i)
    (strictCarrier_analytic w M B hD hClass H hState P n i)

private theorem carrier_comparison (n : ℕ) (i : ι) :
    strictCarrier w M B hD hClass H hState Q n i =
      ambientIso w M B hD hClass H hState P Q n i ⁻¹'
        strictCarrier w M B hD hClass H hState P n i := by
  have h := (ambientIso_isTowerIso w M B hD hClass H hState P Q n i).strictAlong_eq (w i).carrier
  change strictCarrier w M B hD hClass H hState Q n i =
    ambientIso w M B hD hClass H hState P Q n i ⁻¹'
      strictCarrier w M B hD hClass H hState P n i at h
  exact h

/-- Native isomorphism is induced by the SAME actually constructed ambient lift. -/
def nativeWindowIso (n : ℕ) (i : ι) : nativeWindow w M B hD hClass H hState Q n i ≅
    nativeWindow w M B hD hClass H hState P n i := by
  let hC := fun z => Set.ext_iff.mp (carrier_comparison w M B hD hClass H hState P Q n i) z
  let E := actualSubspaceBiholomorphicIso (ambientIso w M B hD hClass H hState P Q n i)
    (strictCarrier w M B hD hClass H hState Q n i)
    (strictCarrier w M B hD hClass H hState P n i) hC
  exact ObjectProperty.isoMk _ (Over.isoMk E
    (actualSubspaceMap_point (ambientIso w M B hD hClass H hState P Q n i).contMDiff
      (fun z hz => (hC z).mp hz)))

theorem nativeWindowIso_point (n : ℕ) (i : ι)
    (z : strictCarrier w M B hD hClass H hState Q n i) :
    ((nativeWindowIso w M B hD hClass H hState P Q n i).hom.hom.left.base z).val =
      ambientIso w M B hD hClass H hState P Q n i z.val := rfl

/-- The FULL native projection to the SAME actual initial window model. -/
def nativeProjection (P : FootprintCover w M) (n : ℕ) (i : ι) :
    nativeWindow w M B hD hClass H hState P n i ⟶ ofClosedAnalytic (w i).carrier (w i).analytic :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap ((stage w M B hD hClass H hState P n).T i).2.contMDiff_proj
      (fun _ hz => MemberInterTowerAlong.strictAlong_subset_preimage
        ((stage w M B hD hClass H hState P n).T i).2 (w i).analytic.isClosed hz))
    (actualSubspaceMap_point _ _))

theorem nativeProjection_square (n : ℕ) (i : ι) :
    (nativeWindowIso w M B hD hClass H hState P Q n i).hom ≫
        nativeProjection w M B hD hClass H hState P n i =
      nativeProjection w M B hD hClass H hState Q n i := by
  apply morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  change ((SP n).T i).2.proj (ambientIso w M B hD hClass H hState P Q n i z.val) =
    ((SQ n).T i).2.proj z.val
  exact ((ambientIso_isTowerIso w M B hD hClass H hState P Q n i).proj_comm z.val).symm

private theorem next_maps_to (P : FootprintCover w M) (n : ℕ) (i : ι) :
    ∀ z ∈ strictCarrier w M B hD hClass H hState P (n + 1) i,
      ambientStepProjection w M B hD hClass H hState P n i z ∈ strictCarrier w M B hD hClass H hState P n i := by
  intro z hz
  exact BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
    (ambientStepProjection_isBlowup w M B hD hClass H hState P n i).contMDiff.continuous
    (strictCarrier_analytic w M B hD hClass H hState P n i).isClosed hz

/-- The actual chronological native projection, retaining every empty/Cartier step. -/
def nativeStepProjection (P : FootprintCover w M) (n : ℕ) (i : ι) :
    nativeWindow w M B hD hClass H hState P (n + 1) i ⟶
      nativeWindow w M B hD hClass H hState P n i :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (ambientStepProjection_isBlowup w M B hD hClass H hState P n i).contMDiff
      (next_maps_to w M B hD hClass H hState P n i))
    (actualSubspaceMap_point _ _))

/-- FULL native successor square, derived from the actual one-step ambient UP lift. -/
theorem nativeStepProjection_square (n : ℕ) (i : ι) :
    (nativeWindowIso w M B hD hClass H hState P Q (n + 1) i).hom ≫
        nativeStepProjection w M B hD hClass H hState P n i =
      nativeStepProjection w M B hD hClass H hState Q n i ≫
        (nativeWindowIso w M B hD hClass H hState P Q n i).hom := by
  apply morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  change ambientStepProjection w M B hD hClass H hState P n i
      (ambientIso w M B hD hClass H hState P Q (n + 1) i z.val) =
    ambientIso w M B hD hClass H hState P Q n i (ambientStepProjection w M B hD hClass H hState Q n i z.val)
  exact ambientIso_successor_square w M B hD hClass H hState P Q n i z.val

/-- The actual current canonical centre trace on the SAME native strict window. -/
def nativeCentreTrace (P : FootprintCover w M) (n : ℕ) (i : ι) :
    Set (nativeWindow w M B hD hClass H hState P n i).obj.left :=
  (Subtype.val : strictCarrier w M B hD hClass H hState P n i → _) ⁻¹'
    gcentre B.toResolutionInvariant M P.K (stage w M B hD hClass H hState P n).T i

theorem nativeCentre_preimage_eq (n : ℕ) (i : ι) :
    (nativeWindowIso w M B hD hClass H hState P Q n i).hom.hom.left.base ⁻¹'
        nativeCentreTrace w M B hD hClass H hState P n i =
      nativeCentreTrace w M B hD hClass H hState Q n i := by
  ext z
  exact Set.ext_iff.mp (centre_preimage_eq w M B hD hClass H hState P Q n i) z.val

private theorem nativeWindowIso_isOpen (n : ℕ) (i : ι) : LocallyRingedSpace.IsOpenImmersion
    (nativeWindowIso w M B hD hClass H hState P Q n i).hom.hom.left := by
  have : IsIso (nativeWindowIso w M B hD hClass H hState P Q n i).hom.hom.left := by
    change IsIso (isoLeft (nativeWindowIso w M B hD hClass H hState P Q n i)).hom
    infer_instance
  infer_instance

abbrev nativeCentreIdeal (P : FootprintCover w M) (n : ℕ) (i : ι) := intrinsicReducedCentreIdealModule
  (nativeWindow w M B hD hClass H hState P n i).obj.left
  (nativeCentreTrace w M B hD hClass H hState P n i)
abbrev nativeCentreInclusion (P : FootprintCover w M) (n : ℕ) (i : ι) := intrinsicReducedCentreIdealInclusion
  (nativeWindow w M B hD hClass H hState P n i).obj.left
  (nativeCentreTrace w M B hD hClass H hState P n i)

/-- ENTIRE native unit submodule equality in the actual current-window scalars. -/
theorem nativeCentreSubmodule_eq (n : ℕ) (i : ι) :
    nativePulledIdealSubmodule (nativeWindowIso w M B hD hClass H hState P Q n i).hom.hom.left
        (nativeCentreIdeal w M B hD hClass H hState P n i) (nativeCentreInclusion w M B hD hClass H hState P n i) =
      intrinsicReducedCentreSubmodule (nativeWindow w M B hD hClass H hState Q n i).obj.left
        (nativeCentreTrace w M B hD hClass H hState Q n i) := by
  have := nativeWindowIso_isOpen w M B hD hClass H hState P Q n i
  rw [openImmersion_pulled_submodule_eq]
  exact congrArg (intrinsicReducedCentreSubmodule
    (nativeWindow w M B hD hClass H hState Q n i).obj.left)
      (nativeCentre_preimage_eq w M B hD hClass H hState P Q n i)

/-- EVERY original section ideal on the actual current native window. -/
theorem nativeCentreSectionIdeal_eq (n : ℕ) (i : ι)
    (V : Opens (nativeWindow w M B hD hClass H hState Q n i).obj.left.toTopCat) :
    nativePulledIdealSectionIdeal (nativeWindowIso w M B hD hClass H hState P Q n i).hom.hom.left
        (nativeCentreIdeal w M B hD hClass H hState P n i) (nativeCentreInclusion w M B hD hClass H hState P n i) V =
      intrinsicReducedCentreSectionIdeal (nativeWindow w M B hD hClass H hState Q n i).obj.left
        (nativeCentreTrace w M B hD hClass H hState Q n i) V := by
  have := nativeWindowIso_isOpen w M B hD hClass H hState P Q n i
  rw [openImmersion_pulled_sectionIdeal_eq]
  exact congrArg (fun C => intrinsicReducedCentreSectionIdeal
    (nativeWindow w M B hD hClass H hState Q n i).obj.left C V)
      (nativeCentre_preimage_eq w M B hD hClass H hState P Q n i)

/-- The ENTIRE native stalk-image ideal, retaining the actual scalar ring map. -/
theorem nativeCentreStalkIdeal_eq (n : ℕ) (i : ι)
    (z : (nativeWindow w M B hD hClass H hState Q n i).obj.left) :
    nativePulledIdealStalkIdeal (nativeWindowIso w M B hD hClass H hState P Q n i).hom.hom.left
        (nativeCentreIdeal w M B hD hClass H hState P n i) (nativeCentreInclusion w M B hD hClass H hState P n i) z =
      intrinsicCentreStalkRange (nativeWindow w M B hD hClass H hState Q n i).obj.left
        (nativeCentreTrace w M B hD hClass H hState Q n i) z := by
  have := nativeWindowIso_isOpen w M B hD hClass H hState P Q n i
  rw [openImmersion_pulled_stalkIdeal_eq]
  exact congrArg (fun C => intrinsicCentreStalkRange
    (nativeWindow w M B hD hClass H hState Q n i).obj.left C z)
      (nativeCentre_preimage_eq w M B hD hClass H hState P Q n i)

end
end SGPT.Unibranch.HironakaG1IndependentFootprintDrivers

import SGPT.Unibranch.HironakaG1UnionNativeHistories

/-!
# Actual bijective atlas reindex drivers and global native histories

Both independent drivers are compared from zero. The index bijection is used
on ordinary original presentations and footprints only; no computed driver
or positive-prefix equality is supplied. Blueprint FIRST:
`hironaka-g1-atlas-permutation.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1AtlasPermutation

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG11PresLineState
  HironakaG1CanonicalStageCentreIdeal HironakaG1IndependentFootprintDrivers
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism BlowupTowerIsomorphism
  HironakaNormalCrossingsFirstStepChartHistory HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11SingularCentreModification SmoothCentreModification
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk HironakaG11NativeTowerRepresentation
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι κ : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))

/-- Actual original atlas composed with the given index bijection. -/
abbrev permutedWindows (σ : κ ≃ ι) : κ → DimEmbedding X N := fun i => w (σ i)

/-- Entire original records, without rewriting or recomputing their invariants. -/
abbrev permutedRecords (σ : κ ≃ ι) : ∀ i, MarkedIdeal N (Amb (permutedWindows w σ) i) := fun i => M (σ i)

variable (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (σ : κ ≃ ι) (P : FootprintCover w M)

include hClass in
/-- Genuine INITIAL class data are reindexed only. -/
theorem permutedClass : InitialClassData (permutedWindows w σ) (permutedRecords w M σ) :=
  HironakaG1CanonicalStageChoiceIndependence.reindexClass w M hClass σ

/-- Ordinary cover transported by actual bijectivity, no future-stage fields. -/
def permutedCover : FootprintCover (permutedWindows w σ) (permutedRecords w M σ) where
  K i := P.K (σ i)
  cover i c hc := by
    obtain ⟨j, z, hz, hzc⟩ := P.cover (σ i) c hc
    obtain ⟨a, rfl⟩ := σ.surjective j
    exact ⟨a, z, hz, hzc⟩
  compact i := P.compact (σ i)

abbrev permutedStage (n : ℕ) := stage (permutedWindows w σ) (permutedRecords w M σ) B
  (fun i => hD (σ i)) (permutedClass w M hClass σ) (fun i => H (σ i))
  (fun i => hState (σ i)) (permutedCover w M σ P) n

abbrev originalStage (n : ℕ) := stage w M B hD hClass H hState P n

local notation "SS" => permutedStage w M B hD hClass H hState σ P
local notation "SU" => originalStage w M B hD hClass H hState P

abbrev permutedFootValues (n : ℕ) : Set Λ :=
  gfootValues B.toResolutionInvariant (permutedRecords w M σ) (permutedCover w M σ P).K (SS n).T
abbrev originalFootValues (n : ℕ) : Set Λ :=
  gfootValues B.toResolutionInvariant M P.K (SU n).T

private abbrev initialId (i : κ) := Diffeomorph.refl 𝓘(ℂ, ComplexModel N) (Amb (permutedWindows w σ) i) ∞

private structure Comparison (n : ℕ) where
  equiv : ∀ i, ((SU n).T (σ i)).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ ((SS n).T i).1
  towerIso : ∀ i, IsTowerIso (initialId w σ i) ((SU n).T (σ i)).2 ((SS n).T i).2 (equiv i)

include hD in
private theorem pullback_initialId (i : κ) :
    MarkedIdeal.pullback (initialId w σ i) (M (σ i)) = M (σ i) := by
  change MarkedIdeal.pullback (id : Amb w (σ i) → Amb w (σ i)) (M (σ i)) = _
  exact ContactCanonicalAlong.pullback_id _ (hD (σ i)).isWellFormed.isCoherent

private theorem comparison_cosupp (n : ℕ) (A : Comparison w M B hD hClass H hState σ P n) (i : κ) :
    rcos M (SU n).T (σ i) = A.equiv i ⁻¹' rcos (permutedRecords w M σ) (SS n).T i := by
  have ht := B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical
    (hD (σ i)) _ ((SS n).canonical i)
  have h := IsTowerIso.cosupp_geoTransformAlong (initialId w σ i)
    (hD (σ i)).isWellFormed.isClosedSubmanifold_N
    (hD (σ i)).isWellFormed.isCoherent (A.towerIso i) ht
  rw [pullback_initialId w M hD σ i] at h
  exact h

private theorem comparison_value (n : ℕ) (A : Comparison w M B hD hClass H hState σ P n) (i : κ)
    (z : ((SU n).T (σ i)).1) (hz : A.equiv i z ∈ rcos (permutedRecords w M σ) (SS n).T i) :
    rvalue B.toResolutionInvariant M (SU n).T (σ i) z =
      rvalue B.toResolutionInvariant (permutedRecords w M σ) (SS n).T i (A.equiv i z) := by
  have h := B.toResolutionInvariant.isInvValue.towerIso (initialId w σ i) (M (σ i)) (hD (σ i))
    ((SU n).T (σ i)).2 ((SS n).T i).2 (A.equiv i) (A.towerIso i) ((SS n).canonical i) z hz
  simpa only [pullback_initialId w M hD σ i] using h

private theorem comparison_proj (n : ℕ) (A : Comparison w M B hD hClass H hState σ P n) (i : κ)
    (z : ((SU n).T (σ i)).1) :
    ((SU n).T (σ i)).2.proj z = ((SS n).T i).2.proj (A.equiv i z) :=
  (A.towerIso i).proj_comm z

private theorem comparison_values (n : ℕ) (A : Comparison w M B hD hClass H hState σ P n) : permutedFootValues w M B hD hClass H hState σ P n = originalFootValues w M B hD hClass H hState P n := by
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨i, y, ⟨hy, hyK⟩, rfl⟩ := mem_iUnion.mp hv
    let z := (A.equiv i).symm y
    have hzy : A.equiv i z = y := (A.equiv i).apply_symm_apply y
    have hz : z ∈ rcos M (SU n).T (σ i) := by
      rw [comparison_cosupp w M B hD hClass H hState σ P n A i]
      change A.equiv i z ∈ rcos (permutedRecords w M σ) (SS n).T i
      rwa [hzy]
    refine mem_iUnion.mpr ⟨σ i, z, ⟨hz, ?_⟩, ?_⟩
    · change ((SU n).T (σ i)).2.proj z ∈ P.K (σ i)
      rw [comparison_proj w M B hD hClass H hState σ P n A i z, hzy]
      exact hyK
    · rw [comparison_value w M B hD hClass H hState σ P n A i z (by rwa [hzy]), hzy]
  · intro v hv
    obtain ⟨a, z, ⟨hz, hzK⟩, hv⟩ := mem_iUnion.mp hv
    obtain ⟨i, rfl⟩ := σ.surjective a
    have hy : A.equiv i z ∈ rcos (permutedRecords w M σ) (SS n).T i := by
      rw [comparison_cosupp w M B hD hClass H hState σ P n A i] at hz
      exact hz
    refine mem_iUnion.mpr ⟨i, A.equiv i z, ⟨hy, ?_⟩, ?_⟩
    · change ((SS n).T i).2.proj (A.equiv i z) ∈ P.K (σ i)
      exact (comparison_proj w M B hD hClass H hState σ P n A i z) ▸ hzK
    · exact (comparison_value w M B hD hClass H hState σ P n A i z hy).symm.trans hv

private theorem comparison_centre (n : ℕ) (A : Comparison w M B hD hClass H hState σ P n) (i : κ) :
    A.equiv i ⁻¹' gcentre B.toResolutionInvariant (permutedRecords w M σ) (permutedCover w M σ P).K (SS n).T i =
      gcentre B.toResolutionInvariant M (P).K (SU n).T (σ i) := by
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    have hc : z ∈ rcos M (SU n).T (σ i) := by
      rw [comparison_cosupp w M B hD hClass H hState σ P n A i]
      exact hz
    refine ⟨hc, ?_⟩
    change rvalue B.toResolutionInvariant M (SU n).T (σ i) z ∈ upperBounds (originalFootValues w M B hD hClass H hState P n)
    rw [comparison_value w M B hD hClass H hState σ P n A i z hz,
      ← comparison_values w M B hD hClass H hState σ P n A]
    exact hmax
  · rintro ⟨hz, hmax⟩
    have hc : A.equiv i z ∈ rcos (permutedRecords w M σ) (SS n).T i := by
      rw [comparison_cosupp w M B hD hClass H hState σ P n A i] at hz
      exact hz
    refine ⟨hc, ?_⟩
    change rvalue B.toResolutionInvariant (permutedRecords w M σ) (SS n).T i (A.equiv i z) ∈ upperBounds (permutedFootValues w M B hD hClass H hState σ P n)
    rw [← comparison_value w M B hD hClass H hState σ P n A i z hc,
      comparison_values w M B hD hClass H hState σ P n A]
    exact hmax

abbrev permutedStepProjection (n : ℕ) (i : κ) : ((SS (n + 1)).T i).1 → ((SS n).T i).1 :=
  ambientStepProjection (permutedWindows w σ) (permutedRecords w M σ) B (fun i => hD (σ i))
    (permutedClass w M hClass σ) (fun i => H (σ i)) (fun i => hState (σ i))
    (permutedCover w M σ P) n i

abbrev originalStepProjection (n : ℕ) (i : κ) :
    ((SU (n + 1)).T (σ i)).1 → ((SU n).T (σ i)).1 :=
  ambientStepProjection w M B hD hClass H hState (P) n (σ i)

private theorem nextChoice (n : ℕ) (A : Comparison w M B hD hClass H hState σ P n) (i : κ) :
    ∃ E : ((SU (n + 1)).T (σ i)).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ ((SS (n + 1)).T i).1,
      IsTowerIso (A.equiv i)
        (.step .refl _ (originalStepProjection w M B hD hClass H hState σ P n i)
          (ambientStepProjection_isBlowup w M B hD hClass H hState (P) n (σ i)))
        (.step .refl _ (permutedStepProjection w M B hD hClass H hState σ P n i)
          (ambientStepProjection_isBlowup (permutedWindows w σ) (permutedRecords w M σ) B
            (fun i => hD (σ i)) (permutedClass w M hClass σ) (fun i => H (σ i))
            (fun i => hState (σ i)) (permutedCover w M σ P) n i)) E :=
  exists_oneStep_isTowerIso (A.equiv i)
    (ambientStepProjection_isBlowup w M B hD hClass H hState (P) n (σ i))
    (ambientStepProjection_isBlowup (permutedWindows w σ) (permutedRecords w M σ) B
      (fun i => hD (σ i)) (permutedClass w M hClass σ) (fun i => H (σ i))
      (fun i => hState (σ i)) (permutedCover w M σ P) n i)
    (comparison_centre w M B hD hClass H hState σ P n A i)

private def nextComparison (n : ℕ) (A : Comparison w M B hD hClass H hState σ P n) :
    Comparison w M B hD hClass H hState σ P (n + 1) where
  equiv i := (nextChoice w M B hD hClass H hState σ P n A i).choose
  towerIso i := IsTowerIso.step (A.towerIso i)
    (ambientStepProjection_isBlowup w M B hD hClass H hState (P) n (σ i))
    (ambientStepProjection_isBlowup (permutedWindows w σ) (permutedRecords w M σ) B
      (fun i => hD (σ i)) (permutedClass w M hClass σ) (fun i => H (σ i))
      (fun i => hState (σ i)) (permutedCover w M σ P) n i) _
    (fun z => ((nextChoice w M B hD hClass H hState σ P n A i).choose_spec.proj_comm z).symm)
    (comparison_centre w M B hD hClass H hState σ P n A i)

private def comparison : (n : ℕ) → Comparison w M B hD hClass H hState σ P n
  | 0 => ⟨initialId w σ, fun _ => IsTowerIso.refl⟩
  | n + 1 => nextComparison w M B hD hClass H hState σ P n (comparison n)

def permutedAmbientIso (n : ℕ) (i : κ) :
    ((SU n).T (σ i)).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ ((SS n).T i).1 :=
  (comparison w M B hD hClass H hState σ P n).equiv i

theorem permutedAmbientIso_isTowerIso (n : ℕ) (i : κ) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel N) (Amb (permutedWindows w σ) i) ∞)
      ((SU n).T (σ i)).2 ((SS n).T i).2 (permutedAmbientIso w M B hD hClass H hState σ P n i) :=
  (comparison w M B hD hClass H hState σ P n).towerIso i

theorem footValues_eq (n : ℕ) : permutedFootValues w M B hD hClass H hState σ P n = originalFootValues w M B hD hClass H hState P n :=
  comparison_values w M B hD hClass H hState σ P n (comparison w M B hD hClass H hState σ P n)

theorem permuted_centre_preimage_eq (n : ℕ) (i : κ) :
    permutedAmbientIso w M B hD hClass H hState σ P n i ⁻¹'
        gcentre B.toResolutionInvariant (permutedRecords w M σ) (permutedCover w M σ P).K (SS n).T i =
      gcentre B.toResolutionInvariant M (P).K (SU n).T (σ i) :=
  comparison_centre w M B hD hClass H hState σ P n (comparison w M B hD hClass H hState σ P n) i

theorem permuted_successor_square (n : ℕ) (i : κ) (z : ((SU (n + 1)).T (σ i)).1) :
    permutedStepProjection w M B hD hClass H hState σ P n i
        (permutedAmbientIso w M B hD hClass H hState σ P (n + 1) i z) =
      permutedAmbientIso w M B hD hClass H hState σ P n i
        (originalStepProjection w M B hD hClass H hState σ P n i z) :=
  ((nextChoice w M B hD hClass H hState σ P n (comparison w M B hD hClass H hState σ P n) i).choose_spec.proj_comm z).symm


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


local notation "WS" => permutedWindows w σ
local notation "MS" => permutedRecords w M σ
local notation "DS" => (fun i => hD (σ i))
local notation "CS" => permutedClass w M hClass σ
local notation "HS" => (fun i => H (σ i))
local notation "NS" => (fun i => hState (σ i))
local notation "PS" => permutedCover w M σ P
local notation "PU" => P
local notation "jS" => HironakaG1IndependentNativeHistories.windowMap WS MS B DS CS HS NS PS
local notation "jU" => HironakaG1IndependentNativeHistories.windowMap w M B hD hClass H hState P

private theorem carrier_comparison (n : ℕ) (i : κ) :
    strictCarrier w M B hD hClass H hState PU n (σ i) =
      permutedAmbientIso w M B hD hClass H hState σ P n i ⁻¹' strictCarrier WS MS B DS CS HS NS PS n i := by
  have h := (permutedAmbientIso_isTowerIso w M B hD hClass H hState σ P n i).strictAlong_eq
    (w (σ i)).carrier
  change strictCarrier w M B hD hClass H hState PU n (σ i) =
    permutedAmbientIso w M B hD hClass H hState σ P n i ⁻¹' strictCarrier WS MS B DS CS HS NS PS n i at h
  exact h

/-- The ACTUAL native quotient-window iso induced by the produced permuted prefix lift. -/
def permutedWindowIso (n : ℕ) (i : κ) : nativeWindow w M B hD hClass H hState PU n (σ i) ≅
    nativeWindow WS MS B DS CS HS NS PS n i := by
  let hC := fun z => Set.ext_iff.mp (carrier_comparison w M B hD hClass H hState σ P n i) z
  let E := actualSubspaceBiholomorphicIso (permutedAmbientIso w M B hD hClass H hState σ P n i)
    (strictCarrier w M B hD hClass H hState PU n (σ i)) (strictCarrier WS MS B DS CS HS NS PS n i) hC
  exact ObjectProperty.isoMk _ (Over.isoMk E
    (actualSubspaceMap_point (permutedAmbientIso w M B hD hClass H hState σ P n i).contMDiff
      (fun z hz => (hC z).mp hz)))

theorem permutedWindowIso_point (n : ℕ) (i : κ)
    (z : strictCarrier w M B hD hClass H hState PU n (σ i)) :
    ((permutedWindowIso w M B hD hClass H hState σ P n i).hom.hom.left.base z).val =
      permutedAmbientIso w M B hD hClass H hState σ P n i z.val := rfl

theorem permuted_nativeProjection_square (n : ℕ) (i : κ) :
    (permutedWindowIso w M B hD hClass H hState σ P n i).hom ≫ nativeProjection WS MS B DS CS HS NS PS n i =
      nativeProjection w M B hD hClass H hState PU n (σ i) := by
  apply morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  change ((SS n).T i).2.proj (permutedAmbientIso w M B hD hClass H hState σ P n i z.val) =
    ((SU n).T (σ i)).2.proj z.val
  exact ((permutedAmbientIso_isTowerIso w M B hD hClass H hState σ P n i).proj_comm z.val).symm

theorem permuted_nativeCentre_preimage_eq (n : ℕ) (i : κ) :
    (permutedWindowIso w M B hD hClass H hState σ P n i).hom.hom.left.base ⁻¹'
        nativeCentreTrace WS MS B DS CS HS NS PS n i =
      nativeCentreTrace w M B hD hClass H hState PU n (σ i) := by
  ext z
  exact Set.ext_iff.mp (permuted_centre_preimage_eq w M B hD hClass H hState σ P n i) z.val

/-- Actual permuted current native window maps, reusing the full original normalizations. -/
abbrev permuted_windowMap (n : ℕ) (xs : XStage WS (SS n).T) (i : κ) := jS n xs i

/-- Only actual original windows are normalized; no whole-stage cover is assumed. -/
abbrev original_windowMap (n : ℕ) (ys : XStage w (SU n).T) (i : κ) := jU n ys (σ i)

abbrev permutedCentre (n : ℕ) (xs : XStage WS (SS n).T) : Set xs.Y.obj.left :=
  HironakaG1IndependentNativeHistories.actualCentre WS MS B DS CS HS NS PS n xs

abbrev originalCentre (n : ℕ) (ys : XStage w (SU n).T) : Set ys.Y.obj.left :=
  HironakaG1IndependentNativeHistories.actualCentre w M B hD hClass H hState PU n ys

/-- Surjectivity reindexes the ACTUAL full centre image-union, not a whole-stage cover. -/
theorem original_centre_mem_iff (n : ℕ) (ys : XStage w (SU n).T) (x : ys.Y.obj.left) :
    x ∈ originalCentre w M B hD hClass H hState P n ys ↔
      ∃ i : κ, ∃ z ∈ nativeCentreTrace w M B hD hClass H hState P n (σ i),
        (jU n ys (σ i)).hom.left.base z = x := by
  constructor
  · intro hx
    obtain ⟨a, z, hz, hzx⟩ :=
      (HironakaG1IndependentNativeHistories.actualCentre_mem_iff w M B hD hClass H hState P n ys x).mp hx
    obtain ⟨i, rfl⟩ := σ.surjective a
    exact ⟨i, z, hz, hzx⟩
  · rintro ⟨i, z, hz, hzx⟩
    exact (HironakaG1IndependentNativeHistories.actualCentre_mem_iff w M B hD hClass H hState P n ys x).mpr
      ⟨σ i, z, hz, hzx⟩

section StageComparison

variable (n : ℕ)
  (xs : XStage (permutedWindows w σ) (permutedStage w M B hD hClass H hState σ P n).T)
  (ys : XStage w (originalStage w M B hD hClass H hState P n).T)
  (e : ys.Y ≅ xs.Y) (he : e.hom ≫ xs.q = ys.q)

include he in
/-- A preceding global iso is an induction field ONLY; the full permuted
current-window agreement is derived on the same actual original window. -/
theorem current_window_square (i : κ) :
    jU n ys (σ i) ≫ e.hom = (permutedWindowIso w M B hD hClass H hState σ P n i).hom ≫ jS n xs i := by
  let E := permutedWindowIso w M B hD hClass H hState σ P n i
  have := iso_isOpen E
  have := HironakaG1IndependentNativeHistories.windowMap_isOpen WS MS B DS CS HS NS PS n xs i
  have hG : LocallyRingedSpace.IsOpenImmersion (E.hom ≫ jS n xs i).hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (E.hom.hom.left ≫ (jS n xs i).hom.left)
    infer_instance
  apply nativeLift_eq xs.isSingularCentreModification _ _ hG
  calc
    (jU n ys (σ i) ≫ e.hom) ≫ xs.q = jU n ys (σ i) ≫ ys.q := by rw [Category.assoc, he]
    _ = nativeProjection w M B hD hClass H hState PU n (σ i) ≫
        EmbeddedBlowupOverlap.chartMorphism (w (σ i)).toLocalEmbedding :=
      HironakaG1IndependentNativeHistories.windowMap_original_square w M B hD hClass H hState PU n ys (σ i)
    _ = E.hom ≫ (nativeProjection WS MS B DS CS HS NS PS n i ≫
        EmbeddedBlowupOverlap.chartMorphism (WS i).toLocalEmbedding) := by
      rw [← Category.assoc, permuted_nativeProjection_square]
    _ = (E.hom ≫ jS n xs i) ≫ xs.q := by
      simpa only [Category.assoc] using (congrArg (fun t => E.hom ≫ t)
        (HironakaG1IndependentNativeHistories.windowMap_original_square WS MS B DS CS HS NS PS n xs i)).symm

include he in
theorem global_centre_preimage_eq :
    e.hom.hom.left.base ⁻¹' permutedCentre w M B hD hClass H hState σ P n xs =
      originalCentre w M B hD hClass H hState P n ys := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, zS, hzS, hSx⟩ :=
      (HironakaG1IndependentNativeHistories.actualCentre_mem_iff WS MS B DS CS HS NS PS n xs
        (e.hom.hom.left.base x)).mp hx
    let E := permutedWindowIso w M B hD hClass H hState σ P n i
    obtain ⟨zU, hU⟩ := (isoHomeomorph E).surjective zS
    have hzU : zU ∈ nativeCentreTrace w M B hD hClass H hState PU n (σ i) := by
      apply (Set.ext_iff.mp (permuted_nativeCentre_preimage_eq w M B hD hClass H hState σ P n i) zU).mp
      change E.hom.hom.left.base zU ∈ nativeCentreTrace WS MS B DS CS HS NS PS n i
      exact hU.symm ▸ hzS
    apply (original_centre_mem_iff w M B hD hClass H hState σ P n ys x).mpr
    refine ⟨i, zU, hzU, ?_⟩
    apply (isoHomeomorph e).injective
    exact (congrArg (fun t => t.hom.left.base zU)
      (current_window_square w M B hD hClass H hState σ P n xs ys e he i)).trans
      ((congrArg (fun z => (jS n xs i).hom.left.base z) hU).trans hSx)
  · intro hx
    obtain ⟨i, zU, hzU, hUx⟩ := (original_centre_mem_iff w M B hD hClass H hState σ P n ys x).mp hx
    apply (HironakaG1IndependentNativeHistories.actualCentre_mem_iff WS MS B DS CS HS NS PS n xs
      (e.hom.hom.left.base x)).mpr
    refine ⟨i, (permutedWindowIso w M B hD hClass H hState σ P n i).hom.hom.left.base zU, ?_, ?_⟩
    · exact (Set.ext_iff.mp (permuted_nativeCentre_preimage_eq w M B hD hClass H hState σ P n i) zU).mpr hzU
    · exact (congrArg (fun t => t.hom.left.base zU)
        (current_window_square w M B hD hClass H hState σ P n xs ys e he i)).symm.trans
          (congrArg e.hom.hom.left.base hUx)

local notation "CSEL" => permutedCentre w M B hD hClass H hState σ P n xs
local notation "CUNION" => originalCentre w M B hD hClass H hState P n ys

include he in
theorem wholeCentreSubmodule_eq : nativePulledIdealSubmodule e.hom.hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left CSEL)
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left CSEL) =
    intrinsicReducedCentreSubmodule ys.Y.obj.left CUNION := by
  have := iso_isOpen e
  rw [openImmersion_pulled_submodule_eq]
  exact congrArg (intrinsicReducedCentreSubmodule ys.Y.obj.left)
    (global_centre_preimage_eq w M B hD hClass H hState σ P n xs ys e he)

include he in
theorem wholeCentreStalkIdeal_eq (y : ys.Y.obj.left) : nativePulledIdealStalkIdeal e.hom.hom.left
      (intrinsicReducedCentreIdealModule xs.Y.obj.left CSEL)
      (intrinsicReducedCentreIdealInclusion xs.Y.obj.left CSEL) y =
    intrinsicCentreStalkRange ys.Y.obj.left CUNION y := by
  have := iso_isOpen e
  rw [openImmersion_pulled_stalkIdeal_eq]
  exact congrArg (fun C => intrinsicCentreStalkRange ys.Y.obj.left C y)
    (global_centre_preimage_eq w M B hD hClass H hState σ P n xs ys e he)

variable [Finite κ]
  (a : HironakaG1CanonicalStageSuccessor.Successor (permutedWindows w σ) (permutedRecords w M σ) B
    (fun i => hD (σ i)) (permutedClass w M hClass σ) (fun i => H (σ i))
    (fun i => hState (σ i)) (permutedCover w M σ P).K (permutedCover w M σ P).cover
    (permutedStage w M B hD hClass H hState σ P n) xs (permutedCover w M σ P).compact)

include he in
private theorem other_isIdealBlowup : IsIdealBlowup (a.p ≫ e.inv)
    (intrinsicReducedCentreIdealModule ys.Y.obj.left CUNION)
    (intrinsicReducedCentreIdealInclusion ys.Y.obj.left CUNION) := by
  have h := isIdealBlowup_comp_baseIso CSEL a.isIdealBlowup e
  rw [global_centre_preimage_eq w M B hD hClass H hState σ P n xs ys e he] at h
  exact h

variable [Finite ι]
  (b : HironakaG1CanonicalStageSuccessor.Successor w M B hD hClass H hState
    P.K P.cover (originalStage w M B hD hClass H hState P n) ys
    P.compact)

include he in
private theorem successor_exists : ∃ E : b.Y ≅ a.Y,
    E.hom ≫ (a.p ≫ e.inv) = b.p ∧ ∀ t : b.Y ⟶ a.Y, t ≫ (a.p ≫ e.inv) = b.p → t = E.hom :=
  RIsoAModification.isIdealBlowup_exists_unique_iso b.isIdealBlowup
    (other_isIdealBlowup w M B hD hClass H hState σ P n xs ys e he a)

/-- The actual GLOBAL permutation successor comparison. -/
def successorIso : b.Y ≅ a.Y :=
  (successor_exists w M B hD hClass H hState σ P n xs ys e he a b).choose

theorem successorIso_projection :
    (successorIso w M B hD hClass H hState σ P n xs ys e he a b).hom ≫ a.p = b.p ≫ e.hom := by
  have h := congrArg (fun t => t ≫ e.hom)
    (successor_exists w M B hD hClass H hState σ P n xs ys e he a b).choose_spec.1
  simpa only [successorIso, Category.assoc, e.inv_hom_id, Category.comp_id] using h

theorem successorIso_original_projection :
    (successorIso w M B hD hClass H hState σ P n xs ys e he a b).hom ≫ a.toXStage.q = b.toXStage.q := by
  change _ ≫ (a.p ≫ xs.q) = b.p ≫ ys.q
  rw [← Category.assoc, successorIso_projection, Category.assoc, he]

end StageComparison

section Histories

variable [Finite κ]

/-- The existing ACTUAL finite native histories on the permuted original atlas. -/
abbrev PermutedHistory (n : ℕ) (xs : XStage WS (SS n).T) : Prop :=
  HironakaG1IndependentNativeHistories.NativeHistory WS MS B DS CS HS NS PS n xs

variable [Finite ι]

/-- The existing ACTUAL finite native histories on the original atlas. -/
abbrev OriginalHistory (n : ℕ) (ys : XStage w (SU n).T) : Prop :=
  HironakaG1IndependentNativeHistories.NativeHistory w M B hD hClass H hState PU n ys

/-- Both genuine native constructions exist from the ordinary INITIAL data alone. -/
theorem exists_native_histories (n : ℕ) : ∃ xs ys,
    PermutedHistory w M B hD hClass H hState σ P n xs ∧ OriginalHistory w M B hD hClass H hState P n ys := by
  obtain ⟨xs, hx⟩ := HironakaG1IndependentNativeHistories.exists_native_history WS MS B DS CS HS NS PS n
  obtain ⟨ys, hy⟩ := HironakaG1IndependentNativeHistories.exists_native_history w M B hD hClass H hState PU n
  exact ⟨xs, ys, hx, hy⟩

/-- Genuine induction of TWO actual finite histories with genuinely DIFFERENT index types;
the global comparison is produced from original identity, not an input packet. -/
theorem exists_global_history_iso {n : ℕ} {xs : XStage WS (SS n).T} {ys : XStage w (SU n).T}
    (hx : PermutedHistory w M B hD hClass H hState σ P n xs)
    (hy : OriginalHistory w M B hD hClass H hState P n ys) :
    ∃ E : ys.Y ≅ xs.Y, E.hom ≫ xs.q = ys.q := by
  induction hx with
  | zero =>
    cases hy
    exact ⟨Iso.refl X, Category.id_comp _⟩
  | @step n xs hx a ih =>
    cases hy with
    | @step _ ys hy b =>
      obtain ⟨e, he⟩ := ih hy
      exact ⟨successorIso w M B hD hClass H hState σ P n xs ys e he a b,
        successorIso_original_projection w M B hD hClass H hState σ P n xs ys e he a b⟩

variable {n : ℕ}
  {xs : XStage (permutedWindows w σ) (permutedStage w M B hD hClass H hState σ P n).T}
  {ys : XStage w (originalStage w M B hD hClass H hState P n).T}
  (hx : PermutedHistory w M B hD hClass H hState σ P n xs)
  (hy : OriginalHistory w M B hD hClass H hState P n ys)

/-- The actual full GLOBAL native isomorphism produced by that finite induction. -/
def globalHistoryIso : ys.Y ≅ xs.Y :=
  (exists_global_history_iso w M B hD hClass H hState σ P hx hy).choose

theorem globalHistoryIso_projection :
    (globalHistoryIso w M B hD hClass H hState σ P hx hy).hom ≫ xs.q = ys.q :=
  (exists_global_history_iso w M B hD hClass H hState σ P hx hy).choose_spec

/-- Full native over-original uniqueness, with no whole-stage window cover assumption. -/
theorem globalHistoryHom_unique (t : ys.Y ⟶ xs.Y) (ht : t ≫ xs.q = ys.q) :
    t = (globalHistoryIso w M B hD hClass H hState σ P hx hy).hom := by
  apply nativeLift_eq xs.isSingularCentreModification _ _
    (iso_isOpen (globalHistoryIso w M B hD hClass H hState σ P hx hy))
  exact ht.trans (globalHistoryIso_projection w M B hD hClass H hState σ P hx hy).symm

theorem globalHistoryIso_window_square (i : κ) :
    jU n ys (σ i) ≫ (globalHistoryIso w M B hD hClass H hState σ P hx hy).hom =
      (permutedWindowIso w M B hD hClass H hState σ P n i).hom ≫ jS n xs i :=
  current_window_square w M B hD hClass H hState σ P n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState σ P hx hy) i

/-- Actual GLOBAL centre equality at the from-zero produced comparison. -/
theorem globalHistoryIso_centre_preimage_eq :
    (globalHistoryIso w M B hD hClass H hState σ P hx hy).hom.hom.left.base ⁻¹'
        permutedCentre w M B hD hClass H hState σ P n xs = originalCentre w M B hD hClass H hState P n ys :=
  global_centre_preimage_eq w M B hD hClass H hState σ P n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState σ P hx hy)

/-- ENTIRE global centre ideal transport in the actual original native scalars. -/
theorem globalHistoryIso_wholeCentreSubmodule_eq :
    nativePulledIdealSubmodule (globalHistoryIso w M B hD hClass H hState σ P hx hy).hom.hom.left
        (intrinsicReducedCentreIdealModule xs.Y.obj.left (permutedCentre w M B hD hClass H hState σ P n xs))
        (intrinsicReducedCentreIdealInclusion xs.Y.obj.left (permutedCentre w M B hD hClass H hState σ P n xs)) =
      intrinsicReducedCentreSubmodule ys.Y.obj.left (originalCentre w M B hD hClass H hState P n ys) :=
  wholeCentreSubmodule_eq w M B hD hClass H hState σ P n xs ys _
    (globalHistoryIso_projection w M B hD hClass H hState σ P hx hy)

end Histories


end
end SGPT.Unibranch.HironakaG1AtlasPermutation

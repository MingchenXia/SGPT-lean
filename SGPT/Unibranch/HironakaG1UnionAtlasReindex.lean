import SGPT.Unibranch.HironakaG1IndependentFootprintDrivers
import SGPT.Unibranch.HironakaG1CanonicalStageChoiceIndependence

/-!
# Selected original subcover versus its genuine inactive union extension

The auxiliary footprints are literally EMPTY. Selected-prefix comparisons and
actual footprint/centre equalities are produced recursively from zero. The
actual GLOBAL union centre is then proved to be covered by selected centre
images using the held exists_footprint theorem, never a full XStage cover.

Blueprint FIRST: `hironaka-g1-union-atlas-reindex.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1UnionAtlasReindex

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG11PresLineState
  HironakaG1CanonicalStageCentreIdeal HironakaG1IndependentFootprintDrivers
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism BlowupTowerIsomorphism
  HironakaNormalCrossingsFirstStepChartHistory
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {κ ν : Type*} (w : κ ⊕ ν → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))

/-- SAME original selected windows; no new presentation or transformed record. -/
abbrev selectedWindows : κ → DimEmbedding X N :=
  HironakaG1CanonicalStageChoiceIndependence.windows w Sum.inl

abbrev selectedRecords : ∀ i, MarkedIdeal N (Amb (selectedWindows w) i) :=
  HironakaG1CanonicalStageChoiceIndependence.records w M Sum.inl

/-- Ordinary INITIAL selected-side footprint coverage of union cosupports.
No current value, centre, isomorphism or future-history comparison field. -/
structure SelectedFootprints where
  K : ∀ i : κ, Set (w (Sum.inl i)).ambient
  cover : ∀ a (c : (w a).carrier), c.val ∈ (M a).cosupp →
    ∃ i : κ, ∃ c' : (w (Sum.inl i)).carrier, c'.val ∈ K i ∧
      (w (Sum.inl i)).toLocalEmbedding.toPoint c' = (w a).toLocalEmbedding.toPoint c
  compact : ∀ i, IsCompact (K i)

variable (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : (κ ⊕ ν) → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))

include hClass in
/-- Only the genuine INITIAL class data are restricted. -/
theorem selectedClass : InitialClassData (selectedWindows w) (selectedRecords w M) :=
  HironakaG1CanonicalStageChoiceIndependence.reindexClass w M hClass Sum.inl

def selectedCover (P : SelectedFootprints w M) : FootprintCover (selectedWindows w) (selectedRecords w M) where
  K := P.K
  cover i := P.cover (Sum.inl i)
  compact := P.compact

/-- The union extension has genuinely INACTIVE, literal empty auxiliary footprints. -/
def unionCover (P : SelectedFootprints w M) : FootprintCover w M where
  K a := match a with
    | Sum.inl i => P.K i
    | Sum.inr _ => ∅
  cover a c hc := by
    obtain ⟨i, c', hi, he⟩ := P.cover a c hc
    exact ⟨Sum.inl i, c', hi, he⟩
  compact a := by
    cases a with
    | inl i => exact P.compact i
    | inr _ => exact isCompact_empty

abbrev selectedStage (P : SelectedFootprints w M) (n : ℕ) :
    GStage B.toResolutionInvariant (selectedRecords w M) (mapAdm (selectedWindows w)) n :=
  HironakaG1IndependentFootprintDrivers.stage (selectedWindows w) (selectedRecords w M) B
    (fun i => hD (Sum.inl i)) (selectedClass w M hClass) (fun i => H (Sum.inl i))
    (fun i => hState (Sum.inl i)) (selectedCover w M P) n

abbrev unionStage (P : SelectedFootprints w M) (n : ℕ) : GStage B.toResolutionInvariant M (mapAdm w) n :=
  HironakaG1IndependentFootprintDrivers.stage w M B hD hClass H hState (unionCover w M P) n

variable (P : SelectedFootprints w M)

local notation "SS" => selectedStage w M B hD hClass H hState P
local notation "SU" => unionStage w M B hD hClass H hState P
abbrev selectedFootValues (n : ℕ) : Set Λ :=
  gfootValues B.toResolutionInvariant (selectedRecords w M) P.K (SS n).T
abbrev unionFootValues (n : ℕ) : Set Λ :=
  gfootValues B.toResolutionInvariant M (unionCover w M P).K (SU n).T

private abbrev initialId (i : κ) := Diffeomorph.refl 𝓘(ℂ, ComplexModel N) (Amb (selectedWindows w) i) ∞

private structure Comparison (n : ℕ) where
  equiv : ∀ i, ((SU n).T (Sum.inl i)).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ ((SS n).T i).1
  towerIso : ∀ i, IsTowerIso (initialId w i) ((SU n).T (Sum.inl i)).2 ((SS n).T i).2 (equiv i)

include hD in
private theorem pullback_initialId (i : κ) :
    MarkedIdeal.pullback (initialId w i) (M (Sum.inl i)) = M (Sum.inl i) := by
  change MarkedIdeal.pullback (id : Amb w (Sum.inl i) → Amb w (Sum.inl i)) (M (Sum.inl i)) = _
  exact ContactCanonicalAlong.pullback_id _ (hD (Sum.inl i)).isWellFormed.isCoherent

private theorem comparison_cosupp (n : ℕ) (A : Comparison w M B hD hClass H hState P n) (i : κ) :
    rcos M (SU n).T (Sum.inl i) = A.equiv i ⁻¹' rcos (selectedRecords w M) (SS n).T i := by
  have ht := B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical
    (hD (Sum.inl i)) _ ((SS n).canonical i)
  have h := IsTowerIso.cosupp_geoTransformAlong (initialId w i)
    (hD (Sum.inl i)).isWellFormed.isClosedSubmanifold_N
    (hD (Sum.inl i)).isWellFormed.isCoherent (A.towerIso i) ht
  rw [pullback_initialId w M hD i] at h
  exact h

private theorem comparison_value (n : ℕ) (A : Comparison w M B hD hClass H hState P n) (i : κ)
    (z : ((SU n).T (Sum.inl i)).1) (hz : A.equiv i z ∈ rcos (selectedRecords w M) (SS n).T i) :
    rvalue B.toResolutionInvariant M (SU n).T (Sum.inl i) z =
      rvalue B.toResolutionInvariant (selectedRecords w M) (SS n).T i (A.equiv i z) := by
  have h := B.toResolutionInvariant.isInvValue.towerIso (initialId w i) (M (Sum.inl i)) (hD (Sum.inl i))
    ((SU n).T (Sum.inl i)).2 ((SS n).T i).2 (A.equiv i) (A.towerIso i) ((SS n).canonical i) z hz
  simpa only [pullback_initialId w M hD i] using h

private theorem comparison_proj (n : ℕ) (A : Comparison w M B hD hClass H hState P n) (i : κ)
    (z : ((SU n).T (Sum.inl i)).1) :
    ((SU n).T (Sum.inl i)).2.proj z = ((SS n).T i).2.proj (A.equiv i z) :=
  (A.towerIso i).proj_comm z

private theorem comparison_values (n : ℕ) (A : Comparison w M B hD hClass H hState P n) : selectedFootValues w M B hD hClass H hState P n = unionFootValues w M B hD hClass H hState P n := by
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨i, y, ⟨hy, hyK⟩, rfl⟩ := mem_iUnion.mp hv
    let z := (A.equiv i).symm y
    have hzy : A.equiv i z = y := (A.equiv i).apply_symm_apply y
    have hz : z ∈ rcos M (SU n).T (Sum.inl i) := by
      rw [comparison_cosupp w M B hD hClass H hState P n A i]
      change A.equiv i z ∈ rcos (selectedRecords w M) (SS n).T i
      rwa [hzy]
    refine mem_iUnion.mpr ⟨Sum.inl i, z, ⟨hz, ?_⟩, ?_⟩
    · change ((SU n).T (Sum.inl i)).2.proj z ∈ P.K i
      rw [comparison_proj w M B hD hClass H hState P n A i z, hzy]
      exact hyK
    · rw [comparison_value w M B hD hClass H hState P n A i z (by rwa [hzy]), hzy]
  · intro v hv
    obtain ⟨a, z, ⟨hz, hzK⟩, hv⟩ := mem_iUnion.mp hv
    cases a with
    | inr j => exact False.elim hzK
    | inl i =>
      have hy : A.equiv i z ∈ rcos (selectedRecords w M) (SS n).T i := by
        rw [comparison_cosupp w M B hD hClass H hState P n A i] at hz
        exact hz
      refine mem_iUnion.mpr ⟨i, A.equiv i z, ⟨hy, ?_⟩, ?_⟩
      · change ((SS n).T i).2.proj (A.equiv i z) ∈ P.K i
        exact (comparison_proj w M B hD hClass H hState P n A i z) ▸ hzK
      · exact (comparison_value w M B hD hClass H hState P n A i z hy).symm.trans hv

private theorem comparison_centre (n : ℕ) (A : Comparison w M B hD hClass H hState P n) (i : κ) :
    A.equiv i ⁻¹' gcentre B.toResolutionInvariant (selectedRecords w M) P.K (SS n).T i =
      gcentre B.toResolutionInvariant M (unionCover w M P).K (SU n).T (Sum.inl i) := by
  ext z
  constructor
  · rintro ⟨hz, hmax⟩
    have hc : z ∈ rcos M (SU n).T (Sum.inl i) := by
      rw [comparison_cosupp w M B hD hClass H hState P n A i]
      exact hz
    refine ⟨hc, ?_⟩
    change rvalue B.toResolutionInvariant M (SU n).T (Sum.inl i) z ∈ upperBounds (unionFootValues w M B hD hClass H hState P n)
    rw [comparison_value w M B hD hClass H hState P n A i z hz,
      ← comparison_values w M B hD hClass H hState P n A]
    exact hmax
  · rintro ⟨hz, hmax⟩
    have hc : A.equiv i z ∈ rcos (selectedRecords w M) (SS n).T i := by
      rw [comparison_cosupp w M B hD hClass H hState P n A i] at hz
      exact hz
    refine ⟨hc, ?_⟩
    change rvalue B.toResolutionInvariant (selectedRecords w M) (SS n).T i (A.equiv i z) ∈ upperBounds (selectedFootValues w M B hD hClass H hState P n)
    rw [← comparison_value w M B hD hClass H hState P n A i z hc,
      comparison_values w M B hD hClass H hState P n A]
    exact hmax

abbrev selectedStepProjection (n : ℕ) (i : κ) : ((SS (n + 1)).T i).1 → ((SS n).T i).1 :=
  ambientStepProjection (selectedWindows w) (selectedRecords w M) B (fun i => hD (Sum.inl i))
    (selectedClass w M hClass) (fun i => H (Sum.inl i)) (fun i => hState (Sum.inl i))
    (selectedCover w M P) n i

abbrev unionSelectedStepProjection (n : ℕ) (i : κ) :
    ((SU (n + 1)).T (Sum.inl i)).1 → ((SU n).T (Sum.inl i)).1 :=
  ambientStepProjection w M B hD hClass H hState (unionCover w M P) n (Sum.inl i)

private theorem nextChoice (n : ℕ) (A : Comparison w M B hD hClass H hState P n) (i : κ) :
    ∃ E : ((SU (n + 1)).T (Sum.inl i)).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ ((SS (n + 1)).T i).1,
      IsTowerIso (A.equiv i)
        (.step .refl _ (unionSelectedStepProjection w M B hD hClass H hState P n i)
          (ambientStepProjection_isBlowup w M B hD hClass H hState (unionCover w M P) n (Sum.inl i)))
        (.step .refl _ (selectedStepProjection w M B hD hClass H hState P n i)
          (ambientStepProjection_isBlowup (selectedWindows w) (selectedRecords w M) B
            (fun i => hD (Sum.inl i)) (selectedClass w M hClass) (fun i => H (Sum.inl i))
            (fun i => hState (Sum.inl i)) (selectedCover w M P) n i)) E :=
  exists_oneStep_isTowerIso (A.equiv i)
    (ambientStepProjection_isBlowup w M B hD hClass H hState (unionCover w M P) n (Sum.inl i))
    (ambientStepProjection_isBlowup (selectedWindows w) (selectedRecords w M) B
      (fun i => hD (Sum.inl i)) (selectedClass w M hClass) (fun i => H (Sum.inl i))
      (fun i => hState (Sum.inl i)) (selectedCover w M P) n i)
    (comparison_centre w M B hD hClass H hState P n A i)

private def nextComparison (n : ℕ) (A : Comparison w M B hD hClass H hState P n) :
    Comparison w M B hD hClass H hState P (n + 1) where
  equiv i := (nextChoice w M B hD hClass H hState P n A i).choose
  towerIso i := IsTowerIso.step (A.towerIso i)
    (ambientStepProjection_isBlowup w M B hD hClass H hState (unionCover w M P) n (Sum.inl i))
    (ambientStepProjection_isBlowup (selectedWindows w) (selectedRecords w M) B
      (fun i => hD (Sum.inl i)) (selectedClass w M hClass) (fun i => H (Sum.inl i))
      (fun i => hState (Sum.inl i)) (selectedCover w M P) n i) _
    (fun z => ((nextChoice w M B hD hClass H hState P n A i).choose_spec.proj_comm z).symm)
    (comparison_centre w M B hD hClass H hState P n A i)

private def comparison : (n : ℕ) → Comparison w M B hD hClass H hState P n
  | 0 => ⟨initialId w, fun _ => IsTowerIso.refl⟩
  | n + 1 => nextComparison w M B hD hClass H hState P n (comparison n)

def selectedAmbientIso (n : ℕ) (i : κ) :
    ((SU n).T (Sum.inl i)).1 ≃ₘ⟮𝓘(ℂ, ComplexModel N), 𝓘(ℂ, ComplexModel N)⟯ ((SS n).T i).1 :=
  (comparison w M B hD hClass H hState P n).equiv i

theorem selectedAmbientIso_isTowerIso (n : ℕ) (i : κ) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel N) (Amb (selectedWindows w) i) ∞)
      ((SU n).T (Sum.inl i)).2 ((SS n).T i).2 (selectedAmbientIso w M B hD hClass H hState P n i) :=
  (comparison w M B hD hClass H hState P n).towerIso i

theorem footValues_eq (n : ℕ) : selectedFootValues w M B hD hClass H hState P n = unionFootValues w M B hD hClass H hState P n :=
  comparison_values w M B hD hClass H hState P n (comparison w M B hD hClass H hState P n)

theorem selected_centre_preimage_eq (n : ℕ) (i : κ) :
    selectedAmbientIso w M B hD hClass H hState P n i ⁻¹'
        gcentre B.toResolutionInvariant (selectedRecords w M) P.K (SS n).T i =
      gcentre B.toResolutionInvariant M (unionCover w M P).K (SU n).T (Sum.inl i) :=
  comparison_centre w M B hD hClass H hState P n (comparison w M B hD hClass H hState P n) i

theorem selected_successor_square (n : ℕ) (i : κ) (z : ((SU (n + 1)).T (Sum.inl i)).1) :
    selectedStepProjection w M B hD hClass H hState P n i
        (selectedAmbientIso w M B hD hClass H hState P (n + 1) i z) =
      selectedAmbientIso w M B hD hClass H hState P n i
        (unionSelectedStepProjection w M B hD hClass H hState P n i z) :=
  ((nextChoice w M B hD hClass H hState P n (comparison w M B hD hClass H hState P n) i).choose_spec.proj_comm z).symm

/-- The actual UNION centre is exactly the selected-side centre-image union,
derived via existing footprint lifting; selected windows need not cover XStage. -/
theorem selected_centre_support_eq (n : ℕ) (xs : XStage w (SU n).T) :
    HironakaG1CanonicalStageCentreIdeal.support w M B hD hClass H hState
        (unionCover w M P).K (unionCover w M P).cover (SU n) xs =
      ⋃ i : κ, (xs.map (Sum.inl i)).hom.left.base ''
        ((Subtype.val : xs.carrier (Sum.inl i) → ((SU n).T (Sum.inl i)).1) ⁻¹'
          gcentre B.toResolutionInvariant M (unionCover w M P).K (SU n).T (Sum.inl i)) := by
  let F := HironakaG1CanonicalStageCentreIdeal.localCentres w M B hD hClass H hState
    (unionCover w M P).K (unionCover w M P).cover (SU n) xs
  have hcos : ∀ a, (M a).cosupp ⊆ (w a).carrier := fun a =>
    ((hState a).hsTowerState (BlowupTower.refl : BlowupTower (Amb w a) (Amb w a)) (by trivial)).2.1
  ext x
  constructor
  · intro hx
    obtain ⟨a, y, hy, hyx⟩ := F.mem_support.mp hx
    obtain ⟨j, z, hzK, hzy, hzc⟩ := xs.exists_footprint hD hcos (unionCover w M P).cover
      (recordsTransport w M B hD hClass) (SU n) a y hy.1
    cases j with
    | inr j => exact False.elim hzK
    | inl i => exact mem_iUnion.mpr ⟨i, z, hzc.mpr hy, hzy.trans hyx⟩
  · intro hx
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
    exact F.mem_support.mpr ⟨Sum.inl i, z, hz, hzx⟩

theorem selected_centre_window_cover (n : ℕ) (xs : XStage w (SU n).T) :
    HironakaG1CanonicalStageCentreIdeal.support w M B hD hClass H hState
        (unionCover w M P).K (unionCover w M P).cover (SU n) xs ⊆
      ⋃ i : κ, range (xs.map (Sum.inl i)).hom.left.base := by
  intro x hx
  rw [selected_centre_support_eq w M B hD hClass H hState P n xs] at hx
  obtain ⟨i, z, -, hzx⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨i, z, hzx⟩

end
end SGPT.Unibranch.HironakaG1UnionAtlasReindex

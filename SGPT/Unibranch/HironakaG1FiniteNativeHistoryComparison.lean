import SGPT.Unibranch.HironakaG1CanonicalStageIsoTransport

/-!
# Genuine finite native comparison by induction from ordinary initial data

The held ambient driver derives its canonical prefix comparisons from the
initial full class data. Finite native histories start at the original space
and take actual Successor outputs. Their native comparison is then proved by
induction, with no caller current/future-prefix compatibility certificate.

Blueprint FIRST: `hironaka-g1-finite-native-history-comparison.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1FiniteNativeHistoryComparison

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG11PresLineState
  HironakaG1CanonicalStageCentreIdeal HironakaG1CanonicalStageIsoTransport
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism HironakaIntrinsicComplexAnalyticRegularLocus
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (K : ∀ i, Set (w i).ambient)
  (hCover : ∀ i (c : (w i).carrier), c.val ∈ (M i).cosupp →
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ K j ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)

include hState in
private theorem initial_cosupp_subset (i : ι) : (M i).cosupp ⊆ (w i).carrier :=
  ((hState i).hsTowerState (BlowupTower.refl : BlowupTower (Amb w i) (Amb w i))
    (by trivial)).2.1

/-- The existing actual canonical ambient driver, with its transport input
DERIVED from the ordinary initial class data, not supplied by a caller. -/
abbrev ambientStage (n : ℕ) : GStage B.toResolutionInvariant M (mapAdm w) n :=
  gstage B.toResolutionInvariant M (mapAdm w) K hD
    (initial_cosupp_subset w M H hState) hCover (adm_exists_map w)
    (recordsTransport w M B hD hClass) n

variable [Finite ι] (hK : ∀ i, IsCompact (K i))

/-- Actual finite construction cases ONLY: original zero stage, or a genuine
native successor of a preceding finite construction. No comparison field. -/
inductive History : (n : ℕ) → XStage w (ambientStage w M B hD hClass H hState K hCover n).T → Prop
  | zero : History 0 (XStage.zero w)
  | step {n : ℕ} {xs : XStage w (ambientStage w M B hD hClass H hState K hCover n).T}
      (h : History n xs)
      (a : HironakaG1CanonicalStageSuccessor.Successor w M B hD hClass H hState K hCover
        (ambientStage w M B hD hClass H hState K hCover n) xs hK) :
      History (n + 1) a.toXStage

/-- Every finite clock is realised from ordinary initial data alone. -/
theorem exists_history (n : ℕ) :
    ∃ xs, History w M B hD hClass H hState K hCover hK n xs := by
  induction n with
  | zero => exact ⟨XStage.zero w, History.zero⟩
  | succ n ih =>
    obtain ⟨xs, hx⟩ := ih
    obtain ⟨a⟩ := HironakaG1CanonicalStageSuccessor.exists_successor
      w M B hD hClass H hState K hCover (ambientStage w M B hD hClass H hState K hCover n) xs hK
    exact ⟨a.toXStage, History.step hx a⟩

/-- Genuine finite induction from zero; no prefix isomorphism is a caller input. -/
theorem exists_history_iso {n : ℕ}
    {xs ys : XStage w (ambientStage w M B hD hClass H hState K hCover n).T}
    (hx : History w M B hD hClass H hState K hCover hK n xs)
    (hy : History w M B hD hClass H hState K hCover hK n ys) :
    ∃ e : xs.Y ≅ ys.Y, e.hom ≫ ys.q = xs.q := by
  induction hx with
  | zero =>
    cases hy
    exact ⟨Iso.refl X, Category.id_comp _⟩
  | @step n xs hx a ih =>
    cases hy with
    | @step _ ys hy b =>
      obtain ⟨e, he⟩ := ih hy
      exact ⟨successorIso w M B hD hClass H hState K hCover
          (ambientStage w M B hD hClass H hState K hCover n) xs ys e he hK a b,
        successorIso_original_projection w M B hD hClass H hState K hCover
          (ambientStage w M B hD hClass H hState K hCover n) xs ys e he hK a b⟩

variable {n : ℕ}
  {xs ys : XStage w (ambientStage w M B hD hClass H hState K hCover n).T}
  (hx : History w M B hD hClass H hState K hCover hK n xs)
  (hy : History w M B hD hClass H hState K hCover hK n ys)

/-- The comparison actually produced by the preceding finite induction. -/
def comparisonIso : xs.Y ≅ ys.Y :=
  (exists_history_iso w M B hD hClass H hState K hCover hK hx hy).choose

theorem comparisonIso_projection :
    (comparisonIso w M B hD hClass H hState K hCover hK hx hy).hom ≫ ys.q = xs.q :=
  (exists_history_iso w M B hD hClass H hState K hCover hK hx hy).choose_spec

/-- Uniqueness as a FULL original morphism over the initial original space. -/
theorem comparisonHom_unique (t : xs.Y ⟶ ys.Y) (ht : t ≫ ys.q = xs.q) :
    t = (comparisonIso w M B hD hClass H hState K hCover hK hx hy).hom := by
  let e := comparisonIso w M B hD hClass H hState K hCover hK hx hy
  have : IsIso e.hom.hom.left := by
    change IsIso (isoLeft e).hom
    infer_instance
  have he : LocallyRingedSpace.IsOpenImmersion e.hom.hom.left := inferInstance
  have hcomp : t ≫ ys.q = e.hom ≫ ys.q :=
    ht.trans (comparisonIso_projection w M B hD hClass H hState K hCover hK hx hy).symm
  have hint : interior (ys.q.hom.left.base ⁻¹' (intrinsicRegularLocus X.obj)ᶜ) = ∅ :=
    ys.isSingularCentreModification.interior_preimage_intrinsicSingularLocus
  have hpoints := HironakaG11LiftUniqueness.eq_of_comp_eq_of_isOpenMap
    ys.isSingularCentreModification.isIsoOver_intrinsicRegularLocus hint
    t.hom.left.base.hom.continuous e.hom.hom.left.base.hom.continuous he.base_open.isOpenMap
    (fun z => congrArg (fun f => f.hom.left.base z) hcomp)
  exact morphism_eq_of_pointwise_eq t e.hom (fun z => congrFun hpoints z)

/-- Every full original current-window square is now DERIVED at every finite clock. -/
theorem comparisonIso_window_square (i : ι) :
    xs.map i ≫ (comparisonIso w M B hD hClass H hState K hCover hK hx hy).hom =
      (windowIso w (ambientStage w M B hD hClass H hState K hCover n).T xs ys i).hom ≫ ys.map i :=
  window_square w _ xs ys _
    (comparisonIso_projection w M B hD hClass H hState K hCover hK hx hy) i

/-- Three arbitrary actual finite native choices satisfy the triple cocycle. -/
theorem comparisonIso_cocycle
    {zs : XStage w (ambientStage w M B hD hClass H hState K hCover n).T}
    (hz : History w M B hD hClass H hState K hCover hK n zs) :
    (comparisonIso w M B hD hClass H hState K hCover hK hx hy).trans
        (comparisonIso w M B hD hClass H hState K hCover hK hy hz) =
      comparisonIso w M B hD hClass H hState K hCover hK hx hz := by
  apply Iso.ext
  apply comparisonHom_unique w M B hD hClass H hState K hCover hK hx hz
  change ((comparisonIso w M B hD hClass H hState K hCover hK hx hy).hom ≫
    (comparisonIso w M B hD hClass H hState K hCover hK hy hz).hom) ≫ zs.q = xs.q
  rw [Category.assoc, comparisonIso_projection]
  exact comparisonIso_projection w M B hD hClass H hState K hCover hK hx hy

variable [WellFoundedLT Λ]

include hK in
private theorem termination : ∃ n, ∀ i,
    rcos M (ambientStage w M B hD hClass H hState K hCover n).T i = ∅ :=
  exists_gstage_cosupp_eq_empty hD (initial_cosupp_subset w M H hState) hCover (adm_exists_map w)
    (recordsTransport w M B hD hClass) hK

/-- The first ACTUAL cosupport-exhaustion clock; isomorphic/Cartier steps are not deleted. -/
def stoppingTime : ℕ := by
  classical
  exact Nat.find (termination w M B hD hClass H hState K hCover hK)

theorem stoppingTime_cosupp (i : ι) :
    rcos M (ambientStage w M B hD hClass H hState K hCover
      (stoppingTime w M B hD hClass H hState K hCover hK)).T i = ∅ :=
  by
    classical
    exact Nat.find_spec (termination w M B hD hClass H hState K hCover hK) i

/-- An actual native finite history resolves all SAME original marked records
at the common true stopping clock, retaining the full ordered step/birth clocks. -/
theorem exists_stopped_history : ∃ xs,
    History w M B hD hClass H hState K hCover hK
        (stoppingTime w M B hD hClass H hState K hCover hK) xs ∧
      ∀ i, IsGeoResolution (M i)
        ((ambientStage w M B hD hClass H hState K hCover
          (stoppingTime w M B hD hClass H hState K hCover hK)).T i).2 := by
  obtain ⟨xs, hx⟩ := exists_history w M B hD hClass H hState K hCover hK
    (stoppingTime w M B hD hClass H hState K hCover hK)
  refine ⟨xs, hx, fun i => ⟨?_, stoppingTime_cosupp w M B hD hClass H hState K hCover hK i⟩⟩
  exact B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical (hD i) _
    ((ambientStage w M B hD hClass H hState K hCover
      (stoppingTime w M B hD hClass H hState K hCover hK)).canonical i)

end
end SGPT.Unibranch.HironakaG1FiniteNativeHistoryComparison

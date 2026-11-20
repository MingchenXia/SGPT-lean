import SGPT.Unibranch.HironakaG1CanonicalStageSuccessor
import SGPT.Foundations.Analysis.Pending.HironakaNativePulledIdealComposition
import SGPT.Foundations.Analysis.Pending.HironakaG10ChowGermIdealDictionary
import SGPT.Foundations.Analysis.Pending.HironakaNormalCrossingsOriginalExponents
import SGPT.Foundations.Analysis.Pending.HironakaActualIntrinsicLabelledBoundaryIdeals

/-!
# The whole born Cartier image ideal at the SAME actual canonical successor

The actual successor square and the entire same-stage centre ideal derive
the native born ideal agreement. The held whole subspace pullback and
exceptional-ideal equality are reused, including Cartier-centre steps.
No boundary-ideal equality, overlap frame or future history is input.

Blueprint FIRST: `hironaka-g1-canonical-born-boundary-ideal.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Opposite
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1CanonicalBornBoundaryIdeal

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  HironakaG1CanonicalStageSuccessor BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSeq MarkedIdealBiholomorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealComposition HironakaG10ChowGermIdealDictionary
  HironakaActualAnalyticSubspace HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSingularSubspaceBlowupCartier
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
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)

local notation "C" => support w M B hD hClass H hState K hCover s xs
local notation "J" => intrinsicReducedCentreIdealModule xs.Y.obj.left C
local notation "bJ" => intrinsicReducedCentreIdealInclusion xs.Y.obj.left C
local notation "π" => nextProjection w M B hD hClass H hState K hCover s
/-- The full ordered boundary of the prescribed next original record. -/
abbrev nextBoundary (i : ι) : List (Set (nextAmbient w M B hD hClass H hState K hCover s i)) :=
  (geoTransformAlong (M i) ((nextStage w M B hD hClass H hState K hCover s).T i).2).E

local notation "E₊" => nextBoundary w M B hD hClass H hState K hCover s

/-- The original last label is retained, including an empty born member. -/
def bornLabel (i : ι) : Fin (E₊ i).length :=
  ⟨(geoTransformAlong (M i) (s.T i).2).E.length, by
    change _ < (geoTransformAlong (M i)
      ((nextStage w M B hD hClass H hState K hCover s).T i).2).E.length
    rw [next_boundary_eq w M B hD hClass H hState K hCover s i]
    simp⟩

/-- The literal actual next record selects the actual exceptional member. -/
theorem bornLabel_get (i : ι) :
    (E₊ i).get (bornLabel w M B hD hClass H hState K hCover s i) =
      (π i) ⁻¹' gcentre B.toResolutionInvariant M K s.T i := by
  change ((_ ++ [(π i) ⁻¹' gcentre B.toResolutionInvariant M K s.T i]).get
    ⟨(geoTransformAlong (M i) (s.T i).2).E.length, _⟩) = _
  apply List.getElem_concat_length
  simp

variable [Finite ι] (hK : ∀ i, IsCompact (K i))
  (a : Successor w M B hD hClass H hState K hCover s xs hK)

/-- The native image ideal of the SAME global centre is the ENTIRE actual
born Cartier image ideal, derived from both full actual native squares. -/
theorem window_stalkIdeal_eq_born (i : ι)
    (z : (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left) :
    nativePulledIdealStalkIdeal (a.map i).hom.left
      (nativePulledIdealModule a.p.hom.left J bJ)
      (nativePulledIdealInclusion a.p.hom.left J bJ) z =
    actualLabelledBoundaryTraceIdeal
      (strictTransform N (π i) (xs.carrier i)) (E₊ i)
      (bornLabel w M B hD hClass H hState K hCover s i) z := by
  rw [stalkIdeal_comp]
  have hsq : (a.map i).hom.left ≫ a.p.hom.left =
      (nextWindowProjection w M B hD hClass H hState K hCover s xs i).hom.left ≫
        (xs.map i).hom.left := congrArg (fun f => f.hom.left) (a.square i)
  rw [hsq, nativePulledIdealStalkIdeal_comp,
    window_ambient_stalkIdeal_eq w M B hD hClass H hState K hCover s xs i]
  have hπ := nextProjection_isBlowup w M B hD hClass H hState K hCover s i
  have hMap := map_actualSubspace_stalk_ideal_pullback hπ.contMDiff
    (fun y (hy : y ∈ strictTransform N (π i) (xs.carrier i)) =>
      (closure_minimal sdiff_subset ((xs.analytic i).isClosed.preimage
        hπ.contMDiff.continuous)) hy)
    (vanishingIdeal (n := N) (gcentre B.toResolutionInvariant M K s.T i))
    (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ) z
  apply hMap.trans
  rw [actualLabelledBoundaryTraceIdeal, bornLabel_get]
  exact congrArg (fun I => Ideal.map
    ((actualSubspaceInclusion (n := N)
      (strictTransform N (π i) (xs.carrier i))).stalkMap z).hom
    (actualWholeSheafStalkIdeal I z.val))
      (HironakaNormalCrossingsOriginalExponents.exceptionalIdeal_eq_vanishingIdeal hπ)

/-- EVERY actual original section is read by the SAME complete born ideal
at EVERY original germ; this retains the native module/scalar inclusion. -/
theorem window_sectionIdeal_mem_iff_born (i : ι)
    (U : Opens (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left.toTopCat)
    (t : ((nextWindow w M B hD hClass H hState K hCover s xs i).obj.left.presheaf.obj
      (op U)).carrier) :
    t ∈ nativePulledIdealSectionIdeal (a.map i).hom.left
      (nativePulledIdealModule a.p.hom.left J bJ)
      (nativePulledIdealInclusion a.p.hom.left J bJ) U ↔
    ∀ (z : (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left) (hz : z ∈ U),
      (nextWindow w M B hD hClass H hState K hCover s xs i).obj.left.presheaf.germ U z hz t ∈
        actualLabelledBoundaryTraceIdeal
          (strictTransform N (π i) (xs.carrier i)) (E₊ i)
          (bornLabel w M B hD hClass H hState K hCover s i) z := by
  change (∀ z hz, _ ∈ nativePulledIdealStalkIdeal _ _ _ z) ↔ _
  constructor
  · intro ht z hz
    rw [← window_stalkIdeal_eq_born w M B hD hClass H hState K hCover s xs hK a i]
    exact ht z hz
  · intro ht z hz
    rw [window_stalkIdeal_eq_born w M B hD hClass H hState K hCover s xs hK a i]
    exact ht z hz

end
end SGPT.Unibranch.HironakaG1CanonicalBornBoundaryIdeal

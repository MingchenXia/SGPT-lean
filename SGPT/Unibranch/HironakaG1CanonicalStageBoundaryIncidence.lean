import SGPT.Unibranch.HironakaG1CanonicalStageCentreIdeal
import SGPT.Foundations.Analysis.Pending.HironakaG1NativeBoundaryIncidence
import SGPT.Foundations.Analysis.Pending.MarkedIdealOpenBiholomorphism

/-!
# The SAME current canonical old-member incidence from native whole ideals

Ordinary initial canonical/native data derive current SNC and centre
containment. The existing entire global centre ideal yields the genuine
current exponent readout. If ONE current global old ideal has already been
constructed by induction, actual open-stalk isomorphisms derive exponent
agreement at the same native stage point. Its existence is not assumed as
a final G1 compatibility theorem and is not produced here.

Blueprint FIRST: `hironaka-g1-canonical-stage-boundary-incidence.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry Opposite Classical
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1CanonicalStageBoundaryIncidence

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11ManifoldWindowCentres HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSeq MarkedIdealBiholomorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreIdealModel
  HironakaNativePulledIdealSheaf HironakaSingularModuleSheafStalk
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaG1NativeBoundaryIncidence
  HironakaG1NativeOldBoundaryFactor
open ResolutionInvariantSpec (IsInvDomain)

noncomputable section

private theorem native_pulled_le_iff {A Y : LocallyRingedSpace.{0}}
    (f : A ⟶ Y) [LocallyRingedSpace.IsOpenImmersion f]
    (D J : SheafOfModules.{0} (forgetRing Y.toSheafedSpace.sheaf))
    (bD : D ⟶ SheafOfModules.unit _) (bJ : J ⟶ SheafOfModules.unit _) (p : A) :
    nativePulledIdealStalkIdeal f D bD p ≤ nativePulledIdealStalkIdeal f J bJ p ↔
      LinearMap.range (stalkInclusionLinearMap Y.toSheafedSpace.sheaf D bD (f.base p)) ≤
        LinearMap.range (stalkInclusionLinearMap Y.toSheafedSpace.sheaf J bJ (f.base p)) := by
  exact ((asIso (f.stalkMap p)).commRingCatIsoToRingEquiv.idealComapOrderIso.symm).le_iff_le

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
/-- The full boundary of the SAME original current marked record. -/
abbrev currentBoundary (i : ι) : List (Set (s.T i).1) :=
  (geoTransformAlong (M i) (s.T i).2).E

local notation "E" => currentBoundary w M B s

/-- Both current SNC and centre incidence are INTERNALLY derived from the
SAME ordinary initial record/native state and actual canonical prefix. -/
theorem local_centre_subset_iff_native_le (i : ι) (a : Fin (E i).length)
    (p : (ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left) :
    (∀ᶠ y in 𝓝 p.val,
      y ∈ gcentre B.toResolutionInvariant M K s.T i → y ∈ (E i).get a) ↔
    actualLabelledBoundaryTraceIdeal (xs.carrier i) (E i) a p ≤
      nativePulledIdealStalkIdeal (xs.map i).hom.left J bJ p := by
  have hTest := B.toResolutionInvariant.isInvValue.isGeoTestTower_of_isCanonical
    (hD i) (s.T i).2 (s.canonical i)
  have hSNC := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (hD i).isWellFormed (s.T i).2 hTest).isSNCDivisor
  have hCW : gcentre B.toResolutionInvariant M K s.T i ⊆ xs.carrier i := by
    intro y hy
    rw [xs.carrier_eq i]
    exact ((hState i).hsTowerState (s.T i).2 hTest).2.1 hy.1
  rw [local_centre_subset_member_iff_native_image_le hCW hSNC a p,
    intrinsicReducedCentreStalkInclusion_range_model hCW p,
    ← window_ambient_stalkIdeal_eq w M B hD hClass H hState K hCover s xs i p]

/-- The genuine current exponent is read from the actual entire old image
and SAME internally produced global centre ideal, with no comparison input. -/
theorem memberExponent_eq_native_ite (i : ι) (a : Fin (E i).length)
    (p : (ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left) :
    centreMemberExponent (gcentre B.toResolutionInvariant M K s.T i) ((E i).get a) p.val =
      if actualLabelledBoundaryTraceIdeal (xs.carrier i) (E i) a p ≤
        nativePulledIdealStalkIdeal (xs.map i).hom.left J bJ p then 1 else 0 := by
  simp only [centreMemberExponent,
    local_centre_subset_iff_native_le w M B hD hClass H hState K hCover s xs i a p]

variable (D : SheafOfModules.{0} (forgetRing xs.Y.obj.left.toSheafedSpace.sheaf))
  (bD : D ⟶ SheafOfModules.unit _)

/-- One CURRENT global old ideal with its actual current local readout
makes incidence an inclusion in the ORIGINAL native stage local ring.
The existence of this induction field is deliberately not asserted here. -/
theorem memberExponent_eq_global_ite (i : ι) (a : Fin (E i).length)
    (p : (ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left)
    (hOld : nativePulledIdealStalkIdeal (xs.map i).hom.left D bD p =
      actualLabelledBoundaryTraceIdeal (xs.carrier i) (E i) a p) :
    centreMemberExponent (gcentre B.toResolutionInvariant M K s.T i) ((E i).get a) p.val =
      if LinearMap.range (stalkInclusionLinearMap xs.Y.obj.left.toSheafedSpace.sheaf
          D bD ((xs.map i).hom.left.base p)) ≤
        LinearMap.range (stalkInclusionLinearMap xs.Y.obj.left.toSheafedSpace.sheaf
          J bJ ((xs.map i).hom.left.base p)) then 1 else 0 := by
  have : LocallyRingedSpace.IsOpenImmersion (xs.map i).hom.left := xs.isOpenImmersion i
  rw [memberExponent_eq_native_ite w M B hD hClass H hState K hCover s xs i a p,
    ← hOld, native_pulled_le_iff]

include hD hClass H hState hCover in
/-- At the SAME actual native point the derived exponents coincide.
Only current old-ideal induction readouts are supplied, never incidence,
future canonical history or a centre/target compatibility packet. -/
theorem memberExponent_eq_of_same_native_point (i j : ι)
    (a : Fin (E i).length) (b : Fin (E j).length)
    (p : (ofClosedAnalytic (xs.carrier i) (xs.analytic i)).obj.left)
    (q : (ofClosedAnalytic (xs.carrier j) (xs.analytic j)).obj.left)
    (hOldi : nativePulledIdealStalkIdeal (xs.map i).hom.left D bD p =
      actualLabelledBoundaryTraceIdeal (xs.carrier i) (E i) a p)
    (hOldj : nativePulledIdealStalkIdeal (xs.map j).hom.left D bD q =
      actualLabelledBoundaryTraceIdeal (xs.carrier j) (E j) b q)
    (hpq : (xs.map i).hom.left.base p = (xs.map j).hom.left.base q) :
    centreMemberExponent (gcentre B.toResolutionInvariant M K s.T i) ((E i).get a) p.val =
      centreMemberExponent (gcentre B.toResolutionInvariant M K s.T j) ((E j).get b) q.val := by
  rw [memberExponent_eq_global_ite w M B hD hClass H hState K hCover s xs D bD i a p hOldi,
    memberExponent_eq_global_ite w M B hD hClass H hState K hCover s xs D bD j b q hOldj,
    hpq]

end
end SGPT.Unibranch.HironakaG1CanonicalStageBoundaryIncidence

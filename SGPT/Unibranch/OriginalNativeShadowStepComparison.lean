import SGPT.Unibranch.OriginalNativeShadowCommonCentre
import SGPT.Unibranch.OriginalNativeBlowupOpenRestriction
import SGPT.Unibranch.RIsoAModification

/-! TWO actual computed level-centre blowups have a derived full native
comparison on the SAME common inverse open. Their own distinct centre
models and whole UPs are retained. Blueprint FIRST:
original-native-shadow-step-comparison.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.OriginalNativeShadowStepComparison
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11CompatibleCanonicalTowers HironakaG11StrictTransformTowers
  HironakaG11InvBMClass HironakaG8LocalHistory HironakaG1CanonicalStageCentreIdeal
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HironakaActualPowerBoundaryExponents
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf SmoothCentreModification
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
open ResolutionInvariantSpec (IsInvDomain)

variable {X Z : SourceReducedComplexSpace} {N : ℕ} {Λ : Type*}
  [LinearOrder Λ] [Nonempty Λ] {ι κ ν : Type*}
  (w : ι → DimEmbedding X N) (raw : ∀ i, MarkedIdeal N (Amb w i))
  (H : ℕ → ℕ) (hrec : ∀ i, HironakaG11PresReduction.IsNativeWindowRecord (w i) (raw i) H)
  (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
  (hd : ∀ i j, (powerMarked (raw i) (e i)).d = (powerMarked (raw j) (e j)).d)
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') N Λ)


variable {m : ℕ} (s : GStage B.toResolutionInvariant (fun i : ι => powerMarked (raw i) (e i)) (mapAdm w) m)
  (xs : XStage w s.T) (q : xs.Y ⟶ Z) (hq : IsProperMap q.hom.left.base)
  (K : Set Z.obj.left) (hK : IsCompact K) (C : Set xs.Y.obj.left) (hC : IsClosed C)
  (hTrace : ∀ i (c : xs.carrier i),
    (xs.map i).hom.left.base c ∈ C ↔ c.val ∈ rcos (fun i : ι => powerMarked (raw i) (e i)) s.T i)
  (f : κ → ι) (g : ν → ι)
  (hP : C ∩ q.hom.left.base ⁻¹' K ⊆ OriginalNativeShadowCommonCentre.chartOpen w (fun i : ι => powerMarked (raw i) (e i)) B s xs f)
  (hQ : C ∩ q.hom.left.base ⁻¹' K ⊆ OriginalNativeShadowCommonCentre.chartOpen w (fun i : ι => powerMarked (raw i) (e i)) B s xs g)

local notation "nC" => OriginalNativeShadowCommonCentre.commonNeighbourhood w (fun i : ι => powerMarked (raw i) (e i)) B s xs q hq K hK C hC f g hP hQ
local notation "yC" => OriginalNativeShadowCommonCentre.commonSource w (fun i : ι => powerMarked (raw i) (e i)) B s xs q hq K hK C hC f g hP hQ
local notation "jC" => OriginalNativeShadowCommonCentre.commonInclusion w (fun i : ι => powerMarked (raw i) (e i)) B s xs q hq K hK C hC f g hP hQ

/-- Ordinary OWN actual closed-analytic level centre and its actual native blowup. -/
structure LevelBlowup {μ : Type*} (a : μ → ι) (l : Λ) where
  centre_analytic : xs.Y.IsAnalyticSubset (OriginalNativeShadowCommonCentre.levelSupport w (fun i : ι => powerMarked (raw i) (e i)) B s xs a l)
  source : SourceReducedComplexSpace
  projection : source ⟶ xs.Y
  blowup : IsSmoothCentreBlowup projection
    (OriginalAnalyticClosedSubspace.inclusion xs.Y
      (OriginalNativeShadowCommonCentre.levelSupport w (fun i : ι => powerMarked (raw i) (e i)) B s xs a l) centre_analytic)

/-- The literal WHOLE inverse-open subset in the original current native Y. -/
def targetOpen : Opens xs.Y.obj.left := OriginalRelativelyCompactRestriction.preimageOpen (nC).openSet q

omit [Nonempty Λ] in
theorem targetOpen_compactClosure :
    IsCompact (closure (targetOpen w raw e B s xs q hq K hK C hC f g hP hQ : Set xs.Y.obj.left)) :=
  OriginalRelativelyCompactRestriction.isCompact_closure_preimage (nC).openSet q (nC).compactClosure hq

variable {μ : Type*} {a : μ → ι} {l : Λ}
  (t : LevelBlowup w raw e B s xs a l)

local notation "uC" => targetOpen w raw e B s xs q hq K hK C hC f g hP hQ
local notation "huC" => targetOpen_compactClosure w raw e B s xs q hq K hK C hC f g hP hQ
local notation "iT" => OriginalAnalyticClosedSubspace.inclusion xs.Y
  (OriginalNativeShadowCommonCentre.levelSupport w (fun i : ι => powerMarked (raw i) (e i)) B s xs a l) t.centre_analytic

def restrictedSource : SourceReducedComplexSpace :=
  OriginalRelativelyCompactRestriction.preimageRestriction uC t.projection huC t.blowup.2.2.2.2.2.2.1

def restrictedProjection : restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t ⟶ yC :=
  OriginalRelativelyCompactRestriction.restrictionProjection uC t.projection huC t.blowup.2.2.2.2.2.2.1

def sourceInclusion : restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t ⟶ t.source :=
  OriginalRelativelyCompactRestriction.inclusion t.source (OriginalRelativelyCompactRestriction.preimageOpen uC t.projection)
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage uC t.projection huC t.blowup.2.2.2.2.2.2.1)

omit [Nonempty Λ] in
theorem restrictedProjection_square :
    restrictedProjection w raw e B s xs q hq K hK C hC f g hP hQ t ≫ (jC) =
      sourceInclusion w raw e B s xs q hq K hK C hC f g hP hQ t ≫ t.projection :=
  OriginalRelativelyCompactRestriction.restrictionProjection_inclusion _ _ _ _

def restrictedCentre : SourceReducedComplexSpace :=
  OriginalNativeBlowupOpenRestriction.centreSource t.projection (iT) t.blowup uC huC

def restrictedCentreMap : restrictedCentre w raw e B s xs q hq K hK C hC f g hP hQ t ⟶ yC :=
  OriginalNativeBlowupOpenRestriction.centreProjection t.projection (iT) t.blowup uC huC

omit [Nonempty Λ] in
theorem restricted_isSmoothCentreBlowup : IsSmoothCentreBlowup
    (restrictedProjection w raw e B s xs q hq K hK C hC f g hP hQ t)
    (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t) :=
  OriginalNativeBlowupOpenRestriction.restriction_isSmoothCentreBlowup t.projection (iT) t.blowup uC huC

omit [Nonempty Λ] in
theorem restrictedCentre_range :
    range (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t).hom.left.base =
      (jC).hom.left.base ⁻¹' OriginalNativeShadowCommonCentre.levelSupport w (fun i : ι => powerMarked (raw i) (e i)) B s xs a l := by
  have h := OriginalNativeBlowupOpenRestriction.centreProjection_range t.projection (iT) t.blowup uC huC
  rw [OriginalAnalyticClosedSubspace.inclusion_range] at h
  exact h

variable (t₀ : LevelBlowup w raw e B s xs f l) (t₁ : LevelBlowup w raw e B s xs g l)

include hrec he hd hTrace in
theorem restricted_centres_eq :
    range (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t₀).hom.left.base =
      range (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t₁).hom.left.base := by
  let hD : ∀ i, IsInvDomain N ((fun i : ι => powerMarked (raw i) (e i)) i) :=
    fun i => powerMarked_isInvDomain (raw i) (hrec i).1 (he i)
  have hClass := HironakaG1NativeWindowInitialClass.initialClassData_of_native_powers
    w raw H hrec e he hd
  rw [restrictedCentre_range, restrictedCentre_range]
  exact OriginalNativeShadowCommonCentre.levelSupport_preimage_eq_each_other w (fun i : ι => powerMarked (raw i) (e i)) B s xs hD hClass
    q hq K hK C hC hTrace f g hP hQ l

include hrec he hd hTrace in
theorem restricted_wholeSubmodule_eq :
    intrinsicReducedCentreSubmodule (yC).obj.left
      (range (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t₀).hom.left.base) =
    intrinsicReducedCentreSubmodule (yC).obj.left
      (range (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t₁).hom.left.base) := by
  exact congrArg (intrinsicReducedCentreSubmodule (yC).obj.left)
    (restricted_centres_eq w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁)

include hrec he hd hTrace in
private theorem comparison_exists :
    ∃ E : restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₀ ≅
      restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₁,
      E.hom ≫ restrictedProjection w raw e B s xs q hq K hK C hC f g hP hQ t₁ =
        restrictedProjection w raw e B s xs q hq K hK C hC f g hP hQ t₀ ∧
      ∀ F, F ≫ restrictedProjection w raw e B s xs q hq K hK C hC f g hP hQ t₁ =
        restrictedProjection w raw e B s xs q hq K hK C hC f g hP hQ t₀ → F = E.hom := by
  exact RIsoAModification.isSmoothCentreBlowup_exists_unique_iso
    (restricted_isSmoothCentreBlowup w raw e B s xs q hq K hK C hC f g hP hQ t₀)
    (restricted_isSmoothCentreBlowup w raw e B s xs q hq K hK C hC f g hP hQ t₁)
    (restricted_centres_eq w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁)

/-- The full actual comparison is constructed from OWN UPs and DERIVED entire centres. -/
def comparison : restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₀ ≅
    restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₁ :=
  (comparison_exists w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁).choose

local notation "E" => comparison w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁
local notation "p₀" => restrictedProjection w raw e B s xs q hq K hK C hC f g hP hQ t₀
local notation "p₁" => restrictedProjection w raw e B s xs q hq K hK C hC f g hP hQ t₁
local notation "j₀" => sourceInclusion w raw e B s xs q hq K hK C hC f g hP hQ t₀
local notation "j₁" => sourceInclusion w raw e B s xs q hq K hK C hC f g hP hQ t₁

theorem comparison_projection : (E).hom ≫ (p₁) = (p₀) :=
  (comparison_exists w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁).choose_spec.1

theorem comparison_unique
    (F : restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₀ ⟶
      restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₁)
    (hF : F ≫ (p₁) = (p₀)) : F = (E).hom :=
  (comparison_exists w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁).choose_spec.2 F hF

theorem comparison_current_square :
    (E).hom ≫ ((j₁) ≫ t₁.projection) = (j₀) ≫ t₀.projection := by
  rw [← restrictedProjection_square, ← Category.assoc, comparison_projection,
    restrictedProjection_square]

theorem comparison_original_square :
    (E).hom ≫ ((j₁) ≫ t₁.projection ≫ xs.q) = (j₀) ≫ t₀.projection ≫ xs.q := by
  simpa only [Category.assoc] using congrArg (fun F => F ≫ xs.q)
    (comparison_current_square w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁)

theorem comparison_base_square :
    (E).hom ≫ ((j₁) ≫ t₁.projection ≫ q) = (j₀) ≫ t₀.projection ≫ q := by
  simpa only [Category.assoc] using congrArg (fun F => F ≫ q)
    (comparison_current_square w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁)

theorem comparison_scalar : (E).hom.hom.left ≫
    (restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₁).obj.hom =
      (restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₀).obj.hom :=
  Over.w (E).hom.hom

/-- ONE genuine local blowup yields BOTH native windows and their full comparison square. -/
theorem exists_common_window {W TW : SourceReducedComplexSpace} (r : W ⟶ yC)
    (hr : LocallyRingedSpace.IsOpenImmersion r.hom.left) (π : TW ⟶ W)
    (hπ : IsIdealBlowup π
      (intrinsicReducedCentreIdealModule W.obj.left (r.hom.left.base ⁻¹' range
        (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t₀).hom.left.base))
      (intrinsicReducedCentreIdealInclusion W.obj.left (r.hom.left.base ⁻¹' range
        (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t₀).hom.left.base))) :
    ∃ L₀ : TW ⟶ restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₀,
    ∃ L₁ : TW ⟶ restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₁,
      (L₀ ≫ (p₀) = π ≫ r ∧ ∀ L, L ≫ (p₀) = π ≫ r → L = L₀) ∧
      (L₁ ≫ (p₁) = π ≫ r ∧ ∀ L, L ≫ (p₁) = π ≫ r → L = L₁) ∧
      LocallyRingedSpace.IsOpenImmersion L₀.hom.left ∧
      LocallyRingedSpace.IsOpenImmersion L₁.hom.left ∧
      range L₀.hom.left.base = (p₀).hom.left.base ⁻¹' range r.hom.left.base ∧
      range L₁.hom.left.base = (p₁).hom.left.base ⁻¹' range r.hom.left.base ∧
      L₀ ≫ (E).hom = L₁ ∧
      L₀.hom.left ≫ (restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₀).obj.hom = TW.obj.hom ∧
      L₁.hom.left ≫ (restrictedSource w raw e B s xs q hq K hK C hC f g hP hQ t₁).obj.hom = TW.obj.hom := by
  obtain ⟨L₀, hL₀, hO₀, hR₀⟩ :=
    HironakaG11BlowupLocality.exists_openImmersion_of_isSmoothCentreBlowup
      (restricted_isSmoothCentreBlowup w raw e B s xs q hq K hK C hC f g hP hQ t₀) hr hπ
  have hπ' : IsIdealBlowup π
      (intrinsicReducedCentreIdealModule W.obj.left (r.hom.left.base ⁻¹' range
        (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t₁).hom.left.base))
      (intrinsicReducedCentreIdealInclusion W.obj.left (r.hom.left.base ⁻¹' range
        (restrictedCentreMap w raw e B s xs q hq K hK C hC f g hP hQ t₁).hom.left.base)) := by
    rw [← restricted_centres_eq w raw H hrec e he hd B s xs q hq K hK C hC hTrace f g hP hQ t₀ t₁]
    exact hπ
  obtain ⟨L₁, hL₁, hO₁, hR₁⟩ :=
    HironakaG11BlowupLocality.exists_openImmersion_of_isSmoothCentreBlowup
      (restricted_isSmoothCentreBlowup w raw e B s xs q hq K hK C hC f g hP hQ t₁) hr hπ'
  refine ⟨L₀, L₁, hL₀, hL₁, hO₀, hO₁, hR₀, hR₁, ?_, Over.w L₀.hom, Over.w L₁.hom⟩
  apply hL₁.2
  rw [Category.assoc, comparison_projection, hL₀.1]

end
end SGPT.Unibranch.OriginalNativeShadowStepComparison

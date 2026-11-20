import SGPT.Okounkov.OF12AmbientProjectiveTrace
import SGPT.Okounkov.OF12NormalResolution
import SGPT.Unibranch.ComplexSpaceAnalyticInterior
import SGPT.Unibranch.Resolution
import SGPT.Unibranch.OriginalSmoothSourceAnalytic
import SGPT.Unibranch.OriginalNativeModification
import SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
import SGPT.Foundations.Analysis.Pending.CodimOneSupport

/-! Analyticity and empty interior of proper algebraic traces on the projective analytification. -/
set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Projective SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.BDivisor.GM SGPT.Okounkov
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra SGPT.Toric.monomialProjectiveTopology

local instance projectivePointTopology (n : ℕ) :
    TopologicalSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :=
  schemeAnalyticPointTopology _

/-- A Zariski-closed subset of the original projective space has an analytic point trace
in the usual complex projective manifold. -/
theorem isComplexAnalyticSubset_originalProjectiveTrace (n : ℕ)
    (Z : Set (polynomialProj ℂ n)) (hZ : IsClosed Z) :
    IsComplexAnalyticSubset (n := n)
      ((originalProjectiveHomeomorph n) ''
        schemeNativeAlgebraicTrace (polynomialProjStructureMap ℂ n) Z) := by
  let p := polynomialProjStructureMap ℂ n
  let I := SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint.identityEmbedding n
  let : IsSeparated p := I.isSeparated
  let : QuasiCompact p := I.quasiCompact
  let : SmoothOfRelativeDimension n p := inferInstance
  let : ChartedSpace (ComplexModel n) (SchemeComplexPoint p) := schemeAnalyticTNChartedSpace p n
  let : IsComplexManifold n (SchemeComplexPoint p) := schemeAnalyticTN_isComplexManifold p n
  let : CompactSpace (SchemeComplexPoint p) := I.analyticCompact
  have hread : projectivePoint p I n = originalProjectiveHomeomorph n := by
    funext q
    rw [← ambientPoint_eq_projectivePoint I n q]
    change originalProjectiveHomeomorph n (schemeComplexPointMap p p (𝟙 _) I.over_base q) = _
    apply congrArg (originalProjectiveHomeomorph n)
    apply Subtype.ext
    exact Category.comp_id q.val
  rw [← hread]
  exact isComplexAnalyticSubset_image (isHolomorphicEmbedding_projectivePoint p I n)
    (schemeNativeAlgebraicTrace_isComplexAnalyticSubset p n Z hZ)

/-- A proper analytic subset of a connected unibranch space has empty interior. -/
theorem interior_eq_empty_of_proper_analyticSubset {D : SourceReducedComplexSpace}
    [ConnectedSpace D.obj.left] (hD : D.IsUnibranch)
    {A : Set D.obj.left} (hA : D.IsAnalyticSubset A) (hproper : A ≠ univ) :
    interior A = ∅ := by
  rcases isClopen_iff.mp ⟨hD.isClosed_interior_of_isAnalyticSubset hA, isOpen_interior⟩ with h | h
  · exact h
  · exfalso
    apply hproper
    apply Set.eq_univ_of_univ_subset
    rw [← h]
    exact interior_subset

/-- A connected smooth source has thin pullback of an analytic exceptional subset as soon
as one point of the source maps outside that subset. -/
theorem interior_preimage_eq_empty_of_smooth_source
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [ConnectedSpace M] {D : SourceReducedComplexSpace}
    (π : OriginalNativeModification.wholeModel (n := n) M ⟶ D)
    {A : Set D.obj.left} (hA : D.IsAnalyticSubset A)
    (hgood : ∃ x : M, OriginalSmoothSourceAnalytic.pointMap π x ∉ A) :
    interior (π.hom.left.base ⁻¹' A) = ∅ := by
  let N := OriginalSmoothSourceAnalytic.pointMap π ⁻¹' A
  have hN : IsComplexAnalyticSubset (n := n) N :=
    OriginalSmoothSourceAnalytic.isComplexAnalyticSubset_preimage π hA
  have hproper : N ≠ univ := by
    obtain ⟨x, hx⟩ := hgood
    intro h
    apply hx
    exact (show x ∈ N from h.symm ▸ mem_univ x)
  have hthin :=
    PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ hN hproper
  change interior ((Homeomorph.Set.univ M) ⁻¹' N) = ∅
  rw [← (Homeomorph.Set.univ M).preimage_interior, hthin, preimage_empty]

/-- For the point-compatible comparison with the reduced closed projective image, the literal
trace of a proper Zariski-closed subset is closed analytic and has empty interior. -/
theorem algebraicTrace_isAnalyticSubset_and_interior_eq_empty
    {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    (E : ClosedProjectiveEmbedding f)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (i : UnibAn.analytification f ≅ ofClosedAnalytic (range (ambientPoint E))
      (isComplexAnalyticSubset_ambientPoint_range E))
    (hi : ∀ x : (UnibAn.analytification f).obj.left,
      (isoHomeomorph i x).val = ambientPoint E (UnibAn.pointMap f x))
    (Z : Set X) (hZ : IsClosed Z) (hproper : Z ≠ univ) :
    let T := (schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' Z
    (UnibAn.analytification f).IsAnalyticSubset T ∧ interior T = ∅ := by
  let C := range (ambientPoint E)
  let p := polynomialProjStructureMap ℂ E.ambientDimension
  let A := (originalProjectiveHomeomorph E.ambientDimension) ''
    schemeNativeAlgebraicTrace p (E.map '' Z)
  let T := (schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' Z
  have hA : IsComplexAnalyticSubset (n := E.ambientDimension) A :=
    isComplexAnalyticSubset_originalProjectiveTrace _ _
      (E.map.isClosedEmbedding.isClosedMap _ hZ)
  have heq : T = isoHomeomorph i ⁻¹' ((Subtype.val : C → ComplexProjectiveSpace E.ambientDimension) ⁻¹' A) := by
    ext x
    let q := UnibAn.pointMap f x
    let y := schemeComplexPointMap f p E.map E.over_base q
    change schemeComplexPointImage f q ∈ Z ↔ (isoHomeomorph i x).val ∈ A
    rw [hi x]
    change schemeComplexPointImage f q ∈ Z ↔ originalProjectiveHomeomorph E.ambientDimension y ∈
      (originalProjectiveHomeomorph E.ambientDimension) '' schemeNativeAlgebraicTrace p (E.map '' Z)
    rw [(originalProjectiveHomeomorph E.ambientDimension).injective.mem_set_image]
    change schemeComplexPointImage f q ∈ Z ↔ E.map (schemeComplexPointImage f q) ∈ E.map '' Z
    exact E.map.isClosedEmbedding.injective.mem_set_image.symm
  have ht : (UnibAn.analytification f).IsAnalyticSubset T := by
    rw [heq]
    exact (isAnalyticSubset_preimage_val (isComplexAnalyticSubset_ambientPoint_range E) hA).preimage_iso i
  have hC := analyticallyIrreducible_ambientPoint_range E
  let : ConnectedSpace (ofClosedAnalytic (range (ambientPoint E))
      (isComplexAnalyticSubset_ambientPoint_range E)).obj.left := by
    change ConnectedSpace C
    exact Subtype.connectedSpace
      ⟨hC.nonempty, CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible hC⟩
  let : ConnectedSpace (UnibAn.analytification f).obj.left :=
    (isoHomeomorph i).symm.surjective.connectedSpace (isoHomeomorph i).symm.continuous
  have hTproper : T ≠ univ := by
    intro h
    apply hproper
    have hsub : range (schemeComplexPointImage f) ⊆ Z := by
      rintro _ ⟨q, rfl⟩
      obtain ⟨x, hx⟩ := UnibAn.pointMap_surjective q
      have hxT : x ∈ T := h.symm ▸ mem_univ x
      change schemeComplexPointImage f (UnibAn.pointMap f x) ∈ Z at hxT
      simpa only [hx] using hxT
    exact Set.eq_univ_of_univ_subset fun x _ =>
      closure_minimal hsub hZ (OF14.dense_range_schemeComplexPointImage f x)
  exact ⟨ht, interior_eq_empty_of_proper_analyticSubset
    (isUnibranch_analytification_of_normal f hX) ht hTproper⟩

end SGPT.Okounkov.OF12

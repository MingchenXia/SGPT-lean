import SGPT.Unibranch.UnibAnProjectiveReducedComparison
import SGPT.Unibranch.OriginalAnalyticClosedSubspaceStalkQuotient
import SGPT.Unibranch.SmoothCentreModification

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaIntrinsicReducedCentreOpenPullback
open SGPT.Okounkov SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.SmoothCentreModification SGPT.Foundations.Schemes
open scoped Manifold ContDiff

namespace SGPT.Unibranch.UnibAn

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The analytification of a projective scheme is the native reduced analytic
subspace of its actual image in the usual smooth projective model. The
isomorphism uses exactly the original complex-point map of the embedding. -/
theorem exists_projectiveAnalytification_iso_nativeReducedImage
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IsSeparated f] [QuasiCompact f]
    [LocallyOfFiniteType f] (E : ClosedProjectiveEmbedding f) :
    let n := E.ambientDimension
    let g := polynomialProjStructureMap ℂ n
    letI : TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
    letI : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g n
    letI : IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n
    let C := schemeNativeAlgebraicTrace g (range E.map)
    ∃ (hC : IsComplexAnalyticSubset (n := n) C)
      (e : analytification f ≅ ofClosedAnalytic C hC), ∀ x : analytificationLRS f,
        (e.hom.hom.left.base x).val = schemeComplexPointMap f g E.map E.over_base (pointMap f x) := by
  let n := E.ambientDimension
  let g := polynomialProjStructureMap ℂ n
  let : TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
  let : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g n
  let : IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n
  let C := schemeNativeAlgebraicTrace g (range E.map)
  have hC : IsComplexAnalyticSubset (n := n) C :=
    schemeNativeAlgebraicTrace_isComplexAnalyticSubset g n _ E.map.isClosedEmbedding.isClosed_range
  let W : Set (SchemeComplexPoint g) := univ
  let hW : IsComplexAnalyticSubset (n := n) W := isComplexAnalyticSubset_univ (n := n)
  let Y := wholeModel (n := n) (SchemeComplexPoint g)
  let B := analytification g
  let A := ofClosedAnalytic C hC
  let i : A ⟶ Y := OriginalClosedSubspaceFactorization.inclusion hC hW (subset_univ C)
  obtain ⟨a, ha⟩ := exists_smoothModel_analytification_iso g n
  let F : analytification f ⟶ B := analytificationMorphism E.map E.over_base
  let S := range F.hom.left.base
  have hS : B.IsAnalyticSubset S := analytificationMorphism_projective_range_isAnalyticSubset E
  let G : A ⟶ B := i ≫ a.hom
  let : IsIso (a.hom.hom.left) := (isoLeft a).isIso_hom
  let : LocallyRingedSpace.IsOpenImmersion (a.hom.hom.left) := inferInstance
  have hSread : S = (schemeComplexPointImage g ∘ pointMap g) ⁻¹' range E.map :=
    analytificationMorphism_projective_range E
  have hpre : a.hom.hom.left.base ⁻¹' S =
      (Subtype.val : W → SchemeComplexPoint g) ⁻¹' C := by
    ext y
    change a.hom.hom.left.base y ∈ S ↔ y.val ∈ C
    rw [hSread]
    change schemeComplexPointImage g (pointMap g (a.hom.hom.left.base y)) ∈ range E.map ↔
      schemeComplexPointImage g y.val ∈ range E.map
    rw [show pointMap g (a.hom.hom.left.base y) = y.val from ha y.val]
  have hread (x : A.obj.left) : pointMap g (G.hom.left.base x) = x.val := by
    change pointMap g (a.hom.hom.left.base (i.hom.left.base x)) = x.val
    exact (ha _).trans (OriginalClosedSubspaceFactorization.inclusion_base_val hC hW (subset_univ C) x)
  have hG : range G.hom.left.base = S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      apply (Set.ext_iff.mp hSread _).mpr
      change schemeComplexPointImage g (pointMap g (G.hom.left.base x)) ∈ range E.map
      rw [hread]
      exact x.property
    · intro hy
      have hc : pointMap g y ∈ C := (Set.ext_iff.mp hSread y).mp hy
      exact ⟨⟨pointMap g y, hc⟩, pointMap_injective (hread _)⟩
  have hGemb : IsClosedEmbedding G.hom.left.base :=
    (isoHomeomorph a).isClosedEmbedding.comp
      (contained_inclusion_isClosedEmbedding hC hW (subset_univ C))
  have hGsurj (x : A.obj.left) : Function.Surjective (G.hom.left.stalkMap x) := by
    change Function.Surjective ((i.hom.left ≫ a.hom.hom.left).stalkMap x)
    rw [LocallyRingedSpace.stalkMap_comp]
    exact (contained_inclusion_stalk_surjective hC hW (subset_univ C) x).comp
      (ConcreteCategory.bijective_of_isIso (a.hom.hom.left.stalkMap (i.hom.left.base x))).2
  have hGker (x : A.obj.left) : RingHom.ker (G.hom.left.stalkMap x).hom =
      intrinsicCentreStalkRange B.obj.left S (G.hom.left.base x) := by
    change RingHom.ker ((i.hom.left ≫ a.hom.hom.left).stalkMap x).hom = _
    rw [LocallyRingedSpace.stalkMap_comp]
    change RingHom.ker ((i.hom.left.stalkMap x).hom.comp
      (a.hom.hom.left.stalkMap (i.hom.left.base x)).hom) = _
    rw [← RingHom.comap_ker]
    have hi := OriginalAnalyticClosedSubspaceStalkQuotient.contained_inclusion_stalk_kernel_eq_intrinsicCentreStalkRange
      hC hW (subset_univ C) x
    let y : Y.obj.left := i.hom.left.base x
    have hker : RingHom.ker (i.hom.left.stalkMap x).hom =
        intrinsicCentreStalkRange Y.obj.left (a.hom.hom.left.base ⁻¹' S) y := by
      exact hi.trans (congrArg (fun D : Set Y.obj.left =>
        intrinsicCentreStalkRange Y.obj.left D y) hpre.symm)
    rw [hker]
    have hp := openImmersion_pulled_stalkIdeal_eq a.hom.hom.left S (i.hom.left.base x)
    change Ideal.map (a.hom.hom.left.stalkMap (i.hom.left.base x)).hom
        (intrinsicCentreStalkRange B.obj.left S (a.hom.hom.left.base (i.hom.left.base x))) =
      intrinsicCentreStalkRange Y.obj.left (a.hom.hom.left.base ⁻¹' S) (i.hom.left.base x) at hp
    rw [← hp, Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]
    rfl
  obtain ⟨aF, haF⟩ := exists_projectiveAnalytification_iso_reducedImage E
  obtain ⟨aG, haG⟩ := exists_iso_factory_of_projectiveStalkData G hS hG hGemb hGsurj hGker
  let e := aF ≪≫ aG.symm
  let j := OriginalAnalyticClosedSubspace.inclusion B S hS
  have hinv : aG.inv ≫ G = j :=
    (congrArg (aG.inv ≫ ·) haG.symm).trans (aG.inv_hom_id_assoc j)
  have hfac : e.hom ≫ G = F := by
    change (aF.hom ≫ aG.inv) ≫ G = F
    calc
      _ = aF.hom ≫ (aG.inv ≫ G) := Category.assoc _ _ _
      _ = aF.hom ≫ j := congrArg (aF.hom ≫ ·) hinv
      _ = F := haF
  refine ⟨hC, e, fun x => ?_⟩
  have hx : G.hom.left.base (e.hom.hom.left.base x) = F.hom.left.base x :=
    congrArg (fun k : analytification f ⟶ B => k.hom.left.base x) hfac
  exact (hread _).symm.trans ((congrArg (pointMap g) hx).trans
    (pointMap_analytificationMorphism E.map E.over_base x))

end

end SGPT.Unibranch.UnibAn

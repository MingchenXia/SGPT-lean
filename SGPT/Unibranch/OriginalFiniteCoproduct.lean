import SGPT.Unibranch.Resolution
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# The actual compact finite coproduct in the ORIGINAL category

Reuse native locally-ringed coproduct/Cofan/OI/topological-Sigma APIs.
All original topology/local-model properties and entire scalar/descent maps
are derived on the SAME native coproduct. No replacement space category.
Blueprint FIRST: `original-finite-coproduct.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.OriginalFiniteCoproduct

open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace

noncomputable section

variable {ι : Type} (Z : ι → SourceReducedComplexSpace)

private def diagram : Discrete ι ⥤ LocallyRingedSpace.{0} :=
  Discrete.functor (fun i => (Z i).obj.left)

private def raw : LocallyRingedSpace.{0} := LocallyRingedSpace.coproduct (diagram Z)

private def rawCofan : Cocone (diagram Z) := LocallyRingedSpace.coproductCofan (diagram Z)

private def rawColimit : IsColimit (rawCofan Z) :=
  LocallyRingedSpace.coproductCofanIsColimit (diagram Z)

private def rawInclusion (i : ι) : (Z i).obj.left ⟶ raw Z :=
  (rawCofan Z).ι.app (Discrete.mk i)

private def scalarMap : raw Z ⟶ complexPoint :=
  (rawColimit Z).desc (Cofan.mk complexPoint (fun i => (Z i).obj.hom))

private theorem rawInclusion_scalar (i : ι) :
    rawInclusion Z i ≫ scalarMap Z = (Z i).obj.hom :=
  (rawColimit Z).fac (Cofan.mk complexPoint (fun i => (Z i).obj.hom)) (Discrete.mk i)

private def sheafDiagram := diagram Z ⋙ LocallyRingedSpace.forgetToSheafedSpace

private def topDiagram := sheafDiagram Z ⋙ SheafedSpace.forget CommRingCat.{0}

private def rawTopIso : (raw Z).toTopCat ≅ TopCat.of (Σ i, (Z i).obj.left) :=
  preservesColimitIso (SheafedSpace.forget CommRingCat.{0}) (sheafDiagram Z) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := topDiagram Z)) ≪≫
      TopCat.sigmaIsoSigma (fun i => (Z i).obj.left.toTopCat)

private theorem rawInclusion_topIso (i : ι) :
    (rawInclusion Z i).base ≫ (rawTopIso Z).hom =
      TopCat.sigmaι (fun j => (Z j).obj.left.toTopCat) i := by
  let P := preservesColimitIso (SheafedSpace.forget CommRingCat.{0}) (sheafDiagram Z)
  let Q := HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := topDiagram Z))
  let R := TopCat.sigmaIsoSigma (fun j => (Z j).obj.left.toTopCat)
  exact (show (rawInclusion Z i).base ≫ (rawTopIso Z).hom =
      (((rawInclusion Z i).base ≫ P.hom) ≫ Q.hom) ≫ R.hom from rfl).trans
    ((congrArg (fun K => (K ≫ Q.hom) ≫ R.hom)
      (ι_preservesColimitIso_hom (SheafedSpace.forget CommRingCat.{0}) (sheafDiagram Z) (Discrete.mk i))).trans
      ((congrArg (fun K => K ≫ R.hom)
        (HasColimit.isoOfNatIso_ι_hom (Discrete.natIsoFunctor (F := topDiagram Z)) (Discrete.mk i))).trans
          (TopCat.sigmaIsoSigma_hom_ι (fun j => (Z j).obj.left.toTopCat) i)))

private def rawPointHomeomorph : raw Z ≃ₜ (Σ i, (Z i).obj.left) :=
  TopCat.homeoOfIso (rawTopIso Z)

private theorem rawPointHomeomorph_inclusion (i : ι) (z : (Z i).obj.left) :
    rawPointHomeomorph Z ((rawInclusion Z i).base z) = Sigma.mk i z :=
  ConcreteCategory.congr_hom (rawInclusion_topIso Z i) z

private theorem rawInclusion_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (rawInclusion Z i) :=
  SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion (sheafDiagram Z) (Discrete.mk i)

private theorem rawJointlySurjective (x : raw Z) :
    ∃ (i : ι) (z : (Z i).obj.left), (rawInclusion Z i).base z = x := by
  cases hpoint : rawPointHomeomorph Z x with
  | mk i z =>
    exact ⟨i, z, (rawPointHomeomorph Z).injective
      ((rawPointHomeomorph_inclusion Z i z).trans hpoint.symm)⟩

private theorem rawDisjoint : Pairwise (fun i j =>
    Disjoint (range (rawInclusion Z i).base) (range (rawInclusion Z j).base)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨a, ha⟩ ⟨b, hb⟩
  have hs : (Sigma.mk i a : Σ k, (Z k).obj.left) = Sigma.mk j b :=
    (rawPointHomeomorph_inclusion Z i a).symm.trans
      ((congrArg (rawPointHomeomorph Z) (ha.trans hb.symm)).trans
        (rawPointHomeomorph_inclusion Z j b))
  exact hij (congrArg Sigma.fst hs)

private theorem rawT2 : T2Space (raw Z) := by
  have : ∀ i, T2Space (Z i).obj.left := fun i => (Z i).property.1
  exact (rawPointHomeomorph Z).isEmbedding.t2Space

private theorem rawAnalyticAtlas :
    ∀ x : raw Z, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ f : (modelOver U C).left ⟶ raw Z,
        LocallyRingedSpace.IsOpenImmersion f ∧
        f ≫ scalarMap Z = (modelOver U C).hom ∧ x ∈ range f.base := by
  intro x
  obtain ⟨i, z, rfl⟩ := rawJointlySurjective Z x
  obtain ⟨n, U, C, hC, f, hf, hp, c, hc⟩ := (Z i).property.2.2 z
  refine ⟨n, U, C, hC, f ≫ rawInclusion Z i,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ f hf _ (rawInclusion_isOpenImmersion Z i), ?_,
    c, congrArg (rawInclusion Z i).base hc⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun K => f ≫ K) (rawInclusion_scalar Z i)).trans hp)

section Finite

variable [Finite ι] [∀ i, CompactSpace (Z i).obj.left]

private theorem rawCompact : CompactSpace (raw Z) := by
  apply isCompact_univ_iff.mp
  simpa only [preimage_univ] using
    (rawPointHomeomorph Z).isProperMap.isCompact_preimage
      (isCompact_univ : IsCompact (univ : Set (Σ i, (Z i).obj.left)))

/-- The SAME actual native coproduct, with ORIGINAL properties derived. -/
def coproduct : SourceReducedComplexSpace := by
  refine ⟨Over.mk (scalarMap Z), rawT2 Z, ?_, rawAnalyticAtlas Z⟩
  exact @paracompact_of_compact (raw Z) _ (rawCompact Z)

/-- The genuine entire native cofan inclusion as an ORIGINAL morphism. -/
def inclusion (i : ι) : Z i ⟶ coproduct Z :=
  ObjectProperty.homMk (Over.homMk (rawInclusion Z i) (rawInclusion_scalar Z i))

theorem compactSpace_coproduct : CompactSpace (coproduct Z).obj.left := rawCompact Z

theorem inclusion_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (inclusion Z i).hom.left :=
  rawInclusion_isOpenImmersion Z i

theorem inclusion_jointly_surjective (x : (coproduct Z).obj.left) :
    ∃ (i : ι) (z : (Z i).obj.left), (inclusion Z i).hom.left.base z = x :=
  rawJointlySurjective Z x

theorem inclusion_pairwise_disjoint : Pairwise (fun i j =>
    Disjoint (range (inclusion Z i).hom.left.base) (range (inclusion Z j).hom.left.base)) :=
  rawDisjoint Z

/-- Local actual smooth models may have unrelated dimensions. -/
theorem isSmooth_coproduct (h : ∀ i, (Z i).IsSmooth) : (coproduct Z).IsSmooth := by
  intro x
  obtain ⟨i, z, rfl⟩ := inclusion_jointly_surjective Z x
  obtain ⟨n, V, f, hf, hp, v, hv⟩ := h i z
  refine ⟨n, V, f ≫ (inclusion Z i).hom.left,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ f hf _ (inclusion_isOpenImmersion Z i), ?_,
    v, congrArg (inclusion Z i).hom.left.base hv⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun K => f ≫ K) (Over.w (inclusion Z i).hom)).trans hp)

variable {X : SourceReducedComplexSpace}

private def rawDesc (F : ∀ i, Z i ⟶ X) : (coproduct Z).obj.left ⟶ X.obj.left :=
  (rawColimit Z).desc (Cofan.mk X.obj.left (fun i => (F i).hom.left))

private theorem rawDesc_fac (F : ∀ i, Z i ⟶ X) (i : ι) :
    (inclusion Z i).hom.left ≫ rawDesc Z F = (F i).hom.left :=
  (rawColimit Z).fac (Cofan.mk X.obj.left (fun i => (F i).hom.left)) (Discrete.mk i)

private theorem rawDesc_scalar (F : ∀ i, Z i ⟶ X) :
    rawDesc Z F ≫ X.obj.hom = (coproduct Z).obj.hom := by
  apply (rawColimit Z).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun K => K ≫ X.obj.hom) (rawDesc_fac Z F i.as)).trans
      ((Over.w (F i.as).hom).trans (rawInclusion_scalar Z i.as).symm))

/-- The EXISTING native entire coproduct descent retains the scalar square. -/
def desc (F : ∀ i, Z i ⟶ X) : coproduct Z ⟶ X :=
  ObjectProperty.homMk (Over.homMk (rawDesc Z F) (rawDesc_scalar Z F))

theorem inclusion_desc (F : ∀ i, Z i ⟶ X) (i : ι) :
    inclusion Z i ≫ desc Z F = F i := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact rawDesc_fac Z F i

theorem hom_ext (F G : coproduct Z ⟶ X)
    (h : ∀ i, inclusion Z i ≫ F = inclusion Z i ≫ G) : F = G := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (rawColimit Z).hom_ext
  intro i
  exact congrArg (fun K : Z i.as ⟶ X => K.hom.left) (h i.as)

end Finite

end

end SGPT.Unibranch.OriginalFiniteCoproduct

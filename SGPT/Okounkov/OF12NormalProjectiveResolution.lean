import SGPT.Okounkov.OF12ValCurrNormal
import SGPT.Okounkov.OF12NormalProjectiveField

/-!
# Resolution data from a projective model of an analytic resolution

The properness and the original algebraic field map both follow from the actual projective model.
The analytic input gives the exceptional set, thinness on both sides, and the isomorphism
off that set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open Set TopologicalSpace

/-- The actual analytic isomorphism over an open is bijective on its points. -/
theorem analytic_bijOn_of_isIsoOver {A B : SourceReducedComplexSpace}
    {π : A ⟶ B} {U : Set B.obj.left} (h : IsIsoOver π U) :
    BijOn π.hom.left.base (π.hom.left.base ⁻¹' U) U := by
  obtain ⟨V, j, _hj, hjRange, hcomp, hcompRange⟩ := h
  refine ⟨fun _ hx => hx, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ range j.base := hjRange.symm ▸ hx
    have hy' : y ∈ range j.base := hjRange.symm ▸ hy
    obtain ⟨a, rfl⟩ := hx'
    obtain ⟨b, rfl⟩ := hy'
    have hab : a = b := hcomp.base_open.injective hxy
    exact congrArg j.base hab
  · intro y hy
    have hy' : y ∈ range (j ≫ π.hom.left).base := hcompRange.symm ▸ hy
    obtain ⟨a, rfl⟩ := hy'
    exact ⟨j.base a, hjRange ▸ mem_range_self a, rfl⟩

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  {f : X ⟶ Spec (.of ℂ)} [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
  {m : ℕ} (ρ : Y ⟶ X) [SmoothOfRelativeDimension (m + 1) (ρ ≫ f)]
  [IsSeparated (ρ ≫ f)] [QuasiCompact (ρ ≫ f)]

/-- Package the smooth projective model of an analytic resolution of a normal variety.
The given map on complex points is the actual map of the algebraic morphism. -/
noncomputable def Resolution.ofProjectiveModel
    (E : ClosedProjectiveEmbedding (ρ ≫ f))
    (U : X.Opens) [Nonempty U]
    (hbij : Function.Bijective
      (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ f)) (U.ι ≫ f) (ρ ∣_ U) rfl))
    (π : smoothModel (ρ ≫ f) (m + 1) ⟶ UnibAn.analytification f)
    (hπ : ∀ y : SchemeComplexPoint (ρ ≫ f),
      UnibAn.pointMap f (π.hom.left.base ⟨y, mem_univ y⟩) =
        schemeComplexPointMap (ρ ≫ f) f ρ rfl y)
    (Z : Set (UnibAn.analytification f).obj.left) (hZ : (UnibAn.analytification f).IsAnalyticSubset Z)
    (hthin : interior Z = ∅) (hpre : interior (π.hom.left.base ⁻¹' Z) = ∅)
    (hiso : IsIsoOver π Zᶜ) : Resolution f m := by
  let : IsProper (ρ ≫ f) := E.isProper
  let : IsProper ρ := IsProper.of_comp ρ f
  have hfield :=
    exists_stalkCompatible_fieldEquiv_of_restrict_complexPoint_bijective f ρ U hbij
  letI : TopologicalSpace (SchemeComplexPoint (ρ ≫ f)) := schemeAnalyticPointTopology (ρ ≫ f)
  letI : CompactSpace (SchemeComplexPoint (ρ ≫ f)) := E.analyticCompact
  have hcompact : CompactSpace (smoothModel (ρ ≫ f) (m + 1)).obj.left := by
    change CompactSpace (↥(univ : Set (SchemeComplexPoint (ρ ≫ f))))
    exact isCompact_iff_compactSpace.mp isCompact_univ
  have hproper : IsProperMap π.hom.left.base :=
    @Continuous.isProperMap _ _ _ _ _ hcompact (UnibAn.analytification_t2Space (f := f))
      π.hom.left.base.hom.continuous
  exact
    { Y := Y
      fY := ρ ≫ f
      E := E
      ρ := ρ
      comp_eq := rfl
      φ := hfield.choose
      stalkCompatible := hfield.choose_spec
      π := π
      isProperBimeromorphic := ⟨hproper, Z, hZ, hthin, hpre, hiso⟩
      point_eq := hπ }

end SGPT.Okounkov.OF12

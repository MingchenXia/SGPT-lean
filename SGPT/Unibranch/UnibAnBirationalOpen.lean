import SGPT.Unibranch.UnibAnMorphismFunctor
import SGPT.Unibranch.Resolution
import Mathlib.AlgebraicGeometry.Noetherian

/-! An original algebraic isomorphism over an open gives the corresponding analytic open isomorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Unibranch.UnibAn

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Unibranch.SourceReducedComplexSpace

/-- The analytic image of an algebraic open immersion is the literal complex-point trace
of its algebraic range. -/
theorem analytificationMorphism_open_range
    {X Y : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {g : Y ⟶ Spec (.of ℂ)}
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [IsSeparated g] [QuasiCompact g] [LocallyOfFiniteType g]
    (ρ : Y ⟶ X) (h : ρ ≫ f = g) [IsOpenImmersion ρ] :
    Set.range (analytificationMorphism ρ h).hom.left.base =
      (schemeComplexPointImage f ∘ pointMap f) ⁻¹' Set.range ρ := by
  subst g
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have heq := pointMap_analytificationMorphism ρ rfl y
    have hx := congrArg (schemeComplexPointImage f) heq
    exact ⟨schemeComplexPointImage (ρ ≫ f) (pointMap (ρ ≫ f) y),
      (Scheme.Hom.comp_apply _ _ _).symm.trans hx.symm⟩
  · intro hx
    let q := schemeComplexPointLift f ρ (pointMap f x) hx
    obtain ⟨y, hy⟩ := pointMap_surjective q
    refine ⟨y, pointMap_injective ?_⟩
    exact (pointMap_analytificationMorphism ρ rfl y).trans
      ((congrArg (schemeComplexPointMap (ρ ≫ f) f ρ rfl) hy).trans
        (Subtype.ext (schemeComplexPointLift_fac f ρ (pointMap f x) hx)))

/-- The map of reduced complex spaces is an isomorphism over the actual trace of any
algebraic open on which the algebraic morphism is an isomorphism. -/
theorem analytificationMorphism_isIsoOver_of_isIso_restrict
    {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (ρ : Y ⟶ X)
    [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [IsSeparated (ρ ≫ f)] [QuasiCompact (ρ ≫ f)] [LocallyOfFiniteType (ρ ≫ f)]
    (U : X.Opens) [IsIso (ρ ∣_ U)] :
    IsIsoOver (analytificationMorphism ρ rfl)
      ((schemeComplexPointImage f ∘ pointMap f) ⁻¹' (U : Set X)) := by
  let W := ρ ⁻¹ᵁ U
  let g := ρ ≫ f
  let h := W.ι ≫ g
  let : AlgebraicGeometry.IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian g, toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  let : NoetherianSpace W := W.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : IsSeparated h := inferInstanceAs (IsSeparated (W.ι ≫ g))
  let : QuasiCompact h := inferInstanceAs (QuasiCompact (W.ι ≫ g))
  let : LocallyOfFiniteType h := inferInstanceAs (LocallyOfFiniteType (W.ι ≫ g))
  let F : UnibAn.analytification g ⟶ UnibAn.analytification f :=
    analytificationMorphism ρ rfl
  let j : UnibAn.analytification h ⟶ UnibAn.analytification g :=
    analytificationMorphism W.ι rfl
  let q := W.ι ≫ ρ
  have hq : q ≫ f = h := Category.assoc _ _ _
  have hq' : q = (ρ ∣_ U) ≫ U.ι := (morphismRestrict_ι ρ U).symm
  let : IsOpenImmersion q := hq'.symm ▸ inferInstanceAs (IsOpenImmersion ((ρ ∣_ U) ≫ U.ι))
  have hcomp : analytificationMorphism q hq = j ≫ F :=
    analytificationMorphism_comp W.ι ρ rfl rfl
  have hcompLRS : (analytificationMorphism q hq).hom.left = j.hom.left ≫ F.hom.left :=
    congrArg (fun G => G.hom.left) hcomp
  refine ⟨analytificationLRS h, j.hom.left, analytificationMorphism_isOpenImmersion W.ι rfl,
    ?_, ?_, ?_⟩
  · change range (analytificationMorphism W.ι rfl).hom.left.base = _
    rw [analytificationMorphism_open_range, Scheme.Opens.range_ι]
    ext x
    change schemeComplexPointImage g (pointMap g x) ∈ (W : Set Y) ↔
      schemeComplexPointImage f (pointMap f (F.hom.left.base x)) ∈ U
    rw [show pointMap f (F.hom.left.base x) =
      schemeComplexPointMap g f ρ rfl (pointMap g x) from pointMap_analytificationMorphism ρ rfl x]
    change ρ ((pointMap g x).val default) ∈ U ↔ ((pointMap g x).val ≫ ρ) default ∈ U
    rw [Scheme.Hom.comp_apply]
  · rw [← hcompLRS]
    exact analytificationMorphism_isOpenImmersion q hq
  · rw [← hcompLRS]
    have hqRange : range q = (U : Set X) := by
      rw [hq']
      change range (U.ι ∘ (ρ ∣_ U)) = (U : Set X)
      rw [range_comp, (ρ ∣_ U).surjective.range_eq, image_univ, Scheme.Opens.range_ι]
    exact (analytificationMorphism_open_range (g := h) q hq).trans
      (congrArg (fun S => (schemeComplexPointImage f ∘ pointMap f) ⁻¹' S) hqRange)

end SGPT.Unibranch.UnibAn

import SGPT.Projective.OriginalComplexPointClosedFactor
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! Actual original complex-point injectivity detects universal
injectivity via the TRUE diagonal; properness then PRODUCES finiteness.
Blueprint: original-proper-complex-point-finite.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace

/-- Genuine complex-point injection PROVES universal injection of the
actual separated finite-type original scheme map, via its whole diagonal. -/
theorem originalUniversallyInjective_of_complexPoint_injective {X Y : Scheme.{0}}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of ℂ))
    [IsSeparated g] [LocallyOfFiniteType g] [LocallyOfFiniteType (g ≫ f)]
    (hinj : Function.Injective (schemeComplexPointMap (g ≫ f) f g rfl)) :
    UniversallyInjective g := by
  let fY := g ≫ f
  let fP := pullback.fst g g ≫ fY
  have hpoints : ∀ q : SchemeComplexPoint fP,
      (𝟙 (pullback g g)) (schemeComplexPointImage fP q) ∈ range (pullback.diagonal g) := by
    intro q
    let α := schemeComplexPointMap fP fY (pullback.fst g g) rfl q
    have hsecond : pullback.snd g g ≫ fY=fP := by
      dsimp only [fY,fP]
      rw [← Category.assoc,← pullback.condition,Category.assoc]
    let β := schemeComplexPointMap fP fY (pullback.snd g g) hsecond q
    have hX : schemeComplexPointMap fY f g rfl α=schemeComplexPointMap fY f g rfl β := by
      apply Subtype.ext
      change (q.val ≫ pullback.fst g g) ≫ g=(q.val ≫ pullback.snd g g) ≫ g
      rw [Category.assoc,Category.assoc,pullback.condition]
    have hab := congrArg Subtype.val (hinj hX)
    have hdiag : q.val=α.val ≫ pullback.diagonal g := by
      apply pullback.hom_ext
      · rw [Category.assoc,pullback.diagonal_fst,Category.comp_id]
        rfl
      · rw [Category.assoc,pullback.diagonal_snd,Category.comp_id]
        exact hab.symm
    refine ⟨schemeComplexPointImage fY α,?_⟩
    exact congrArg (fun h : Spec (.of ℂ) ⟶ pullback g g => h default) hdiag.symm
  have hrange := originalRangeSubset_of_complexPoints (𝟙 (pullback g g)) fP (pullback.diagonal g) hpoints
  apply (UniversallyInjective.iff_diagonal g).mpr
  exact ⟨fun z => hrange ⟨z,rfl⟩⟩

/-- Proper original map + genuine complex-point injection PRODUCES actual
finiteness. No quasi-finiteness, diagonal surjectivity or finite-map input. -/
theorem originalFinite_of_proper_complexPoint_injective {X Y : Scheme.{0}}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of ℂ)) [IsProper g] [LocallyOfFiniteType (g ≫ f)]
    (hinj : Function.Injective (schemeComplexPointMap (g ≫ f) f g rfl)) : IsFinite g := by
  let : UniversallyInjective g := originalUniversallyInjective_of_complexPoint_injective g f hinj
  let : LocallyQuasiFinite g := inferInstance
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

/-- Properness and true complex-point surjectivity PRODUCE surjectivity
on EVERY original scheme point, via closed range and Jacobson density. -/
theorem originalSurjective_of_proper_complexPoint_surjective {X Y : Scheme.{0}}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of ℂ)) [IsProper g] [LocallyOfFiniteType f]
    (hsurj : Function.Surjective (schemeComplexPointMap (g ≫ f) f g rfl)) : Surjective g := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hclosed : IsClosed (range g) := g.isClosedMap.isClosed_range
  have hpoints : closedPoints X ⊆ range g := by
    intro x hx
    let p : SchemeComplexPoint f := ⟨pointOfClosedPoint f x hx,pointOfClosedPoint_comp f x hx⟩
    obtain ⟨q,hq⟩ := hsurj p
    refine ⟨schemeComplexPointImage (g ≫ f) q,?_⟩
    have hp : schemeComplexPointImage f p=x := pointOfClosedPoint_apply f x hx _
    exact (congrArg (schemeComplexPointImage f) hq).trans hp
  have hfull : (univ : Set X) ⊆ range g := by
    rw [← closure_closedPoints]
    exact closure_minimal hpoints hclosed
  exact ⟨fun x => hfull (mem_univ x)⟩

/-- Every ordinary geometric prerequisite for finite universally
bijective descent is PRODUCED from properness and SAME actual complex
point bijection; no finite/radicial/full-scheme bijection input. -/
theorem originalFiniteUniversalBijection_of_complexPoint_bijective {X Y : Scheme.{0}}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of ℂ)) [IsProper g] [LocallyOfFiniteType f]
    (hbij : Function.Bijective (schemeComplexPointMap (g ≫ f) f g rfl)) :
    IsFinite g ∧ UniversallyInjective g ∧ Surjective g :=
  ⟨originalFinite_of_proper_complexPoint_injective g f hbij.1,
    originalUniversallyInjective_of_complexPoint_injective g f hbij.1,
    originalSurjective_of_proper_complexPoint_surjective g f hbij.2⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

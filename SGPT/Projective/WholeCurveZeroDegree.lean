import SGPT.Projective.WholeCurveZeroArtinian
import Mathlib.Data.ENat.BigOperators

/-! Independent ACTUAL structural algebraic zero cycle of the ENTIRE original
smooth projective curve and its ALL-component degree sum. Blueprint: whole-curve-zero-degree.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open scoped BigOperators
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤))

/-- Independent actual original structural AlgebraicCycle.map, ALL zero points and original lengths. -/
def wholeCurveSectionZeroCycleDegree (hs : SectionNonzeroOnComponents f E s) :
    AlgebraicCycle (Spec (.of ℂ)) ℤ := by
  let := wholeCurveSectionZero_isArtinian f E a s hs
  exact artinianStructuralPushforward (E.sectionZero a s)

/-- Each SAME ordinary original restricted section has its independent ACTUAL algebraic degree. -/
def curveComponentSectionZeroCycleDegree (hs : SectionNonzeroOnComponents f E s)
    (C : ↥(irreducibleComponents X)) : AlgebraicCycle (Spec (.of ℂ)) ℤ := by
  let := smoothProjective_component_isIntegral f 1 E C.val C.property
  let := smoothProjective_component_smoothDimension f 1 E C.val C.property
  exact sectionZeroCycleDegree ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f)
    (smoothProjective_componentEmbedding f 1 E C.val C.property)
    (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
    (originalCurveComponentSection f E s C) (hs C)

/-- Independent full original zero-cycle coefficient, before any analytic period. -/
theorem wholeCurveSectionZeroCycleDegree_apply (hs : SectionNonzeroOnComponents f E s)
    (b : Spec (.of ℂ)) :
    let := wholeCurveSectionZero_isArtinian f E a s hs
    let : Fintype (sectionZeroSubscheme a s) := Fintype.ofFinite _
    wholeCurveSectionZeroCycleDegree f E a s hs b =
      ((∑ z : sectionZeroSubscheme a s,
        Module.length ((sectionZeroSubscheme a s).presheaf.stalk z)
          ((sectionZeroSubscheme a s).presheaf.stalk z)).toNat : ℤ) := by
  let := wholeCurveSectionZero_isArtinian f E a s hs
  exact artinianStructuralPushforward_apply (E.sectionZero a s) b

/-- Each actual restricted original structural degree is its ENTIRE true local length sum. -/
theorem curveComponentSectionZeroCycleDegree_apply (hs : SectionNonzeroOnComponents f E s)
    (C : ↥(irreducibleComponents X)) (b : Spec (.of ℂ)) :
    let := curveComponentZero_isArtinian f E a s hs C
    let : Fintype (sectionZeroSubscheme
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
      (originalCurveComponentSection f E s C)) := Fintype.ofFinite _
    curveComponentSectionZeroCycleDegree f E a s hs C b =
      ((∑ z : sectionZeroSubscheme
        (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
        (originalCurveComponentSection f E s C),
        Module.length ((sectionZeroSubscheme
          (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
          (originalCurveComponentSection f E s C)).presheaf.stalk z)
          ((sectionZeroSubscheme
          (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
          (originalCurveComponentSection f E s C)).presheaf.stalk z)).toNat : ℤ) := by
  let := smoothProjective_component_isIntegral f 1 E C.val C.property
  let := smoothProjective_component_smoothDimension f 1 E C.val C.property
  exact sectionZeroCycleDegree_eq_sum_lengths
    ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f)
    (smoothProjective_componentEmbedding f 1 E C.val C.property)
    (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
    (originalCurveComponentSection f E s C) (hs C) b

/-- SAME independent original whole zero degree is the genuine sum over ALL original components. -/
theorem wholeCurveSectionZeroCycleDegree_eq_sum_components
    (hs : SectionNonzeroOnComponents f E s) (b : Spec (.of ℂ)) :
    let : Finite ↥(irreducibleComponents X) := smoothProjective_componentIndex_finite f E
    let : Fintype ↥(irreducibleComponents X) := Fintype.ofFinite _
    wholeCurveSectionZeroCycleDegree f E a s hs b =
      ∑ C : ↥(irreducibleComponents X), curveComponentSectionZeroCycleDegree f E a s hs C b := by
  classical
  let := smoothProjective_componentIndex_finite f E
  let : Fintype ↥(irreducibleComponents X) := Fintype.ofFinite _
  let := wholeCurveSectionZero_isArtinian f E a s hs
  let : Fintype (sectionZeroSubscheme a s) := Fintype.ofFinite _
  let (C : ↥(irreducibleComponents X)) : IsArtinianScheme (originalZeroComponentOpen f 1 E a s C) :=
    wholeCurveZeroComponent_isArtinian f E a s hs C
  let (C : ↥(irreducibleComponents X)) : Fintype (originalZeroComponentOpen f 1 E a s C) := Fintype.ofFinite _
  let (C : ↥(irreducibleComponents X)) : IsArtinianScheme (sectionZeroSubscheme
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
      (originalCurveComponentSection f E s C)) := curveComponentZero_isArtinian f E a s hs C
  let (C : ↥(irreducibleComponents X)) : Fintype (sectionZeroSubscheme
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
      (originalCurveComponentSection f E s C)) := Fintype.ofFinite _
  let len (C : ↥(irreducibleComponents X)) := ∑ z : sectionZeroSubscheme
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
      (originalCurveComponentSection f E s C),
      Module.length ((sectionZeroSubscheme
        (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
        (originalCurveComponentSection f E s C)).presheaf.stalk z)
        ((sectionZeroSubscheme
        (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
        (originalCurveComponentSection f E s C)).presheaf.stalk z)
  have hsum : (∑ z : sectionZeroSubscheme a s,
      Module.length ((sectionZeroSubscheme a s).presheaf.stalk z)
        ((sectionZeroSubscheme a s).presheaf.stalk z)) = ∑ C, len C := by
    rw [originalZero_fullLength_sum_components f 1 E a s]
    exact Finset.sum_congr rfl (fun C _ => wholeCurveZeroComponent_fullLength_sum f E a s hs C)
  rw [wholeCurveSectionZeroCycleDegree_apply, hsum,
    ENat.toNat_sum (fun C _ => ENat.sum_ne_top.mpr (fun z _ => artinianLocalLength_ne_top _ z)), Nat.cast_sum]
  exact Finset.sum_congr rfl (fun C _ => (curveComponentSectionZeroCycleDegree_apply f E a s hs C b).symm)

end SGPT.Projective.NumEq.AlgebraicCurveDegree

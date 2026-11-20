import SGPT.Projective.OriginalProperComplexPointFinite
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! Actual original characteristic-zero residue-field descent for a
genuine universally injective original scheme morphism. Blueprint:
original-characteristic-zero-residue.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes

/-- The actual original structural coefficient map into every original
residue field, including nonclosed and generic points. -/
def originalPointResidueScalar {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (x : X) :
    ℂ →+* X.residueField x :=
  (X.residue x).hom.comp ((X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom))

/-- The SAME actual original residue field has characteristic zero,
proved from the actual original structural coefficient map. -/
theorem originalPointResidue_charZero {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (x : X) :
    CharZero (X.residueField x) :=
  charZero_of_injective_ringHom (originalPointResidueScalar f x).injective

/-- Actual universal injection and actual original characteristic-zero
geometry prove that EVERY original residue-field map is an isomorphism.
No generic degree, field equality, or residue-field certificate input. -/
theorem originalResidueFieldMap_isIso_of_universallyInjective {X Y : Scheme}
    (g : Y ⟶ X) (f : X ⟶ Spec (.of ℂ)) [UniversallyInjective g] (y : Y) :
    IsIso (g.residueFieldMap y) := by
  let : CharZero (X.residueField (g y)) := originalPointResidue_charZero f (g y)
  have hg : Function.Injective g ∧ ∀ y, (g.residueFieldMap y).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective g).out 0 2).mp (show UniversallyInjective g from inferInstance)
  have hp : (g.residueFieldMap y).hom.IsPurelyInseparable := hg.2 y
  let := (g.residueFieldMap y).hom.toAlgebra
  let : IsPurelyInseparable (X.residueField (g y)) (Y.residueField y) := hp
  let : PerfectField (X.residueField (g y)) := PerfectField.ofCharZero
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (IsPurelyInseparable.bijective_algebraMap_of_isSeparable
      (X.residueField (g y)) (Y.residueField y))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

import SGPT.Okounkov.AdmissibleFlag
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.LocalRing.Module

/-! Formal smoothness and finite free differentials of the ACTUAL
original structural complex stalk. Blueprint: algebraic-smooth-stalk.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry IsLocalRing
open SGPT.Okounkov

private def complexBaseStalkIso (y : Spec (.of ℂ)) :
    (Spec (.of ℂ)).presheaf.stalk y ≅ CommRingCat.of ℂ :=
  (Spec (.of ℂ)).presheaf.stalkCongr
    (.of_eq (Subsingleton.elim y (closedPoint ℂ))) ≪≫ stalkClosedPointIso (.of ℂ)

private theorem complexBaseStalkIso_germ (y : Spec (.of ℂ)) :
    (Spec (.of ℂ)).presheaf.germ ⊤ y trivial ≫ (complexBaseStalkIso y).hom =
      (Scheme.ΓSpecIso (.of ℂ)).hom := by
  dsimp only [complexBaseStalkIso, Iso.trans_hom]
  rw [← Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.germ_stalkSpecializes]
  exact germ_stalkClosedPointIso_hom (.of ℂ)

private theorem complexBaseStalkIso_inv (y : Spec (.of ℂ)) :
    (complexBaseStalkIso y).inv =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).presheaf.germ ⊤ y trivial := by
  apply (cancel_mono (complexBaseStalkIso y).hom).mp
  rw [Category.assoc, complexBaseStalkIso_germ, Iso.inv_hom_id, Iso.inv_hom_id]

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (x : X)

private theorem originalStalk_structure_map :
    letI := stalkComplexAlgebra f x
    ((complexBaseStalkIso (f x)).inv ≫ f.stalkMap x).hom =
      algebraMap ℂ (X.presheaf.stalk x) := by
  let := stalkComplexAlgebra f x
  rw [complexBaseStalkIso_inv, Category.assoc, f.germ_stalkMap]
  rfl

/-- The actual original structural complex algebra is equivalent to the
actual original morphism stalk map for formal smoothness. -/
theorem originalStalk_formallySmooth_iff :
    letI := stalkComplexAlgebra f x
    Algebra.FormallySmooth ℂ (X.presheaf.stalk x) ↔ (f.stalkMap x).hom.FormallySmooth := by
  let := stalkComplexAlgebra f x
  rw [← RingHom.formallySmooth_algebraMap, ← originalStalk_structure_map f x]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _

/-- An actual original smooth scheme's original structural stalk is
genuinely formally smooth and essentially of finite type, with finite
FREE original differentials. No local regularity/freeness certificate input. -/
theorem originalSmoothStalk_differentials [Smooth f] :
    letI := stalkComplexAlgebra f x
    Algebra.FormallySmooth ℂ (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType ℂ (X.presheaf.stalk x) ∧
      Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] ∧
      Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄ℂ] := by
  let := stalkComplexAlgebra f x
  have hfs : (f.stalkMap x).hom.FormallySmooth := by
    have hmem : x ∈ f.smoothLocus := by rw [f.smoothLocus_eq_top]; trivial
    exact hmem
  let : Algebra.FormallySmooth ℂ (X.presheaf.stalk x) :=
    (originalStalk_formallySmooth_iff f x).mpr hfs
  have hft : (f.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f x
  have hbase : ((complexBaseStalkIso (f x)).inv).hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (complexBaseStalkIso (f x)).commRingCatIsoToRingEquiv.symm.surjective).essFiniteType
  have he : (algebraMap ℂ (X.presheaf.stalk x)).EssFiniteType := by
    rw [← originalStalk_structure_map f x]
    exact hbase.comp hft
  let : Algebra.EssFiniteType ℂ (X.presheaf.stalk x) := RingHom.essFiniteType_algebraMap.mp he
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact Module.free_of_flat_of_isLocalRing

/-- Actual original morphism stalk maps commute with the ORIGINAL
structural complex algebras, before any smoothness or quotient assumption. -/
theorem originalStalk_algebraMap_comp {Y : Scheme.{0}} (i : Y ⟶ X) (y : Y) (c : ℂ) :
    letI := stalkComplexAlgebra f (i y)
    letI := stalkComplexAlgebra (i ≫ f) y
    (i.stalkMap y).hom (algebraMap ℂ (X.presheaf.stalk (i y)) c) =
      algebraMap ℂ (Y.presheaf.stalk y) c := by
  change i.stalkMap y (X.presheaf.germ ⊤ (i y) trivial
    (f.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c))) =
      Y.presheaf.germ ⊤ y trivial ((i ≫ f).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c))
  rw [i.germ_stalkMap_apply]
  rfl

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

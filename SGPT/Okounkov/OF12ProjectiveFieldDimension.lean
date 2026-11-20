import SGPT.Okounkov.OF12NormalProjectiveField
import SGPT.Foundations.Schemes.NativeSmoothFunctionFieldDimension

/-! The actual stalk-compatible field equivalence is linear over the structural base field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Spec (.of K)) (ρ : Y ⟶ X)
  (e : X.functionField ≃+* Y.functionField) (he : IsStalkCompatible ρ e.toRingHom)

/-- The stalk condition forces the scalar action induced by the original structure morphisms,
even when the target scheme is singular. -/
def IsStalkCompatible.toFunctionFieldAlgEquiv :
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionFieldAlgebra (ρ ≫ f)
    X.functionField ≃ₐ[K] Y.functionField := by
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionFieldAlgebra (ρ ≫ f)
  refine { e with commutes' := ?_ }
  intro c
  let y := genericPoint Y
  let a := X.presheaf.germ ⊤ (ρ y) trivial (schemeGlobalConstants f c)
  have hX : algebraMap (X.presheaf.stalk (ρ y)) X.functionField a =
      algebraMap K X.functionField c :=
    X.presheaf.germ_stalkSpecializes_apply (show ρ y ∈ (⊤ : X.Opens) from trivial)
      ((genericPoint_spec X).specializes (show ρ y ∈ (Set.univ : Set X) from trivial))
      (schemeGlobalConstants f c)
  have hY : (ρ.stalkMap y).hom a = algebraMap K Y.functionField c := by
    change (ρ.stalkMap y).hom (X.presheaf.germ ⊤ (ρ y) trivial (schemeGlobalConstants f c)) =
      Y.presheaf.germ ⊤ y trivial (schemeGlobalConstants (ρ ≫ f) c)
    refine (ρ.germ_stalkMap_apply ⊤ y trivial (schemeGlobalConstants f c)).trans ?_
    congr 1
  change e (algebraMap K X.functionField c) = algebraMap K Y.functionField c
  rw [← hX]
  have h := he y a
  change e (algebraMap (X.presheaf.stalk (ρ y)) X.functionField a) =
    Y.presheaf.stalkSpecializes (specializes_refl y) ((ρ.stalkMap y).hom a) at h
  rw [TopCat.Presheaf.stalkSpecializes_refl, hY] at h
  exact h

include e he in
/-- Relative dimension on a smooth model equals the original function-field
transcendence degree, with the original structural scalars on the base. -/
theorem functionField_trdeg_of_stalkCompatible_smooth_model
    (n : ℕ) [SmoothOfRelativeDimension n (ρ ≫ f)] :
    letI := schemeFunctionFieldAlgebra f
    Algebra.trdeg K X.functionField = n := by
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionFieldAlgebra (ρ ≫ f)
  exact (IsStalkCompatible.toFunctionFieldAlgEquiv f ρ e he).trdeg_eq.trans
    (nativeSmoothFunctionField_trdeg (ρ ≫ f) n)

end SGPT.Okounkov.OF12

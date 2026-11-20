import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Actual generic pullback commutes with every original stalk map

This is the literal original structure-sheaf specialization square, including
all original local germs, for any actual generic-point-preserving morphism.
Blueprint: `projective-graph-projection.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality

open CategoryTheory AlgebraicGeometry

variable {X M : Scheme.{0}} [IsIntegral X] [IsIntegral M]
  (ρ : M ⟶ X) (hρ : ρ (genericPoint M) = genericPoint X)

/-- The actual original generic-stalk pullback of an actual generic-point-preserving morphism. -/
def genericPullback : X.functionField →+* M.functionField :=
  (ρ.stalkMap (genericPoint M)).hom.comp
    ((X.presheaf.stalkCongr (.of_eq hρ.symm)).hom.hom)

/-- **The whole original stalk square**: native generic pullback agrees with actual local pullback
and actual specialization on every original stalk element. -/
theorem genericPullback_stalk (y : M) (g : X.presheaf.stalk (ρ y)) :
    genericPullback ρ hρ (algebraMap (X.presheaf.stalk (ρ y)) X.functionField g) =
      algebraMap (M.presheaf.stalk y) M.functionField (ρ.stalkMap y g) := by
  have hnat := ρ.stalkSpecializes_stalkMap (genericPoint M) y ((genericPoint_spec M).specializes trivial)
  have hmap : X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (show ρ y ∈ (Set.univ : Set X) from trivial)) ≫
      (X.presheaf.stalkCongr (.of_eq hρ.symm)).hom ≫ ρ.stalkMap (genericPoint M) =
        ρ.stalkMap y ≫ M.presheaf.stalkSpecializes ((genericPoint_spec M).specializes trivial) := by
    dsimp only [TopCat.Presheaf.stalkCongr]
    rw [← Category.assoc, X.presheaf.stalkSpecializes_comp]
    exact hnat
  exact congrArg (fun k : X.presheaf.stalk (ρ y) ⟶ M.functionField => k g) hmap

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality

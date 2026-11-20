import SGPT.Projective.BDivNov16OriginalClosedImmersionPointDimension
/-! Blueprint first: BDivNov16OriginalPointClosureHeight.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.BDivNov16
open AlgebraicGeometry TopologicalSpace SGPT.Projective.NumEq.AlgebraicCurveDegree

theorem originalIntegralClosedImmersion_generic_pointDimension
    {Z X : Scheme.{0}} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i] :
    (pointDimension X (i (genericPoint Z)) : WithBot ℕ∞) = topologicalKrullDim Z := by
  rw [originalClosedImmersion_pointDimension i]
  let e : Z ≃o Specialization Z :=
    { Specialization.toEquiv with map_rel_iff' := by intros; rfl }
  have hh := Order.height_orderIso e (genericPoint Z)
  change pointDimension Z (genericPoint Z) = Order.height (genericPoint Z) at hh
  rw [hh]
  change (Order.height (⊤ : Z) : WithBot ℕ∞) = _
  rw [Order.height_top_eq_krullDim]
  exact (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Z))).symm
end SGPT.Projective.BDivNov16

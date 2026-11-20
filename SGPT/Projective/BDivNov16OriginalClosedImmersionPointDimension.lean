import SGPT.Projective.AlgebraicArtinianCycleDegree
/-! Blueprint first: BDivNov16OriginalClosedImmersionPointDimension.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.BDivNov16
open AlgebraicGeometry TopologicalSpace SGPT.Projective.NumEq.AlgebraicCurveDegree

theorem originalClosedImmersion_pointDimension {Z X : Scheme.{0}}
    (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    pointDimension X (i z) = pointDimension Z z := by
  let e : Specialization Z ↪o Specialization X :=
    { toFun := fun a => Specialization.toEquiv (i (Specialization.ofEquiv a))
      inj' := fun _ _ h => i.isClosedEmbedding.injective h
      map_rel_iff' := by
        intro a b
        exact i.isClosedEmbedding.isEmbedding.isInducing.specializes_iff }
  have hlow : ∀ a : Specialization Z, ∀ b : Specialization X,
      b < e a → ∃ a', a' < a ∧ e a' = b := by
    intro a b hba
    have hs : i (Specialization.ofEquiv a) ⤳ Specialization.ofEquiv b := hba.le
    have hb : Specialization.ofEquiv b ∈ Set.range i :=
      (specializes_iff_forall_closed.mp hs) (Set.range i)
        i.isClosedEmbedding.isClosed_range ⟨Specialization.ofEquiv a,rfl⟩
    obtain ⟨a',ha'⟩ := hb
    refine ⟨Specialization.toEquiv a',?_,ha'⟩
    apply e.lt_iff_lt.mp
    simpa only [show e (Specialization.toEquiv a') = b from ha'] using hba
  exact (Order.height_eq_of_strictMono e e.strictMono hlow
    (Specialization.toEquiv z)).symm
end SGPT.Projective.BDivNov16

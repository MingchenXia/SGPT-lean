import SGPT.Foundations.Schemes.NativeArtinianProjectiveComplexFiniteness
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The ACTUAL singleton open of a discrete scheme. -/
def discreteSingletonOpen (X : Scheme.{u}) [DiscreteTopology X] (x : X) : X.Opens :=
  ⟨{x}, isOpen_discrete _⟩

/-- Actual singleton opens genuinely cover, without a finiteness premise. -/
theorem discreteSingletonOpens_covers (X : Scheme.{u}) [DiscreteTopology X] :
    iSup (discreteSingletonOpen X) = ⊤ := by
  ext x
  simp [discreteSingletonOpen]

/-- The literal singleton germ is the terminal-index colimit insertion and
is genuinely invertible on the SAME actual scheme stalk. -/
theorem discreteSingletonGerm_isIso (X : Scheme.{u}) [DiscreteTopology X] (x : X) :
    IsIso (X.presheaf.germ (discreteSingletonOpen X x) x (by simp [discreteSingletonOpen])) := by
  let U : OpenNhds x := ⟨discreteSingletonOpen X x, by simp [discreteSingletonOpen]⟩
  have hU : IsInitial U := IsInitial.ofUniqueHom
    (fun V ↦ homOfLE (show U ≤ V from by
      intro y hy
      have hyx : y = x := hy
      simpa only [hyx] using V.property))
    (fun V f ↦ Subsingleton.elim _ _)
  exact isIso_ι_of_isTerminal hU.op ((OpenNhds.inclusion x).op ⋙ X.presheaf)

/-- Isomorphism whose forward map is the LITERAL original singleton germ. -/
def discreteSingletonGermIso (X : Scheme.{u}) [DiscreteTopology X] (x : X) :
    Γ(X, discreteSingletonOpen X x) ≅ X.presheaf.stalk x := by
  let := discreteSingletonGerm_isIso X x
  exact asIso (X.presheaf.germ (discreteSingletonOpen X x) x (Set.mem_singleton x))


/-- Actual base scalars on the SAME native structure-sheaf stalk. -/
abbrev schemeStalkGlobalConstantsAlgebra {X : Scheme.{u}} {K : Type u} [CommRing K]
    (c : K →+* Γ(X, ⊤)) (x : X) : Algebra K (X.presheaf.stalk x) :=
  ((X.presheaf.Γgerm x).hom.comp c).toAlgebra


end
end SGPT.Foundations.Schemes

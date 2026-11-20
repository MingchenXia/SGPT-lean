import SGPT.Unibranch.ComplexSpaceUnibranchFibers
import SGPT.Unibranch.ComplexSpaceThetaFiberMaximum

/-! Actual original unibranch/birational hypotheses internally produce
fiber constancy and unique USC descent of the SAME unbounded theta-PSH
function. Blueprint: complex-space-theta-unibranch-descent.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- All literal fiber connectedness is produced from the ORIGINAL
unibranch and actual proper-bimeromorphic hypotheses. -/
theorem IsThetaPSH.eq_on_fiber_of_isProperBimeromorphic
    {X Y : SourceReducedComplexSpace} (θ : SpaceForm X 2) (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {ψ : Y.obj.left → EReal} (hψ : Y.IsThetaPSH (SpaceForm.pullback θ π) ψ)
    {a b : Y.obj.left} (hab : π.hom.left.base a = π.hom.left.base b) : ψ a = ψ b :=
  hψ.eq_on_connected_proper_fiber θ π hπ.1 (π.hom.left.base a)
    (hπ.isConnected_fiber_of_isUnibranch hX _) rfl hab.symm

/-- Original actual birational/unibranch geometry internally supplies the
unique literal USC descent, with NO output PSH or connected-fiber premise. -/
theorem IsThetaPSH.exists_unique_usc_descent_of_isProperBimeromorphic
    {X Y : SourceReducedComplexSpace} (θ : SpaceForm X 2) (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {ψ : Y.obj.left → EReal} (hψ : Y.IsThetaPSH (SpaceForm.pullback θ π) ψ) :
    ∃! φ : X.obj.left → EReal,UpperSemicontinuous φ ∧
      ∀ y : Y.obj.left,φ (π.hom.left.base y) = ψ y :=
  hψ.exists_unique_usc_descent_of_connected_proper_fibers θ π hπ.1
    (fun x => hπ.isConnected_fiber_of_isUnibranch hX x)

end SGPT.Unibranch.SourceReducedComplexSpace

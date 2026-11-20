import SGPT.Unibranch.HironakaG10SumCentreSupportGeometry
import SGPT.Foundations.Analysis.Pending.HironakaNativeFiniteIdealSections

/-!
# Sum centres from an actual finite-type ideal module

A compactly supported native ideal module supplies the second family in the
sum-centre construction. No choice of stalk generators or compactness of the
intersection is supplied as extra family data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Unibranch.HironakaG10FiniteIdealSumCentre

open SGPT.Foundations.Analysis.Pending HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaNativeFiniteIdealSections
open SGPT.Unibranch.HironakaG10HirLocalFlattener
  SGPT.Unibranch.HironakaG10ChowTrackedDatum
  SGPT.Unibranch.HironakaG10ChowFlatteningDriver
  SGPT.Unibranch.HironakaG10ChowStrictFlatLocus
  SGPT.Unibranch.HironakaG10SumCentreSupportGeometry
  SGPT.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- The whole image ideal of a native ideal-module map at each stalk. -/
def wholeIdealFamily {X : SourceReducedComplexSpace}
    (E : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (e : E ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (x : X.obj.left) : Ideal (X.obj.left.presheaf.stalk x) := by
  exact LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf E e x)

/-- The whole stalk images of an actual finite-type ideal module form a
locally finitely generated ideal family on any chosen domain. -/
theorem locallyFinite_wholeIdealFamily {X : SourceReducedComplexSpace}
    (E : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (e : E ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
    [E.IsFiniteType] (V : Set X.obj.left) :
    IsLocallyFinitelyGeneratedOn X.obj.left V
      (wholeIdealFamily E e) := by
  intro x _hx
  obtain ⟨U, hxU, r, s, _, hs⟩ := exists_finite_ideal_sections E e x
  exact ⟨U, hxU, r, fun i => e.val.app (op U) (s i), fun y hy _ => hs y hy⟩

/-- A compactly supported finite-type ideal module supplies an actual
admissible sum centre once its intersection with the flattener support is
known to lie in the non-flat image. -/
theorem exists_admissible_sumCentre_from_finiteIdeal
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (Z : LocalFlattener f)
    (E : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (e : E ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
    [E.IsFiniteType]
    (hCompact : IsCompact (nonunitLocus E e))
    (hInside : nonunitLocus E e ⊆ Z.V)
    (hDense : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf E e x) = ⊤})
    (hNonflat : {x : X.obj.left | x ∈ Z.support ∧ x ∈ nonunitLocus E e} ⊆ nonflatImage f) :
    ∃ α : ℕ, ∀ β : ℕ, α ≤ β →
      ∃ c : AdmissibleCentre f,
        nonunitLocus c.B c.b = {x | x ∈ Z.support ∧ x ∈ nonunitLocus E e} ∧
        IsSumCentreFor c.B c.b f β := by
  let IS := wholeIdealFamily E e
  have hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS :=
    locallyFinite_wholeIdealFamily E e Z.V
  have hQK : {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤} ⊆ nonunitLocus E e := by
    intro x hx
    exact hx.2
  exact exists_admissible_sumCentre_of_compact_container f Z IS hIS
    (nonunitLocus E e) hCompact hInside hQK hDense hNonflat

end
end SGPT.Unibranch.HironakaG10FiniteIdealSumCentre

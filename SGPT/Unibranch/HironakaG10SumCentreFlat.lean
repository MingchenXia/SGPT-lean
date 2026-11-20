import SGPT.Unibranch.HironakaG10HirGermFlattener
import SGPT.Unibranch.HironakaG10ChowTrackedDatum

/-! # Flatness over an actual tracked sum centre -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace SGPT.Unibranch.HironakaG10SumCentreFlat

open SGPT.Foundations.Analysis.Pending HironakaSingularModuleSheafStalk
open SGPT.Unibranch.HironakaG10HirGermFlattener
  SGPT.Unibranch.HironakaG10ChowTrackedDatum
  SGPT.Unibranch.HironakaG10ChowLeavingRounds
  SGPT.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- A tracked sum centre satisfies the flatness condition in Hironaka's
  definition of permissibility at every centre point. -/
theorem flatOver_sumCentre {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (β : ℕ) (hSum : IsSumCentreFor B b f β) :
    ∀ x ∈ nonunitLocus B b, FlatOverAt f x
      (LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x)) := by
  intro x hx
  obtain ⟨IS, α, hα, hAR, hB⟩ := hSum x hx
  have h := isGermFlattenerAt_germFlattener f x
  apply (h _).2
  rw [hB]
  exact le_sup_right

end
end SGPT.Unibranch.HironakaG10SumCentreFlat

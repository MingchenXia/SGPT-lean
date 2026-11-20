import SGPT.Unibranch.HironakaG10ChowTrackedDatum
import SGPT.Foundations.Analysis.Pending.HironakaG10StrictIdealGenerator

/-! # Germ strict-transform membership from one regular chart generator -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.HironakaG10StrictChartMembership
open SGPT.Foundations.Analysis.Pending HironakaG10ChowArtinReesCentre
  HironakaG10StrictIdealGenerator
open SGPT.Unibranch.HironakaG10ChowTrackedDatum

/-- One chosen regular generator suffices to test the universal
regular-generator condition defining germ strict-transform membership. -/
theorem onStrictTransform_iff_of_generator
    {X X' : SourceReducedComplexSpace} (σ : X' ⟶ X) (x' : X'.obj.left)
    (I D : Ideal (X.obj.left.presheaf.stalk (σ.hom.left.base x')))
    (G : X'.obj.left.presheaf.stalk x') (hG : IsRegular G)
    (hD : Ideal.map (σ.hom.left.stalkMap x').hom D = Ideal.span {G}) :
    OnStrictTransform σ x' I D ↔
      strictIdeal (σ.hom.left.stalkMap x').hom I D G ≠ ⊤ := by
  constructor
  · intro h
    exact h G hG hD
  · intro h H _hH hDH
    have heq := strictIdeal_eq_of_regular_span_eq
      (σ.hom.left.stalkMap x').hom I D hG (hD.symm.trans hDH)
    exact heq ▸ h

end SGPT.Unibranch.HironakaG10StrictChartMembership

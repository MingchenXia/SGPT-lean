import SGPT.Checks.Comparison.BJTopology
import SGPT.NAPotential.BJSectionValuation
import SGPT.Foundations.Envelope.Berkovich.SchemeCenterAffine

/-! Actual native centers share original center neighborhoods, proved from
original germ nonnegativity and native proper bounded-affine uniqueness.
All original supports and the trivial point are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.BJ
open AlgebraicGeometry CategoryTheory Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Envelope.Berkovich
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProper p]

/-- Native regular-function boundedness is INTERNALLY proved from the
actual original center, not supplied by an incoming centering certificate. -/
theorem nativeEval_le_one_of_sourceCenter_mem (v : BerkovichPoint p)
    (U : X.Opens) (hc : v.center∈U) (s : Γ(X,U)) :
    SchemeValuedPoint.eval (pointEquiv p v).1 U
      (v.support_specializes_center.mem_open U.isOpen hc) s≤1 := by
  have hn : 0≤v.sectionVal U
      (v.support_specializes_center.mem_open U.isOpen hc) s := by
    rw [← centerVal_germ_eq_sectionVal v U hc]
    exact v.centerVal_nonneg _
  change expNegNN (v.sectionVal U
    (v.support_specializes_center.mem_open U.isOpen hc) s)≤1
  simpa only [expNegNN_zero] using expNegNN_antitone hn

/-- Genuine bounded-affine valuative uniqueness places the ACTUAL native
center in the SAME original affine neighborhood of the original center. -/
theorem nativeCenter_mem_affine_of_sourceCenter_mem (v : BerkovichPoint p)
    (U : X.affineOpens) (hc : v.center∈U.1) :
    RelativeSchemeValuedPoint.center Valuation.one_apply_le_one (pointEquiv p v)∈U.1 := by
  exact RelativeSchemeValuedPoint.center_mem_of_bounded_affine Valuation.one_apply_le_one
    (pointEquiv p v) U (v.support_specializes_center.mem_open U.1.isOpen hc)
    (fun s => nativeEval_le_one_of_sourceCenter_mem p v U.1 hc s)

/-- Every original center-containing frame open also contains the actual
native center. No center-equality/norm-compatibility hypothesis is assumed. -/
theorem nativeCenter_mem_of_sourceCenter_mem (v : BerkovichPoint p)
    (U : X.Opens) (hc : v.center∈U) :
    RelativeSchemeValuedPoint.center Valuation.one_apply_le_one (pointEquiv p v)∈U := by
  obtain ⟨W,hW,hcW,hWU⟩ := exists_isAffineOpen_mem_and_subset (X:=X) (U:=U) (x:=v.center) hc
  exact hWU (nativeCenter_mem_affine_of_sourceCenter_mem p v ⟨W,hW⟩ hcW)

end SGPT.NAPotential.BJ

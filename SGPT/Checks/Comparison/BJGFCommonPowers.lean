import SGPT.Checks.Comparison.BJPrintedDefinition
import SGPT.Checks.Comparison.BJRationalPicardCommonPowers

/-! The genuine common-power producer applied to literal source rational
GF membership. No supplied common line, isomorphism or torsion bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ.NativePicard
variable {X : Scheme.{0}}

/-- Original class equality alone produces an actual isomorphism of the
actual section-power sheaves with common positive normalizations. -/
theorem RationalGFPackage.exists_common_tensorPower_iso
    (D E : RationalGFPackage X) (h : D.picardClass=E.picardClass) :
    ∃ k : ℕ,0<k ∧ Nonempty
      (bundleTensorPower (bundleTensorPower D.line D.n) (E.m*k)≅
        bundleTensorPower (bundleTensorPower E.line E.n) (D.m*k)) := by
  apply exists_pos_tensorPower_iso_of_normalized_class_eq
    (powerAtlas D.atlas D.n) (powerAtlas E.atlas E.n)
    D.data.denominator_pos E.data.denominator_pos
  simpa only [RationalGFPackage.picardClass,gfPicardClass_eq_powerClass] using h

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- Both actual presentations and their true common-power isomorphism are
internally produced from the original two source-GF membership hypotheses. -/
theorem IsRationalGF.exists_common_tensorPower_iso
    {L : RationalPicardSpace X} {φ ψ : BerkovichPoint p → EReal}
    (hφ : IsRationalGF p L φ) (hψ : IsRationalGF p L ψ) :
    ∃ (D E : RationalGFPackage X),D.picardClass=L ∧ E.picardClass=L ∧
      D.eval p=φ ∧ E.eval p=ψ ∧ ∃ k : ℕ,0<k ∧ Nonempty
        (bundleTensorPower (bundleTensorPower D.line D.n) (E.m*k)≅
          bundleTensorPower (bundleTensorPower E.line E.n) (D.m*k)) := by
  obtain ⟨D,hDL,hDφ⟩ := hφ
  obtain ⟨E,hEL,hEψ⟩ := hψ
  exact ⟨D,E,hDL,hEL,hDφ,hEψ,D.exists_common_tensorPower_iso E (hDL.trans hEL.symm)⟩

end SGPT.NAPotential.BJ.Printed

import SGPT.Checks.Comparison.BJPair3Comparison
import SGPT.Checks.Comparison.BJOriginalRegularity

/-!
# Psh metrics are determined by their values on `X^Div`

Source: `chapter_NApotential.tex`, the uniqueness clauses of `prop:PhiinducePSH` and
`cor:testcurvegivepshme` ("the extension is unique if it exists by `thm:pshdetbydiv`"): two psh
metrics on `L^An` (`def:BJpshmetric`) that agree on `X^Div` (the divisorial valuations `t ord_E`,
`t ∈ ℚ_{>0}`, and `v_triv`: `sourceDivisorialSet`) agree on all of `X^An`. This is
`thm:pshdetbydiv` (`SGPT.NAPotential.BJ.divisorialComparison`) applied in both directions, psh
metrics being upper semicontinuous.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJ.Assembly

open AlgebraicGeometry CategoryTheory
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- **Uniqueness of psh extensions from `X^Div`**: two psh metrics on `L^An` that agree on
`X^Div` are equal. -/
theorem eq_of_eqOn_sourceDivisorialSet {L : RationalPicardSpace X}
    {φ ψ : BerkovichPoint p → EReal} (hφ : IsModuleTopologyPSH.{0} p L φ)
    (hψ : IsModuleTopologyPSH.{0} p L ψ) (h : ∀ v ∈ sourceDivisorialSet p, φ v = ψ v) :
    φ = ψ :=
  le_antisymm
    (divisorialComparison p L φ ψ hφ (hψ.upperSemicontinuous p) fun v hv => (h v hv).le)
    (divisorialComparison p L ψ φ hψ (hφ.upperSemicontinuous p) fun v hv => (h v hv).ge)

/-- **Uniqueness of the extension** (`cor:testcurvegivepshme`, `prop:PhiinducePSH`): a function on
`X^Div` admits at most one extension to a psh metric on `L^An`. -/
theorem existsUnique_of_isModuleTopologyPSH {L : RationalPicardSpace X}
    {φ : BerkovichPoint p → EReal} (hφ : IsModuleTopologyPSH.{0} p L φ) :
    ∃! ψ : BerkovichPoint p → EReal, IsModuleTopologyPSH.{0} p L ψ ∧
      ∀ v ∈ sourceDivisorialSet p, ψ v = φ v :=
  ⟨φ, ⟨hφ, fun _ _ => rfl⟩, fun _ hψ => eq_of_eqOn_sourceDivisorialSet p hψ.1 hφ hψ.2⟩

end SGPT.NAPotential.BJ.Assembly

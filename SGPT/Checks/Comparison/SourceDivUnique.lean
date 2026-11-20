import SGPT.Checks.Comparison.BJPair3DivOriginalDivisorialComparison
import SGPT.Checks.Comparison.BJOriginalRegularity

/-! Original divisorial uniqueness, independent of energy pairings.
Blueprint: source-comparison-slices.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.BJ.SourceDivUnique

open AlgebraicGeometry CategoryTheory
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- Original PSH metrics agreeing on the original divisorial set agree everywhere. -/
theorem eq_of_eqOn_sourceDivisorialSet {L : RationalPicardSpace X}
    {φ ψ : BerkovichPoint p → EReal} (hφ : IsModuleTopologyPSH.{0} p L φ)
    (hψ : IsModuleTopologyPSH.{0} p L ψ) (h : ∀ v ∈ sourceDivisorialSet p, φ v = ψ v) :
    φ = ψ :=
  le_antisymm
    (Pair3Div.original_le_of_sourceDivisorial_le p hφ (hψ.upperSemicontinuous p)
      fun v hv => (h v hv).le)
    (Pair3Div.original_le_of_sourceDivisorial_le p hψ (hφ.upperSemicontinuous p)
      fun v hv => (h v hv).ge)

end SGPT.NAPotential.BJ.SourceDivUnique

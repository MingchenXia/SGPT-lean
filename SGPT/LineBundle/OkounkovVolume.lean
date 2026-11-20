import SGPT.LineBundle.BigLineBundle
import SGPT.Okounkov.AlgebraicSectionBodies

/-!
# The volume of a line bundle and its Okounkov body

Source `cor:Okounvol` (chapter *The theory of Okounkov bodies*):
`vol Δ_ν(L) = vol(L) / n!`, stated with the volume `SGPT.LineBundle.volume` of
`SGPT.LineBundle.BigLineBundle`, in the conditional form of the existing
`SGPT.Okounkov.tendsto_finrank_div_pow_lineBundleOkounkovBody`: under the conclusion
`Γ(L) ∈ 𝒮'(C)` of source `prop:Okounbiglbdl` (not proved), for the flag valuation of a smooth
flag.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov SGPT.AlmostSemigroup
open SGPT.Foundations.Analysis.FirstPass MeasureTheory
open scoped Nat ENNReal

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance okVolTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okVolCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable [IsIntegral X] (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- Source `cor:Okounvol`, conditional form: if the section semigroup `Γ(L)` lies in an
admissible cone and generates `ℤⁿ⁺¹` (the conclusion of source `prop:Okounbiglbdl`), then
`vol(L) = n! · vol Δ_{Y•}(L)`, i.e. `vol Δ_{Y•}(L) = vol(L)/n!`; in particular the `limsup`
defining `vol(L)` is a limit. -/
theorem volume_eq_factorial_mul_okounkovBody {L : X.Modules} (a : LineBundleAtlas L)
    (C : AdmissibleCone n)
    (hS : schemeProjectiveSectionSemigroup f n E Y hY a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (schemeProjectiveSectionSemigroup f n E Y hY a) = ⊤) :
    volume f L n =
      ENNReal.ofReal ((n ! : ℝ) * MeasureTheory.volume.real (lineBundleOkounkovBody f n E Y hY a)) :=
  volume_eq_of_tendsto (tendsto_finrank_div_pow_lineBundleOkounkovBody a C hS hG)

end SGPT.LineBundle

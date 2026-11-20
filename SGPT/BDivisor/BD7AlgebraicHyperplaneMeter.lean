import SGPT.NAPotential.FSPosKahler
import SGPT.NAPotential.FSPosSections
import SGPT.Okounkov.SchemeSectionWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.BDivisor.BD7

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.NAPotential.GAGAMult
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]
  [LocallyOfFiniteType f] (E : ClosedProjectiveEmbedding f)

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

include E in
/-- An actual hyperplane section supplies the effective metered divisor used in the
decreasing algebraic nef Cartier approximation. -/
theorem exists_metered_hyperplane_isKahler :
    ∃ (D : EffectiveDivisor (m + 1) (SchemeComplexPoint f))
      (H : MeteredEffectiveQDivisor (m + 1) (SchemeComplexPoint f)),
      DivisorMetric.IsDivisorMetric D H ∧ H.curvature.val.IsKahler := by
  obtain ⟨p⟩ := integralFiniteTypeSchemeComplexPoint_nonempty f
  obtain ⟨i, hi⟩ := (hyperplaneAtlas E).covers (schemeComplexPointImage f p)
  change schemeComplexPointImage f p ∈ coordOpen E i at hi
  let a := hyperplaneAtlas E
  let s := polySection E (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i)
  have hs : s ≠ 0 := by
    intro hzero
    have hcoef := algCoef_polySection E (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) i
    change algCoef (a.frame i) 1 s = _ at hcoef
    rw [hzero] at hcoef
    have hregular : (0 : Γ(X, coordOpen E i)) = polyCoef E i (MvPolynomial.X i) := by
      simpa only [algCoef, map_zero] using hcoef
    have hvalue := congrArg (fun r => schemeOpenRegularFunction f (m + 1) E (coordOpen E i) r p)
      hregular
    rw [schemeOpenRegularFunction_polyCoef f (m + 1) E i _ p hi,
      MvPolynomial.eval_X, ratio_self,
      schemeOpenRegularFunction_one f (m + 1) E (coordOpen E i) hi] at hvalue
    exact zero_ne_one (by simpa only [schemeOpenRegularFunction, dif_pos hi, map_zero] using hvalue)
  let H := fubiniStudyMetric f E (m + 1)
  refine ⟨schemeSectionAnalyticDivisor f (m + 1) E a 1 s hs,
    H.sectionMeteredDivisor a 1 s hs, H.sectionMeteredDivisor_isDivisorMetric a 1 s hs, ?_⟩
  apply (H.sectionMeteredDivisor_curvature a 1 s hs).isKahler_iff.mpr
  simpa only [Nat.cast_one, one_smul] using fubiniStudy_isKahler f E (m + 1)

end SGPT.BDivisor.BD7

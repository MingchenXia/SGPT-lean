import SGPT.NAPotential.DivDict2Unconditional
import SGPT.NAPotential.QwNANonTrivRestZero
import SGPT.NAPotential.QwNAConcavity

/-!
# The source piecewise-linear analytification identity in dimension zero

Complete blueprint: `pl-curve-dim-zero.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.PLCurveDimZero

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData
open SGPT.NAPotential.BJPrep
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 0 f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance pointManifold : IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}

omit [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)] in
/-- Every actual Berkovich point reads the original largest node in dimension zero. -/
theorem curveAn_eq_cutoff (D : PiecewiseLinearData θ) (v : BerkovichPoint f) :
    D.curveAn 0 E v = (D.τ 0 : EReal) := by
  refine le_antisymm (D.curveAn_le_tau_zero 0 E v) ?_
  have h := D.le_curveAn 0 E v 0
  have hn := (isThetaPSH_iff_nativeThetaPotential θ (D.A 0)).mp (D.isThetaPSH 0)
  have hq : IsGlobalQuasiPshPotential (n := 0) (D.A 0) :=
    ⟨hn.1.quasiPlurisubharmonic, hn.2⟩
  rw [NANS.potentialAn_eq_zero_of_dim_zero hq, zero_add] at h
  exact h

/-- The ACTUAL regularized concave I-hull has the SAME original cutoff at every point. -/
theorem naPotentialAnAt_hull_eq_cutoff (D : PiecewiseLinearData θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt 0 E (hullNAPotential D) ω v = (D.τ 0 : EReal) := by
  rw [NANS.naPotentialAnAt_eq_of_dim_zero, hullNAPotential_max]

/-- Source lma:psieqpsiprimeondiv in dimension zero, on ALL actual Berkovich points,
including the actual trivial valuation. No dictionary or desired equality is assumed. -/
theorem curveAn_eq_naPotentialAnAt_hull (D : PiecewiseLinearData θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    D.curveAn 0 E v = naPotentialAnAt 0 E (hullNAPotential D) ω v :=
  (curveAn_eq_cutoff E D v).trans (naPotentialAnAt_hull_eq_cutoff E D ω v).symm

end SGPT.NAPotential.PLCurveDimZero

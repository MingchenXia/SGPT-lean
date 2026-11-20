import SGPT.TestCurve.GlobalSkodaMain
import SGPT.GAGA.H0LSections

/-!
# `rmk:PhongSturm` with GAGA discharged

`phongSturmRemark_of_sectionsAlgebraic` derives `rmk:PhongSturm` from GAGA for
the sections of `L^j`, `j ≫ 0`. GAGA for the sections of every line bundle, every atlas, every
smooth metric and every `j` is `SGPT.GAGA.H0L.schemeSectionsAlgebraic`. Combining
the two removes the hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.TestCurve.GlobalSkoda

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Metric SGPT.Okounkov SGPT.LineBundle
open SGPT.TestCurve.TestConfig SGPT.TestCurve.SkodaInc SGPT.TestCurve.SkodaRWN MeasureTheory Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.NAPotential.GAGAMult SGPT.Bergman.TensorDictionaryDraft SGPT.PSH.GlobalL2
open SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open scoped Topology ENNReal ContDiff Manifold

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance phongSturmFinalTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance phongSturmFinalCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance phongSturmFinalMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance phongSturmFinalBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

local instance phongSturmFinalManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- **Source `rmk:PhongSturm`, no extra hypotheses**: for an ample line bundle `L` on an
integral smooth projective complex scheme `X` and a smooth metric `H` with Kähler curvature, the
Phong–Sturm remark holds for the measure `μ = (dd^c φ)^n`. -/
theorem phongSturmRemark [IsSeparated f] [QuasiCompact f] [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) :
    PhongSturmRemark H a (curvatureVolume H a hK) :=
  phongSturmRemark_of_sectionsAlgebraic H a P hK
    (Eventually.of_forall fun j => SGPT.GAGA.H0L.schemeSectionsAlgebraic a H j)

end SGPT.TestCurve.GlobalSkoda

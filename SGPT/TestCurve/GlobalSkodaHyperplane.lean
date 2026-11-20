import SGPT.TestCurve.GlobalSkodaMain
import SGPT.GAGA.H0SSchemeGAGA
import SGPT.NAPotential.FSPosAlgebraic

/-!
# Skoda's division theorem and `rmk:PhongSturm` for `𝒪_X(1)` with the Fubini–Study metric

Blueprint `claude-global-skoda.tex`, node `global-skoda:hyperplane`.

For the hyperplane bundle `𝒪_X(1)` of the closed projective embedding `E : X ↪ ℙᴺ` with the
Fubini–Study metric, GAGA for the sections of `𝒪_X(j)`, `j ≫ 0`, is proved
(`SGPT.GAGA.H0S.eventually_schemeSectionsAlgebraic'`) and `c₁(𝒪_X(1), h_FS)` is Kähler
(`SGPT.NAPotential.FSPos.fubiniStudy_curvature_isKahler`). Hence, unconditionally:

* `globalSkodaDivision_hyperplane`: Skoda's division theorem `GlobalSkodaDivision` for
  `(𝒪_X(1), h_FS)`;
* `hyperplanePolarization`: `𝒪_X(1)` is (very) ample;
* `phongSturmRemark_hyperplane`: `rmk:PhongSturm` for `L = 𝒪_X(1)`, `h = h_FS` and
  `μ = c₁(𝒪_X(1), h_FS)ⁿ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.GlobalSkoda

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter SGPT.Okounkov SGPT.LineBundle
open SGPT.TestCurve.TestConfig SGPT.TestCurve.SkodaInc SGPT.TestCurve.SkodaRWN
open SGPT.NAPotential.GAGAMult SGPT.NAPotential.FSPos
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance globalSkodaHypTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance globalSkodaHypCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance globalSkodaHypManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance globalSkodaHypMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance globalSkodaHypBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- GAGA for `𝒪_X(j)` with the Fubini–Study metric, `j ≫ 0`, in the form used by
`globalSkodaDivision_of_sectionsAlgebraic`. -/
theorem eventually_hyperplaneSectionsAlgebraic :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E (hyperplaneAtlas E) (fubiniStudyMetric f E n) j := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact SGPT.GAGA.H0S.eventually_schemeSectionsAlgebraic' f E n

/-- **Skoda's division theorem for `(𝒪_X(1), h_FS)`**, unconditionally. -/
theorem globalSkodaDivision_hyperplane [IsIntegral X] [Nonempty (SchemeComplexPoint f)] :
    GlobalSkodaDivision (fubiniStudyMetric f E n) (hyperplaneAtlas E) :=
  globalSkodaDivision_of_sectionsAlgebraic _ _ (eventually_hyperplaneSectionsAlgebraic E)

/-- `𝒪_X(1)` is very ample: the embedding `E` with the unit isomorphism `𝒪_X(1)^{⊗ 1} ≅ 𝒪_X(1)`. -/
def hyperplanePolarization : AmplePolarization f (hyperplaneBundle E) where
  power := 1
  power_pos := one_pos
  ambientDimension := E.ambientDimension
  map := E.map
  isClosedImmersion := E.closedImmersion
  over_base := E.over_base
  iso := (bundleTensorLeftUnitIso (hyperplaneBundle E) :
    bundleTensor (SheafOfModules.unit X.ringCatSheaf) (hyperplaneBundle E) ≅ hyperplaneBundle E)

/-- **`rmk:PhongSturm` for `(𝒪_X(1), h_FS)`**, unconditionally: for the hyperplane bundle of
the projective embedding with the Fubini–Study metric `h = e^{-φ}` and `μ = (dd^c φ)ⁿ`, for every
ample test configuration (normalized finitely generated `ℤ`-filtration) `Γ^{𝓕*}_t = Φ(t)` for
all `t > 0` and every choice of adapted orthonormal bases. -/
theorem phongSturmRemark_hyperplane [IsIntegral X] [Nonempty (SchemeComplexPoint f)]
    [CompactSpace (SchemeComplexPoint f)] :
    PhongSturmRemark (fubiniStudyMetric f E n) (hyperplaneAtlas E)
      (curvatureVolume (fubiniStudyMetric f E n) (hyperplaneAtlas E)
        (fubiniStudy_curvature_isKahler f n E)) :=
  phongSturmRemark_of_sectionsAlgebraic _ _ (hyperplanePolarization E)
    (fubiniStudy_curvature_isKahler f n E) (eventually_hyperplaneSectionsAlgebraic E)

end SGPT.TestCurve.GlobalSkoda

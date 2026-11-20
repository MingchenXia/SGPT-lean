import SGPT.Projective.OriginalAlgebraicRegularCut
import SGPT.Projective.OriginalSmoothSectionRegularity
import SGPT.Projective.OriginalTwistedCartierEuler
import SGPT.GAGA.H0LRegular

/-! The SAME actual original algebraic/native CI cut produces genuine
Cartier regularity and arbitrary original-line Euler difference. No regularity,
exactness, Euler, metric-period or comparison conclusion premise.
Blueprint: original-ci-cut-euler.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Okounkov SGPT.NAPotential.GAGAMult
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f)

local instance ciCutEulerTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance ciCutEulerCharts (d : ℕ) [SmoothOfRelativeDimension d f] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f d
local instance ciCutEulerManifold (d : ℕ) [SmoothOfRelativeDimension d f] :
    IsComplexManifold d (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f d

/-- Genuine regularity of the SAME native cut and original coefficient
readers force the SAME original algebraic section nonzero on EVERY original
component. No independently chosen section/cut or comparison is identified. -/
theorem originalCICut_sectionNonzeroOnComponents (P : OriginalPositiveLine f (n + 1) E)
    (C : OriginalRegularCut f n E P) :
    OriginalSmoothSectionNonzeroOnComponents f (n + 1) E C.originalSection := by
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  intro F hs
  let U := smoothProjectiveComponentOpen f (n + 1) E F.val F.property
  obtain ⟨x, hx⟩ := F.property.1.nonempty
  have hxU : x ∈ U := hx
  obtain ⟨p, hpU, _⟩ := SGPT.GAGA.H0L.exists_specializes_schemeComplexPoint f hxU
  obtain ⟨j, hj⟩ := P.atlas.covers (schemeComplexPointImage f p)
  have hg : X.presheaf.germ (P.atlas.opens j) (schemeComplexPointImage f p) hj
      (algCoef (P.atlas.frame j) C.nativeCut.power C.originalSection) = 0 :=
    originalSection_coefficientGerm_eq_zero_of_open_pull_zero U C.originalSection hs
      ((P.atlas.frame j).tensorPower C.nativeCut.power) (schemeComplexPointImage f p) hpU hj
  have hvalue : schemeOpenRegularFunction f (n + 1) E (P.atlas.opens j)
      (algCoef (P.atlas.frame j) C.nativeCut.power C.originalSection) p = 0 := by
    rw [schemeOpenRegularFunction_apply f (n + 1) E (P.atlas.opens j) _ p hj,
      hg, map_zero, map_zero]
  have hsupp : schemeComplexPointImage f p ∈
      (sectionZeroIdealSheaf (P.atlas.tensorPower C.nativeCut.power) C.originalSection).support :=
    (sectionZero_support_iff_coefficient_zero f (n + 1) E (P.atlas.tensorPower C.nativeCut.power)
      C.originalSection ((P.atlas.frame j).tensorPower C.nativeCut.power) p hj).mpr hvalue
  have hxD := (regularCut_support_iff_member f (n + 1) E P.atlas P.metric P.positive
    C.nativeCut C.originalSection C.coefficient p).mp hsupp
  obtain ⟨δ, hδ⟩ := regularCut_stalk_derivation f (n + 1) E P.atlas P.metric P.positive
    C.nativeCut C.originalSection C.coefficient j p hj hxD
  exact hδ (hg ▸ map_zero δ)

/-- The SAME actual original CI cut manufactures original dual-evaluation
injectivity on EVERY original open, with no Cartier regularity certificate. -/
theorem originalCICut_dualEvaluation_injective (P : OriginalPositiveLine f (n + 1) E)
    (C : OriginalRegularCut f n E P) (V : X.Opens) :
    Function.Injective (sectionZeroEvaluation (bundleTensorPower P.sheaf C.nativeCut.power)
      C.originalSection V) :=
  originalSmoothSectionZeroEvaluation_injective f (n + 1) E
    (P.atlas.tensorPower C.nativeCut.power) C.originalSection
    (originalCICut_sectionNonzeroOnComponents f n E P C) V

/-- Unconditional genuine ORIGINAL arbitrary-line Euler difference for the
SAME actual original algebraic/native CI cut. All regularity, complex
exactness, homology finiteness and full geometric restriction are proved. -/
theorem originalCICut_twistedEuler (P : OriginalPositiveLine f (n + 1) E)
    (C : OriginalRegularCut f n E P) {B : X.Modules} (b : LineBundleAtlas B) :
    originalProjectiveLineCechEuler f E (bundleTensor B (bundleTensorPower P.sheaf C.nativeCut.power)) =
      originalProjectiveLineCechEuler f E B +
        (originalSectionZeroRestrictedCechComplex f E
          (P.atlas.tensorPower C.nativeCut.power) C.originalSection
          (bundleTensor B (bundleTensorPower P.sheaf C.nativeCut.power))).homologyEulerChar :=
  originalTwistedCartierEuler_eq_restricted f E
    (P.atlas.tensorPower C.nativeCut.power) b C.originalSection
    (originalCICut_dualEvaluation_injective f n E P C)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

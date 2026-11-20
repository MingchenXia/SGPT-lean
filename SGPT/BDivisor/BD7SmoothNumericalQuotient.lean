import SGPT.BDivisor.BD7SmoothNumericalKernel
import SGPT.BDivisor.BD6Cycle
import SGPT.Projective.OriginalFiniteSupportReader
import Mathlib.LinearAlgebra.Isomorphisms

/-! The algebraic quotient detected by the smooth closed-curve tests.
The equality with the quotient by all integral curves additionally needs the
algebraic comparison of a singular curve degree with its normalization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.BDivisor.DFAlg
open scoped BigOperators

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)

local instance bd7NumericalTopology {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance bd7NumericalCharts {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance bd7NumericalManifold {Y : Scheme.{0}} (g : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

abbrev CartierCombinations (X : Scheme.{0}) := IntrinsicLineBundle X →₀ ℝ

/-- A degree test uses only the actual algebraic degree on the smooth curve. -/
def smoothCurveDegree_bd7 (C : OriginalCurveOver f) (p : Spec (.of ℂ)) :
    CartierCombinations X →ₗ[ℝ] ℝ :=
  letI := (C.embedding E).isSeparated
  letI := (C.embedding E).quasiCompact
  Finsupp.linearCombination ℝ fun A =>
    ((originalCurveLineDegree_bd3 C.structureMap (C.embedding E)
      (matePullbackAtlas C.inclusion A.atlas) p : ℤ) : ℝ)

/-- The numerical relation is specified by the independent algebraic tests. -/
def smoothCurveRelations_bd7 : Submodule ℝ (CartierCombinations X) :=
  ⨅ (C : OriginalCurveOver f) (p : Spec (.of ℂ)), (smoothCurveDegree_bd7 f E C p).ker

abbrev SmoothCurveNumericalQuotient_bd7 :=
  CartierCombinations X ⧸ smoothCurveRelations_bd7 f E

variable [IsSeparated f] [QuasiCompact f] (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The Chern class of the identical finite algebraic Cartier combination. -/
def cartierChern_bd7 :
    CartierCombinations X →ₗ[ℝ] RealBottChern n (SchemeComplexPoint f) :=
  Finsupp.linearCombination ℝ fun A =>
    RealBottChern.ofRepresentative ((schemeLineBundleMetric f n E A.atlas).curvature A.atlas)

theorem smoothCurveRelations_eq_chernKernel_bd7 [ConnectedSpace (SchemeComplexPoint f)] :
    smoothCurveRelations_bd7 f E = (cartierChern_bd7 f E n).ker := by
  classical
  ext v
  let A : Fin v.support.card → IntrinsicLineBundle X := fun i => (v.support.equivFin.symm i).val
  let L := fun i => (A i).sheaf
  let a := fun i => (A i).atlas
  let H := fun i => schemeLineBundleMetric f n E (a i)
  let r := fun i => v (A i)
  have hchern : cartierChern_bd7 f E n v =
      RealBottChern.ofRepresentative (∑ i, r i • (H i).curvature (a i)) := by
    have hs := originalLinearCombination_eq_supportFinSum v (fun B : IntrinsicLineBundle X =>
      RealBottChern.ofRepresentative ((schemeLineBundleMetric f n E B.atlas).curvature B.atlas))
    change cartierChern_bd7 f E n v = ∑ i, r i •
      RealBottChern.ofRepresentative ((H i).curvature (a i)) at hs
    refine hs.trans ?_
    change _ = RealBottChern.ofRepresentativeLinearMap (∑ i, r i • (H i).curvature (a i))
    rw [map_sum]
    simp only [map_smul, RealBottChern.ofRepresentativeLinearMap]
    rfl
  have hdegree (C : OriginalCurveOver f) (p : Spec (.of ℂ)) :
      letI := (C.embedding E).isSeparated
      letI := (C.embedding E).quasiCompact
      smoothCurveDegree_bd7 f E C p v =
        ∑ i, r i * ((originalCurveLineDegree_bd3 C.structureMap (C.embedding E)
          (matePullbackAtlas C.inclusion (a i)) p : ℤ) : ℝ) := by
    let := (C.embedding E).isSeparated
    let := (C.embedding E).quasiCompact
    simpa only [smoothCurveDegree_bd7, smul_eq_mul, A, a, r] using
      originalLinearCombination_eq_supportFinSum v (fun B : IntrinsicLineBundle X =>
        ((originalCurveLineDegree_bd3 C.structureMap (C.embedding E)
          (matePullbackAtlas C.inclusion B.atlas) p : ℤ) : ℝ))
  simp only [smoothCurveRelations_bd7, Submodule.mem_iInf, LinearMap.mem_ker, hchern, hdegree]
  exact originalWeightedSmoothEmbeddedCurveZeroTests_iff_chernClass_eq_zero_allDims_bd7
    f n E L a H r

/-- This map is onto the existing Néron--Severi space for positive-dimensional
smooth integral projective schemes. -/
def smoothCurveNumericalEquivNS_bd7 (m : ℕ)
    [SmoothOfRelativeDimension (m + 1) f] [ConnectedSpace (SchemeComplexPoint f)]
    [IsIntegral X] [CompactSpace (SchemeComplexPoint f)] :
    SmoothCurveNumericalQuotient_bd7 f E ≃ₗ[ℝ] neronSeveri (m + 1) (SchemeComplexPoint f) :=
  (Submodule.quotEquivOfEq _ _ (smoothCurveRelations_eq_chernKernel_bd7 f E (m + 1))).trans
    ((cartierChern_bd7 f E (m + 1)).quotKerEquivRange.trans
      (LinearEquiv.ofEq (LinearMap.range (cartierChern_bd7 f E (m + 1)))
        (neronSeveri (m + 1) (SchemeComplexPoint f)) (by
          rw [cartierChern_bd7, Finsupp.range_linearCombination]
          exact (SGPT.BDivisor.BD6.neronSeveri_eq_span_algChern f E m).symm)))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

import SGPT.NAPotential.ProjectiveGraphEmbedding
import SGPT.NAPotential.ProjectiveGraphPivotScheme
import SGPT.NAPotential.NativeSchemeImmersion
import SGPT.Foundations.Schemes.PolynomialProjectiveCanonical

/-!
# The actual smooth open of the original full graph quotient is a native immersion

The native map is the actual quotient closed immersion restricted to the actual
smooth open. Its literal complex-point map has an injective derivative in the
unchanged book TN manifold charts, by the original coborder factorization.
Blueprint: `native-graph-immersion.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphNativeImmersion

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MvPolynomial
open SGPT.Okounkov
open ProjectiveGraphRelationCore ProjectiveGraphPivotScheme
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [CommRing K] [Algebra ℂ K] {N : ℕ}

/-- The actual original quotient closed immersion into the actual native projective space. -/
def relationEmbedding (v : Fin (N + 1) → K) : relationScheme (A := ℂ) v ⟶ polynomialProj ℂ N :=
  GradedGraphQuotient.quotientSchemeMap (homogeneousSubmodule (Fin (N + 1)) ℂ) (relationCore (A := ℂ) v)

instance relationEmbedding_isClosedImmersion (v : Fin (N + 1) → K) : IsClosedImmersion (relationEmbedding v) := by
  exact GradedGraphQuotient.instIsClosedImmersion_quotientSchemeMap _ _

/-- The original structure morphism of the original full relation quotient. -/
def relationStructureMap (v : Fin (N + 1) → K) : relationScheme (A := ℂ) v ⟶ Spec (.of ℂ) :=
  relationEmbedding v ≫ polynomialProjStructureMap ℂ N

/-- The actual original graph's actual open, with its actual restricted projective embedding. -/
def smoothOpenEmbedding (v : Fin (N + 1) → K) (U : (relationScheme (A := ℂ) v).Opens) :
    U.toScheme ⟶ polynomialProj ℂ N := U.ι ≫ relationEmbedding v

instance smoothOpenEmbedding_isImmersion (v : Fin (N + 1) → K)
    (U : (relationScheme (A := ℂ) v).Opens) : IsImmersion (smoothOpenEmbedding v U) := by
  dsimp only [smoothOpenEmbedding]
  infer_instance

/-- The actual original structural morphism on this actual open of the same graph quotient. -/
def smoothOpenStructureMap (v : Fin (N + 1) → K) (U : (relationScheme (A := ℂ) v).Opens) :
    U.toScheme ⟶ Spec (.of ℂ) := U.ι ≫ relationStructureMap v

theorem smoothOpenEmbedding_overBase (v : Fin (N + 1) → K) (U : (relationScheme (A := ℂ) v).Opens) :
    smoothOpenEmbedding v U ≫ polynomialProjStructureMap ℂ N = smoothOpenStructureMap v U :=
  Category.assoc _ _ _

variable (v : Fin (N + 1) → K) (U : (relationScheme (A := ℂ) v).Opens) (n : ℕ)
  [SmoothOfRelativeDimension n (smoothOpenStructureMap v U)]

local instance graphSourceTopology : TopologicalSpace (SchemeComplexPoint (smoothOpenStructureMap v U)) :=
  schemeAnalyticPointTopology (smoothOpenStructureMap v U)
local instance graphTargetTopology : TopologicalSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ N)) :=
  schemeAnalyticPointTopology (polynomialProjStructureMap ℂ N)
local instance graphSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (smoothOpenStructureMap v U)) :=
  schemeAnalyticTNChartedSpace (smoothOpenStructureMap v U) n
local instance graphTargetCharts : ChartedSpace (ComplexModel N) (SchemeComplexPoint (polynomialProjStructureMap ℂ N)) :=
  schemeAnalyticTNChartedSpace (polynomialProjStructureMap ℂ N) N

/-- The actual smooth graph open's same original projective embedding is holomorphic. -/
theorem smoothOpenEmbedding_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
      (schemeComplexPointMap (smoothOpenStructureMap v U) (polynomialProjStructureMap ℂ N)
        (smoothOpenEmbedding v U) (smoothOpenEmbedding_overBase v U)) :=
  NativeSchemeImmersion.contMDiff_pointMap _ _ _ _ n N ∞

/-- **Actual smooth graph open's tangent map is injective**, proved for the same original map and book charts. -/
theorem smoothOpenEmbedding_mfderiv_injective (p : SchemeComplexPoint (smoothOpenStructureMap v U)) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      (schemeComplexPointMap (smoothOpenStructureMap v U) (polynomialProjStructureMap ℂ N)
        (smoothOpenEmbedding v U) (smoothOpenEmbedding_overBase v U)) p) :=
  NativeSchemeImmersion.immersion_mfderiv_injective _ _ _ _ n N p

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphNativeImmersion

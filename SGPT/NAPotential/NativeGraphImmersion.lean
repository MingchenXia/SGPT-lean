import SGPT.Okounkov.SchemeAnalyticMorphism
import SGPT.Okounkov.SchemeNativeOpenJacobian
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Native closed immersion derivatives in the book's Euclidean manifold charts

The original native retraction theorem supplies the derivative, and the actual
PiLp chart equivalences transfer it to the unchanged book manifold structure.
Blueprint: `native-graph-immersion.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.NativeGraphImmersion

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Manifold
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {X Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y)
  [IsClosedImmersion i] (n m : ℕ)
  [SmoothOfRelativeDimension n (i ≫ f)] [SmoothOfRelativeDimension m f]

local instance sourceTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) :=
  schemeAnalyticPointTopology (i ≫ f)
local instance targetTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance sourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (i ≫ f)) :=
  schemeAnalyticTNChartedSpace (i ≫ f) n
local instance targetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f m

/-- The actual original native coordinate map in the book's original Euclidean coordinates. -/
def tnCoordinateMap (p : SchemeComplexPoint (i ≫ f)) (q : SchemeComplexPoint f) :
    ComplexModel n → ComplexModel m :=
  fun z => (schemeCoordinateModelEquiv m).symm
    (nativeClosedImmersionCoordinateMap f i n m p q (schemeCoordinateModelEquiv n z))

/-- The original coordinate derivative remains injective under the actual PiLp linear chart equivalences. -/
theorem tnCoordinateMap_fderiv_injective (p : SchemeComplexPoint (i ≫ f)) :
    Function.Injective (fderiv ℂ (tnCoordinateMap f i n m p
      (schemeComplexPointMap (i ≫ f) f i rfl p)) (schemeAnalyticTNChart (i ≫ f) n p p)) := by
  let q := schemeComplexPointMap (i ≫ f) f i rfl p
  let z := schemeAnalyticTNChart (i ≫ f) n p p
  have hz : schemeCoordinateModelEquiv n z = schemeAnalyticCoordinateChart (i ≫ f) n p p := by
    change schemeCoordinateModelEquiv n ((schemeCoordinateModelEquiv n).symm _) = _
    exact (schemeCoordinateModelEquiv n).apply_symm_apply _
  have hmem : schemeCoordinateModelEquiv n z ∈ nativeClosedImmersionCoordinateDomain f i n m p q := by
    rw [hz]
    exact nativeClosedImmersionCoordinateDomain_point_mem f i n m p
  have hD := (nativeClosedImmersionCoordinateMap_analyticOnNhd f i n m p q _ hmem).differentiableAt
  have hderiv := (schemeCoordinateModelEquiv m).symm.hasFDerivAt.comp z
    (hD.hasFDerivAt.comp z (schemeCoordinateModelEquiv n).hasFDerivAt)
  have hformula : fderiv ℂ (tnCoordinateMap f i n m p q) z =
      (schemeCoordinateModelEquiv m).symm.toContinuousLinearMap.comp
        ((fderiv ℂ (nativeClosedImmersionCoordinateMap f i n m p q) (schemeCoordinateModelEquiv n z)).comp
          (schemeCoordinateModelEquiv n).toContinuousLinearMap) := hderiv.fderiv
  rw [hformula]
  exact (schemeCoordinateModelEquiv m).symm.injective.comp
    ((nativeClosedImmersionCoordinateMap_fderiv_injective f i n m p q _ hmem).comp
      (schemeCoordinateModelEquiv n).injective)

omit [IsClosedImmersion i] in
/-- The original manifold derivative is exactly that same original transported coordinate derivative. -/
theorem closedImmersion_mfderiv_eq (p : SchemeComplexPoint (i ≫ f)) :
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m)
      (schemeComplexPointMap (i ≫ f) f i rfl) p =
    fderiv ℂ (tnCoordinateMap f i n m p (schemeComplexPointMap (i ≫ f) f i rfl p))
      (schemeAnalyticTNChart (i ≫ f) n p p) := by
  have hd := (schemeComplexPointMap_contMDiff f i n m 1).mdifferentiable (by norm_num) p
  simp only [mfderiv, hd, ↓reduceIte, mfld_simps, fderivWithin_univ]
  rfl

/-- **Actual closed-immersion injective tangent map**, in the same original TN manifold charts. -/
theorem closedImmersion_mfderiv_injective (p : SchemeComplexPoint (i ≫ f)) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m)
      (schemeComplexPointMap (i ≫ f) f i rfl) p) := by
  rw [closedImmersion_mfderiv_eq f i n m p]
  exact tnCoordinateMap_fderiv_injective f i n m p

end SGPT.NAPotential.NativeGraphImmersion

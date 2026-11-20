import SGPT.Projective.WholeOriginalAlgebraicCI
import SGPT.NAPotential.NativeSchemeImmersion
import SGPT.Bergman.SiuNativeProjectiveNS

/-! Actual native point geometry of the SAME original whole algebraic curve.
Blueprint: original-curve-native-geometry.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff

namespace OriginalCurveOver
variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (C : OriginalCurveOver f)

instance structure_separated [IsSeparated f] : IsSeparated C.structureMap := by
  rw [← C.over_base]
  infer_instance

instance structure_quasiCompact [QuasiCompact f] : QuasiCompact C.structureMap := by
  rw [← C.over_base]
  infer_instance

local instance curveNativeTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance curveNativeCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d
local instance curveNativeManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

/-- The actual original composed projective embedding gives entire native compactness. -/
theorem native_compact (E : ClosedProjectiveEmbedding f) :
    CompactSpace (SchemeComplexPoint C.structureMap) := (C.embedding E).analyticCompact

variable (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

/-- The actual original inclusion on the SAME entire original complex-point source. -/
def nativeMap : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n)
    (SchemeComplexPoint C.structureMap) (SchemeComplexPoint f) ∞ :=
  ⟨schemeComplexPointMap C.structureMap f C.inclusion C.over_base,
    SGPT.NAPotential.NativeSchemeImmersion.contMDiff_pointMap C.structureMap f C.inclusion C.over_base 1 n ∞⟩

/-- Actual whole original curve gets the TRUE pulled ambient Kähler background. -/
def nativeBackground (κ : KahlerBackground n (SchemeComplexPoint f)) :
    KahlerBackground 1 (SchemeComplexPoint C.structureMap) := by
  let hf := (C.nativeMap n).contMDiff
  have hd := SGPT.NAPotential.NativeSchemeImmersion.closedImmersion_mfderiv_injective
    C.structureMap f C.inclusion C.over_base 1 n
  have hcoord := SGPT.BDivisor.NSKodaira.coordinateMap_fderiv_injective_of_native_mfderiv hf hd
  exact ⟨ClosedRealOneOneForm.pullback hf κ.form,
    SmoothRealForm.IsKahler.pullback_of_injective hf (fun e d _ hz => hcoord e d hz) κ.isKahler⟩

/-- Its actual background form is the literal original inclusion pullback. -/
theorem nativeBackground_form (κ : KahlerBackground n (SchemeComplexPoint f)) :
    (C.nativeBackground n κ).form = ClosedRealOneOneForm.pullback (C.nativeMap n).contMDiff κ.form := rfl

end OriginalCurveOver
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

import SGPT.Projective.OriginalPhysicalMetricPullback
import SGPT.NAPotential.NativeSchemeImmersion
import SGPT.Bergman.SiuNativeProjectiveNS

/-! Actual inherited physical native fibres and genuine positive
closed-immersion restriction. Blueprint: original-pulled-physical-fibres.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff ComplexConjugate

variable {X Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℂ)) (h : X ⟶ Y)
  (n m : ℕ) [SmoothOfRelativeDimension n (h ≫ f)] [SmoothOfRelativeDimension m f]
  (EX : ClosedProjectiveEmbedding (h ≫ f)) (EY : ClosedProjectiveEmbedding f)

local instance pulledFibreSourceTopology : TopologicalSpace (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticPointTopology (h ≫ f)
local instance pulledFibreTargetTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pulledFibreSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint (h ≫ f)) :=
  schemeAnalyticTNChartedSpace (h ≫ f) n
local instance pulledFibreTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f m
local instance pulledFibreSourceManifold [IsSeparated (h ≫ f)] [QuasiCompact (h ≫ f)] :
    IsComplexManifold n (SchemeComplexPoint (h ≫ f)) := schemeAnalyticTN_isComplexManifold (h ≫ f) n
local instance pulledFibreTargetManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold m (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f m

variable {L : Y.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f m EY L)

/-- Actual original native fibres, identified by genuine SAME original frame coordinates. -/
def originalPulledFibreEquiv (p : SchemeComplexPoint (h ≫ f)) :
    (schemeLineBundleCore (h ≫ f) n EX (matePullbackAtlas h a)).Fiber p ≃ₗ[ℂ]
      (schemeLineBundleCore f m EY a).Fiber (schemeComplexPointMap (h ≫ f) f h rfl p) := by
  let Z := schemeLineBundleCore (h ≫ f) n EX (matePullbackAtlas h a)
  let i : a.I := Z.indexAt p
  have hi : schemeComplexPointImage (h ≫ f) p ∈ h ⁻¹ᵁ a.opens i := Z.mem_baseSet_at p
  exact (schemeLineBundleFibreFrame (h ≫ f) n EX (matePullbackAtlas h a)
    (matePullbackFrame h (a.frame i)) p hi).trans
      (schemeLineBundleFibreFrame f m EY a (a.frame i)
        (schemeComplexPointMap (h ≫ f) f h rfl p) hi).symm

/-- The actual manufactured fibre equivalence preserves the FULL actual original Hermitian pairing. -/
theorem originalPulledFibreEquiv_hermitian (p : SchemeComplexPoint (h ≫ f))
    (v w : (schemeLineBundleCore (h ≫ f) n EX (matePullbackAtlas h a)).Fiber p) :
    (originalPhysicalPullbackMetric f h n m EX EY a H).nativeHermitian (matePullbackAtlas h a) p v w =
      H.nativeHermitian a (schemeComplexPointMap (h ≫ f) f h rfl p)
        (originalPulledFibreEquiv f h n m EX EY a p v)
        (originalPulledFibreEquiv f h n m EX EY a p w) := by
  let Z := schemeLineBundleCore (h ≫ f) n EX (matePullbackAtlas h a)
  let i : a.I := Z.indexAt p
  have hi : schemeComplexPointImage (h ≫ f) p ∈ h ⁻¹ᵁ a.opens i := Z.mem_baseSet_at p
  rw [(originalPhysicalPullbackMetric f h n m EX EY a H).nativeHermitian_frame
      (matePullbackAtlas h a) (matePullbackFrame h (a.frame i)) p hi v w,
    H.nativeHermitian_frame a (a.frame i) (schemeComplexPointMap (h ≫ f) f h rfl p) hi,
    originalPhysicalPullbackMetric_frame f h n m EX EY a H (a.frame i) p hi]
  simp only [originalPulledFibreEquiv, i, Z, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- An ACTUAL closed immersion inherits actual original positive Chern metric. -/
theorem originalPhysicalPullbackMetric_isKahler [IsClosedImmersion h]
    (hK : letI := EY.isSeparated; letI := EY.quasiCompact; (H.curvature a).val.IsKahler) :
    letI := EX.isSeparated
    letI := EX.quasiCompact
    ((originalPhysicalPullbackMetric f h n m EX EY a H).curvature (matePullbackAtlas h a)).val.IsKahler := by
  let := EX.isSeparated
  let := EX.quasiCompact
  let := EY.isSeparated
  let := EY.quasiCompact
  have hd := SGPT.NAPotential.NativeSchemeImmersion.closedImmersion_mfderiv_injective
    (h ≫ f) f h rfl n m
  have hcoord := SGPT.BDivisor.NSKodaira.coordinateMap_fderiv_injective_of_native_mfderiv
    (schemeComplexPointMap_contMDiff f h n m ∞) hd
  have hpos := SmoothRealForm.IsKahler.pullback_of_injective
    (schemeComplexPointMap_contMDiff f h n m ∞) (fun e d _ hz => hcoord e d hz) hK
  exact (originalPhysicalPullbackMetric_curvature f h n m EX EY a H).isKahler_iff.mpr hpos

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

import SGPT.Toric.NativeMetricTransfer
import SGPT.Toric.NativePhysicalLineBundle
import Lean.Elab.Command

section F1CanonicalFragment001
/- BEGIN ToricSameDivisorBundleMapDraft; original source SHA256 79b54b993a2b10be5aed779391853450db2a83df8239ba54fc9ca61e79990f65 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.LineBundleMetric
open scoped Topology Manifold ContDiff

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
  {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ} {D : ToricDivisor γ hs}

/-- Actual physical same-divisor scalar, from the SAME internally chosen original covering frame. -/
def toricSameDivisorScalar (hL hR : BigToricMetric D) (p : PolytopeToricVariety γ hs) : ℂ :=
  let v := toricNativePreferredVertex γ hs p
  (toricNativeFrameCoefficient hR v p)⁻¹ * toricNativeFrameCoefficient hL v p

theorem toricSameDivisorScalar_ne_zero (hL hR : BigToricMetric D) (p : PolytopeToricVariety γ hs) :
    toricSameDivisorScalar hL hR p ≠ 0 :=
  mul_ne_zero (inv_ne_zero (toricNativeFrameCoefficient_ne_zero hR _ (toricNativePreferredVertex_mem p)))
    (toricNativeFrameCoefficient_ne_zero hL _ (toricNativePreferredVertex_mem p))

/-- The ACTUAL shared Cartier transition law gives this scalar in EVERY original chart. -/
theorem toricSameDivisorScalar_local (hL hR : BigToricMetric D) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricSameDivisorScalar hL hR p =
      (toricNativeFrameCoefficient hR v p)⁻¹ * toricNativeFrameCoefficient hL v p := by
  let w := toricNativePreferredVertex γ hs p
  have hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source := toricNativePreferredVertex_mem p
  have hLw := toricNativeFrameCoefficient_transition hL w v hw hv
  have hRw := toricNativeFrameCoefficient_transition hR w v hw hv
  change (toricNativeFrameCoefficient hR w p)⁻¹ * toricNativeFrameCoefficient hL w p = _
  rw [← hLw, ← hRw]
  field_simp [toricCartierTransition_ne_zero D w v hw hv,
    toricNativeFrameCoefficient_ne_zero hR w hw]

/-- Genuine complex-linear isomorphism of the two ACTUAL native physical fibres of the SAME divisor. -/
def toricSameDivisorFiberEquiv (hL hR : BigToricMetric D) (p : PolytopeToricVariety γ hs) :
    ToricNativeLineFiber hL p ≃ₗ[ℂ] ToricNativeLineFiber hR p where
  toFun t := toricSameDivisorScalar hL hR p * (show ℂ from t)
  invFun t := (toricSameDivisorScalar hL hR p)⁻¹ * (show ℂ from t)
  left_inv t := by
    change (toricSameDivisorScalar hL hR p)⁻¹ * (toricSameDivisorScalar hL hR p * (show ℂ from t)) = _
    rw [← mul_assoc, inv_mul_cancel₀ (toricSameDivisorScalar_ne_zero hL hR p), one_mul]
  right_inv t := by
    change toricSameDivisorScalar hL hR p * ((toricSameDivisorScalar hL hR p)⁻¹ * (show ℂ from t)) = _
    rw [← mul_assoc, mul_inv_cancel₀ (toricSameDivisorScalar_ne_zero hL hR p), one_mul]
  map_add' t s := by
    change toricSameDivisorScalar hL hR p * ((show ℂ from t) + (show ℂ from s)) = _
    exact mul_add _ _ _
  map_smul' a t := by
    change toricSameDivisorScalar hL hR p * (a * (show ℂ from t)) =
      a * (toricSameDivisorScalar hL hR p * (show ℂ from t))
    ring

/-- Coefficient one in EVERY pair of original actual holomorphic frames. -/
theorem toricSameDivisorFiberEquiv_coordinate (hL hR : BigToricMetric D) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs} (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (t : ToricNativeLineFiber hL p) :
    (toricNativeLineTrivialization hR v ⟨p, toricSameDivisorFiberEquiv hL hR p t⟩).2 =
      (toricNativeLineTrivialization hL v ⟨p, t⟩).2 := by
  change toricNativeFrameCoefficient hR v p * (toricSameDivisorScalar hL hR p * (show ℂ from t)) =
    toricNativeFrameCoefficient hL v p * (show ℂ from t)
  rw [toricSameDivisorScalar_local hL hR v hv]
  field_simp [toricNativeFrameCoefficient_ne_zero hR v hv]

def toricSameDivisorTotalMap (hL hR : BigToricMetric D) (x : TotalSpace ℂ (ToricNativeLineFiber hL)) :
    TotalSpace ℂ (ToricNativeLineFiber hR) :=
  ⟨x.proj, toricSameDivisorFiberEquiv hL hR x.proj x.snd⟩

/-- ACTUAL global holomorphy across the two independently constructed native total-space topologies. -/
theorem contMDiff_toricSameDivisorTotalMap (hL hR : BigToricMetric D) :
    ContMDiff ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞ (toricSameDivisorTotalMap hL hR) := by
  intro x
  let v := toricNativePreferredVertex γ hs x.proj
  have hv : x.proj ∈ (originalPolytopeNativeModelChart γ hs v).source := toricNativePreferredVertex_mem x.proj
  let eL := toricNativeLineTrivialization hL v
  let eR := toricNativeLineTrivialization hR v
  have hxL : x ∈ eL.source := eL.mem_source.mpr hv
  have hxR : toricSameDivisorTotalMap hL hR x ∈ eR.source := eR.mem_source.mpr hv
  have hc := ((eL.contMDiffOn (IB := 𝓘(ℂ, ComplexModel n)) (n := ∞)).contMDiffAt
    (eL.open_source.mem_nhds hxL)).snd
  have heq : (fun y => (eR (toricSameDivisorTotalMap hL hR y)).2) =ᶠ[𝓝 x] (fun y => (eL y).2) := by
    have hU := (originalPolytopeNativeModelChart γ hs v).open_source.preimage
      (FiberBundle.continuous_proj ℂ (ToricNativeLineFiber hL))
    filter_upwards [hU.mem_nhds hv] with y hy
    exact toricSameDivisorFiberEquiv_coordinate hL hR v hy y.snd
  exact (eR.contMDiffAt_iff (f := toricSameDivisorTotalMap hL hR) (x₀ := x) hxR).mpr
    ⟨contMDiffAt_proj _, hc.congr_of_eventuallyEq heq⟩

end SGPT.Toric.F1IntersectionDraft

end
/- END ToricSameDivisorBundleMapDraft -/
end F1CanonicalFragment001

section F1CanonicalFragment002
/- BEGIN ToricSameDivisorChernClassDraft; original source SHA256 1b0c5f7c2e5663761885d5466a340173d3697966b7e3deba008b2834f523c890 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.LineBundleMetric
open scoped Topology Manifold ContDiff

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
  {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ} {D : ToricDivisor γ hs}

/-- Genuine native Chern-class metric independence for the SAME original toric divisor,
through the produced actual holomorphic physical fibre map and ALL-local-section metrics.
No class equality or metric-comparison output is an input. -/
theorem toricSameDivisor_firstChernClass (hL hR : BigToricMetric D) :
    RealBottChern.ofRepresentative hL.form = RealBottChern.ofRepresentative hR.form := by
  let L := toricNativeHermitianLineBundle hL
  let R := toricNativeHermitianLineBundle hR
  let hLs := isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle hL
  let hRs := isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle hR
  let mL := sourceNativeHermitianMetric L hLs
  let mR := sourceNativeHermitianMetric R hRs
  let mT := nativeMetricTransfer (toricSameDivisorFiberEquiv hL hR)
    (contMDiff_toricSameDivisorTotalMap hL hR) mR
  have hcl : RealBottChern.ofRepresentative (firstChernForm mL) =
      RealBottChern.ofRepresentative hL.form :=
    RealBottChern.ofRepresentative_eq_of_geometricallyEq (toricNativeFirstChernForm_geometricallyEq hL)
  have hcr : RealBottChern.ofRepresentative (firstChernForm mR) =
      RealBottChern.ofRepresentative hR.form :=
    RealBottChern.ofRepresentative_eq_of_geometricallyEq (toricNativeFirstChernForm_geometricallyEq hR)
  calc
    _ = RealBottChern.ofRepresentative (firstChernForm mL) := hcl.symm
    _ = RealBottChern.ofRepresentative (firstChernForm mT) := firstChernClass_eq mL mT
    _ = RealBottChern.ofRepresentative (firstChernForm mR) :=
      nativeMetricTransfer_firstChernClass (toricSameDivisorFiberEquiv hL hR)
        (contMDiff_toricSameDivisorTotalMap hL hR) mR
    _ = _ := hcr

end SGPT.Toric.F1IntersectionDraft

end
/- END ToricSameDivisorChernClassDraft -/
end F1CanonicalFragment002


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`NativeHolomorphicMetricTransferDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicChernPullbackDraft, `NativeNefCurvePullbackDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft, `OriginalExceptionalTransitionDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalTautologicalVectorDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalNegativeMetricDraft, `ExceptionalNegativeChernDraft, `ExceptionalCurveChernIntegralDraft, `OriginalNonNefRestrictionDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefBigCurrentDraft, `PhysicalProjectiveHyperplaneChernDraft, `PhysicalOriginalHyperplaneChernDraft, `SourceF1ExceptionalIntersectionsDraft, `OriginalNonNefCurveObstructionDraft, `OriginalHyperplaneSelfIntersectionDraft, `SourceF1BigNonNefExampleDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private provider in proper F1 module: {m}"

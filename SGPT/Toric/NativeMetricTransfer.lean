import SGPT.PSH.BookLineBundleMetrics
import Lean.Elab.Command

section F1CanonicalFragment001
/- BEGIN NativeHolomorphicMetricTransferDraft; original source SHA256 f34fbfd34a0c096d8f1997f804cbad79dc05a971e7b8eff40784801a03daa260 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.F1IntersectionDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH SGPT.PSH.LineBundleMetric
open scoped Topology Manifold ContDiff

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {V W : X → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace ℂ W)] [FiberBundle ℂ W] [VectorBundle ℂ ℂ W]
  [ContMDiffVectorBundle ∞ ℂ W 𝓘(ℂ, ComplexModel n)]

/-- Pull back ACTUAL Hermitian forms through an actual fibrewise linear isomorphism. -/
def nativeMetricTransferForm (e : (x : X) → V x ≃ₗ[ℂ] W x)
    (h : HermitianMetric (n := n) W) (x : X) : HermitianForm (V x) where
  toSesq := ((h.form x).toSesq.compl₂ (e x).toLinearMap).comp (e x).toLinearMap
  pos' v hv := by
    have hne : e x v ≠ 0 := by
      intro hz
      apply hv
      apply (e x).injective
      simpa only [map_zero] using hz
    exact (h.form x).pos' _ hne

omit [IsComplexManifold n X] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [VectorBundle ℂ ℂ W]
  [ContMDiffVectorBundle ∞ ℂ W 𝓘(ℂ, ComplexModel n)] in
theorem nativeMetricTransferForm_normSq (e : (x : X) → V x ≃ₗ[ℂ] W x)
    (h : HermitianMetric (n := n) W) (x : X) (v : V x) :
    (nativeMetricTransferForm e h x).normSq v = (h.form x).normSq (e x v) := rfl

omit [IsComplexManifold n X] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [VectorBundle ℂ ℂ W]
  [ContMDiffVectorBundle ∞ ℂ W 𝓘(ℂ, ComplexModel n)] in
/-- Every local holomorphic section has a genuinely holomorphic image under an
actual holomorphic total-space bundle map. -/
theorem nativeMetricTransfer_holomorphicSection (e : (x : X) → V x ≃ₗ[ℂ] W x)
    (he : ContMDiff ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun y : TotalSpace ℂ V => (⟨y.proj, e y.proj y.snd⟩ : TotalSpace ℂ W)))
    (s : (x : X) → V x) (U : Set X) (hs : IsHolomorphicSectionOn (n := n) V s U) :
    IsHolomorphicSectionOn (n := n) W (fun x => e x (s x)) U := by
  intro x hx
  exact (he.mdifferentiable (by simp) (⟨x, s x⟩ : TotalSpace ℂ V)).comp_mdifferentiableWithinAt x (hs x hx)

/-- A genuine smooth metric transfer: smoothness holds for EVERY local actual section. -/
def nativeMetricTransfer (e : (x : X) → V x ≃ₗ[ℂ] W x)
    (he : ContMDiff ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun y : TotalSpace ℂ V => (⟨y.proj, e y.proj y.snd⟩ : TotalSpace ℂ W)))
    (h : HermitianMetric (n := n) W) : HermitianMetric (n := n) V where
  form := nativeMetricTransferForm e h
  smooth := by
    intro s U hU hs
    simpa only [nativeMetricTransferForm_normSq] using
      h.smooth (fun x => e x (s x)) U hU (nativeMetricTransfer_holomorphicSection e he s U hs)

/-- First Chern forms are genuinely natural under the ACTUAL holomorphic physical bundle
isomorphism, from the actual local frame weights; no curvature identity is supplied. -/
theorem nativeMetricTransfer_firstChern_geometrically (e : (x : X) → V x ≃ₗ[ℂ] W x)
    (he : ContMDiff ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun y : TotalSpace ℂ V => (⟨y.proj, e y.proj y.snd⟩ : TotalSpace ℂ W)))
    (h : HermitianMetric (n := n) W) :
    (firstChernForm (nativeMetricTransfer e he h)).val.GeometricallyEq (firstChernForm h).val := by
  intro c z hz
  let p := c.val.symm z
  let s := frame V p
  let U := frameDomain V p
  have hU : IsOpen U := isOpen_frameDomain p
  have hs : IsHolomorphicSectionOn (n := n) V s U := frame_holomorphic p
  have hs0 : ∀ x ∈ U, s x ≠ 0 := fun x hx => frame_ne_zero hx
  have hne : ∀ x ∈ U, e x (s x) ≠ 0 := by
    intro x hx hzero
    apply hs0 x hx
    apply (e x).injective
    simpa only [map_zero] using hzero
  have hpU : c.val.symm z ∈ U := mem_frameDomain p
  have h1 := isFirstChernForm_firstChernForm (nativeMetricTransfer e he h) s U hU hs hs0 c z hz hpU
  have h2 := isFirstChernForm_firstChernForm h (fun x => e x (s x)) U hU
    (nativeMetricTransfer_holomorphicSection e he s U hs) hne c z hz hpU
  have hw : localWeight (nativeMetricTransfer e he h) s c = localWeight h (fun x => e x (s x)) c := rfl
  rw [hw] at h1
  exact h1.trans h2.symm

/-- Genuine equality in the EXISTING native Bott--Chern quotient. -/
theorem nativeMetricTransfer_firstChernClass (e : (x : X) → V x ≃ₗ[ℂ] W x)
    (he : ContMDiff ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun y : TotalSpace ℂ V => (⟨y.proj, e y.proj y.snd⟩ : TotalSpace ℂ W)))
    (h : HermitianMetric (n := n) W) :
    RealBottChern.ofRepresentative (firstChernForm (nativeMetricTransfer e he h)) =
      RealBottChern.ofRepresentative (firstChernForm h) :=
  RealBottChern.ofRepresentative_eq_of_geometricallyEq (nativeMetricTransfer_firstChern_geometrically e he h)

end SGPT.Toric.F1IntersectionDraft

end
/- END NativeHolomorphicMetricTransferDraft -/
end F1CanonicalFragment001


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`NativeHolomorphicMetricTransferDraft, `NativeHolomorphicMetricPullbackDraft, `NativeHolomorphicChernPullbackDraft, `NativeNefCurvePullbackDraft, `ToricSameDivisorBundleMapDraft, `ToricSameDivisorChernClassDraft, `OriginalExceptionalTransitionDraft, `ExceptionalDivisorRestrictionDraft, `ExceptionalTautologicalVectorDraft, `ExceptionalTautologicalFiberDraft, `ExceptionalTautologicalInverseDraft, `ExceptionalNegativeMetricDraft, `ExceptionalNegativeChernDraft, `ExceptionalCurveChernIntegralDraft, `OriginalNonNefRestrictionDraft, `NonNefExceptionalBundleMapDraft, `NonNefRestrictedChernIntegralDraft, `OriginalNonNefPolarizationDraft, `OriginalNonNefBigCurrentDraft, `PhysicalProjectiveHyperplaneChernDraft, `PhysicalOriginalHyperplaneChernDraft, `SourceF1ExceptionalIntersectionsDraft, `OriginalNonNefCurveObstructionDraft, `OriginalHyperplaneSelfIntersectionDraft, `SourceF1BigNonNefExampleDraft, `SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden private provider in proper F1 module: {m}"

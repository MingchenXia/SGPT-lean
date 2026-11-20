import SGPT.Trace.BertiniOriginalTangentResidue
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Actual native canonical fibres and the original local-equation residue.

The construction retains actual native canonical fibres on the original
ambient manifold and its literal original native member. Global holomorphic
adjunction still requires the normal-line tensor and overlap identities.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual differentiated original chart/inverse round trips give the
genuine native chart tangent equivalence, with no derivative certificate. -/
def nativeOriginalChartTangentEquiv (e : ComplexChart n X) (x : X) (hx : x ∈ e.val.source) :
    TangentSpace 𝓘(ℂ, ComplexModel n) x ≃ₗ[ℂ] ComplexModel n :=
  ((mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property).mfderiv hx).toLinearEquiv

theorem nativeOriginalChartTangentEquiv_apply (e : ComplexChart n X) (x : X)
    (hx : x ∈ e.val.source) (v : TangentSpace 𝓘(ℂ, ComplexModel n) x) :
    nativeOriginalChartTangentEquiv e x hx v =
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val x v := rfl

/-- The original native canonical fibre, interpreted as actual coordinate
top covectors in an arbitrary original chart through the original point. -/
def nativeCanonicalFiberInChart [CompactSpace X]
    (e : ComplexChart n X) (x : X) (hx : x ∈ e.val.source) :
    (nativeCanonicalBundle (n := n) (X := X)).Fiber x ≃ₗ[ℂ]
      ((ComplexModel n) [⋀^Fin n]→ₗ[ℂ] ℂ) :=
  (nativeCanonicalFiberEquiv (n := n) x).trans
    (AlternatingMap.domLCongr ℂ ℂ (Fin n) ℂ (nativeOriginalChartTangentEquiv e x hx))

namespace SliceChart

open Metric
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  [CompactSpace Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- Actual fibrewise local-equation residue between the actual native
canonical fibres of the ORIGINAL ambient manifold and ORIGINAL native member. -/
def originalSliceCanonicalFiberResidueEquiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q) ≃ₗ[ℂ]
      (nativeCanonicalBundle (n := d) (X := member p (affinePoint c.i q.1.val))).Fiber
        (c.originalSliceMemberPoint q) := by
  letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  exact ((nativeCanonicalFiberInChart c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1).trans
    (c.originalSliceTopFormResidueEquiv hp q hsm)).trans
      (nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)).symm

theorem originalSliceCanonicalFiberResidueEquiv_apply
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) (c.originalSliceMemberPoint q)),
      nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
        (c.originalSliceCanonicalFiberResidueEquiv hp q hsm α) v =
      (nativeCanonicalFiberInChart c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1 α)
        (Matrix.vecCons (c.originalNormalizedNormal q)
          (fun i => (c.originalSliceNativeTangentEquiv hp q hsm (v i)).val)) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  intro α v
  change nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)
    ((nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)).symm
      (c.originalSliceTopFormResidueEquiv hp q hsm
        (nativeCanonicalFiberInChart c.e (c.tangentPoint q) (c.tangentPoint_chart_coordinates q).1 α))) v = _
  rw [LinearEquiv.apply_symm_apply]
  exact c.originalSliceTopFormResidueEquiv_apply hp q hsm _ v

end SliceChart

end SGPT.Trace.Bertini

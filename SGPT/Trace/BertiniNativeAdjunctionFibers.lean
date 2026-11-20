import SGPT.Trace.BertiniNativeCanonicalFiberResidue
import SGPT.Trace.BertiniDefiningSectionCoordinates

/-! The actual original normal line in canonical adjunction fibres.

The original normal line P=p*O(1), original coordinate-section physical
frame, original canonical fibres and original conormal equation are all
retained. This is fibrewise adjunction in that frame; compatible global
holomorphic gluing and the source intrinsic Hodge norm are separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  [CompactSpace Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- The original physical normal-line tensor and original actual canonical
fibres, with the exact original coordinate-section frame. -/
def originalSliceAdjunctionFiberEquiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    (tensor (nativeCanonicalBundle (n := d + 1) (X := Y))
      (nativeBertiniHyperplaneBundle ⟨p, hp⟩)).Fiber (c.tangentPoint q) ≃ₗ[ℂ]
      (nativeCanonicalBundle (n := d) (X := member p (affinePoint c.i q.1.val))).Fiber
        (c.originalSliceMemberPoint q) := by
  letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  have hpoint := c.tangentPoint_chart_coordinates q
  have hpx : p (c.tangentPoint q) ∈ (affineChart c.j).source :=
    (mem_chartLiftDomain_iff p hpoint.1).mp hpoint.2.2
  exact (TensorProduct.congr (c.originalSliceCanonicalFiberResidueEquiv hp q hsm)
    (nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q) hpx)).trans
      (TensorProduct.rid ℂ _)

theorem originalSliceAdjunctionFiberEquiv_tmul
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q))
      (v : (nativeBertiniHyperplaneBundle ⟨p, hp⟩).Fiber (c.tangentPoint q)),
      c.originalSliceAdjunctionFiberEquiv hp q hsm (α ⊗ₜ[ℂ] v) =
        nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q)
          ((mem_chartLiftDomain_iff p (c.tangentPoint_chart_coordinates q).1).mp
            (c.tangentPoint_chart_coordinates q).2.2) v •
          c.originalSliceCanonicalFiberResidueEquiv hp q hsm α := by
  intros
  rfl

theorem originalSliceAdjunctionFiberEquiv_coordinate
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ α : (nativeCanonicalBundle (n := d + 1) (X := Y)).Fiber (c.tangentPoint q),
      c.originalSliceAdjunctionFiberEquiv hp q hsm
        (α ⊗ₜ[ℂ] nativeBertiniCoordinateSection ⟨p, hp⟩ c.j (c.tangentPoint q)) =
        c.originalSliceCanonicalFiberResidueEquiv hp q hsm α := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p hp.continuous (affinePoint c.i q.1.val)).isCompact
  intro α
  rw [c.originalSliceAdjunctionFiberEquiv_tmul, nativeBertiniCoordinateFiberEquiv_coordinate, one_smul]

omit [CompactSpace Y] in
/-- The actual native defining section in this SAME actual original normal
frame is exactly the ORIGINAL equation used by the residue construction. -/
theorem originalSliceDefiningSection_coefficient
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    nativeBertiniCoordinateFiberEquiv ⟨p, hp⟩ c.j (c.tangentPoint q)
      ((mem_chartLiftDomain_iff p (c.tangentPoint_chart_coordinates q).1).mp
        (c.tangentPoint_chart_coordinates q).2.2)
      (nativeBertiniAffineSection ⟨p, hp⟩ c.i q.1.val (c.tangentPoint q)) =
      c.originalFixedMemberEquation q (c.e.val (c.tangentPoint q)) := by
  rw [nativeBertiniCoordinateFiberEquiv_definingSection]
  change _ = pairing (affineLift c.i q.1.val)
    (chartLift p c.e c.j (c.e.val (c.tangentPoint q)))
  rw [chartLift_chart p (c.tangentPoint_chart_coordinates q).1]
  rfl

end SGPT.Trace.Bertini.SliceChart

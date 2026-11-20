import SGPT.Projective.NativeSubmanifoldKahlerArea

/-! Actual compact source patches from original ambient compact supports.
Blueprint: `native-member-compact-patch.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
  [CompactSpace W]

/-- The original ambient compact support produces the SAME whole native
member chart patch, with its actual compactness and both literal image
identities. Only genuine chart-domain membership is assumed. -/
theorem native_member_compact_patch :
    letI := SubmanifoldChartedSpace.chartedSpace hk hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
    ∀ (e : ComplexChart k W) (a : ComplexChart n X) (K : Set X)
      (_hK : IsCompact K) (_hKa : K ⊆ a.val.source)
      (_hKe : ∀ y : W, y.1 ∈ K → y ∈ e.val.source),
      let P := e.val '' ((Subtype.val : W → X) ⁻¹' K)
      IsCompact P ∧ P ⊆ coordinateDomain (Subtype.val : W → X) e a ∧
        coordinateMap (Subtype.val : W → X) e a '' P = a.val '' (W ∩ K) ∧
        e.val.symm '' P = (Subtype.val : W → X) ⁻¹' K := by
  let := SubmanifoldChartedSpace.chartedSpace hk hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW
  dsimp only
  intro e a K hK hKa hKe
  let P := e.val '' ((Subtype.val : W → X) ⁻¹' K)
  have hKpre : IsCompact ((Subtype.val : W → X) ⁻¹' K) :=
    (hK.isClosed.preimage continuous_subtype_val).isCompact
  have hPc : IsCompact P := hKpre.image_of_continuousOn
    (e.val.continuousOn.mono (fun y hy => hKe y hy))
  have hPdomain : P ⊆ coordinateDomain (Subtype.val : W → X) e a := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨e.val.map_source (hKe y hy), ?_⟩
    change ((e.val.symm (e.val y) : W) : X) ∈ a.val.source
    rw [e.val.left_inv (hKe y hy)]
    exact hKa hy
  refine ⟨hPc, hPdomain, ?_, ?_⟩
  · ext ζ
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y.1, ⟨y.2, hy⟩, ?_⟩
      simp only [coordinateMap, Function.comp_apply, e.val.left_inv (hKe y hy)]
    · rintro ⟨y, ⟨hyW, hyK⟩, rfl⟩
      let w : W := ⟨y, hyW⟩
      refine ⟨e.val w, ⟨w, hyK, rfl⟩, ?_⟩
      simp only [coordinateMap, Function.comp_apply, e.val.left_inv (hKe w hyK), w]
  · ext y
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [e.val.left_inv (hKe w hw)] using hw
    · intro hy
      exact ⟨e.val y, ⟨y, hy, rfl⟩, e.val.left_inv (hKe y hy)⟩

end SGPT.Projective.NumEq.CompleteIntersections

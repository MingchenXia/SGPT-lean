import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

/-!
# Actual compact affine charts on a complex curve

A compact test set fits in an actual curve chart after an internally chosen
positive affine contraction. The inverse affine time is holomorphic in every
actual atlas overlap. No period lattice bound or chart-fit certificate is used.
-/

open Set Filter Topology
open scoped Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.CompactAffineCurveCharts

open FirstPass

noncomputable section

/-- The actual one-coordinate complex continuous linear equivalence. -/
def curveModelEquiv : ComplexModel 1 ≃L[ℂ] ℂ :=
  PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)

/-- Every compact set fits in an open neighborhood by a positive real contraction. -/
theorem exists_pos_affine_image_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K O : Set E} {z0 : E}
    (hK : IsCompact K) (hO : IsOpen O) (hz0 : z0 ∈ O) :
    ∃ δ : ℝ, 0 < δ ∧ (fun z => z0 + δ • z) '' K ⊆ O := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hz0)
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_norm.continuousOn
  have hA : 0 < |B| + 1 := by positivity
  have hδ : 0 < r / (|B| + 1) := div_pos hr hA
  refine ⟨r / (|B| + 1), hδ, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  apply hball
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hδ]
  have hzB : ‖z‖ ≤ B := hB ⟨z, hz, rfl⟩
  have hzA : ‖z‖ < |B| + 1 := lt_of_le_of_lt hzB (by linarith [le_abs_self B])
  calc
    r / (|B| + 1) * ‖z‖ < r / (|B| + 1) * (|B| + 1) :=
      mul_lt_mul_of_pos_left hzA hδ
    _ = r := div_mul_cancel₀ r (ne_of_gt hA)

variable {T : Type*} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
  [IsComplexManifold 1 T]

omit [IsComplexManifold 1 T] in
/-- Internally place any compact complex test set in a genuine atlas chart. -/
theorem exists_compact_affine_curve_chart (p : T) {K : Set ℂ} (hK : IsCompact K) :
    ∃ (e : ComplexChart 1 T) (z0 : ComplexModel 1) (δ : ℝ),
      z0 ∈ e.val.target ∧ 0 < δ ∧
      ∀ τ ∈ K, z0 + δ • curveModelEquiv.symm τ ∈ e.val.target := by
  let e := complexChartAt (n := 1) p
  have hz0 : e.val p ∈ e.val.target := e.val.map_source (mem_complexChartAt_source p)
  obtain ⟨δ, hδ, hfit⟩ := exists_pos_affine_image_subset
    (hK.image curveModelEquiv.symm.continuous) e.val.open_target hz0
  refine ⟨e, e.val p, δ, hz0, hδ, ?_⟩
  intro τ hτ
  exact hfit ⟨curveModelEquiv.symm τ, ⟨τ, hτ, rfl⟩, rfl⟩

/-- The inverse affine chart time is holomorphic on every actual atlas overlap. -/
theorem differentiableOn_affine_chart_time (e b : ComplexChart 1 T)
    (z0 : ComplexModel 1) (δ : ℝ) :
    DifferentiableOn ℂ
      (fun z => curveModelEquiv (δ⁻¹ • (e.val (b.val.symm z) - z0)))
      (b.val.target ∩ b.val.symm ⁻¹' e.val.source) := by
  have htrans := RegularPatchNeighborhood.differentiableOn_chartTransition b e
  have hsub := htrans.sub_const z0
  have hscaled := hsub.const_smul (δ⁻¹ : ℝ)
  simpa only [chartTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.coe_trans,
    Function.comp_def, Pi.smul_apply] using
    curveModelEquiv.differentiable.comp_differentiableOn hscaled

end

end SGPT.Foundations.Analysis.Pending.CompactAffineCurveCharts

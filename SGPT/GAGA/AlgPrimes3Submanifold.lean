import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

/-!
# Holomorphic maps into a closed complex submanifold


Let `W` be a closed complex submanifold of dimension `k` of a complex manifold `X`, with the
flattening atlas of `SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace.chartedSpace`.  A map
`μ : Z → W` from a complex manifold is holomorphic at `z` as soon as its composite with the
inclusion `W → X` is (`contMDiffAt_of_contMDiffAt_val`): read in the flattening chart of `W` at
`μ z`, `μ` is the coordinate projection of the flattening biholomorphism applied to the ambient
chart of `val ∘ μ`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace SGPT.GAGA.AlgPrimes3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

variable {n k d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X} (hk : k ≤ n)
  (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel d) Z]

include hk hW in
/-- **Holomorphy into a closed submanifold is tested in the ambient manifold.**  If
`Subtype.val ∘ μ : Z → X` is holomorphic at `z`, then `μ : Z → W` is holomorphic at `z` for the
flattening atlas of `W`. -/
theorem contMDiffAt_of_contMDiffAt_val {μ : Z → W} {z : Z}
    (h : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val ∘ μ) z) :
    letI := chartedSpace hk hW
    ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞ μ z := by
  let := chartedSpace hk hW
  have hcont : ContinuousAt μ z :=
    (Topology.IsInducing.subtypeVal.continuousAt_iff).mpr h.continuousAt
  rw [contMDiffAt_iff_target]
  refine ⟨hcont, ?_⟩
  set F := FlatData.ofRegularAtDim (hW (μ z).1 (μ z).2) with hF
  have hchart : chartAt (ComplexModel k) (μ z) = F.chart hk := rfl
  -- the ambient chart of `val ∘ μ`
  have hamb : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞
      (extChartAt 𝓘(ℂ, ComplexModel n) ((μ z) : X) ∘ (Subtype.val ∘ μ)) z :=
    (contMDiffAt_iff_target.mp h).2
  have hFamb : F.amb.val = chartAt (ComplexModel n) ((μ z) : X) := rfl
  -- the flattening is smooth at the image point
  have hflat : ContDiffAt ℂ ∞ F.flat (F.amb.val ((μ z) : X)) := by
    have hs : F.flat.source ∈ 𝓝 (F.amb.val ((μ z) : X)) :=
      F.flat.open_source.mem_nhds (FlatData.mem_ambSource_ofRegularAtDim (hW (μ z).1 (μ z).2)).2
    exact (contDiffOn_of_differentiableOn_complex F.differentiableOn_flat
      F.flat.open_source).contDiffAt hs
  have hproj : ContDiff ℂ ∞ (coordinateProjection n k) :=
    (coordinateProjection n k).contDiff
  have hcomp : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞
      (coordinateProjection n k ∘ F.flat ∘
        (extChartAt 𝓘(ℂ, ComplexModel n) ((μ z) : X) ∘ (Subtype.val ∘ μ))) z := by
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞
        (F.flat ∘ (extChartAt 𝓘(ℂ, ComplexModel n) ((μ z) : X) ∘ (Subtype.val ∘ μ))) z := by
      refine ContDiffAt.comp_contMDiffAt (g := F.flat) ?_ hamb
      simpa [hFamb] using hflat
    exact hproj.contDiffAt.comp_contMDiffAt h1
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hcont.preimage_mem_nhds ((F.chart hk).open_source.mem_nhds
    (FlatData.mem_ambSource_ofRegularAtDim (hW (μ z).1 (μ z).2)))] with z' _
  simp only [Function.comp_apply, extChartAt, OpenPartialHomeomorph.extend_coe,
    modelWithCornersSelf_coe, Function.id_comp, hchart, FlatData.chart_apply, FlatData.toCoord,
    hFamb]

include hk hW in
/-- `contMDiffAt_of_contMDiffAt_val` on an open set. -/
theorem contMDiffOn_of_contMDiffOn_val {μ : Z → W} {U : Set Z} (hU : IsOpen U)
    (h : ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val ∘ μ) U) :
    letI := chartedSpace hk hW
    ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞ μ U := by
  let := chartedSpace hk hW
  intro z hz
  exact (contMDiffAt_of_contMDiffAt_val hk hW (h.contMDiffAt (hU.mem_nhds hz))).contMDiffWithinAt

include hk hW in
/-- `contMDiffAt_of_contMDiffAt_val` everywhere. -/
theorem contMDiff_of_contMDiff_val {μ : Z → W}
    (h : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val ∘ μ)) :
    letI := chartedSpace hk hW
    ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel k) ∞ μ := by
  let := chartedSpace hk hW
  intro z
  exact contMDiffAt_of_contMDiffAt_val hk hW (h z)

end SGPT.GAGA.AlgPrimes3

end

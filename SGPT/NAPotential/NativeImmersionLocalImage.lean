import SGPT.NAPotential.NativeImmersionEmbedding
import SGPT.NAPotential.NativeImmersionRange

/-! # Actual native immersion locally parametrizes its whole original image closure
Blueprint: `native-graph-local-image.tex`. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.NativeImmersionLocalImage

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold

variable {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
  (j : X ⟶ Y) (hj : j ≫ fY = fX) (n m : ℕ)
  [SmoothOfRelativeDimension n fX] [SmoothOfRelativeDimension m fY] [IsImmersion j]
local instance sourceTopology : TopologicalSpace (SchemeComplexPoint fX) := schemeAnalyticPointTopology fX
local instance targetTopology : TopologicalSpace (SchemeComplexPoint fY) := schemeAnalyticPointTopology fY

include n m in
/-- **Actual local-image theorem**: every original analytic neighbourhood covers the SAME image closure near the actual native image point. -/
theorem pointMap_local (p : SchemeComplexPoint fX) (U : Set (SchemeComplexPoint fX)) (hU : U ∈ 𝓝 p) :
    ∃ V ∈ 𝓝 (schemeComplexPointMap fX fY j hj p),
      {q | schemeComplexPointImage fY q ∈ closure (Set.range j)} ∩ V ⊆
        schemeComplexPointMap fX fY j hj '' U := by
  let b := schemeComplexPointMap fX fY j hj
  have he := NativeImmersionEmbedding.Immersion.immersion_pointMap_isEmbedding fX fY j hj n m p
  have himage : b '' U ∈ 𝓝[Set.range b] b p := by
    rw [← he.map_nhds_eq p]
    exact Filter.image_mem_map hU
  obtain ⟨V, hV, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp himage
  let Z : Set (SchemeComplexPoint fY) := {q | schemeComplexPointImage fY q ∈ j.coborderRange}
  have hZo : IsOpen Z := j.coborderRange.isOpen.preimage (schemeComplexPointImage_continuous fY)
  have hpZ : b p ∈ Z := by
    apply subset_coborder
    exact ⟨schemeComplexPointImage fX p, (Scheme.Hom.comp_apply p.val j default).symm⟩
  refine ⟨V ∩ Z, inter_mem hV (hZo.mem_nhds hpZ), ?_⟩
  intro q hq
  have hscheme : schemeComplexPointImage fY q ∈ Set.range j := by
    have hm : schemeComplexPointImage fY q ∈ coborder (Set.range j) ∩ closure (Set.range j) := ⟨hq.2.2, hq.1⟩
    rwa [coborder_inter_closure] at hm
  have hpoint : q ∈ Set.range b := by
    rw [NativeImmersionRange.pointMap_range]
    exact hscheme
  exact hsub ⟨hq.2.1, hpoint⟩

end SGPT.NAPotential.NativeImmersionLocalImage

import SGPT.PSH.LocalIntrinsicAnalyticPullback
import SGPT.Foundations.Analysis.FirstPass.FormPullback

/-! # Actual holomorphic coordinate chain rules in independently dimensional atlases -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Actual map in the two original, independently dimensional charts. -/
def atlasCoordinateMap (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (f : X → Y) (i : A.Index) (j : B.Index) :
    ComplexModel (A.dimension i) → ComplexModel (B.dimension j) :=
  B.chart j ∘ f ∘ (A.chart i).symm

/-- The original open domain on which both chosen charts are valid. -/
def atlasCoordinateDomain (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (f : X → Y) (i : A.Index) (j : B.Index) : Set (ComplexModel (A.dimension i)) :=
  (A.chart i).target ∩ (A.chart i).symm ⁻¹' (f ⁻¹' (B.chart j).source)

/-- The actual domain is open, without matching source/target dimensions. -/
theorem atlasCoordinateDomain_isOpen {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) (j : B.Index) : IsOpen (atlasCoordinateDomain A B f i j) :=
  (A.chart i).isOpen_inter_preimage_symm ((B.chart j).open_source.preimage hf.1)

/-- The original image lies in the actual chosen target chart target. -/
theorem atlasCoordinateMap_mem_target {f : X → Y} {i : A.Index} {j : B.Index}
    {z : ComplexModel (A.dimension i)} (hz : z ∈ atlasCoordinateDomain A B f i j) :
    atlasCoordinateMap A B f i j z ∈ (B.chart j).target := (B.chart j).map_source hz.2

/-- The original all-chart holomorphy produces full complex smoothness. -/
theorem atlasCoordinateMap_contDiffOn {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) (j : B.Index) :
    ContDiffOn ℂ ∞ (atlasCoordinateMap A B f i j) (atlasCoordinateDomain A B f i j) :=
  contDiffOn_of_differentiableOn_complex (hf.2 i j) (atlasCoordinateDomain_isOpen hf i j)

/-- Actual pointwise complex smoothness on the original open domain. -/
theorem atlasCoordinateMap_contDiffAt {f : X → Y} (hf : A.IsHolomorphic B f)
    {i : A.Index} {j : B.Index} {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j) :
    ContDiffAt ℂ ∞ (atlasCoordinateMap A B f i j) z :=
  (atlasCoordinateMap_contDiffOn hf i j).contDiffAt
    ((atlasCoordinateDomain_isOpen hf i j).mem_nhds hz)

/-- The same coordinate map is real smooth on its actual open domain. -/
theorem atlasCoordinateMap_contDiffOn_real {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) (j : B.Index) :
    ContDiffOn ℝ ∞ (atlasCoordinateMap A B f i j) (atlasCoordinateDomain A B f i j) :=
  (atlasCoordinateMap_contDiffOn hf i j).restrict_scalars ℝ

/-- The real pointwise smoothness has the same geometric qualifications. -/
theorem atlasCoordinateMap_contDiffAt_real {f : X → Y} (hf : A.IsHolomorphic B f)
    {i : A.Index} {j : B.Index} {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j) :
    ContDiffAt ℝ ∞ (atlasCoordinateMap A B f i j) z :=
  (atlasCoordinateMap_contDiffAt hf hz).restrict_scalars ℝ

/-- Complex linearity of the real derivative is proved by restriction of scalars. -/
theorem atlasCoordinateMap_fderiv_restrictScalars {f : X → Y}
    (hf : A.IsHolomorphic B f) {i : A.Index} {j : B.Index}
    {z : ComplexModel (A.dimension i)} (hz : z ∈ atlasCoordinateDomain A B f i j) :
    fderiv ℝ (atlasCoordinateMap A B f i j) z =
      (fderiv ℂ (atlasCoordinateMap A B f i j) z).restrictScalars ℝ :=
  ((atlasCoordinateMap_contDiffAt hf hz).differentiableAt (by simp)).fderiv_restrictScalars ℝ

/-- The genuine real derivative commutes with every original complex scalar. -/
theorem atlasCoordinateMap_fderiv_map_smul_complex {f : X → Y}
    (hf : A.IsHolomorphic B f) {i : A.Index} {j : B.Index}
    {z : ComplexModel (A.dimension i)} (hz : z ∈ atlasCoordinateDomain A B f i j)
    (c : ℂ) (w : ComplexModel (A.dimension i)) :
    fderiv ℝ (atlasCoordinateMap A B f i j) z (c • w) =
      c • fderiv ℝ (atlasCoordinateMap A B f i j) z w := by
  rw [atlasCoordinateMap_fderiv_restrictScalars hf hz]
  exact (fderiv ℂ (atlasCoordinateMap A B f i j) z).map_smul c w

/-- Every actual atlas transition is real smooth, including different declared dimensions. -/
theorem atlasTransition_contDiffAt_real {i j : A.Index}
    {z : ComplexModel (A.dimension i)}
    (hz : z ∈ ((A.chart i).symm.trans (A.chart j)).source) :
    ContDiffAt ℝ ∞ ((A.chart i).symm.trans (A.chart j)) z :=
  ((contDiffOn_of_differentiableOn_complex (A.holomorphic i j)
    ((A.chart i).symm.trans (A.chart j)).open_source).contDiffAt
      (((A.chart i).symm.trans (A.chart j)).open_source.mem_nhds hz)).restrict_scalars ℝ

/-- Two actual target qualifications give the literal target transition domain. -/
theorem atlasCoordinateMap_mem_transition_source {f : X → Y}
    {i : A.Index} {j j' : B.Index} {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j)
    (hz' : z ∈ atlasCoordinateDomain A B f i j') :
    atlasCoordinateMap A B f i j z ∈ ((B.chart j).symm.trans (B.chart j')).source := by
  refine ⟨atlasCoordinateMap_mem_target hz, ?_⟩
  change (B.chart j).symm (B.chart j (f ((A.chart i).symm z))) ∈ (B.chart j').source
  rw [(B.chart j).left_inv hz.2]
  exact hz'.2

/-- The actual inverse equation identifies the unchanged target point. -/
theorem atlasCoordinateMap_change_target {f : X → Y}
    {i : A.Index} {j j' : B.Index} {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j) :
    atlasCoordinateMap A B f i j' z =
      ((B.chart j).symm.trans (B.chart j')) (atlasCoordinateMap A B f i j z) := by
  change B.chart j' (f ((A.chart i).symm z)) =
    B.chart j' ((B.chart j).symm (B.chart j (f ((A.chart i).symm z))))
  rw [(B.chart j).left_inv hz.2]

/-- The real derivative chain rule for an actual target chart change. -/
theorem atlasCoordinateMap_fderiv_change_target {f : X → Y}
    (hf : A.IsHolomorphic B f) (i : A.Index) (j j' : B.Index)
    {z : ComplexModel (A.dimension i)}
    (hz : z ∈ atlasCoordinateDomain A B f i j)
    (hz' : z ∈ atlasCoordinateDomain A B f i j') :
    fderiv ℝ (atlasCoordinateMap A B f i j') z =
      (fderiv ℝ ((B.chart j).symm.trans (B.chart j')) (atlasCoordinateMap A B f i j z)).comp
        (fderiv ℝ (atlasCoordinateMap A B f i j) z) := by
  have heq : atlasCoordinateMap A B f i j' =ᶠ[𝓝 z]
      ((B.chart j).symm.trans (B.chart j')) ∘ atlasCoordinateMap A B f i j := by
    filter_upwards [(atlasCoordinateDomain_isOpen hf i j).mem_nhds hz] with y hy
    exact atlasCoordinateMap_change_target hy
  rw [heq.fderiv_eq]
  exact fderiv_comp z
    ((atlasTransition_contDiffAt_real
      (atlasCoordinateMap_mem_transition_source hz hz')).differentiableAt (by simp))
    ((atlasCoordinateMap_contDiffAt_real hf hz).differentiableAt (by simp))

/-- A valid source transition retains the same actual target qualification. -/
theorem atlasCoordinateDomain_change_source {f : X → Y} {i i' : A.Index}
    {j : B.Index} {z : ComplexModel (A.dimension i)}
    (hz : z ∈ ((A.chart i).symm.trans (A.chart i')).source)
    (hzf : z ∈ atlasCoordinateDomain A B f i j) :
    ((A.chart i).symm.trans (A.chart i')) z ∈ atlasCoordinateDomain A B f i' j := by
  change z ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart i').source at hz
  refine ⟨(A.chart i').map_source hz.2, ?_⟩
  change f ((A.chart i').symm (A.chart i' ((A.chart i).symm z))) ∈ (B.chart j).source
  rw [(A.chart i').left_inv hz.2]
  exact hzf.2

/-- The original source chart change keeps the same geometric point. -/
theorem atlasCoordinateMap_change_source {f : X → Y} {i i' : A.Index}
    {j : B.Index} {z : ComplexModel (A.dimension i)}
    (hz : z ∈ ((A.chart i).symm.trans (A.chart i')).source) :
    atlasCoordinateMap A B f i j z =
      atlasCoordinateMap A B f i' j (((A.chart i).symm.trans (A.chart i')) z) := by
  change z ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart i').source at hz
  change B.chart j (f ((A.chart i).symm z)) =
    B.chart j (f ((A.chart i').symm (A.chart i' ((A.chart i).symm z))))
  rw [(A.chart i').left_inv hz.2]

/-- The real derivative chain rule for an actual source chart change. -/
theorem atlasCoordinateMap_fderiv_change_source {f : X → Y}
    (hf : A.IsHolomorphic B f) (i i' : A.Index) (j : B.Index)
    {z : ComplexModel (A.dimension i)}
    (hz : z ∈ ((A.chart i).symm.trans (A.chart i')).source)
    (hzf : z ∈ atlasCoordinateDomain A B f i j) :
    fderiv ℝ (atlasCoordinateMap A B f i j) z =
      (fderiv ℝ (atlasCoordinateMap A B f i' j)
        (((A.chart i).symm.trans (A.chart i')) z)).comp
          (fderiv ℝ ((A.chart i).symm.trans (A.chart i')) z) := by
  have heq : atlasCoordinateMap A B f i j =ᶠ[𝓝 z]
      atlasCoordinateMap A B f i' j ∘ ((A.chart i).symm.trans (A.chart i')) := by
    filter_upwards [((A.chart i).symm.trans (A.chart i')).open_source.mem_nhds hz] with y hy
    exact atlasCoordinateMap_change_source hy
  rw [heq.fderiv_eq]
  exact fderiv_comp z
    ((atlasCoordinateMap_contDiffAt_real hf
      (atlasCoordinateDomain_change_source hz hzf)).differentiableAt (by simp))
    ((atlasTransition_contDiffAt_real hz).differentiableAt (by simp))

end SGPT.PSH.VariableComplexAtlas

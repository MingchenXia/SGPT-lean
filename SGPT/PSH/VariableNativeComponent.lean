import SGPT.PSH.VariableLelong
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

include A in
/-- Genuine chart balls produce locally connected ORIGINAL topology, in every dimension. -/
theorem locallyConnectedSpace_of_variableAtlas : LocallyConnectedSpace X := by
  apply locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr
  intro x U hU
  obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.mp hU
  obtain ⟨i, hi⟩ := A.cover x
  let e := A.chart i
  have hxD : e x ∈ e.target ∩ e.symm ⁻¹' O := by
    refine ⟨e.map_source hi, ?_⟩
    simpa only [mem_preimage, e.left_inv hi] using hxO
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (e.isOpen_inter_preimage_symm hO) _ hxD
  have hbT : ball (e x) r ⊆ e.target := fun _ hz => (hball hz).1
  refine ⟨e.symm '' ball (e x) r, ?_,
    e.isOpen_image_symm_of_subset_target isOpen_ball hbT, ?_,
    (isConnected_ball hr).image e.symm (e.continuousOn_symm.mono hbT)⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hOU (hball hz).2
  · exact ⟨e x, mem_ball_self hr, e.left_inv hi⟩

/-- The original component is an actual open subset of X. -/
def componentOpen (x : X) : Opens X := by
  letI := A.locallyConnectedSpace_of_variableAtlas
  exact ⟨connectedComponent x, isOpen_connectedComponent⟩

theorem componentOpen_coe (x : X) : (A.componentOpen x : Set X) = connectedComponent x := rfl

/-- Nonemptiness is produced from the original component's distinguished point. -/
theorem componentNonempty (x : X) : Nonempty (A.componentOpen x) :=
  ⟨⟨x, mem_connectedComponent⟩⟩

/-- Canonical inclusion retains the literal original subtype topology. -/
def componentInclusion (x : X) : OpenPartialHomeomorph (A.componentOpen x) X :=
  (A.componentOpen x).openPartialHomeomorphSubtypeCoe (A.componentNonempty x)

theorem componentInclusion_source (x : X) : (A.componentInclusion x).source = univ := rfl

theorem componentInclusion_target (x : X) :
    (A.componentInclusion x).target = connectedComponent x := by
  exact (A.componentOpen x).openPartialHomeomorphSubtypeCoe_target (A.componentNonempty x)

/-- Only original charts actually meeting the component enter its native atlas. -/
def ComponentChartIndex (x : X) :=
  {i : A.Index // ((A.chart i).source ∩ connectedComponent x).Nonempty}

/-- Dimension equality is proved internally from the original chart and component. -/
theorem componentChartDimension (x : X) (i : A.ComponentChartIndex x) :
    A.dimension i.val = A.pointDimension x := by
  obtain ⟨y, hys, hyc⟩ := i.property
  exact (A.pointDimension_eq_chart y i.val hys).symm.trans
    (A.pointDimension_eq_on_connectedComponent x hyc)

private def castModelChart {d n : ℕ} (e : OpenPartialHomeomorph X (ComplexModel d))
    (h : d = n) : OpenPartialHomeomorph X (ComplexModel n) := h ▸ e

private theorem castModelChart_source {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (h : d = n) :
    (castModelChart e h).source = e.source := by subst n; rfl

private theorem castModelChart_holomorphic {d m n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d))
    (f : OpenPartialHomeomorph X (ComplexModel m)) (hd : d = n) (hm : m = n)
    (h : DifferentiableOn ℂ (e.symm.trans f) (e.symm.trans f).source) :
    DifferentiableOn ℂ ((castModelChart e hd).symm.trans (castModelChart f hm))
      ((castModelChart e hd).symm.trans (castModelChart f hm)).source := by
  subst d; subst m
  exact h

/-- Restrict the original chart, transporting only its proved natural-number dimension. -/
def componentChart (x : X) (i : A.ComponentChartIndex x) :
    OpenPartialHomeomorph (A.componentOpen x) (ComplexModel (A.pointDimension x)) :=
  (castModelChart (A.chart i.val) (A.componentChartDimension x i)).subtypeRestr
    (A.componentNonempty x)

theorem componentChart_source (x : X) (i : A.ComponentChartIndex x) :
    (A.componentChart x i).source = Subtype.val ⁻¹' (A.chart i.val).source := by
  simp only [componentChart, OpenPartialHomeomorph.subtypeRestr_source, castModelChart_source]

/-- Exact native target: original chart target whose actual inverse lies in the component. -/
theorem componentChart_target (x : X) (i : A.ComponentChartIndex x) :
    (A.componentChart x i).target =
      (castModelChart (A.chart i.val) (A.componentChartDimension x i)).target ∩
      (castModelChart (A.chart i.val) (A.componentChartDimension x i)).symm ⁻¹'
        connectedComponent x := by
  simp only [componentChart, OpenPartialHomeomorph.subtypeRestr_def,
    OpenPartialHomeomorph.trans_target,
    Opens.openPartialHomeomorphSubtypeCoe_target, componentOpen_coe]

theorem componentChart_cover (x : X) (p : A.componentOpen x) :
    ∃ i : A.ComponentChartIndex x, p ∈ (A.componentChart x i).source := by
  obtain ⟨i, hi⟩ := A.cover p.val
  have hpc : p.val ∈ connectedComponent x := p.property
  have hmeet : ((A.chart i).source ∩ connectedComponent x).Nonempty := ⟨p.val, hi, hpc⟩
  let j : A.ComponentChartIndex x := ⟨i, hmeet⟩
  refine ⟨j, ?_⟩
  rw [A.componentChart_source x j]
  exact hi

/-- The actual native charted-space structure on the original component subtype. -/
@[instance_reducible]
def componentChartedSpace (x : X) :
    ChartedSpace (ComplexModel (A.pointDimension x)) (A.componentOpen x) where
  atlas := range (A.componentChart x)
  chartAt := fun p => A.componentChart x (Classical.choose (A.componentChart_cover x p))
  mem_chart_source := fun p => Classical.choose_spec (A.componentChart_cover x p)
  chart_mem_atlas := fun p => ⟨Classical.choose (A.componentChart_cover x p), rfl⟩

private theorem differentiableOn_subtypeRestr_transition {n : ℕ} (U : Opens X)
    (hU : Nonempty U) (e f : OpenPartialHomeomorph X (ComplexModel n))
    (h : DifferentiableOn ℂ (e.symm.trans f) (e.symm.trans f).source) :
    DifferentiableOn ℂ ((e.subtypeRestr hU).symm.trans (f.subtypeRestr hU))
      ((e.subtypeRestr hU).symm.trans (f.subtypeRestr hU)).source := by
  have hs : ((e.subtypeRestr hU).symm.trans (f.subtypeRestr hU)).source ⊆
      (e.symm.trans f).source := by
    intro z hz
    change z ∈ (e.subtypeRestr hU).target ∧
      (e.subtypeRestr hU).symm z ∈ (f.subtypeRestr hU).source at hz
    refine ⟨e.subtypeRestr_target_subset hU hz.1, ?_⟩
    have hz2 : ((e.subtypeRestr hU).symm z).val ∈ f.source := by
      simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hz.2
    have heq := e.subtypeRestr_symm_apply hU hz.1
    change ((e.subtypeRestr hU).symm z).val = e.symm z at heq
    change e.symm z ∈ f.source
    rwa [heq] at hz2
  apply (h.mono hs).congr
  intro z hz
  change f ((e.subtypeRestr hU).symm z).val = f (e.symm z)
  have heq := e.subtypeRestr_symm_apply hU hz.1
  change ((e.subtypeRestr hU).symm z).val = e.symm z at heq
  exact congrArg f heq

/-- Every actual native transition is a genuine restriction of an original holomorphic overlap. -/
theorem componentChart_transition_differentiableOn (x : X)
    (i j : A.ComponentChartIndex x) :
    DifferentiableOn ℂ ((A.componentChart x i).symm.trans (A.componentChart x j))
      ((A.componentChart x i).symm.trans (A.componentChart x j)).source := by
  exact differentiableOn_subtypeRestr_transition (A.componentOpen x) (A.componentNonempty x)
    _ _ (castModelChart_holomorphic _ _ (A.componentChartDimension x i)
      (A.componentChartDimension x j) (A.holomorphic i.val j.val))

/-- Genuine smoothness is produced from all original restricted overlaps. -/
theorem componentIsManifold (x : X) :
    letI := A.componentChartedSpace x
    IsManifold (𝓘(ℂ, ComplexModel (A.pointDimension x))) ∞ (A.componentOpen x) := by
  let := A.componentChartedSpace x
  apply isManifold_of_contDiffOn (𝓘(ℂ, ComplexModel (A.pointDimension x))) ∞
    (A.componentOpen x)
  intro e f he hf
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := hf
  simpa using contDiffOn_of_differentiableOn_complex
    (A.componentChart_transition_differentiableOn x i j)
    ((A.componentChart x i).symm.trans (A.componentChart x j)).open_source

/-- Original Hausdorff and second-countable assumptions supply the native complex record. -/
theorem componentComplexManifold [T2Space X] [SecondCountableTopology X] (x : X) :
    letI := A.componentChartedSpace x
    IsComplexManifold (A.pointDimension x) (A.componentOpen x) := by
  let := A.componentChartedSpace x
  exact {
    toT2Space := inferInstance
    toSecondCountableTopology := inferInstance
    toIsManifold := A.componentIsManifold x }

end SGPT.PSH.VariableComplexAtlas

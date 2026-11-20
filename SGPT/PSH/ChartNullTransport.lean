import SGPT.PSH.AtlasAE
import SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

set_option autoImplicit false

noncomputable section
namespace SGPT.PSH
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

private theorem finrank_le_of_open_partial_holomorphic_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source)
    (hi : DifferentiableOn ℂ e.symm e.target) {x : E} (hx : x ∈ e.source) :
    Module.finrank ℂ E ≤ Module.finrank ℂ F := by
  have hf := (he x hx).differentiableAt (e.open_source.mem_nhds hx)
  have hg := (hi (e x) (e.map_source hx)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hlocal : (fun y ↦ e.symm (e y)) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hcomp : (fderiv ℂ e.symm (e x)).comp (fderiv ℂ e x) =
      ContinuousLinearMap.id ℂ E :=
    ((hg.hasFDerivAt.comp x hf.hasFDerivAt).congr_of_eventuallyEq hlocal.symm).unique
      (hasFDerivAt_id x)
  apply LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℂ e x).toLinearMap)
  intro v w hvw
  calc
    v = fderiv ℂ e.symm (e x) (fderiv ℂ e x v) :=
      (congrArg (fun L : E →L[ℂ] E ↦ L v) hcomp).symm
    _ = fderiv ℂ e.symm (e x) (fderiv ℂ e x w) := congrArg _ hvw
    _ = w := congrArg (fun L : E →L[ℂ] E ↦ L w) hcomp

/-- Actual inverse derivatives force equal complex model dimensions on every
nonempty holomorphic coordinate domain. -/
theorem model_dimension_eq_of_holomorphic_openPartial
    {n m : ℕ} (e : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m))
    (he : DifferentiableOn ℂ e e.source)
    (hi : DifferentiableOn ℂ e.symm e.target) (hne : e.source.Nonempty) : n = m := by
  obtain ⟨x, hx⟩ := hne
  have hle := finrank_le_of_open_partial_holomorphic_inverse e he hi hx
  have hge := finrank_le_of_open_partial_holomorphic_inverse e.symm hi he
    (e.map_source hx)
  simpa [ComplexModel] using le_antisymm hle hge

/-- Genuine holomorphic transition inverses force equal dimensions on every
actual overlap, even when the atlas varies between connected components. -/
theorem VariableComplexAtlas.dimension_eq_of_common_source
    {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)
    {i j : A.Index} {x : X} (hi : x ∈ (A.chart i).source)
    (hj : x ∈ (A.chart j).source) : A.dimension i = A.dimension j := by
  let F := (A.chart i).symm.trans (A.chart j)
  have hF : DifferentiableOn ℂ F F.source := A.holomorphic i j
  have hG : DifferentiableOn ℂ F.symm F.target := by
    change DifferentiableOn ℂ F.symm F.symm.source
    simpa only [F, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using A.holomorphic j i
  have hx : A.chart i x ∈ F.source := by
    refine ⟨(A.chart i).map_source hi, ?_⟩
    change (A.chart i).symm (A.chart i x) ∈ (A.chart j).source
    simpa only [(A.chart i).left_inv hi] using hj
  exact model_dimension_eq_of_holomorphic_openPartial F hF hG ⟨_, hx⟩

/-- Original coordinate Lebesgue almost-everywhere statements pull back through
an actual holomorphic chart with a genuine inverse, in every dimension. -/
theorem ae_comp_of_holomorphic_model_openPartial {n : ℕ}
    (e : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n))
    (he : DifferentiableOn ℂ e e.source)
    (hi : DifferentiableOn ℂ e.symm e.target) {P : ComplexModel n → Prop}
    (hP : ∀ᵐ y ∂volume.restrict e.target, P y) :
    ∀ᵐ x ∂volume.restrict e.source, P (e x) := by
  let A : TopologicalSpace.Opens (ComplexModel n) := ⟨e.source, e.open_source⟩
  let B : TopologicalSpace.Opens (ComplexModel n) := ⟨e.target, e.open_target⟩
  have h : SGPT.Foundations.Analysis.Pending.BedfordTaylor.IsBiholomorphicPair A B e e.symm := {
    holo := contDiffOn_of_differentiableOn_complex he e.open_source
    holo_inv := contDiffOn_of_differentiableOn_complex hi e.open_target
    mapsTo := e.mapsTo
    mapsTo_inv := e.symm.mapsTo
    left_inv := fun _ hx ↦ e.left_inv hx
    right_inv := fun _ hy ↦ e.right_inv hy }
  exact (ae_restrict_iff' e.open_source.measurableSet).mpr
    (SGPT.Foundations.Analysis.Pending.LocalCurrentPullback.ae_comp_of_ae h
      ((ae_restrict_iff' e.open_target.measurableSet).mp hP))

/-- Actual overlap dimension equality, rather than a fixed-dimensional atlas
assumption, gives genuine null-set transport for varying complex chart models. -/
theorem ae_comp_of_variable_holomorphic_model_openPartial {n m : ℕ}
    (e : OpenPartialHomeomorph (ComplexModel n) (ComplexModel m))
    (he : DifferentiableOn ℂ e e.source)
    (hi : DifferentiableOn ℂ e.symm e.target) {P : ComplexModel m → Prop}
    (hP : ∀ᵐ y ∂volume.restrict e.target, P y) :
    ∀ᵐ x ∂volume.restrict e.source, P (e x) := by
  by_cases hne : e.source.Nonempty
  · have hnm := model_dimension_eq_of_holomorphic_openPartial e he hi hne
    subst m
    exact ae_comp_of_holomorphic_model_openPartial e he hi hP
  · have hempty : e.source = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, Measure.restrict_empty, ae_zero, Filter.eventually_bot]

end SGPT.PSH

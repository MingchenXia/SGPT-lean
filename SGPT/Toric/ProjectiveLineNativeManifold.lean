import SGPT.Toric.ProjectiveLineFubiniStudy
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff Manifold

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The actual native finite atlas uses the ORIGINAL quotient topology and charts. -/
instance projectiveNativeChartedSpace : ChartedSpace (ComplexModel 1) P1 where
  atlas := range projectiveModelChart
  chartAt := fun p => projectiveModelChart (Classical.choose (projectiveLineAtlas.cover p))
  mem_chart_source := fun p => Classical.choose_spec (projectiveLineAtlas.cover p)
  chart_mem_atlas := fun p => ⟨Classical.choose (projectiveLineAtlas.cover p), rfl⟩

/-- Every native chart is exactly one of the actual two quotient charts. -/
theorem mem_projectiveNativeAtlas_iff (e : OpenPartialHomeomorph P1 (ComplexModel 1)) :
    e ∈ atlas (ComplexModel 1) P1 ↔ ∃ i : Bool, e = projectiveModelChart i := by
  change e ∈ range projectiveModelChart ↔ _
  simp only [mem_range, eq_comm]

/-- The original preferred quotient charts belong to the genuine native atlas. -/
def projectiveNativeChart (i : Bool) : ComplexChart 1 P1 :=
  ⟨projectiveModelChart i, ⟨i, rfl⟩⟩

theorem projectiveNativeChart_val (i : Bool) :
    (projectiveNativeChart i).val = projectiveModelChart i := rfl

/-- Compactness is transported through the genuine original quotient homeomorphism. -/
instance projectiveNativeCompactSpace : CompactSpace P1 := projectiveLineHomeomorph.compactSpace

/-- Genuine Hausdorffness is a consequence of the actual original homeomorphism. -/
instance projectiveNativeT2Space : T2Space P1 := projectiveLineHomeomorph.t2Space

/-- The actual compact native charted space has a second-countable model. -/
instance projectiveNativeSecondCountable : SecondCountableTopology P1 :=
  ChartedSpace.secondCountable_of_sigmaCompact (ComplexModel 1) P1

/-- True holomorphicity on ALL actual overlaps supplies the native manifold structure. -/
theorem projectiveNativeIsManifold : IsManifold (𝓘(ℂ, ComplexModel 1)) ∞ P1 := by
  apply isManifold_of_contDiffOn (𝓘(ℂ, ComplexModel 1)) ∞ P1
  intro e f he hf
  obtain ⟨i, rfl⟩ := (mem_projectiveNativeAtlas_iff e).mp he
  obtain ⟨j, rfl⟩ := (mem_projectiveNativeAtlas_iff f).mp hf
  simpa using contDiffOn_of_differentiableOn_complex
    (differentiableOn_projectiveModelChart_transition i j)
    ((projectiveModelChart i).symm.trans (projectiveModelChart j)).open_source

/-- A genuine Hausdorff second-countable complex manifold on the unchanged quotient. -/
instance projectiveNativeComplexManifold : IsComplexManifold 1 P1 where
  toT2Space := inferInstance
  toSecondCountableTopology := inferInstance
  toIsManifold := projectiveNativeIsManifold

/-- Connectedness comes from the actual connected one-point complex plane. -/
instance projectiveNativeConnectedSpace : ConnectedSpace P1 :=
  projectiveLineHomeomorph.surjective.connectedSpace projectiveLineHomeomorph.continuous

/-- The exact original coefficient family, transported to EVERY native atlas member. -/
def projectiveNativeFSForm : SmoothRealForm 1 P1 2 where
  coeff := fun _ => smoothDDC projectiveFSPotential
  smooth := by
    intro e
    obtain ⟨i, hi⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
    change ContDiffOn ℝ ∞ (smoothDDC projectiveFSPotential) e.val.target
    rw [hi]
    exact projectiveFSForm.smooth i
  compatible := by
    intro e f z hz v
    obtain ⟨i, hi⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
    obtain ⟨j, hj⟩ := (mem_projectiveNativeAtlas_iff f.val).mp f.property
    change z ∈ (e.val.symm.trans f.val).source at hz
    rw [hi, hj] at hz
    change smoothDDC projectiveFSPotential z v =
      smoothDDC projectiveFSPotential ((e.val.symm.trans f.val) z)
        (fun a => fderiv ℝ (e.val.symm.trans f.val) z (v a))
    rw [hi, hj]
    exact projectiveFSForm.compatible i j z hz v

/-- Actual exterior closedness is reused on each original native chart target. -/
theorem projectiveNativeFSForm_closed : projectiveNativeFSForm.IsClosed := by
  intro e z hz
  obtain ⟨i, hi⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  rw [hi] at hz
  exact projectiveFSForm.closed i z hz

/-- The original type-(1,1) equation retains every tangent and every target point. -/
theorem projectiveNativeFSForm_typeOneOne : projectiveNativeFSForm.IsTypeOneOne := by
  intro e z hz
  obtain ⟨i, hi⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  rw [hi] at hz
  exact projectiveFSForm.typeOneOne i z hz

/-- Genuine original curvature as a native closed real (1,1) form. -/
def projectiveNativeFSClosedForm : ClosedRealOneOneForm 1 P1 :=
  ⟨projectiveNativeFSForm, projectiveNativeFSForm_closed, projectiveNativeFSForm_typeOneOne⟩

/-- Actual original strict Levi positivity supplies the genuine native Kahler property. -/
theorem projectiveNativeFSForm_isKahler : projectiveNativeFSForm.IsKahler := by
  refine ⟨?_, projectiveNativeFSForm_closed⟩
  intro e z hz
  refine ⟨projectiveNativeFSForm_typeOneOne e z hz, ?_⟩
  intro v hv
  exact projectiveFSForm_strictlyPositive false z hv

/-- The original quotient projective line now has an internally produced native background. -/
def projectiveNativeFSBackground : KahlerBackground 1 P1 :=
  ⟨projectiveNativeFSClosedForm, projectiveNativeFSForm_isKahler⟩

/-- Exact preferred-chart readback preserves the original source normalization. -/
theorem projectiveNativeFSBackground_coeff (i : Bool) (z : ComplexModel 1) :
    projectiveNativeFSBackground.form.val.coeff (projectiveNativeChart i) z =
      projectiveFSForm.coeff i z := rfl

end SGPT.Toric

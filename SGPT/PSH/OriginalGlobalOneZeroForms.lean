import SGPT.PSH.RealCovectorComplexLift
import SGPT.PSH.AtlasHolomorphicCoordinates

/-! Genuine original global smooth (1,0) forms and actual producers from
real smooth functions, with full ORIGINAL tensor overlap laws. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Actual original GLOBAL smooth (1,0) differential form, in the genuine
complex cotangent fibers and with the full actual transition law. -/
structure OriginalGlobalOneZeroForm where
  coeff : ∀ i : A.Index,ComplexModel (A.dimension i) →
    ComplexModel (A.dimension i) →L[ℂ] ℂ
  smooth : ∀ i,ContDiffOn ℝ ∞ (coeff i) (A.chart i).target
  compatible : ∀ i j z,z∈((A.chart i).symm.trans (A.chart j)).source →
    ∀ v : ComplexModel (A.dimension i),
      coeff i z v=coeff j (((A.chart i).symm.trans (A.chart j)) z)
        (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) z v)

/-- Genuine all-original-chart smoothness of a real function. -/
def OriginalRealSmooth (f : X → ℝ) : Prop :=
  ∀ i : A.Index,ContDiffOn ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i).target

/-- Actual original smooth scalar derivatives satisfy the full cotangent
chain rule, proved on an actual open neighborhood rather than only a point. -/
theorem original_real_smooth_fderiv_transition (f : X → ℝ)
    (hf : OriginalRealSmooth A f) (i j : A.Index) {z : ComplexModel (A.dimension i)}
    (hz : z∈((A.chart i).symm.trans (A.chart j)).source) :
    fderiv ℝ (f ∘ (A.chart i).symm) z=
      (fderiv ℝ (f ∘ (A.chart j).symm) (((A.chart i).symm.trans (A.chart j)) z)).comp
        (fderiv ℝ ((A.chart i).symm.trans (A.chart j)) z) := by
  let F := (A.chart i).symm.trans (A.chart j)
  have heq : (f ∘ (A.chart i).symm)=ᶠ[𝓝 z] (f ∘ (A.chart j).symm) ∘ F := by
    filter_upwards [F.open_source.mem_nhds hz] with y hy
    change f ((A.chart i).symm y)=f ((A.chart j).symm ((A.chart j) ((A.chart i).symm y)))
    have hyj : (A.chart i).symm y∈(A.chart j).source := hy.2
    rw [(A.chart j).left_inv hyj]
  rw [heq.fderiv_eq]
  exact fderiv_comp z
    (((hf j).contDiffAt ((A.chart j).open_target.mem_nhds (F.map_source hz).1)).differentiableAt (by simp))
    ((atlasTransition_contDiffAt_real hz).differentiableAt (by simp))

/-- Actual original real smooth functions PRODUCE genuine GLOBAL smooth
(1,0) forms; all complex linearity/smoothness/overlap fields are proved. -/
def originalOneZeroOfRealSmooth (f : X → ℝ) (hf : OriginalRealSmooth A f) :
    OriginalGlobalOneZeroForm A where
  coeff i z := realCovectorComplexLift (fderiv ℝ (f ∘ (A.chart i).symm) z)
  smooth i := (realCovectorComplexLiftCLM (A.dimension i)).contDiff.comp_contDiffOn
    ((hf i).fderiv_of_isOpen (A.chart i).open_target (by simp))
  compatible i j z hz v := by
    rw [original_real_smooth_fderiv_transition A f hf i j hz]
    apply realCovectorComplexLift_comp
    intro w
    have hF := ((A.holomorphic i j).differentiableAt
      (((A.chart i).symm.trans (A.chart j)).open_source.mem_nhds hz)).fderiv_restrictScalars ℝ
    rw [hF]
    exact (fderiv ℂ ((A.chart i).symm.trans (A.chart j)) z).map_smul Complex.I w

/-- Entire physical coefficient value of the PRODUCED global (1,0) form. -/
theorem originalOneZeroOfRealSmooth_apply (f : X → ℝ) (hf : OriginalRealSmooth A f)
    (i : A.Index) (z v : ComplexModel (A.dimension i)) :
    (originalOneZeroOfRealSmooth A f hf).coeff i z v=
      (fderiv ℝ (f ∘ (A.chart i).symm) z v : ℂ)-
        Complex.I*(fderiv ℝ (f ∘ (A.chart i).symm) z (Complex.I • v) : ℂ) := rfl

end SGPT.PSH.ComplexCurrentDraft

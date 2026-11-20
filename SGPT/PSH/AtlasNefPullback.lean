import SGPT.PSH.AtlasCohomologyPullback
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-! The literal ORIGINAL global smooth-potential nef criterion and genuine
holomorphic pullback by the true tensor/dd^c/complex-line chain rules. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff Classical
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- EXACT source global nef criterion on actual original representatives:
one genuine globally smooth real potential for EVERY positive epsilon and
positivity on EVERY original chart/tangent line, without component flags. -/
def OriginalNefWithRespectTo (omega theta : AtlasClosedRealOneOneForm A) : Prop :=
  ∀ epsilon : ℝ,0<epsilon → ∃ h : X → ℝ,A.ChartSmoothOn h univ ∧
    ∀ i z,z∈(A.chart i).target → CoefficientSemipositive
      (theta.coeff i z+smoothDDC (h ∘ (A.chart i).symm) z+epsilon • omega.coeff i z)

/-- A genuine original nef approximation pulls back with the SAME actual
global smooth scalar potential. Full tensor and dd^c naturality, and actual
complex-linearity of the derivative, prove EVERY source positivity inequality. -/
theorem OriginalNefWithRespectTo.holomorphicPullback
    {omega theta : AtlasClosedRealOneOneForm B} (hnef : OriginalNefWithRespectTo omega theta)
    {f : X → Y} (hf : A.IsHolomorphic B f) :
    OriginalNefWithRespectTo (omega.holomorphicPullback hf) (theta.holomorphicPullback hf) := by
  intro epsilon hepsilon
  obtain ⟨h,hh,hpos⟩ := hnef epsilon hepsilon
  refine ⟨h ∘ f,?_,?_⟩
  · simpa only [preimage_univ] using hh.comp_holomorphic isOpen_univ hf
  · intro i z hz
    obtain ⟨j,hj⟩ := B.cover (f ((A.chart i).symm z))
    have hzj : z∈atlasCoordinateDomain A B f i j := ⟨hz,hj⟩
    let F := atlasCoordinateMap A B f i j
    let L := fderiv ℝ F z
    have htarget : ContDiffOn ℝ ∞ (h ∘ (B.chart j).symm) (B.chart j).target := by
      simpa only [preimage_univ,inter_univ] using hh j
    have hscalar : ((h ∘ f) ∘ (A.chart i).symm)=ᶠ[𝓝 z] (h ∘ (B.chart j).symm) ∘ F := by
      filter_upwards [(atlasCoordinateDomain_isOpen hf i j).mem_nhds hzj] with y hy
      change h (f ((A.chart i).symm y))=h ((B.chart j).symm ((B.chart j) (f ((A.chart i).symm y))))
      rw [(B.chart j).left_inv hy.2]
    have hddc : smoothDDC ((h ∘ f) ∘ (A.chart i).symm) z=
        (smoothDDC (h ∘ (B.chart j).symm) (F z)).compContinuousLinearMap L := by
      rw [smoothDDC_congr hscalar]
      change smoothDDC (fun y => (h ∘ (B.chart j).symm) (F y)) z=_
      exact HolomorphicDDC.smoothDDC_comp (atlasCoordinateDomain_isOpen hf i j)
        (B.chart j).open_target (atlasCoordinateMap_contDiffOn hf i j) htarget
        (fun _ hy => atlasCoordinateMap_mem_target hy) hzj
    have hcombined : (theta.holomorphicPullback hf).coeff i z+
        smoothDDC ((h ∘ f) ∘ (A.chart i).symm) z+epsilon • (omega.holomorphicPullback hf).coeff i z=
        (theta.coeff j (F z)+smoothDDC (h ∘ (B.chart j).symm) (F z)+epsilon • omega.coeff j (F z)).compContinuousLinearMap L := by
      rw [theta.holomorphicPullback_coeff hf i j hzj,
        omega.holomorphicPullback_coeff hf i j hzj,hddc]
      ext w
      rfl
    rw [hcombined]
    intro v
    have hpair : L ∘ ![v,Complex.I • v]=![L v,Complex.I • L v] := by
      funext t
      fin_cases t
      · rfl
      · exact atlasCoordinateMap_fderiv_map_smul_complex hf hzj Complex.I v
    change 0≤(theta.coeff j (F z)+smoothDDC (h ∘ (B.chart j).symm) (F z)+epsilon • omega.coeff j (F z))
      (L ∘ ![v,Complex.I • v])
    rw [hpair]
    exact hpos j (F z) (atlasCoordinateMap_mem_target hzj) (L v)

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft

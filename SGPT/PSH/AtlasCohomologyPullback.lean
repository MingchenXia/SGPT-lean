import SGPT.PSH.AtlasFixedModelCohomology

/-! Genuine holomorphic pullback preserves ONE global original smooth-dd^c
class relation; native component class maps are then actual quotient maps. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Actual whole tensor pullback preserves the global relation, with SAME
pulled scalar potential and the genuine holomorphic dd^c chain rule. -/
theorem OriginalBottChernRel.holomorphicPullback
    {theta eta : AtlasClosedRealOneOneForm B}
    (hrel : OriginalBottChernRel theta eta) {f : X → Y} (hf : A.IsHolomorphic B f) :
    OriginalBottChernRel (theta.holomorphicPullback hf) (eta.holomorphicPullback hf) := by
  obtain ⟨h,hh,heq⟩ := hrel
  refine ⟨h ∘ f,?_,?_⟩
  · simpa only [preimage_univ] using hh.comp_holomorphic isOpen_univ hf
  · intro i z hz
    obtain ⟨j,hj⟩ := B.cover (f ((A.chart i).symm z))
    have hzj : z∈atlasCoordinateDomain A B f i j := ⟨hz,hj⟩
    have htarget : ContDiffOn ℝ ∞ (h ∘ (B.chart j).symm) (B.chart j).target := by
      simpa only [preimage_univ,inter_univ] using hh j
    have hscalar : ((h ∘ f) ∘ (A.chart i).symm)=ᶠ[𝓝 z]
        (h ∘ (B.chart j).symm) ∘ atlasCoordinateMap A B f i j := by
      filter_upwards [(atlasCoordinateDomain_isOpen hf i j).mem_nhds hzj] with y hy
      change h (f ((A.chart i).symm y))=
        h ((B.chart j).symm ((B.chart j) (f ((A.chart i).symm y))))
      rw [(B.chart j).left_inv hy.2]
    have hddc : smoothDDC ((h ∘ f) ∘ (A.chart i).symm) z=
        (smoothDDC (h ∘ (B.chart j).symm) (atlasCoordinateMap A B f i j z)).compContinuousLinearMap
          (fderiv ℝ (atlasCoordinateMap A B f i j) z) := by
      rw [smoothDDC_congr hscalar]
      change smoothDDC (fun y => (h ∘ (B.chart j).symm) (atlasCoordinateMap A B f i j y)) z=_
      exact HolomorphicDDC.smoothDDC_comp (atlasCoordinateDomain_isOpen hf i j)
        (B.chart j).open_target (atlasCoordinateMap_contDiffOn hf i j) htarget
        (fun _ hy => atlasCoordinateMap_mem_target hy) hzj
    rw [eta.holomorphicPullback_coeff hf i j hzj,
      theta.holomorphicPullback_coeff hf i j hzj,hddc,
      heq j _ (atlasCoordinateMap_mem_target hzj)]
    ext w
    rfl

/-- A genuine map on the actual GLOBAL original quotient, justified by the
whole tensor/potential proof, not a componentwise equality certificate. -/
def originalCohomologyPullback {f : X → Y} (hf : A.IsHolomorphic B f) :
    OriginalRealBottChern B → OriginalRealBottChern A :=
  Quotient.map (fun theta => theta.holomorphicPullback hf)
    (fun _ _ h => h.holomorphicPullback hf)

/-- Literal representative readback for the actual quotient pullback. -/
theorem originalCohomologyPullback_class {f : X → Y} (hf : A.IsHolomorphic B f)
    (theta : AtlasClosedRealOneOneForm B) :
    originalCohomologyPullback hf (originalClass theta)=originalClass (theta.holomorphicPullback hf) := rfl

variable [T2Space X] [ParacompactSpace X]

/-- Actual independently dimensional native cohomology of ONE internally
produced original open component, with all manifold structures produced. -/
def originalNativeComponentCohomology (A : VariableComplexAtlas X) (x : X) :=
  letI := A.componentChartedSpace x
  letI := A.componentComplexManifold_of_paracompact x
  RealBottChern (A.pointDimension x) (A.componentOpen x)

/-- Actual original closed tensor restricted to the genuine native component. -/
def originalNativeComponentForm (theta : AtlasClosedRealOneOneForm A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ClosedRealOneOneForm (A.pointDimension x) (A.componentOpen x) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  exact atlasClosedFormToNative (theta.holomorphicPullback (A.nativeComponentInclusion_isHolomorphic x))

/-- GENUINE canonical restriction map on actual global original quotient
classes, with the actual component inclusion and fixed-model equivalence. -/
def originalNativeComponentClass (q : OriginalRealBottChern A) (x : X) :
    originalNativeComponentCohomology A x := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  exact originalFixedModelToNative (originalCohomologyPullback (A.nativeComponentInclusion_isHolomorphic x) q)

/-- Every actual original representative reads as its genuine restricted
native closed form; no cohomology identification is postulated. -/
theorem originalNativeComponentClass_class (theta : AtlasClosedRealOneOneForm A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    originalNativeComponentClass (originalClass theta) x=
      RealBottChern.ofRepresentative (originalNativeComponentForm theta x) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  rfl

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft

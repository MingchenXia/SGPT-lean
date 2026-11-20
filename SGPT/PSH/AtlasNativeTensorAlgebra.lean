import SGPT.PSH.AtlasCohomologyPullback

/-! Full actual tensor addition/scaling and native component form readback
at EVERY coordinate, including total-function values outside chart targets. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Exact complete coefficient additivity, with no target restriction:
actual chart selection is independent of the form, so the same tensors add. -/
theorem original_holomorphicPullback_add_coeff_all
    (theta eta : AtlasClosedRealOneOneForm B) {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) (z : ComplexModel (A.dimension i)) :
    ((theta.add eta).holomorphicPullback hf).coeff i z=
      (theta.holomorphicPullback hf).coeff i z+(eta.holomorphicPullback hf).coeff i z := by
  ext w
  rfl

/-- Exact complete real scalar coefficient law, with no target restriction. -/
theorem original_holomorphicPullback_scale_coeff_all
    (theta : AtlasClosedRealOneOneForm B) (a : ℝ) {f : X → Y} (hf : A.IsHolomorphic B f)
    (i : A.Index) (z : ComplexModel (A.dimension i)) :
    ((theta.scale a).holomorphicPullback hf).coeff i z=a • (theta.holomorphicPullback hf).coeff i z := by
  ext w
  rfl

private theorem native_form_ext {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {F G : ClosedRealOneOneForm n M} (h : F.val.coeff=G.val.coeff) : F=G := by
  rcases F with ⟨⟨f,hf,hc⟩,hF⟩
  rcases G with ⟨⟨g,hg,hcg⟩,hG⟩
  change f=g at h
  cases h
  rfl

section NativeSource
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual entire native pulled form addition on ANY uniformly modeled
source, with no certificate replacing actual original tensor pullback. -/
theorem nativeSourcePulledForm_add (theta eta : AtlasClosedRealOneOneForm B)
    {f : M → Y} (hf : (ofFixedModel n M).IsHolomorphic B f) :
    atlasClosedFormToNative ((theta.add eta).holomorphicPullback hf)=
      atlasClosedFormToNative (theta.holomorphicPullback hf)+
      atlasClosedFormToNative (eta.holomorphicPullback hf) := by
  apply native_form_ext
  funext e z
  change ((theta.add eta).holomorphicPullback hf).coeff e z=
    (theta.holomorphicPullback hf).coeff e z+(eta.holomorphicPullback hf).coeff e z
  exact original_holomorphicPullback_add_coeff_all theta eta hf e z

/-- Actual entire native pulled form real scaling, in EVERY natural dimension. -/
theorem nativeSourcePulledForm_scale (theta : AtlasClosedRealOneOneForm B) (a : ℝ)
    {f : M → Y} (hf : (ofFixedModel n M).IsHolomorphic B f) :
    atlasClosedFormToNative ((theta.scale a).holomorphicPullback hf)=
      a • atlasClosedFormToNative (theta.holomorphicPullback hf) := by
  apply native_form_ext
  funext e z
  change ((theta.scale a).holomorphicPullback hf).coeff e z=a • (theta.holomorphicPullback hf).coeff e z
  exact original_holomorphicPullback_scale_coeff_all theta a hf e z

/-- Fixed native-source class additivity follows from the ENTIRE proved
native pulled-form equality and the accepted existing native quotient map. -/
theorem nativeSourcePulledForm_class_add (theta eta : AtlasClosedRealOneOneForm B)
    {f : M → Y} (hf : (ofFixedModel n M).IsHolomorphic B f) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative ((theta.add eta).holomorphicPullback hf))=
      RealBottChern.ofRepresentative (atlasClosedFormToNative (theta.holomorphicPullback hf))+
      RealBottChern.ofRepresentative (atlasClosedFormToNative (eta.holomorphicPullback hf)) := by
  rw [nativeSourcePulledForm_add,RealBottChern.ofRepresentative_add]

/-- Fixed native-source class scaling with EXACT accepted real normalization. -/
theorem nativeSourcePulledForm_class_scale (theta : AtlasClosedRealOneOneForm B) (a : ℝ)
    {f : M → Y} (hf : (ofFixedModel n M).IsHolomorphic B f) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative ((theta.scale a).holomorphicPullback hf))=
      a • RealBottChern.ofRepresentative (atlasClosedFormToNative (theta.holomorphicPullback hf)) := by
  rw [nativeSourcePulledForm_scale,RealBottChern.ofRepresentative_smul]
end NativeSource

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft

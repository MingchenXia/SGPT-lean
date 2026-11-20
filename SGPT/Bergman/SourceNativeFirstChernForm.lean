import SGPT.Bergman.SourceNativeHermitianMetric
import SGPT.PSH.GlobalL2Statement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.NativeHermitianMetric
open Bundle Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.PSH SGPT.PSH.LineBundleMetric
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- EVERY actual native holomorphic atlas frame is a genuine local book
holomorphic section; no chosen special frame or output certificate. -/
theorem sourceAtlasFrame_holomorphic (L : HermitianHolomorphicLineBundle n X)
    (e : AtlasFrame L) :
    IsHolomorphicSectionOn (n := n) L.Fiber (fun x => e.val.symm x 1) e.val.baseSet := by
  let := e.property
  rw [IsHolomorphicSectionOn, e.val.mdifferentiableOn_section_baseSet_iff]
  apply (mdifferentiableOn_const (c := (1 : ℂ))).congr
  intro x hx
  exact congrArg Prod.snd (e.val.apply_mk_symm hx (1 : ℂ))

/-- The SAME actual frame is nowhere zero on its actual original domain. -/
theorem sourceAtlasFrame_ne_zero (L : HermitianHolomorphicLineBundle n X)
    (e : AtlasFrame L) {x : X} (hx : x ∈ e.val.baseSet) : e.val.symm x 1 ≠ 0 := by
  let := e.property
  exact norm_pos_iff.mp (frameNorm_pos L.Fiber e.val hx)

/-- Canonical actual Chern form produced by the existing whole book metric
construction, from the SAME physical fiber inner products. -/
def sourceNativeFirstChernForm (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) : ClosedRealOneOneForm n X :=
  firstChernForm (sourceNativeHermitianMetric L hL)

/-- Full original frame-reader needed by native global L2/Bergman theory.
The actual Chern form and every actual frame identity are outputs from
original smooth physical metrics; no Chern or weighted-norm certificate. -/
theorem sourceNativeFirstChernForm_isOwn (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) :
    SGPT.PSH.GlobalL2.IsOwnFirstChernForm L (sourceNativeFirstChernForm L hL) := by
  intro c e z hz hzU
  have h := isFirstChernForm_firstChernForm (sourceNativeHermitianMetric L hL)
    (fun x => e.val.symm x 1) e.val.baseSet e.val.open_baseSet
    (sourceAtlasFrame_holomorphic L e) (fun _ hx => sourceAtlasFrame_ne_zero L e hx)
    c z hz hzU
  have hweight : SGPT.PSH.LineBundleMetric.localWeight (sourceNativeHermitianMetric L hL)
      (fun x => e.val.symm x 1) c =
      fun w => -Real.log (‖e.val.symm (c.val.symm w) 1‖ ^ 2) := by
    funext w
    change -Real.log (((sourceNativeHermitianMetric L hL).form (c.val.symm w)).normSq
      (e.val.symm (c.val.symm w) 1)) = _
    rw [sourceNativeHermitianMetric_normSq]
  rw [hweight] at h
  exact h

/-- Any naturally specified original Chern form matches the manufactured
physical Chern form on all original chart targets. This consumes the
original Chern-form hypothesis, never a desired Bergman conclusion. -/
theorem sourceNativeFirstChernForm_geometricallyEq
    (L : HermitianHolomorphicLineBundle n X) (hL : IsSourceSmoothHermitianMetric L)
    {θ : ClosedRealOneOneForm n X} (hθ : SGPT.PSH.GlobalL2.IsOwnFirstChernForm L θ) :
    (sourceNativeFirstChernForm L hL).val.GeometricallyEq θ.val := by
  intro c z hz
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (c.val.symm z), inferInstance⟩
  have he : c.val.symm z ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber _
  rw [sourceNativeFirstChernForm_isOwn L hL c e z hz he, hθ c e z hz he]

end SGPT.Bergman.NativeHermitianMetric

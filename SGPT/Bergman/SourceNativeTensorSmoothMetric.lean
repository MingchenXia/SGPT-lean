import SGPT.Bergman.SourceNativeFirstChernForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.NativeHermitianMetric
open Bundle Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff TensorProduct

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- EVERY atlas frame of the actual native tensor construction is a genuine
original product frame. Its physical squared norm is smooth internally. -/
theorem sourceNativeTensor_smooth (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) :
    IsSourceSmoothHermitianMetric (tensor L T) := by
  intro c e
  rcases e with ⟨e, he⟩
  rcases he.out with ⟨a, ha, rfl⟩
  rcases ha with ⟨eL, eT, heL, heT, rfl⟩
  let E : AtlasFrame L := ⟨eL, heL⟩
  let F : AtlasFrame T := ⟨eT, heT⟩
  change ContDiffOn ℝ ∞
    (fun z => ‖(tensorAtlasFrame E F).val.symm (c.val.symm z) 1‖ ^ 2)
    (c.val.target ∩ c.val.symm ⁻¹' (eL.baseSet ∩ eT.baseSet))
  have hL' := (hL c E).mono (show
    c.val.target ∩ c.val.symm ⁻¹' (eL.baseSet ∩ eT.baseSet) ⊆
      c.val.target ∩ c.val.symm ⁻¹' eL.baseSet from fun _ hz => ⟨hz.1, hz.2.1⟩)
  have hT' := (hT c F).mono (show
    c.val.target ∩ c.val.symm ⁻¹' (eL.baseSet ∩ eT.baseSet) ⊆
      c.val.target ∩ c.val.symm ⁻¹' eT.baseSet from fun _ hz => ⟨hz.1, hz.2.2⟩)
  apply (hL'.mul hT').congr
  intro z hz
  rw [tensorAtlasFrame_norm_one E F hz.2, mul_pow]

/-- The actual native scalar unit has its original constant physical
frame norm; no auxiliary trivial-bundle metric is introduced. -/
theorem sourceNativeUnit_smooth :
    IsSourceSmoothHermitianMetric (unit (n := n) (M := X)) := by
  intro c e
  have he := e.property.out
  change e.val = Bundle.Trivial.trivialization X ℂ at he
  rw [he]
  simpa only [Bundle.Trivial.trivialization_symm_apply] using!
    (contDiffOn_const (c := ‖(1 : ℂ)‖ ^ 2) :
      ContDiffOn ℝ ∞ (fun _ : ComplexModel n => ‖(1 : ℂ)‖ ^ 2)
        (c.val.target ∩ c.val.symm ⁻¹' (Bundle.Trivial.trivialization X ℂ).baseSet))

/-- Actual recursively constructed positive tensor powers retain original
physical smoothness; the proof follows the native constructors. -/
theorem sourceNativePositivePower_smooth (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) :
    ∀ j : ℕ, IsSourceSmoothHermitianMetric (positivePower L j)
  | 0 => hL
  | j + 1 => sourceNativeTensor_smooth (positivePower L j) L
      (sourceNativePositivePower_smooth L hL j) hL

/-- ALL actual original twists, including degree zero, retain the SAME
physical smooth metric without a tensor-smoothness certificate. -/
theorem sourceNativeTwistedPower_smooth (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) :
    ∀ k : ℕ, IsSourceSmoothHermitianMetric (twistedPower L T k)
  | 0 => sourceNativeTensor_smooth unit T sourceNativeUnit_smooth hT
  | k + 1 => sourceNativeTensor_smooth (positivePower L k) T
      (sourceNativePositivePower_smooth L hL k) hT

end SGPT.Bergman.NativeHermitianMetric

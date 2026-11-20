import SGPT.PSH.GeometricQPreimageComposition
import SGPT.PSH.NativeLogAnyDimension

/-! Full native logarithmic equivalence under actual biholomorphisms,
with pure substitution of dimensions allowed to vary independently. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff
universe u
variable {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

private theorem qdiv_ext {D E : EffectiveGeometricQDivisor n M}
    (h : ∀ Q,D.coefficient Q=E.coefficient Q) : D=E := by
  cases D
  cases E
  have hc := funext h
  cases hc
  rfl

/-- Every coefficient of the actual identity preimage is unchanged. -/
theorem geometricQPreimage_refl (D : EffectiveGeometricQDivisor n M) :
    geometricQDivisorBiholomorphicPreimage D (Homeomorph.refl M) contMDiff_id contMDiff_id=D := by
  apply qdiv_ext
  intro Q
  apply congrArg D.coefficient
  apply GeometricPrimeCarrier.ext
  rfl

/-- Both actual inverse maps cancel on the ENTIRE rational divisor. -/
theorem geometricQPreimage_inverse (D : EffectiveGeometricQDivisor n N)
    (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm) :
    geometricQDivisorBiholomorphicPreimage
      (geometricQDivisorBiholomorphicPreimage D e he hei) e.symm hei he=D := by
  have he2 : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm.symm := by
    simpa only [Homeomorph.symm_symm] using he
  calc
    _ = geometricQDivisorBiholomorphicPreimage D (e.symm.trans e)
        (he.comp hei) (he.comp hei) := by
      simpa only [Homeomorph.symm_symm] using
        (geometricQPreimage_comp D e.symm e hei he2 he hei)
    _ = D := (geometricQPreimage_congr D (e.symm.trans e) (Homeomorph.refl N)
      (he.comp hei) (he.comp hei) contMDiff_id contMDiff_id
      (fun q => e.apply_symm_apply q)).trans (geometricQPreimage_refl D)

/-- Actual full native logarithmic data transport in BOTH directions.
No inverse logarithmic, prime or coefficient certificate is a premise. -/
theorem native_log_preimage_iff
    (D : EffectiveGeometricQDivisor n N) (u : N → EReal) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm) :
    NativeHasLogSingularitiesAlongAnyDimension
      (geometricQDivisorBiholomorphicPreimage D e he hei) (u ∘ e) ↔
    NativeHasLogSingularitiesAlongAnyDimension D u := by
  constructor
  · intro h
    have hback := h.comp_biholomorphic e.symm hei he
    rw [geometricQPreimage_inverse] at hback
    have hu : (u ∘ e) ∘ e.symm=u := by
      funext q
      simp only [Function.comp_apply,e.apply_symm_apply]
    rwa [hu] at hback
  · intro h
    exact h.comp_biholomorphic e he hei

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft

namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
universe u

/-- Independently indexed actual native dimensions are transported ONLY by
substituting their proved equality, retaining all original maps and functions. -/
theorem native_log_preimage_of_dimensionEq_iff
    {a b : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a=b) (D : EffectiveGeometricQDivisor b N) (u : N → EReal) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ e.symm) :
    NativeHasLogSingularitiesAlongAnyDimension
      (geometricQDivisorBiholomorphicPreimageOfDimensionEq h D e he hei) (u ∘ e) ↔
    NativeHasLogSingularitiesAlongAnyDimension D u := by
  subst b
  exact native_log_preimage_iff D u e he hei

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft

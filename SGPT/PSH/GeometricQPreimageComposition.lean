import SGPT.PSH.AtlasNativeReanchor

/-! Genuine full coefficient functoriality of the actual rational preimage;
used to compare the two literal original open/anchor squares. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceLogSingularitiesDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
universe u
variable {n : ℕ} {M N P : Type u} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]

private theorem qdiv_ext {D E : EffectiveGeometricQDivisor n M}
    (h : ∀ Q,D.coefficient Q=E.coefficient Q) : D=E := by
  cases D
  cases E
  have hc := funext h
  cases hc
  rfl

/-- The entire independently defined rational preimage composes on actual
biholomorphisms, in every natural dimension and for every prime coefficient. -/
theorem geometricQPreimage_comp (D : EffectiveGeometricQDivisor n P)
    (e : M ≃ₜ N) (f : N ≃ₜ P)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hfi : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f.symm) :
    geometricQDivisorBiholomorphicPreimage
      (geometricQDivisorBiholomorphicPreimage D f hf hfi) e he hei =
    geometricQDivisorBiholomorphicPreimage D (e.trans f) (hf.comp he) (hei.comp hfi) := by
  apply qdiv_ext
  intro Q
  let Ke := biholomorphic_geometricPrimeCarrier_equiv e he hei
  let Kf := biholomorphic_geometricPrimeCarrier_equiv f hf hfi
  let Kef := biholomorphic_geometricPrimeCarrier_equiv (e.trans f) (hf.comp he) (hei.comp hfi)
  change D.coefficient (Kf.symm (Ke.symm Q))=D.coefficient (Kef.symm Q)
  apply congrArg D.coefficient
  apply GeometricPrimeCarrier.ext
  change (biholomorphic_geometricPrimeCarrier_preimage f.symm hfi hf
      (biholomorphic_geometricPrimeCarrier_preimage e.symm hei he Q)).val =
    (biholomorphic_geometricPrimeCarrier_preimage (e.trans f).symm (hei.comp hfi) (hf.comp he) Q).val
  have he2 : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm.symm := by
    simpa only [Homeomorph.symm_symm] using he
  have hf2 : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f.symm.symm := by
    simpa only [Homeomorph.symm_symm] using hf
  calc
    _ = f.symm ⁻¹' (biholomorphic_geometricPrimeCarrier_preimage e.symm hei he Q).val :=
      biholomorphic_geometricPrimeCarrier_preimage_carrier f.symm hfi hf2 _
    _ = f.symm ⁻¹' (e.symm ⁻¹' Q.val) := congrArg (fun A => f.symm ⁻¹' A)
      (biholomorphic_geometricPrimeCarrier_preimage_carrier e.symm hei he2 Q)
    _ = (e.trans f).symm ⁻¹' Q.val := rfl
    _ = _ := (biholomorphic_geometricPrimeCarrier_preimage_carrier
      (e.trans f).symm (hei.comp hfi)
      (hf.comp he) Q).symm

/-- The actual divisor depends on the actual biholomorphic map, not on an
alternative proof term for the same map or its inverse. -/
theorem geometricQPreimage_congr (D : EffectiveGeometricQDivisor n N)
    (e f : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hfi : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f.symm)
    (h : ∀ x,e x=f x) :
    geometricQDivisorBiholomorphicPreimage D e he hei =
      geometricQDivisorBiholomorphicPreimage D f hf hfi := by
  have hef : e=f := Homeomorph.ext h
  subst f
  rfl

end SGPT.PSH.SourceLogSingularitiesDraft

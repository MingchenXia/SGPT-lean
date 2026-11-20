import SGPT.PSH.BiholomorphicPrimeTransport

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

/-- The ENTIRE actual prime index, with both inverse identities proved from
literal carrier preimages. No prime catalog or positive dimension is supplied. -/
def biholomorphic_geometricPrimeCarrier_equiv (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm) :
    GeometricPrimeCarrier n N ≃ GeometricPrimeCarrier n M where
  toFun := biholomorphic_geometricPrimeCarrier_preimage e he hei
  invFun := biholomorphic_geometricPrimeCarrier_preimage e.symm hei he
  left_inv := by
    intro P
    apply GeometricPrimeCarrier.ext
    ext y
    change e (e.symm y) ∈ P.val ↔ y ∈ P.val
    rw [e.apply_symm_apply]
  right_inv := by
    intro Q
    apply GeometricPrimeCarrier.ext
    ext x
    change e.symm (e x) ∈ Q.val ↔ x ∈ Q.val
    rw [e.symm_apply_apply]

/-- ORIGINAL coefficients on the SAME actual entire prime preimage. Actual
injective reindexing and continuity internally manufacture local finiteness. -/
def geometricQDivisorBiholomorphicPreimage (D : EffectiveGeometricQDivisor n N)
    (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm) :
    EffectiveGeometricQDivisor n M := by
  classical
  let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
  have hcarrier (Q : GeometricPrimeCarrier n M) : e ⁻¹' (K.symm Q).val = Q.val :=
    congrArg (fun P : GeometricPrimeCarrier n M => P.val) (K.apply_symm_apply Q)
  have hLF := (D.locallyFinite.comp_injective K.symm.injective).preimage_continuous e.continuous
  have hfamily : (fun Q : GeometricPrimeCarrier n M =>
      e ⁻¹' (if D.coefficient (K.symm Q) = 0 then ∅ else (K.symm Q).val)) =
      (fun Q : GeometricPrimeCarrier n M =>
        if D.coefficient (K.symm Q) = 0 then ∅ else Q.val) := by
    funext Q
    split_ifs
    · exact preimage_empty
    · exact hcarrier Q
  refine ⟨fun Q => D.coefficient (K.symm Q), fun Q => D.coefficient_nonneg (K.symm Q), ?_⟩
  exact hfamily ▸ hLF

/-- EVERY actual original coefficient survives on the SAME produced prime. -/
theorem geometricQDivisorBiholomorphicPreimage_coefficient
    (D : EffectiveGeometricQDivisor n N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (P : GeometricPrimeCarrier n N) :
    (geometricQDivisorBiholomorphicPreimage D e he hei).coefficient
      (biholomorphic_geometricPrimeCarrier_preimage e he hei P) = D.coefficient P := by
  change D.coefficient ((biholomorphic_geometricPrimeCarrier_equiv e he hei).symm
    ((biholomorphic_geometricPrimeCarrier_equiv e he hei) P)) = _
  rw [Equiv.symm_apply_apply]

/-- ENTIRE support preimage, including absent primes and dimension zero. -/
theorem geometricQDivisorBiholomorphicPreimage_support
    (D : EffectiveGeometricQDivisor n N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm) :
    (geometricQDivisorBiholomorphicPreimage D e he hei).support = e ⁻¹' D.support := by
  let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hpos, hxQ⟩ := ((geometricQDivisorBiholomorphicPreimage D e he hei).mem_support x).mp hx
    have hcarrier : e ⁻¹' (K.symm Q).val = Q.val :=
      congrArg (fun P : GeometricPrimeCarrier n M => P.val) (K.apply_symm_apply Q)
    exact (D.mem_support (e x)).mpr ⟨K.symm Q, hpos, by rwa [← hcarrier] at hxQ⟩
  · intro hx
    obtain ⟨P, hpos, hxP⟩ := (D.mem_support (e x)).mp hx
    apply ((geometricQDivisorBiholomorphicPreimage D e he hei).mem_support x).mpr
    refine ⟨biholomorphic_geometricPrimeCarrier_preimage e he hei P, ?_, hxP⟩
    rwa [geometricQDivisorBiholomorphicPreimage_coefficient]

end SGPT.PSH

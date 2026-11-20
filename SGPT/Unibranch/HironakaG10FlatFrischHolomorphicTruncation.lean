import SGPT.Unibranch.HironakaG10FlatFrischCoefficientUniversal
import SGPT.Unibranch.HironakaG10HolomorphicArtinianParameters

/-! # Non-reduced Frisch universality over actual holomorphic point truncations -/
set_option autoImplicit false
open scoped Topology TensorProduct

namespace SGPT.Unibranch.HironakaG10FlatFrischHolomorphicTruncation
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
open SGPT.Unibranch.HironakaG10ArtinianTensorCoefficients
  SGPT.Unibranch.HironakaG10ArtinianCoefficientOperators
  SGPT.Unibranch.HironakaG10HolomorphicArtinianParameters
  SGPT.Unibranch.HironakaG10FlatFrischCoefficientUniversal

/-- For an actual proper point-truncated holomorphic germ ring, the finite
  coefficient Banach model and nilpotent maximal ideal are constructed
  internally. Flatness of the actual parameter-linear section cokernel and
  agreement with the reference modulo the maximal ideal imply vanishing of
  the actual Frisch Schur operator. -/
theorem schurOp_eq_zero_for_holomorphic_truncation
    {E₂ E₁ E₀ : Type*}
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
    (n q : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (hproper : I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ≠ ⊤)
    (g₀ : E₂ →L[ℂ] E₁) (f₀ : E₁ →L[ℂ] E₀)
    (R₀ : E₁ →L[ℂ] E₂) (S₀ : E₀ →L[ℂ] E₁)
    (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e)
    (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hcomp : ∀ e, f₀ (g₀ e) = 0)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x) :
    let Q := HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    ∃ (hlocal : IsLocalRing Q) (r : ℕ) (b : Module.Basis (Fin r) ℂ Q),
      letI := hlocal
      letI := parameterCoefficientModule (E := E₁) b
      letI := parameterCoefficientModule (E := E₀) b
      ∀ (F : (Fin r → E₁) →L[ℂ] (Fin r → E₀))
        (hC : (opC ((coefficientCLM g₀).comp (coefficientCLM R₀))
          ((coefficientCLM f₀).comp (coefficientCLM S₀)) (coefficientCLM S₀) F).IsInvertible)
        (FA : (Fin r → E₁) →ₗ[Q] (Fin r → E₀)) (hF : ∀ x, FA x = F x)
        (hflat : Module.Flat Q ((Fin r → E₀) ⧸ LinearMap.range FA)),
        (∀ x, FA x - coefficientMap b f₀.toLinearMap x ∈
          IsLocalRing.maximalIdeal Q • (⊤ : Submodule Q (Fin r → E₀))) →
        schurOp ((coefficientCLM g₀).comp (coefficientCLM R₀))
          ((coefficientCLM f₀).comp (coefficientCLM S₀)) (coefficientCLM S₀) F = 0 := by
  let Q := HolGerm (ComplexModel n) ⧸
    (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
  obtain ⟨hlocal,r,⟨b⟩,k,hk⟩ := truncated_germ_finite_local_nilpotent n q I hproper
  letI : IsLocalRing Q := hlocal
  refine ⟨hlocal,r,b,?_⟩
  letI := parameterCoefficientModule (E := E₁) b
  letI := parameterCoefficientModule (E := E₀) b
  intro F hC FA hF hflat hmod
  exact schurOp_eq_zero_on_coefficients b g₀ f₀ R₀ S₀ hR₀ hS₀ hcomp hex
    F hC FA hF hflat (IsLocalRing.maximalIdeal Q) ⟨k,hk⟩ hmod

end SGPT.Unibranch.HironakaG10FlatFrischHolomorphicTruncation

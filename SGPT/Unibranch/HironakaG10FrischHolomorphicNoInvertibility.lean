import SGPT.Unibranch.HironakaG10FrischNilpotentInvertible
import SGPT.Unibranch.HironakaG10FlatFrischHolomorphicTruncation

/-! # Frisch universality on holomorphic truncations without an invertibility assumption -/
set_option autoImplicit false
namespace SGPT.Unibranch.HironakaG10FrischHolomorphicNoInvertibility
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
open SGPT.Unibranch.HironakaG10ArtinianTensorCoefficients
  SGPT.Unibranch.HironakaG10ArtinianCoefficientOperators
  SGPT.Unibranch.HironakaG10HolomorphicArtinianParameters
  SGPT.Unibranch.HironakaG10FlatFrischHolomorphicTruncation
  SGPT.Unibranch.HironakaG10FrischNilpotentInvertible

/-- On actual proper holomorphic point truncations, nilpotence automatically
  supplies Frisch's comparison invertibility. The parameter-linear presentation,
  its flat cokernel and agreement with the reference remain explicit inputs. -/
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
        (FA : (Fin r → E₁) →ₗ[Q] (Fin r → E₀)) (hF : ∀ x, FA x = F x)
        (hflat : Module.Flat Q ((Fin r → E₀) ⧸ LinearMap.range FA)),
        (∀ x, FA x - coefficientMap b f₀.toLinearMap x ∈
          IsLocalRing.maximalIdeal Q • (⊤ : Submodule Q (Fin r → E₀))) →
        schurOp ((coefficientCLM g₀).comp (coefficientCLM R₀))
          ((coefficientCLM f₀).comp (coefficientCLM S₀)) (coefficientCLM S₀) F = 0 := by
  let Q := HolGerm (ComplexModel n) ⧸
    (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
  obtain ⟨hlocal,r,b,h⟩ :=
    SGPT.Unibranch.HironakaG10FlatFrischHolomorphicTruncation.schurOp_eq_zero_for_holomorphic_truncation
      n q I hproper g₀ f₀ R₀ S₀ hR₀ hS₀ hcomp hex
  letI : IsLocalRing Q := hlocal
  letI := parameterCoefficientModule (E := E₁) b
  letI := parameterCoefficientModule (E := E₀) b
  refine ⟨hlocal,r,b,?_⟩
  intro F FA hF hflat hmod
  have hnil : ∃ k : ℕ, IsLocalRing.maximalIdeal Q ^ k = ⊥ := by
    obtain ⟨_,_,⟨_⟩,k,hk⟩ := truncated_germ_finite_local_nilpotent n q I hproper
    exact ⟨k,hk⟩
  have hC := opC_invertible_on_nilpotent_coefficients b g₀ f₀ R₀ S₀ hcomp
    (IsLocalRing.maximalIdeal Q) hnil F FA hF hmod
  exact h F hC FA hF hflat hmod

end SGPT.Unibranch.HironakaG10FrischHolomorphicNoInvertibility

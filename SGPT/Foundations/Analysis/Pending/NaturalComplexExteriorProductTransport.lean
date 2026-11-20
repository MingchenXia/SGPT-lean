import SGPT.Foundations.Analysis.Pending.NaturalRealAlternatingComplexification

/-!
# Faithful complexification transport of the actual exterior product

The complex wedge is the exact normalized alternatization of tensor
concatenation followed by actual complex multiplication. It equals the
genuine alternating coproduct and the unique complexification of the
original continuous real coordinate wedge. No higher-degree span or global
cohomological theorem is asserted.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexExteriorProductTransport

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open NaturalComplexBidegreeTransport NaturalRealAlternatingComplexification

def complexWedgeSum {n p q : ℕ}
    (A : complexification n [⋀^Fin p]→ₗ[ℂ] ℂ)
    (B : complexification n [⋀^Fin q]→ₗ[ℂ] ℂ) :
    complexification n [⋀^(Fin p ⊕ Fin q)]→ₗ[ℂ] ℂ :=
  (p.factorial * q.factorial : ℂ)⁻¹ •
    MultilinearMap.alternatization
      ((TensorProduct.lid ℂ ℂ).toLinearMap.compMultilinearMap
        (MultilinearMap.domCoprod A.toMultilinearMap B.toMultilinearMap))

def complexWedge {n p q : ℕ}
    (A : complexification n [⋀^Fin p]→ₗ[ℂ] ℂ)
    (B : complexification n [⋀^Fin q]→ₗ[ℂ] ℂ) :
    complexification n [⋀^Fin (p + q)]→ₗ[ℂ] ℂ :=
  (complexWedgeSum A B).domDomCongr finSumFinEquiv

theorem complexWedgeSum_apply {n p q : ℕ}
    (A : complexification n [⋀^Fin p]→ₗ[ℂ] ℂ)
    (B : complexification n [⋀^Fin q]→ₗ[ℂ] ℂ)
    (v : Fin p ⊕ Fin q → complexification n) :
    complexWedgeSum A B v = (p.factorial * q.factorial : ℂ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin p ⊕ Fin q), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        (A (v ∘ σ ∘ Sum.inl) * B (v ∘ σ ∘ Sum.inr)) := by
  classical
  simp [complexWedgeSum, AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply, LinearMap.compMultilinearMap_apply,
    TensorProduct.lid_tmul, Units.smul_def, smul_eq_mul, Function.comp_def]

theorem complexWedge_eq_domCoprod {n p q : ℕ}
    (A : complexification n [⋀^Fin p]→ₗ[ℂ] ℂ)
    (B : complexification n [⋀^Fin q]→ₗ[ℂ] ℂ) :
    complexWedge A B =
      ((TensorProduct.lid ℂ ℂ).toLinearMap.compAlternatingMap (A.domCoprod B)).domDomCongr
        finSumFinEquiv := by
  unfold complexWedge complexWedgeSum
  rw [LinearMap.compMultilinearMap_alternatization,
    MultilinearMap.domCoprod_alternization_eq A B]
  simp only [Fintype.card_fin, LinearMap.compAlternatingMap_smul]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul]
  have hp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hc : (p.factorial * q.factorial : ℂ)⁻¹ *
      ((p.factorial * q.factorial : ℕ) : ℂ) = 1 := by
    rw [Nat.cast_mul]
    exact inv_mul_cancel₀ (mul_ne_zero hp hq)
  rw [hc, one_smul]

private theorem complexWedge_realEmbedding {n p q : ℕ}
    (A : ComplexModel n [⋀^Fin p]→L[ℝ] ℝ)
    (B : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ)
    (v : Fin (p + q) → ComplexModel n) :
    complexWedge (complexify A.toAlternatingMap) (complexify B.toAlternatingMap)
        (fun i => realEmbedding n (v i)) = (coordinateWedge A B v : ℂ) := by
  classical
  simp only [complexWedge, AlternatingMap.domDomCongr_apply,
    complexWedgeSum_apply, coordinateWedge_apply, coordinateWedgeSum_apply]
  simp only [Function.comp_def, complexify_realEmbedding]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum,
    Complex.ofReal_natCast, Complex.ofReal_intCast]
  rfl

theorem complexify_coordinateWedge {n p q : ℕ}
    (A : ComplexModel n [⋀^Fin p]→L[ℝ] ℝ)
    (B : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :
    complexify (coordinateWedge A B).toAlternatingMap =
      complexWedge (complexify A.toAlternatingMap) (complexify B.toAlternatingMap) := by
  symm
  apply complexify_unique
  exact complexWedge_realEmbedding A B

theorem complexWedge_add_left {n p q : ℕ}
    (A A' : complexification n [⋀^Fin p]→ₗ[ℂ] ℂ)
    (B : complexification n [⋀^Fin q]→ₗ[ℂ] ℂ) :
    complexWedge (A + A') B = complexWedge A B + complexWedge A' B := by
  ext v
  simp [complexWedge, complexWedgeSum_apply, add_mul, mul_add, Finset.sum_add_distrib]

theorem complexWedge_add_right {n p q : ℕ}
    (A : complexification n [⋀^Fin p]→ₗ[ℂ] ℂ)
    (B B' : complexification n [⋀^Fin q]→ₗ[ℂ] ℂ) :
    complexWedge A (B + B') = complexWedge A B + complexWedge A B' := by
  ext v
  simp [complexWedge, complexWedgeSum_apply, mul_add, Finset.sum_add_distrib]

theorem complexWedge_smul_left {n p q : ℕ} (c : ℂ)
    (A : complexification n [⋀^Fin p]→ₗ[ℂ] ℂ)
    (B : complexification n [⋀^Fin q]→ₗ[ℂ] ℂ) :
    complexWedge (c • A) B = c • complexWedge A B := by
  ext v
  simp only [complexWedge, AlternatingMap.domDomCongr_apply, complexWedgeSum_apply,
    AlternatingMap.smul_apply, smul_eq_mul]
  conv_rhs => rw [mul_left_comm c, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem complexWedge_smul_right {n p q : ℕ} (c : ℂ)
    (A : complexification n [⋀^Fin p]→ₗ[ℂ] ℂ)
    (B : complexification n [⋀^Fin q]→ₗ[ℂ] ℂ) :
    complexWedge A (c • B) = c • complexWedge A B := by
  ext v
  simp only [complexWedge, AlternatingMap.domDomCongr_apply, complexWedgeSum_apply,
    AlternatingMap.smul_apply, smul_eq_mul]
  conv_rhs => rw [mul_left_comm c, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

end SGPT.Foundations.Analysis.Pending.NaturalComplexExteriorProductTransport

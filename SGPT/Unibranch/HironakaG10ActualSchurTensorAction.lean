import SGPT.Unibranch.HironakaG10ActualSchurJet
import SGPT.Unibranch.HironakaG10TensorOperatorComposition

/-! # Actual Schur and inverse actions on whole parameter tensors -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace SGPT.Unibranch.HironakaG10ActualSchurTensorAction
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  SGPT.Unibranch.HironakaG10BanachParameterJet
  SGPT.Unibranch.HironakaG10TensorOperator
  SGPT.Unibranch.HironakaG10TensorOperatorComposition
  SGPT.Unibranch.HironakaG10ActualInverseJet
  SGPT.Unibranch.HironakaG10ActualSchurJet

/-- The actual jet of the actual nearby inverse induces a genuine two-sided
inverse of the original operator jet on the whole parameter tensor space. -/
theorem tensorOperator_actual_inverse
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (C : ComplexModel d → (E →L[ℂ] E))
    (hC : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ C z)
    (hC0 : C 0 = ContinuousLinearMap.id ℂ E) :
    (tensorOperator (Γ := Γ) (E := E) (F := E) (banachJet (E := E →L[ℂ] E) d q φ C)).comp
        (tensorOperator (Γ := Γ) (E := E) (F := E)
          (banachJet (E := E →L[ℂ] E) d q φ (fun z => (C z).inverse))) = LinearMap.id ∧
    (tensorOperator (Γ := Γ) (E := E) (F := E)
      (banachJet (E := E →L[ℂ] E) d q φ (fun z => (C z).inverse))).comp
        (tensorOperator (Γ := Γ) (E := E) (F := E)
          (banachJet (E := E →L[ℂ] E) d q φ C)) = LinearMap.id := by
  obtain ⟨h₁,h₂⟩ := banachJet_actual_inverse d q φ hφ C hC hC0
  constructor
  · rw [← tensorOperator_comp, h₁, tensorOperator_one_id]
  · rw [← tensorOperator_comp, h₂, tensorOperator_one_id]

/-- The action of the actual source Schur jet on whole parameter tensors
is the genuine composition of the three corresponding tensor actions. -/
theorem tensorOperator_actual_schur
    {Γ E₁ E₀ : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : opC P Q S₀ (f 0) = ContinuousLinearMap.id ℂ E₀) :
    tensorOperator (Γ := Γ) (E := E₁) (F := E₀)
      (banachJet (E := E₁ →L[ℂ] E₀) d q φ (fun z => schurOp P Q S₀ (f z))) =
      (tensorOperator (Γ := Γ) (E := E₀) (F := E₀)
        ((1 : Γ) ⊗ₜ[ℂ] (ContinuousLinearMap.id ℂ E₀ - Q))).comp
        ((tensorOperator (Γ := Γ) (E := E₀) (F := E₀)
          (banachJet (E := E₀ →L[ℂ] E₀) d q φ (fun z => (opC P Q S₀ (f z)).inverse))).comp
          (tensorOperator (Γ := Γ) (E := E₁) (F := E₀) (banachJet (E := E₁ →L[ℂ] E₀) d q φ f))) := by
  rw [banachJet_actual_schur d q φ hφ P Q S₀ f hf hC0, tensorOperator_comp, tensorOperator_comp]

end SGPT.Unibranch.HironakaG10ActualSchurTensorAction

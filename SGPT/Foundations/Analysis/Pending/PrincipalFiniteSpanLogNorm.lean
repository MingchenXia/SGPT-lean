import SGPT.Foundations.Analysis.Pending.EuclideanHolomorphicGermSpan
import SGPT.Foundations.Analysis.Pending.PrincipalGeneratorLogNormNormalForm

set_option autoImplicit false

/-! # The full literal principal stalk and its actual original generator logarithm -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.PrincipalFiniteSpanLogNorm

open FirstPass FirstPass.HolomorphicIdealSheaves InvertibleIdealQuotient

noncomputable section

/-- Complete literal principal generation supplies equality in the actual germ ring. -/
theorem ideal_span_eq_of_full_principal_generation {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z)
    {H : ComplexModel n → ℂ} (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z)
    (hfull : ∀ F : ComplexModel n → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range G) (0 : ComplexModel n) F ↔
        IsInSpanAt (n := n) (· = H) (0 : ComplexModel n) F) :
    Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {HolGerm.mk H hH} := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hGi : HolomorphicAt n (G i) 0 :=
      (hG i).mono fun _ hz => hz.mdifferentiableAt
    obtain ⟨_, a, ha, heq⟩ := isInSpanAt_eq_iff.mp
      ((hfull (G i)).mp (isInSpanAt_self ⟨i, rfl⟩ hGi))
    have hac : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ a z :=
      ha.mono fun _ hz => hz.differentiableAt
    have hmk : HolGerm.mk (G i) (hG i) = HolGerm.mk a hac * HolGerm.mk H hH := by
      calc
        HolGerm.mk (G i) (hG i) = HolGerm.mk (fun z => a z * H z)
            (eventually_differentiableAt_mul hac hH) := HolGerm.mk_eq_mk_iff.mpr heq
        _ = _ := HolGerm.mk_mul a H hac hH
    change HolGerm.mk (G i) (hG i) ∈ Ideal.span {HolGerm.mk H hH}
    rw [hmk]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    intro f hf
    have hfH : f = HolGerm.mk H hH := Set.mem_singleton_iff.mp hf
    subst f
    have hHm : HolomorphicAt n H 0 := hH.mono fun _ hz => hz.mdifferentiableAt
    exact (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span G hG hH).mp
      ((hfull H).mpr (isInSpanAt_self rfl hHm))

/-- The original full family, including additional individual zeros, has the genuine AE weight. -/
theorem exists_generatorLog_normal_form_of_full_principal_generation {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z)
    {H : ComplexModel n → ℂ} (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z)
    (hfull : ∀ F : ComplexModel n → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range G) (0 : ComplexModel n) F ↔
        IsInSpanAt (n := n) (· = H) (0 : ComplexModel n) F)
    (hHnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 0, H z = 0 → ∃ j : Fin n, z j = 0) :
    ∃ (a : Fin n → ℕ) (η : ComplexModel n → ℝ) (R : ℝ), 0 < R ∧
      (∀ z ∈ ball (0 : ComplexModel n) R, ContinuousAt η z) ∧
      generatorLog G =ᵐ[volume.restrict (ball 0 R)]
        (fun z => (∑ j : Fin n, ((2 * (a j : ℝ) : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal ‖z j‖)) + (η z : EReal)) :=
  PrincipalGeneratorLogNormNormalForm.exists_generatorLog_coordinate_ae_normal_form
    G hG hH hHnon (ideal_span_eq_of_full_principal_generation G hG hH hfull) hzero

end
end SGPT.Foundations.Analysis.Pending.PrincipalFiniteSpanLogNorm

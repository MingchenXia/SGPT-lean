import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGoodIso

/-! Whole literal graph density and genuine local denominator cancellation.
Blueprint: prime-nov16-analytic-normalization-graph-density.tex. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphDensity
open PrimeNov16AnalyticNormalizationDenominatorGraph

theorem denominator_nonzero_dense {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ) :
    Dense {z : graphClosure U C H G | H (baseProjection n k z.val.val) ≠ 0} := by
  apply Subtype.dense_iff.mpr
  apply closure_mono
  intro z hz
  refine ⟨⟨z,subset_closure hz⟩,?_,rfl⟩
  exact fun he => hz.2 ((mem_badSet U H z).mpr he)

theorem denominator_nonzero_dense_on_open {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (V : Opens (graphClosure U C H G)) :
    Dense {z : V | H (baseProjection n k z.val.val.val) ≠ 0} :=
  (denominator_nonzero_dense U C H G).preimage V.isOpen.isOpenMap_subtype_val

/-- Actual denominator cancellation on EVERY original open source subset. -/
theorem continuous_zero_of_denominator_mul_zero {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (V : Opens (graphClosure U C H G)) (f : V → ℂ) (hf : Continuous f)
    (hzero : ∀ z,H (baseProjection n k z.val.val.val) * f z = 0) :
    ∀ z,f z = 0 := by
  intro z
  apply closure_minimal (s := {z : V | H (baseProjection n k z.val.val.val) ≠ 0})
    (fun y hy => (mul_eq_zero.mp (hzero y)).resolve_left hy)
    (isClosed_eq hf continuous_const)
  exact denominator_nonzero_dense_on_open U C H G V z

theorem continuous_denominator_mul_injective {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (V : Opens (graphClosure U C H G)) (f g : V → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ z,H (baseProjection n k z.val.val.val) * f z =
      H (baseProjection n k z.val.val.val) * g z) : f = g := by
  funext z
  apply sub_eq_zero.mp
  exact continuous_zero_of_denominator_mul_zero U C H G V (f-g) (hf.sub hg)
    (fun y => by change _ * (f y-g y) = 0; rw [mul_sub,heq y,sub_self]) z

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphDensity

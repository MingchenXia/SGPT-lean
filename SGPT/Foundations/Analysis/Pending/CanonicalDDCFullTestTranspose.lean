import SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity
import SGPT.Foundations.Analysis.Pending.DDCOverlap
import SGPT.Foundations.Analysis.Pending.ScalarFullTestTranspose
import SGPT.Foundations.Analysis.Pending.FullLocalSmoothCurrentDensity

set_option autoImplicit false

/-! # Literal canonical geometric transposition on full form-span tests -/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.CanonicalDDCFullTestTranspose

open FirstPass FirstPass.MongeAmpere _root_.SGPT.Foundations.Analysis.LocalCurrents
  FirstPass.HolomorphicDDC StronglyPositiveForms TopDegreeDensity ConstantFormProducts
  DDCOverlap ScalarFullTestTranspose FullLocalSmoothCurrentDensity LocalCurrentLebesgue
  LocalProductCurrents

private def canonicalSplitFrame (m : ℕ) : Fin 2 ⊕ Fin (2 * m) → ComplexModel (m + 1) :=
  fun i => topBasis (m + 1) (Fin.cast (by omega : 2 + 2 * m = 2 * (m + 1))
    (finSumFinEquiv i))

private theorem coordinateWedgeSum_apply_shuffles {n p q : ℕ}
    (A : RealForm n p) (B : RealForm n q)
    (v : Fin p ⊕ Fin q → ComplexModel n) :
    coordinateWedgeSum A B v =
      ∑ s : Equiv.Perm.ModSumCongr (Fin p) (Fin q),
        ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (A (v ∘ s.out ∘ Sum.inl) * B (v ∘ s.out ∘ Sum.inr)) := by
  change (coordinateWedgeSum A B).toAlternatingMap v = _
  rw [coordinateWedgeSum_toAlternatingMap, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  conv_lhs => rw [← Quotient.out_eq s, AlternatingMap.domCoprod.summand_mk'']
  rcases Int.units_eq_one_or (Equiv.Perm.sign s.out) with hs | hs
  · rw [hs]
    simp [TensorProduct.lid_tmul, Function.comp_def]
  · rw [hs]
    simp [TensorProduct.lid_tmul, Function.comp_def]

private theorem ddcDensity_eq_topDensity {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (f : ComplexModel (m + 1) → ℝ) (α : TestForm U (2 * m))
    (hα : ∀ z, α z ∈ formSpan (m + 1) m) (x : ComplexModel (m + 1)) :
    ddcDensity (canonicalSplitFrame m) f α x =
      topDensity (coordinateWedge (α x) (smoothDDC f x)) := by
  change _ = topDensity (wedgeTo (rfl : 2 * m + 2 = 2 * (m + 1))
    (α x) (smoothDDC f x))
  rw [wedgeTo_comm_of_mem_formSpan (hα x) (smoothDDC f x) rfl
    (by omega : 2 + 2 * m = 2 * (m + 1))]
  unfold topDensity
  rw [wedgeTo, castForm_apply, coordinateWedge_apply, coordinateWedgeSum_apply_shuffles]
  rfl

/-- The actual geometric and finite scalar adjoints coincide on every full span test. -/
theorem ddcAdjoint_eq_scalarAdjointTest {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (α : TestForm U (2 * m)) (hα : ∀ z, α z ∈ formSpan (m + 1) m) :
    ddcAdjoint (fun i => topBasis (m + 1)
      (Fin.cast (by omega : 2 + 2 * m = 2 * (m + 1)) (finSumFinEquiv i))) α =
      scalarAdjointTest α := by
  change ddcAdjoint (canonicalSplitFrame m) α = _
  have hc₁ := (ddcAdjoint (canonicalSplitFrame m) α).continuous
  have hc₂ := (scalarAdjointTest α).continuous
  have heq : (ddcAdjoint (canonicalSplitFrame m) α : ComplexModel (m + 1) → ℝ) =
      scalarAdjointTest α := by
    apply (volume : Measure (ComplexModel (m + 1))).eq_of_ae_eq _ hc₁ hc₂
    refine ae_eq_of_integral_contDiff_smul_eq hc₁.locallyIntegrable hc₂.locallyIntegrable
      fun h hh _ => ?_
    simp only [smul_eq_mul]
    simp_rw [mul_comm (h _) _]
    rw [integral_ddcAdjoint_mul hh]
    simp_rw [ddcDensity_eq_topDensity h α hα]
    rw [← ddcWedge_oneCurrent_full_test_integral hh.contDiffOn α hα,
      local_smooth_scalar_full_test_integral hh.contDiffOn]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : scalarAdjointTest α x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx ((scalarAdjointTest α).tsupport_subset h))
    rw [hz, zero_mul]
  ext x
  exact congrFun heq x

/-- Arbitrary scalar distributions retain the literal canonical full-test pairing. -/
theorem wedgePairing_ddC_eq_scalar_full_test {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (T : 𝓓'(U, ℝ)) (α : TestForm U (2 * m))
    (hα : ∀ z, α z ∈ formSpan (m + 1) m) :
    wedgePairing (fun i => topBasis (m + 1)
      (Fin.cast (by omega : 2 + 2 * m = 2 * (m + 1)) (finSumFinEquiv i))) (ddC T) α =
      T (scalarAdjointTest α) ∧
    T (scalarAdjointTest α) =
      ∑ i, LocalBedfordTaylorProducts.ddc (ScalarLeviPositiveCurrent.scalarTopCurrent T)
        (LocalCurrentLebesgue.formBasis (m + 1) m i)
        (CompactVariableCurrentTests.coeffTest α i) := by
  constructor
  · rw [wedgePairing_ddC, ddcAdjoint_eq_scalarAdjointTest α hα]
  · exact (ddc_scalarTopCurrent_full_test_transpose T α).symm

end SGPT.Foundations.Analysis.Pending.CanonicalDDCFullTestTranspose

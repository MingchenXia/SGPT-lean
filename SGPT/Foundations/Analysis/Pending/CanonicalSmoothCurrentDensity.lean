import SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
import SGPT.Foundations.Analysis.Pending.ConstantFormProducts

set_option autoImplicit false

/-! # Full geometric smooth current tests in the actual complex-oriented density -/

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity

open FirstPass FirstPass.MongeAmpere _root_.SGPT.Foundations.Analysis.LocalCurrents StronglyPositiveForms
  TopDegreeDensity ConstantFormProducts CanonicalCurrentFrame GlobalCurrents

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

private theorem currentPairingBasis_canonical_apply {n : ℕ} (k : CurrentDegree n)
    (h : k.val + (Module.finrank ℝ (ComplexModel n) - k.val) = 2 * n)
    (i : Fin k.val ⊕ Fin (Module.finrank ℝ (ComplexModel n) - k.val)) :
    currentPairingBasis (canonicalBasis n) k i =
      topBasis n (Fin.cast h (finSumFinEquiv i)) := by
  simp only [currentPairingBasis, canonicalBasis, Module.Basis.reindex_apply,
    Equiv.symm_symm, Equiv.trans_apply, finCongr_apply, Fin.cast]
  exact congrArg (topBasis n) (Fin.ext rfl)

/-- Every pair of complementary-degree real forms retains its actual wedge density. -/
theorem shuffleDensity_eq_topDensity {n : ℕ} {k : CurrentDegree n}
    (A : RealForm n k.val) (B : RealForm n (Module.finrank ℝ (ComplexModel n) - k.val)) :
    (∑ s : Equiv.Perm.ModSumCongr (Fin k.val)
      (Fin (Module.finrank ℝ (ComplexModel n) - k.val)),
      ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
        (A (fun i => currentPairingBasis (canonicalBasis n) k (s.out (Sum.inl i))) *
          B (fun j => currentPairingBasis (canonicalBasis n) k (s.out (Sum.inr j))))) =
      topDensity (wedgeTo
        (by have hk := k.is_lt; rw [← complexModel_real_finrank n]; omega)
        A B) := by
  unfold topDensity
  rw [wedgeTo, castForm_apply, coordinateWedge_apply, coordinateWedgeSum_apply_shuffles]
  have h : k.val + (Module.finrank ℝ (ComplexModel n) - k.val) = 2 * n := by
    have hk := k.is_lt
    rw [← complexModel_real_finrank n]
    omega
  simp_rw [currentPairingBasis_canonical_apply k h]
  rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual smooth global current acts by the actual Euclidean wedge integral. -/
theorem smoothGlobalCurrent_apply_eq_integral_topDensity {k : CurrentDegree n}
    (a : SmoothRealForm n M k.val) (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)) :
    (smoothGlobalCurrent (canonicalBasis n) a).inChart e η =
      ∫ x, topDensity (wedgeTo
        (by have hk := k.is_lt; rw [← complexModel_real_finrank n]; omega)
        (a.coeff e x) (η x)) := by
  rw [smoothGlobalCurrent_inChart,
    smoothCurrentFamily_apply_eq_integral_smoothWedgeDensity, addHaar_canonicalBasis]
  apply integral_congr_ae
  filter_upwards [] with x
  exact shuffleDensity_eq_topDensity (a.coeff e x) (η x)

end SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity

import SGPT.Foundations.Analysis.Pending.CanonicalDDCFullTestTranspose

set_option autoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.CanonicalComplementaryCurrentTests

open FirstPass FirstPass.MongeAmpere _root_.SGPT.Foundations.Analysis.LocalCurrents
  StronglyPositiveForms TopDegreeDensity ConstantFormProducts CanonicalCurrentFrame
  CanonicalSmoothCurrentDensity


/-- Literal degree transport of the actual full compact test space. -/
def castTestDegree {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b)
    (α : TestForm U a) : TestForm U b := h ▸ α

private theorem castTestDegree_apply {n a b : ℕ} {U : Opens (ComplexModel n)}
    (h : a = b) (α : TestForm U a) (x : ComplexModel n) :
    castTestDegree h α x = castForm h (α x) := by
  subst b
  rfl

private theorem wedgePairing_castTestDegree {n p a b : ℕ} {U : Opens (ComplexModel n)}
    (h : a = b) (B : Fin p ⊕ Fin b → ComplexModel n) (A : DistributionForm U p)
    (α : TestForm U a) :
    wedgePairing B A (castTestDegree h α) =
      wedgePairing (B ∘ Sum.map id (Fin.cast h)) A α := by
  subst b
  have hb : B ∘ Sum.map id (Fin.cast (rfl : a = a)) = B := by
    funext i
    cases i <;> rfl
  rw [hb]
  rfl

private theorem wedgeTo_cast_right {n p a b c : ℕ} (h : a = b)
    (hab : p + b = c) (hac : p + a = c) (A : RealForm n p) (B : RealForm n a) :
    wedgeTo hab A (castForm h B) = wedgeTo hac A B := by
  subst b
  rfl

/-- Every full compact test retains the true canonical geometric wedge pairing. -/
theorem toLocalCurrent_castTestDegree {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (A : DistributionForm U 2) (α : TestForm U (2 * m)) :
    toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m)) A
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      wedgePairing (fun i => topBasis (m + 1)
        (Fin.cast (by omega : 2 + 2 * m = 2 * (m + 1)) (finSumFinEquiv i))) A α := by
  change wedgePairing (currentPairingBasis (canonicalBasis (m + 1))
    (degreeTwo (Nat.succ_pos m))) A (castTestDegree _ α) = _
  rw [wedgePairing_castTestDegree]
  apply congrArg (fun (B : Fin 2 ⊕ Fin (2 * m) → ComplexModel (m + 1)) =>
    wedgePairing B A α)
  funext i
  simp only [Function.comp_apply, currentPairingBasis, canonicalBasis,
    Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.trans_apply, finCongr_apply,
    Fin.cast]
  apply congrArg (topBasis (m + 1))
  apply Fin.ext
  cases i <;> rfl

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The literal complementary-degree transport keeps the actual full smooth wedge integral. -/
theorem smoothGlobalCurrent_castTestDegree_eq_integral
    (a : SmoothRealForm (m + 1) M 2) (e : ComplexChart (m + 1) M)
    (α : TestForm (chartTarget e) (2 * m)) :
    (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) a).inChart e
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      ∫ x, topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
        (a.coeff e x) (α x)) := by
  refine (smoothGlobalCurrent_apply_eq_integral_topDensity
    (k := degreeTwo (Nat.succ_pos m)) a e _).trans ?_
  apply integral_congr_ae
  filter_upwards [] with x
  apply congrArg topDensity
  rw [castTestDegree_apply]
  exact wedgeTo_cast_right _ _ _ _ _

end SGPT.Foundations.Analysis.Pending.CanonicalComplementaryCurrentTests

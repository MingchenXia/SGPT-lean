import SGPT.Projective.NativeDivisorFinitePrimeCurrent

/-! Finite prime span of the unchanged native Néron–Severi subspace. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace SGPT.Projective.BDivNov16
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  CurrentBottChernClass CanonicalCurrentFrame
open SGPT.BDivisor.DFAlg
variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]
local notation "Prime" => SGPT.PSH.GeometricPrimeCarrier (m + 1) M

theorem divisorCurrent_prime_val (P : Prime) :
    (divisorCurrent (SGPT.Siu.primeEffectiveDivisor P)).val =
      SGPT.Siu.primeDivisorCurrent P := by
  rw [divisorCurrent_val_eq _ _ (SGPT.Siu.isDivisorMetric_primeDivisorCurrent_metric P)]
  exact (SGPT.Siu.primeDivisorCurrent_eq_thetaPotentialCurrent P _
    (SGPT.Siu.isDivisorMetric_primeDivisorCurrent_metric P)).symm

theorem cycleClass_eq_finite_prime_sum (D : EffectiveDivisor (m + 1) M) :
    ∃ (F : Finset Prime) (c : Prime → ℝ),
      (∀ P ∈ F, P.val ⊆ D.support ∧ 0 ≤ c P) ∧
      cycleClass D = ∑ P ∈ F, c P • cycleClass (SGPT.Siu.primeEffectiveDivisor P) := by
  classical
  obtain ⟨F, c, hc, hsum⟩ :=
    SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI.nativeDivisorCurrent_eq_finite_prime_sum D
  refine ⟨F, c, hc, ?_⟩
  have hclosed : divisorCurrent D =
      ∑ P ∈ F, c P • divisorCurrent (SGPT.Siu.primeEffectiveDivisor P) := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, divisorCurrent_prime_val] using hsum
  have h := congrArg (bottChernClassLinearMap (M := M) (canonicalBasis (m + 1))
    (Nat.succ_pos m)) hclosed
  simp only [map_sum, map_smul] at h
  exact h

theorem neronSeveri_eq_span_primeCycleClass :
    neronSeveri (m + 1) M = Submodule.span ℝ
      (range fun P : Prime => cycleClass (SGPT.Siu.primeEffectiveDivisor P)) := by
  rw [neronSeveri_eq_span_cycleClass]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨D, rfl⟩
    obtain ⟨F, c, _, h⟩ := cycleClass_eq_finite_prime_sum D
    rw [h]
    exact Submodule.sum_mem _ fun P _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨P, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨P, rfl⟩
    exact Submodule.subset_span ⟨SGPT.Siu.primeEffectiveDivisor P, rfl⟩
end SGPT.Projective.BDivNov16

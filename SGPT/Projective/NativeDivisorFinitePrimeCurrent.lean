import SGPT.BDivisor.DFAlgNeronSeveri
import SGPT.BDivisor.BlowupModel2Divisor
import SGPT.Foundations.Analysis.Pending.CodimOneSupport
import SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient

/-! Actual finite prime decomposition of the unchanged native divisor integration current.
No supplied support/decomposition/positivity certificate and no new resolution construction. -/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  NaturalThetaPshGeometricCurrent CanonicalCurrentFrame
  SGPT.Currents.AnalyticSupport

section Support
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem nativeDivisor_support_analytic (D : EffectiveDivisor n M) :
    IsComplexAnalyticSubset (n := n) D.support :=
  CodimOneSupport.isComplexAnalyticSubset_zeroLocus
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)

omit [IsComplexManifold n M] in
theorem nativeDivisor_support_interior_empty (D : EffectiveDivisor n M) :
    interior D.support = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨U, hU, hyU, g, hg, hnon, hgen⟩ := D.isInvertible y
  obtain ⟨z, hz, hgz⟩ := hnon (interior D.support ∩ U)
    (isOpen_interior.inter hU) inter_subset_right ⟨y, hy, hyU⟩
  have hgh : HolomorphicAt n g z :=
    eventually_of_mem (hU.mem_nhds hz.2) fun w hw =>
      (hg w hw).mdifferentiableAt (hU.mem_nhds hw)
  have hmem := (hgen z hz.2 g).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hgh)
  exact hgz (interior_subset hz.1 g hmem)
end Support

section Current
variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]

local notation "Prime" => SGPT.PSH.GeometricPrimeCarrier (m + 1) M

theorem nativeDivisorCurrent_positive (D : EffectiveDivisor (m + 1) M) :
    SGPT.Siu.IsClosedPositiveCurrent (SGPT.BDivisor.DFAlg.divisorCurrent D).val := by
  obtain ⟨E, -, hE⟩ := DivisorMetric.exists_divisorMetric D
  rw [SGPT.BDivisor.DFAlg.divisorCurrent_val_eq D E hE]
  exact SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ _

theorem nativeDivisorCurrent_eq_finite_prime_sum (D : EffectiveDivisor (m + 1) M) :
    ∃ (F : Finset Prime) (c : Prime → ℝ),
      (∀ P ∈ F, P.val ⊆ D.support ∧ 0 ≤ c P) ∧
      (SGPT.BDivisor.DFAlg.divisorCurrent D).val =
        ∑ P ∈ F, c P • SGPT.Siu.primeDivisorCurrent P := by
  classical
  set T := (SGPT.BDivisor.DFAlg.divisorCurrent D).val
  have hT : SGPT.Siu.IsClosedPositiveCurrent T := nativeDivisorCurrent_positive D
  obtain ⟨E, hEs, hE⟩ := DivisorMetric.exists_divisorMetric D
  have h0 : CurrentEqOn T 0 D.supportᶜ := by
    dsimp only [T]
    rw [SGPT.BDivisor.DFAlg.divisorCurrent_val_eq D E hE,
      SGPT.BDivisor.PrimePushforward.thetaPotentialCurrent_eq_integrationCurrent]
    rw [← hEs]
    exact SGPT.BDivisor.PrimePushforward.currentEqOn_integrationCurrent_zero E
  obtain ⟨hTdiv, hToff⟩ := eq_siuDivisorialPart_of_currentEqOn_zero hT
    (nativeDivisor_support_analytic D) (nativeDivisor_support_interior_empty D) h0
  set F := (finite_setOf_prime_subset (nativeDivisor_support_analytic D)
    (nativeDivisor_support_interior_empty D)).toFinset with hFdef
  set c : Prime → ℝ := fun P => (SGPT.Siu.currentGenericLelong T hT P).toReal with hcdef
  refine ⟨F, c, fun P hP => ⟨?_, ENNReal.toReal_nonneg⟩, ?_⟩
  · rw [hFdef, Set.Finite.mem_toFinset] at hP
    exact hP
  refine hTdiv.trans ?_
  ext e η
  have h1 := SGPT.Siu.hasSum_siuDivisorialPart hT e η
  have h2 : HasSum (fun P : Prime =>
      ((SGPT.Siu.currentGenericLelong T hT P).toReal • SGPT.Siu.primeDivisorCurrent P).inChart e η)
      (∑ P ∈ F, ((SGPT.Siu.currentGenericLelong T hT P).toReal •
        SGPT.Siu.primeDivisorCurrent P).inChart e η) := by
    apply hasSum_sum_of_ne_finset_zero
    intro P hP
    have hc0 : SGPT.Siu.currentGenericLelong T hT P = 0 := by
      apply hToff P
      intro hPD
      exact hP (by rw [hFdef, Set.Finite.mem_toFinset]; exact hPD)
    rw [hc0, ENNReal.toReal_zero, zero_smul]
    rfl
  rw [h1.unique h2, SGPT.Siu.inChart_finsetSum]
end Current
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

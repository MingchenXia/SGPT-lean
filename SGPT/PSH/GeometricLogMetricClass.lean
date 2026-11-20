import SGPT.PSH.RationalMetricDivisorClass
import SGPT.PSH.ZeroLogMetricDictionary

/-! Actual original divisor/log/metric/class dictionary in EVERY natural
dimension, with no connectedness, nonempty or supplied output certificates. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ResidualNefReduction
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- ORIGINAL compact D,u and complete source log fields internally construct
an actual metric representative of the FIXED original prime-current divisor
class and a genuinely bounded real residual, in ALL natural dimensions. -/
theorem compact_exists_actual_log_metric_class_dictionary
    (D : EffectiveGeometricQDivisor n M) (u : M → EReal)
    (hu : NativeHasLogSingularitiesAlongAnyDimension D u) :
    ∃ E : MeteredEffectiveQDivisor n M,
      E.support=D.support ∧
      compact_geometric_divisor_class D=RealBottChern.ofRepresentative E.curvature ∧
      HasLocalDivisorLogType E u ∧ Nonempty (HasLogSingularitiesAlong E u) := by
  cases n with
  | zero =>
    have hlocal := native_zero_log_metric_local_type hu
    refine ⟨MeteredDivisorOperations.zero 0 M,?_,?_,hlocal,hlocal.exists_bounded_divisorResidual⟩
    · rw [MeteredDivisorOperations.zero_support]
      simp only [EffectiveGeometricQDivisor.support,iUnion_of_empty]
    · change (∑ P∈compact_positive_prime_finset D,
        (D.coefficient P : ℝ) • SGPT.Hodge.BDivChain.SourceAugmentedDraft.primeDivisorClassAny P)=
        RealBottChern.ofRepresentative 0
      rw [RealBottChern.ofRepresentative_zero]
      exact Finset.sum_eq_zero (fun P _ => isEmptyElim P)
  | succ m =>
    obtain ⟨d,F,EH,hd,hD,hEH,hsupport,hlocal,hresidual⟩ :=
      compact_exists_actual_metered_log_dictionary D u hu
    have hcoeff (P : GeometricPrimeCarrier (m+1) M) :
        D.coefficient P=(cartierGeometricPrimeCoefficient F P : ℚ)/(d : ℚ) := by
      rw [hD,cartierGeometricQDivisor_coefficient]
      ring
    exact ⟨_,hsupport,actual_rational_metric_class D F d hd hcoeff EH hEH,hlocal,hresidual⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft

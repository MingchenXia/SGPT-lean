import SGPT.PSH.CartierMetricPrimeCurrentClass

/-! The genuine produced rational metric represents the fixed ORIGINAL
prime integration-current divisor class, with all coefficients retained. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Hodge.BDivChain.SourceAugmentedDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

/-- An actual genuine Cartier metric and the proved ORIGINAL coefficient
identity determine the fixed standard divisor class; no target class
certificate, finite index family or metric normalization is a premise. -/
theorem actual_rational_metric_class
    (D : EffectiveGeometricQDivisor (m+1) M)
    (F : EffectiveDivisor (m+1) M) (d : ℕ) (hd : 0<d)
    (hcoeff : ∀ P,D.coefficient P=(cartierGeometricPrimeCoefficient F P : ℚ)/(d : ℚ))
    (EH : MeteredEffectiveQDivisor (m+1) M) (hEH : DivisorMetric.IsDivisorMetric F EH) :
    compact_geometric_divisor_class D=RealBottChern.ofRepresentative
      (MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH).curvature := by
  let s := compact_positive_prime_finset (cartierGeometricQDivisor F 1 (by norm_num))
  have hclass : RealBottChern.ofRepresentative
      (MeteredDivisorScaling.smul (show (0 : ℚ)≤1/(d : ℚ) from by positivity) EH).curvature=
      ∑ P∈s,(D.coefficient P : ℝ) • primeDivisorClassAny P := by
    rw [MeteredDivisorScaling.curvature_smul,RealBottChern.ofRepresentative_smul,
      actual_cartier_metric_class_finite_sum F EH hEH,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro P _
    rw [smul_smul,hcoeff P]
    congr 1
    push_cast
    ring
  apply compact_geometric_divisor_class_eq_of_hasSum D
  let := SGPT.BDivisor.euclideanTopology (RealBottChern (m+1) M)
  change HasSum (fun P => (D.coefficient P : ℝ) • primeDivisorClassAny P) _
  rw [hclass]
  apply hasSum_sum_of_ne_finset_zero
  intro P hP
  have hzero : cartierGeometricPrimeCoefficient F P=0 := by
    by_contra hne
    have hpos : 0<(cartierGeometricQDivisor F 1 (by norm_num)).coefficient P := by
      change 0<(1 : ℚ)*(cartierGeometricPrimeCoefficient F P : ℚ)
      exact mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne))
    exact hP ((mem_compact_positive_prime_finset _ P).mpr hpos)
  simp only [hcoeff P,hzero,Nat.cast_zero,zero_div,Rat.cast_zero,zero_smul]

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft

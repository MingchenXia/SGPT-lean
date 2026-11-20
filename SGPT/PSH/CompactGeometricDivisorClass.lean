import SGPT.PSH.GeometricDivisorMetricAlgebra
import SGPT.Hodge.SourceAugmentedCurrentObjects

/-! The standard compact geometric Q divisor class is the actual finite
sum of EXISTING original prime integration-current classes in every dimension. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Hodge.BDivChain.SourceAugmentedDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Every ACTUAL positive original prime carrier is in a finite produced
set, from actual compact local finiteness; no index catalog is a premise. -/
theorem compact_positive_prime_carriers_finite (D : EffectiveGeometricQDivisor n M) :
    {P : GeometricPrimeCarrier n M | 0<D.coefficient P}.Finite := by
  have h := (compact_positive_prime_finite D).image
    (Subtype.val : {P // 0<D.coefficient P} → GeometricPrimeCarrier n M)
  exact h.subset (fun P hP => ⟨⟨P,hP⟩,mem_univ _,rfl⟩)

/-- Only the internally produced exact finite set of positive ORIGINAL
coefficients, including an actual empty prime type in dimension zero. -/
def compact_positive_prime_finset (D : EffectiveGeometricQDivisor n M) :
    Finset (GeometricPrimeCarrier n M) := (compact_positive_prime_carriers_finite D).toFinset

/-- Exact membership of the SAME original positive coefficient set. -/
theorem mem_compact_positive_prime_finset (D : EffectiveGeometricQDivisor n M)
    (P : GeometricPrimeCarrier n M) : P∈compact_positive_prime_finset D ↔ 0<D.coefficient P :=
  Set.Finite.mem_toFinset _

/-- The ORIGINAL divisor cohomology class is its actual finite coefficient
sum of EXISTING standard prime integration-current classes, not a supplied
curvature representative or newly assumed class certificate. -/
def compact_geometric_divisor_class (D : EffectiveGeometricQDivisor n M) : RealBottChern n M :=
  ∑ P∈compact_positive_prime_finset D,(D.coefficient P : ℝ) • primeDivisorClassAny P

/-- The actual EXISTING unconditional divisor-class sum relation holds for
EVERY original coefficient, including ALL zeros outside the produced finite set. -/
theorem hasSum_compact_geometric_divisor_class (D : EffectiveGeometricQDivisor n M) :
    HasDivisorClassSumAny (fun P => (D.coefficient P : ℝ)) (compact_geometric_divisor_class D) := by
  let := SGPT.BDivisor.euclideanTopology (RealBottChern n M)
  change HasSum (fun P => (D.coefficient P : ℝ) • primeDivisorClassAny P)
    (∑ P∈compact_positive_prime_finset D,(D.coefficient P : ℝ) • primeDivisorClassAny P)
  apply hasSum_sum_of_ne_finset_zero
  intro P hP
  have hzero : D.coefficient P=0 := by
    apply le_antisymm _ (D.coefficient_nonneg P)
    exact le_of_not_gt (fun h => hP ((mem_compact_positive_prime_finset D P).mpr h))
  simp only [hzero,Rat.cast_zero,zero_smul]

/-- Standard original divisor-class sums are unique in the existing actual
Euclidean topology. Any later curvature identification must prove that same
ORIGINAL coefficient sum, rather than posit the desired class as a premise. -/
theorem compact_geometric_divisor_class_eq_of_hasSum (D : EffectiveGeometricQDivisor n M)
    {α : RealBottChern n M} (hα : HasDivisorClassSumAny (fun P => (D.coefficient P : ℝ)) α) :
    compact_geometric_divisor_class D=α := by
  let := SGPT.BDivisor.euclideanTopology (RealBottChern n M)
  have := SGPT.BDivisor.t2Space_euclideanTopology (RealBottChern n M)
  exact HasSum.unique (hasSum_compact_geometric_divisor_class D) hα

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft

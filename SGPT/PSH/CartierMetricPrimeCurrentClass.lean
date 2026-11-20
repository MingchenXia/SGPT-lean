import SGPT.PSH.CompactGeometricDivisorClass
import SGPT.Siu.PrimeDivisorCurrent

/-! Actual whole-current metric independence and unit-prime normalization
identify the SAME Cartier metric class with the standard prime-current sum. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open CurrentBottChernClass CanonicalCurrentFrame ThetaPotentialCurrentBottChernClass
open SGPT.Hodge.BDivChain.SourceAugmentedDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

/-- Full Cartier coefficients on an actual finite support reconstruct the
ENTIRE original Cartier divisor, by genuine all-prime ideal faithfulness. -/
theorem cartier_eq_finite_prime_sum (F : EffectiveDivisor (m+1) M)
    (s : Finset (GeometricPrimeCarrier (m+1) M))
    (hzero : ∀ P,P∉s → cartierGeometricPrimeCoefficient F P=0) :
    F=∑ P∈s,cartierGeometricPrimeCoefficient F P • geometricPrimeCarrierEffectiveDivisor P := by
  apply cartier_eq_of_geometricPrimeCoefficient_eq
  intro Q
  rw [cartierGeometricPrimeCoefficient_finset_sum]
  symm
  calc
    _ = cartierGeometricPrimeCoefficient F Q *
        cartierGeometricPrimeCoefficient (geometricPrimeCarrierEffectiveDivisor Q) Q := by
      apply Finset.sum_eq_single Q
      · intro P _ hPQ
        rw [cartierGeometricPrimeCoefficient_reduced,if_neg (Ne.symm hPQ),mul_zero]
      · intro hQ
        rw [hzero Q hQ,zero_mul]
    _ = _ := by rw [cartierGeometricPrimeCoefficient_reduced,if_pos rfl,mul_one]

variable [CompactSpace M]

/-- Whole-current metric independence gives equality of the ACTUAL
Bott--Chern curvature classes of two genuine metrics on SAME Cartier F. -/
theorem actual_cartier_metric_class_independent (F : EffectiveDivisor (m+1) M)
    (E E' : MeteredEffectiveQDivisor (m+1) M)
    (hE : DivisorMetric.IsDivisorMetric F E) (hE' : DivisorMetric.IsDivisorMetric F E') :
    RealBottChern.ofRepresentative E.curvature=RealBottChern.ofRepresentative E'.curvature := by
  let hθ := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric F E hE
  let hθ' := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric F E' hE'
  have hcur := (SGPT.Okounkov.thetaPotentialCurrent_effectiveDivisorMetric_eq F E hE).trans
    ((ActualDivisorCurrentMetricIndependence.integrationCurrent_eq_of_isDivisorMetric
      (canonicalBasis (m+1)) F E E' hE hE').trans
      (SGPT.Okounkov.thetaPotentialCurrent_effectiveDivisorMetric_eq F E' hE').symm)
  have hclosed : thetaClosedCurrent E.curvature E.weight hθ=
      thetaClosedCurrent E'.curvature E'.weight hθ' := Subtype.ext hcur
  rw [←bottChernClass_thetaClosedCurrent E.curvature E.weight hθ,
    ←bottChernClass_thetaClosedCurrent E'.curvature E'.weight hθ',hclosed]

/-- The SAME actual unit prime metric used by the standard prime current. -/
def actualPrimeMetric (P : GeometricPrimeCarrier (m+1) M) : MeteredEffectiveQDivisor (m+1) M :=
  Classical.choose (DivisorMetric.exists_divisorMetric (geometricPrimeCarrierEffectiveDivisor P))

/-- Its full original Cartier metric property is internally produced. -/
theorem actualPrimeMetric_spec (P : GeometricPrimeCarrier (m+1) M) :
    DivisorMetric.IsDivisorMetric (geometricPrimeCarrierEffectiveDivisor P) (actualPrimeMetric P) :=
  SGPT.Siu.isDivisorMetric_primeDivisorCurrent_metric P

/-- ACTUAL original prime integration-current normalization identifies the
standard prime class with the curvature of SAME genuine unit prime metric. -/
theorem actualPrimeMetric_class (P : GeometricPrimeCarrier (m+1) M) :
    primeDivisorClassAny P=RealBottChern.ofRepresentative (actualPrimeMetric P).curvature := by
  change SGPT.BDivisor.primeDivisorClass P=RealBottChern.ofRepresentative (actualPrimeMetric P).curvature
  let hp := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric
    (geometricPrimeCarrierEffectiveDivisor P) (actualPrimeMetric P) (actualPrimeMetric_spec P)
  have hcur := SGPT.Siu.primeDivisorCurrent_eq_thetaPotentialCurrent P
    (actualPrimeMetric P) (actualPrimeMetric_spec P)
  have hclosed : (SGPT.Siu.primeDivisorBookCurrent P).val=
      thetaClosedCurrent (actualPrimeMetric P).curvature (actualPrimeMetric P).weight hp := Subtype.ext hcur
  rw [SGPT.BDivisor.primeDivisorClass,SGPT.PSH.BookCurrent.currentClass,hclosed,
    bottChernClass_thetaClosedCurrent]

/-- ANY actual metric on an original compact Cartier divisor has its TRUE
standard finite prime-current cohomology sum, with all coefficients produced
from the genuine Cartier divisor and no supplied class certificate. -/
theorem actual_cartier_metric_class_finite_sum (F : EffectiveDivisor (m+1) M)
    (E : MeteredEffectiveQDivisor (m+1) M) (hE : DivisorMetric.IsDivisorMetric F E) :
    RealBottChern.ofRepresentative E.curvature=
      ∑ P∈compact_positive_prime_finset (cartierGeometricQDivisor F 1 (by norm_num)),
        (cartierGeometricPrimeCoefficient F P : ℝ) • primeDivisorClassAny P := by
  let D := cartierGeometricQDivisor F 1 (by norm_num)
  let s := compact_positive_prime_finset D
  have hzero (P : GeometricPrimeCarrier (m+1) M) (hP : P∉s) : cartierGeometricPrimeCoefficient F P=0 := by
    by_contra hne
    have hpos : 0<cartierGeometricPrimeCoefficient F P := Nat.pos_of_ne_zero hne
    have hDP : 0<D.coefficient P := by
      change 0<(1 : ℚ)*(cartierGeometricPrimeCoefficient F P : ℚ)
      positivity
    exact hP ((mem_compact_positive_prime_finset D P).mpr hDP)
  have hF := cartier_eq_finite_prime_sum F s hzero
  obtain ⟨H,hH,hcurv⟩ := exists_actual_metric_finite_cartier_sum s
    (fun P => geometricPrimeCarrierEffectiveDivisor P) actualPrimeMetric
    (fun P _ => actualPrimeMetric_spec P) (fun P => cartierGeometricPrimeCoefficient F P)
  have hHF : DivisorMetric.IsDivisorMetric F H := hF.symm ▸ hH
  calc
    RealBottChern.ofRepresentative E.curvature=RealBottChern.ofRepresentative H.curvature :=
      actual_cartier_metric_class_independent F E H hE hHF
    _ = _ := by
      rw [hcurv]
      change RealBottChern.ofRepresentativeLinearMap
        (∑ P∈s,(cartierGeometricPrimeCoefficient F P : ℝ) • (actualPrimeMetric P).curvature)=_
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro P _
      rw [map_smul]
      change (cartierGeometricPrimeCoefficient F P : ℝ) • RealBottChern.ofRepresentative (actualPrimeMetric P).curvature=_
      rw [←actualPrimeMetric_class]

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft

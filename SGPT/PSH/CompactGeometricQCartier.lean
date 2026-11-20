import SGPT.PSH.SourceOriginalLogModification
import SGPT.PSH.CanonicalCartierAdditivity
import Mathlib.Topology.Compactness.LocallyFinite

/-! Compact ORIGINAL rational divisors internally give a genuine GLOBAL
integral Cartier representative, with every coefficient proved including0. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The original positive prime index is genuinely finite by actual local
finiteness and compactness; no finite index catalog is an input. -/
theorem compact_positive_prime_finite (D : EffectiveGeometricQDivisor n M) :
    (Set.univ : Set {P // 0<D.coefficient P}).Finite :=
  D.locallyFinite_positive.finite_of_compact (fun P => P.val.nonempty)

/-- ORIGINAL compact D ALONE produces one positive GLOBAL denominator and
an ACTUAL integral Cartier divisor with EVERY rational coefficient of SAME
D, including zero. The real zero-dimensional prime type is empty. -/
theorem compact_exists_global_integral_cartier
    (D : EffectiveGeometricQDivisor n M) :
    ∃ (d : ℕ) (F : EffectiveDivisor n M),0<d ∧
      ∀ P : GeometricPrimeCarrier n M,
        D.coefficient P=(nativeCartierCoefficientAny F P : ℚ)/(d : ℚ) := by
  cases n with
  | zero => exact ⟨1,0,by norm_num,fun P => isEmptyElim P⟩
  | succ m =>
    let I := {P // 0<D.coefficient P}
    let : Fintype I := D.locallyFinite_positive.fintypeOfCompact (fun P => P.val.nonempty)
    let s : Finset I := Finset.univ
    obtain ⟨d,a,hd,ha⟩ := exists_finite_positive_rational_denominator s
      (fun P : I => D.coefficient P.val) (fun P _ => P.property)
    let F := ∑ P∈s,a P • geometricPrimeCarrierEffectiveDivisor P.val
    refine ⟨d,F,hd,?_⟩
    intro Q
    change D.coefficient Q=(cartierGeometricPrimeCoefficient F Q : ℚ)/(d : ℚ)
    rw [show cartierGeometricPrimeCoefficient F Q=
      ∑ P∈s,a P * cartierGeometricPrimeCoefficient (geometricPrimeCarrierEffectiveDivisor P.val) Q from
        cartierGeometricPrimeCoefficient_finset_sum s
          (fun P : I => geometricPrimeCarrierEffectiveDivisor P.val) a Q]
    by_cases hpos : 0<D.coefficient Q
    · let QQ : I := ⟨Q,hpos⟩
      have hQQ : QQ∈s := Finset.mem_univ _
      have hsum : (∑ P∈s,a P * cartierGeometricPrimeCoefficient
          (geometricPrimeCarrierEffectiveDivisor P.val) Q)=a QQ := by
        calc
          _ = a QQ * cartierGeometricPrimeCoefficient (geometricPrimeCarrierEffectiveDivisor QQ.val) Q := by
            apply Finset.sum_eq_single QQ
            · intro P _ hne
              have hQP : Q≠P.val := fun h => hne (Subtype.ext h.symm)
              rw [cartierGeometricPrimeCoefficient_reduced,if_neg hQP,mul_zero]
            · intro hnot
              exact False.elim (hnot hQQ)
          _ = a QQ := by rw [cartierGeometricPrimeCoefficient_reduced,if_pos rfl,mul_one]
      rw [hsum]
      exact (ha QQ hQQ).2
    · have hzero : D.coefficient Q=0 := le_antisymm (le_of_not_gt hpos) (D.coefficient_nonneg Q)
      have hsum : (∑ P∈s,a P * cartierGeometricPrimeCoefficient
          (geometricPrimeCarrierEffectiveDivisor P.val) Q)=0 := by
        apply Finset.sum_eq_zero
        intro P _
        have hQP : Q≠P.val := by
          intro h
          have hp := P.property
          rw [←h,hzero] at hp
          exact (lt_irrefl (0 : ℚ)) hp
        rw [cartierGeometricPrimeCoefficient_reduced,if_neg hQP,mul_zero]
      rw [hsum,Nat.cast_zero,zero_div]
      exact hzero

end SGPT.PSH.VariableComplexAtlas.SourceLogResidualDraft

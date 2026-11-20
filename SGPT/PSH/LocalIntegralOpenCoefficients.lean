import SGPT.PSH.FiniteGroupedCartierCoefficients

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending HironakaEffectiveDivisorSum
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual open restriction preserves finite Cartier arithmetic by the
existing FULL coherent-product/unit ideal-image theorems. -/
def cartierOpenRestrictionHom (U : Opens M) : EffectiveDivisor n M →+ EffectiveDivisor n U where
  toFun := fun D => cartierOpenRestriction D U
  map_zero' := by
    apply effectiveDivisor_eq_of_ideal_eq
    exact BlowupExceptionalDivisor.pullback_unitIdeal
  map_add' D E := by
    apply effectiveDivisor_eq_of_ideal_eq
    exact GermIdealTotalTransform.pullback_mul (OpensRestriction.contMDiff_val U)
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
      (DivisorMetric.isCoherent_of_isInvertible E.isInvertible)

theorem cartierOpenRestriction_finset_sum {ι : Type*} (U : Opens M) (s : Finset ι)
    (E : ι → EffectiveDivisor n M) (a : ι → ℕ) :
    cartierOpenRestriction (∑ i ∈ s, a i • E i) U =
      ∑ i ∈ s, a i • cartierOpenRestriction (E i) U := by
  change (cartierOpenRestrictionHom U) (∑ i ∈ s, a i • E i) = _
  simp only [map_sum, map_nsmul]
  rfl

section Rational
variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- ORIGINAL D,x ALONE retain ONE exact original finite family/local
denominator whose genuine integral Cartier restriction reads coefficients on
EVERY original open and every canonical prime meeting the original neighborhood. -/
theorem exists_geometric_q_local_integral_open_coefficients
    (D : EffectiveGeometricQDivisor (m + 1) X) (x : X) :
    ∃ V : Opens X, x ∈ V ∧
      ∃ (s : Finset {P // 0 < D.coefficient P}) (d : ℕ)
        (a : {P // 0 < D.coefficient P} → ℕ),
        (∀ P, P ∈ s ↔ (P.val.val ∩ (V : Set X)).Nonempty) ∧ 0 < d ∧
        (∀ P ∈ s, 0 < a P ∧ D.coefficient P.val = (a P : ℚ) / (d : ℚ)) ∧
        let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
        ∀ (U : Opens X) (A : GeometricPrimeCarrier (m + 1) U),
          (A.val ∩ (Subtype.val : U → X) ⁻¹' (V : Set X)).Nonempty →
          (geometricQDivisorOpenRestriction D U).coefficient A =
            (cartierGeometricPrimeCoefficient (cartierOpenRestriction F U) A : ℚ) / (d : ℚ) := by
  obtain ⟨V, hxV, s, d, a, _g, hs, hd, ha, _hgens, _hrest⟩ :=
    exists_geometric_q_local_integral_cartier_presentation D x
  refine ⟨V, hxV, s, d, a, hs, hd, ha, ?_⟩
  dsimp only
  intro U A hA
  rw [geometricQDivisorOpenRestriction_local_coefficient D U V s hs A hA,
    cartierOpenRestriction_finset_sum, cartierGeometricPrimeCoefficient_finset_sum,
    Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro P hP
  rw [(ha P hP).2, Nat.cast_mul]
  ring

end Rational
end SGPT.PSH

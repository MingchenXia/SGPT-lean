import SGPT.PSH.GeometricQOpenCartierCompatibility
import SGPT.PSH.FiniteCartierPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

universe u
variable {m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X}

/-- ORIGINAL D,x and actual modification ALONE retain SAME V/S/local d/a/F
and genuine H=π*F, with both the global grouped coefficient reader and
EVERY open-prime coefficient reader. No local compatibility is supplied. -/
theorem exists_geometric_q_local_integral_pullback_open_coefficients
    (D : EffectiveGeometricQDivisor (m + 1) X) (x : X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    ∃ V : Opens X, x ∈ V ∧
      ∃ (s : Finset {P // 0 < D.coefficient P}) (d : ℕ)
        (a : {P // 0 < D.coefficient P} → ℕ),
        (∀ P, P ∈ s ↔ (P.val.val ∩ (V : Set X)).Nonempty) ∧ 0 < d ∧
        (∀ P ∈ s, 0 < a P ∧ D.coefficient P.val = (a P : ℚ) / (d : ℚ)) ∧
        let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
        let H := ∑ P ∈ s, a P • geometricPrimeCarrierTotalTransform P.val hπ
        cartierModificationPullback hπ F = H ∧
        (∀ A : GeometricPrimeCarrier (m + 1) Y,
          (A.val ∩ π ⁻¹' (V : Set X)).Nonempty →
          (geometricQDivisorModificationPullback D hπ).coefficient A =
            (cartierGeometricPrimeCoefficient H A : ℚ) / (d : ℚ)) ∧
        ∀ (U : Opens Y) (B : GeometricPrimeCarrier (m + 1) U),
          (B.val ∩ (Subtype.val : U → Y) ⁻¹' (π ⁻¹' (V : Set X))).Nonempty →
          (geometricQDivisorOpenRestriction (geometricQDivisorModificationPullback D hπ) U).coefficient B =
            (cartierGeometricPrimeCoefficient (cartierOpenRestriction H U) B : ℚ) / (d : ℚ) := by
  obtain ⟨V, hxV, s, d, a, hs, hd, ha, hglobal⟩ :=
    exists_geometric_q_local_integral_pullback_coefficients D x hπ
  let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
  let H := ∑ P ∈ s, a P • geometricPrimeCarrierTotalTransform P.val hπ
  refine ⟨V, hxV, s, d, a, hs, hd, ha,
    cartierModificationPullback_finite_prime_sum hπ s (fun P => P.val) a, hglobal, ?_⟩
  intro U B hB
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  calc
    _ = (1 / (d : ℚ)) *
        (cartierGeometricPrimeCoefficient (cartierOpenRestriction H U) B : ℚ) := by
      apply geometricQDivisorOpenRestriction_coefficient_of_local_cartier_coefficients
        (geometricQDivisorModificationPullback D hπ) H (1 / (d : ℚ)) (by positivity)
        (π ⁻¹' (V : Set X)) _ U B hB
      intro A hA
      rw [hglobal A hA]
      ring
    _ = _ := by ring

end SGPT.PSH

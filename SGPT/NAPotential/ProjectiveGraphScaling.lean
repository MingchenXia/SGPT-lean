import SGPT.NAPotential.ProjectiveGraphRelationCore

/-!
# Nonzero original field scaling preserves every homogeneous graph relation

Blueprint: `projective-graph-centred-charts.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphScaling

open MvPolynomial ProjectiveGraphRelations ProjectiveGraphRelationCore
attribute [local instance] MvPolynomial.gradedAlgebra

variable {I A K : Type*} [CommRing A] [Field K] [Algebra A K]

theorem aeval_scale_eq_zero_iff (v : I → K) {t : K} (ht : t ≠ 0)
    {p : MvPolynomial I A} {n : ℕ} (hp : p.IsHomogeneous n) :
    aeval (fun i => t * v i) p = 0 ↔ aeval v p = 0 := by
  simp only [aeval_eq_eval₂Hom]
  rw [eval₂Hom_scale_of_isHomogeneous hp, mul_eq_zero, or_iff_right (pow_ne_zero n ht)]

/-- The full original homogeneous relation ideal is exactly invariant under actual nonzero field scaling. -/
theorem relationCore_scale (v : I → K) {t : K} (ht : t ≠ 0) :
    relationCore (A := A) (fun i => t * v i) = relationCore (A := A) v := by
  apply HomogeneousIdeal.ext
  apply le_antisymm
  · change Ideal.span _ ≤ _
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨p, ⟨n, hn⟩⟩, hp, rfl⟩
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, hn⟩
    exact (aeval_scale_eq_zero_iff v ht hn).mp hp
  · change Ideal.span _ ≤ _
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨p, ⟨n, hn⟩⟩, hp, rfl⟩
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, hn⟩
    exact (aeval_scale_eq_zero_iff v ht hn).mpr hp

/-- Normalize at any actual nonzero coordinate, retaining the original vector's projective class. -/
def normalizeAt (v : I → K) (p : I) : I → K := fun i => (v p)⁻¹ * v i

theorem normalizeAt_self (v : I → K) (p : I) (hp : v p ≠ 0) : normalizeAt v p p = 1 :=
  inv_mul_cancel₀ hp

theorem relationCore_normalizeAt (v : I → K) (p : I) (hp : v p ≠ 0) :
    relationCore (A := A) (normalizeAt v p) = relationCore (A := A) v :=
  relationCore_scale v (inv_ne_zero hp)

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphScaling

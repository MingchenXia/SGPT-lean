import SGPT.Toric.ToricStratumNormalizedVolume

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Pointwise Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Literal original divisor coefficients for the genuine integral
perturbation. This is independent of every potential and target face. -/
theorem toricDivisor_nsmul_add_coeff (D E : ToricDivisor γ hs) (N : ℕ)
    (ρ : PolytopeToricRays γ hs) :
    ((N • D + E) ρ : ℝ) = (N : ℝ) * (D ρ : ℝ) + (E ρ : ℝ) := by
  change ((N • D ρ + E ρ : ℤ) : ℝ) = _
  simp

/-- Nonnegative ORIGINAL supporting slacks force equality in each summand.
Thus the literal selected face of N*A+B is exactly the sum of the literal
selected faces, even when the original divisor is not nef or a face is empty. -/
theorem toricDivisorFace_inter_nsmul_add
    (D E : ToricDivisor γ hs) (R : Set (PolytopeToricRays γ hs))
    (N : ℕ) (hN : 0 < N)
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : A ⊆ toricDivisorPolytope D) (hB : B ⊆ toricDivisorPolytope E) :
    ((N : ℝ) • A + B) ∩ toricDivisorFace (N • D + E) R =
      (N : ℝ) • (A ∩ toricDivisorFace D R) + (B ∩ toricDivisorFace E R) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  ext x
  constructor
  · rintro ⟨⟨p,⟨a,ha,rfl⟩,b,hb,rfl⟩,hface⟩
    have hzero (ρ : PolytopeToricRays γ hs) (hρ : ρ ∈ R) :
        latticeFunctional ρ.val a = -(D ρ : ℝ) ∧
          latticeFunctional ρ.val b = -(E ρ : ℝ) := by
      have hDa := hA ha ρ
      have hEb := hB hb ρ
      have hz := hface.2 ρ hρ
      rw [map_add, map_smul, smul_eq_mul, toricDivisor_nsmul_add_coeff] at hz
      have hslack : (N : ℝ) * (latticeFunctional ρ.val a + (D ρ : ℝ)) = 0 := by
        nlinarith
      constructor
      · have := (mul_eq_zero.mp hslack).resolve_left hNR.ne'
        linarith
      · nlinarith
    refine ⟨(N : ℝ) • a,⟨a,⟨ha,hA ha,fun ρ hρ => (hzero ρ hρ).1⟩,rfl⟩,
      b,⟨hb,hB hb,fun ρ hρ => (hzero ρ hρ).2⟩,rfl⟩
  · rintro ⟨p,⟨a,⟨ha,hfa⟩,rfl⟩,b,⟨hb,hfb⟩,rfl⟩
    refine ⟨⟨(N : ℝ) • a,⟨a,ha,rfl⟩,b,hb,rfl⟩,?_,?_⟩
    · intro ρ
      have hDa := hfa.1 ρ
      have hEb := hfb.1 ρ
      rw [map_add, map_smul, smul_eq_mul, toricDivisor_nsmul_add_coeff]
      nlinarith
    · intro ρ hρ
      rw [map_add, map_smul, smul_eq_mul, hfa.2 ρ hρ, hfb.2 ρ hρ,
        toricDivisor_nsmul_add_coeff]
      ring

/-- The actual original Cartier datum of the integral perturbation is the
literal sum N*m_sigma+m_sigma^H, proved from ORIGINAL integral ray equations. -/
theorem isToricCartierDatumAlong_nsmul_add
    {D E : ToricDivisor γ hs} {R : Set (PolytopeToricRays γ hs)}
    {mσ mH : Fin n → ℤ}
    (hσ : IsToricCartierDatumAlong D R mσ) (hH : IsToricCartierDatumAlong E R mH)
    (N : ℕ) : IsToricCartierDatumAlong (N • D + E) R (N • mσ + mH) := by
  intro ρ hρ
  rw [intPairing_add]
  have hpair : intPairing (N • mσ) ρ.val = (N : ℤ) * intPairing mσ ρ.val := by
    simpa only [Nat.cast_smul_eq_nsmul] using intPairing_smul (N : ℤ) mσ ρ.val
  rw [hpair,hσ ρ hρ,hH ρ hρ]
  change _ = -(N • D ρ + E ρ)
  simp [add_comm]

/-- Literal embedding of the genuine integral perturbation character. -/
theorem latticeVector_nsmul_add (mσ mH : Fin n → ℤ) (N : ℕ) :
    latticeVector (N • mσ + mH) = (N : ℝ) • latticeVector mσ + latticeVector mH := by
  ext i
  simp [latticeVector, integerCast]

end SGPT.Toric

import SGPT.Projective.OkounkovBodyPolynomialGrowth
import SGPT.Convex.FiniteVolumeBounded

/-! Actual admissible cone for SAME original source from true polynomial counts.
Blueprint: okounkov-original-body-cone.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Okounkov.BodyFromGrowth
open Set Filter MeasureTheory SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov
open scoped Topology

/-- Actual SAME original body compactness is manufactured from genuine source counts. -/
theorem isCompact_body_of_polynomial_growth {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    (hG : LatticeSlices.generatedGroup S = ⊤)
    (hfinite : ∀ k : ℕ, (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)).Finite)
    (B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ k : ℕ, 1 ≤ k →
      (Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤ B*(k:ℝ)^n) :
    IsCompact (body S) :=
  SGPT.Convex.isCompact_of_isClosed_convex_interior_nonempty_measure_ne_top volume
    ((isClosed_closedCone S).preimage (continuous_id.prodMk continuous_const))
    (convex_body S) (interior_body_nonempty_of_positiveHeight S hpositive hG)
    (volume_body_ne_top_of_polynomial_growth S hpositive hG hfinite B hB hcount)

/-- Compactness of SAME original body produces a TRUE original norm cone containing ENTIRE `S`. -/
theorem exists_admissibleCone_of_polynomial_growth {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpositive : ∀ z ∈ S, z = 0 ∨ 0 < z.2)
    (hG : LatticeSlices.generatedGroup S = ⊤)
    (hfinite : ∀ k : ℕ, (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)).Finite)
    (B : ℝ) (hB : 0 ≤ B)
    (hcount : ∀ k : ℕ, 1 ≤ k →
      (Nat.card (slice (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)) : ℝ) ≤ B*(k:ℝ)^n) :
    ∃ C : AdmissibleCone n, S ≤ latticePoints C.cone := by
  obtain ⟨M,hM⟩ := (isCompact_body_of_polynomial_growth S hpositive hG hfinite B hB hcount).isBounded.exists_norm_le
  refine ⟨originalNormCone n M, ?_⟩
  intro z hz
  change ‖fun j : Fin n => (z.1 j : ℝ)‖ ≤ M*(z.2:ℝ) ∧ 0 ≤ (z.2:ℝ)
  rcases hpositive z hz with hzero | hpos
  · subst z
    simp
    rfl
  · have hd : (0:ℝ) < (z.2:ℝ) := by exact_mod_cast hpos
    have hnorm := hM _ (normalizedPoint_mem_heightOne _ (mem_closedCone_of_mem S hz) hpos)
    change ‖(z.2:ℝ)⁻¹ • (fun j : Fin n => (z.1 j : ℝ))‖ ≤ M at hnorm
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)] at hnorm
    refine ⟨?_,hd.le⟩
    calc ‖fun j : Fin n => (z.1 j : ℝ)‖ =
          (z.2:ℝ)*((z.2:ℝ)⁻¹ * ‖fun j : Fin n => (z.1 j : ℝ)‖) := by
            rw [←mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
      _ ≤ (z.2:ℝ)*M := mul_le_mul_of_nonneg_left hnorm hd.le
      _ = M*(z.2:ℝ) := mul_comm _ _

end SGPT.Okounkov.BodyFromGrowth

import SGPT.Foundations.Analysis.Pending.BergmanPointJetCriterion
import SGPT.Foundations.Analysis.Pending.BergmanPointLelongLowerBound
import SGPT.Foundations.Analysis.Pending.BergmanPointLelongUpperBound
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

/-! # Real raw Lelong thresholds on one original weighted domain

The native kernel error is `2n/k`. Eligible integer jet thresholds leave that
finite error explicit, and their grid is cofinal below every positive real
threshold. No finite Lelong reader or analytic superlevel is an input.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RawLelongBergmanJetEquations

open FirstPass FirstPass.NonKahlerLocus BergmanGenerators BergmanSupWeight
  BergmanWeightConvergence

noncomputable section

private theorem exists_eligible_grid (n : ℕ) {b q : ℝ} (hb : 0 < b) (hbq : b < q) :
    ∃ k K : ℕ, 1 ≤ k ∧ b ≤ 2 * (K : ℝ) / (k : ℝ) ∧
      2 * ((K : ℝ) + (n : ℝ)) / (k : ℝ) ≤ q := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (2 * ((n : ℝ) + 1) / (q - b)))
  have hkone : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkNat : 1 ≤ k := by exact_mod_cast hkone.le
  have hklarge : 2 * ((n : ℝ) + 1) / (q - b) < k :=
    (le_max_right _ _).trans_lt hk
  have hgap : 2 * ((n : ℝ) + 1) < (k : ℝ) * (q - b) := by
    exact (div_lt_iff₀ (sub_pos.mpr hbq)).mp hklarge
  let K : ℕ := ⌈b * (k : ℝ) / 2⌉₊
  have hKlow : b * (k : ℝ) / 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKhigh : (K : ℝ) < b * (k : ℝ) / 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  refine ⟨k, K, hkNat, ?_, ?_⟩
  · apply (le_div_iff₀ hkpos).mpr
    linarith
  · apply (div_le_iff₀ hkpos).mpr
    nlinarith

/-- All original weighted functions on the same ball give the exact real raw
Lelong threshold, with the actual finite kernel error retained. -/
theorem superlevel_iff (m : ℕ) : by
    letI : MeasurableSpace (ComplexModel (m + 1)) := borel _
    letI : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R →
      ∀ P : ComplexModel (m + 1) → EReal,
        PlurisubharmonicOn P (ball 0 (4 * R)) →
      ∀ x ∈ ball (0 : ComplexModel (m + 1)) (2 * R), ∀ q : ℝ,
        (ENNReal.ofReal q ≤ lelongNumber (n := m + 1) P x) ↔
          ∀ k : ℕ, 1 ≤ k → ∀ K : ℕ,
            2 * ((K : ℝ) + ((m + 1 : ℕ) : ℝ)) / (k : ℝ) ≤ q →
            ∀ f ∈ bergmanUnitBall 0 R (fun y => multiplierWeight (k : ℝ) (P y)),
              ∀ j, j < K → iteratedFDeriv ℂ j f x = 0 := by
  let _ : MeasurableSpace (ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (ComplexModel (m + 1)) := ⟨rfl⟩
  intro R hR P hP x hx q
  have hsub : closedBall (0 : ComplexModel (m + 1)) (2 * R) ⊆ ball 0 (4 * R) :=
    closedBall_subset_ball (by linarith)
  have hsmall : ball (0 : ComplexModel (m + 1)) (2 * R) ⊆ ball 0 (4 * R) :=
    ball_subset_closedBall.trans hsub
  obtain ⟨A, _, hA⟩ := hP.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall 0 (2 * R)) hsub
  have hcrit (k : ℕ) (hk : 1 ≤ k) (K : ℕ) :
      (ENNReal.ofReal (2 * (K : ℝ) / (k : ℝ)) ≤ lelongNumber (n := m + 1)
        (bergmanWeight (ball 0 (2 * R)) P k) x) ↔
        ∀ f ∈ bergmanUnitBall 0 R (fun y => multiplierWeight (k : ℝ) (P y)),
          ∀ j, j < K → iteratedFDeriv ℂ j f x = 0 := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hw : AEMeasurable (fun y => multiplierWeight (k : ℝ) (P y))
        (volume.restrict (ball 0 (2 * R))) :=
      DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
        (hP.upperSemicontinuousOn.mono hsmall) hkpos.ne'
    have hlow : ∀ y ∈ ball (0 : ComplexModel (m + 1)) (2 * R),
        ENNReal.ofReal (Real.exp (-((k : ℝ) * A))) ≤ multiplierWeight (k : ℝ) (P y) := by
      intro y hy
      rw [← multiplierWeight_coe]
      exact multiplierWeight_antitone hkpos.le (hA y (ball_subset_closedBall hy))
    have h := BergmanPointJetCriterion.kernel_point_jet_iff hR hw
      (Real.exp_pos _) hlow hx (inv_pos.mpr hkpos) K
    have heq : 2 * (k : ℝ)⁻¹ * (K : ℝ) = 2 * (K : ℝ) / (k : ℝ) := by ring
    rw [heq] at h
    exact h
  have hupper (k : ℕ) (hk : 1 ≤ k) : lelongNumber (n := m + 1)
      (bergmanWeight (ball 0 (2 * R)) P k) x ≤ lelongNumber (n := m + 1) P x :=
    BergmanPointLelongUpperBound.lelongNumber_bergmanWeight_le (m + 1)
      (2 * R) (by positivity) (ball 0 (2 * R)) isOpen_ball (convex_ball 0 (2 * R))
      (fun y hy => mem_ball_zero_iff.mp hy) P (hP.mono hsmall) x hx k hk
  constructor
  · intro hq k hk K helig
    apply (hcrit k hk K).mp
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hsum : ENNReal.ofReal (2 * (K : ℝ) / (k : ℝ)) +
        ENNReal.ofReal (2 * ((m + 1 : ℕ) : ℝ) / (k : ℝ)) =
        ENNReal.ofReal (2 * ((K : ℝ) + ((m + 1 : ℕ) : ℝ)) / (k : ℝ)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hbound := BergmanPointLelongLowerBound.lelongNumber_le_bergmanWeight_add_error
      isOpen_ball hx P hk
    have hchain : ENNReal.ofReal (2 * (K : ℝ) / (k : ℝ)) +
        ENNReal.ofReal (2 * ((m + 1 : ℕ) : ℝ) / (k : ℝ)) ≤
        lelongNumber (n := m + 1) (bergmanWeight (ball 0 (2 * R)) P k) x +
          ENNReal.ofReal (2 * ((m + 1 : ℕ) : ℝ) / (k : ℝ)) := by
      rw [hsum]
      exact (ENNReal.ofReal_le_ofReal helig).trans (hq.trans hbound)
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  · intro hjets
    by_contra hnot
    have hvlt : lelongNumber (n := m + 1) P x < ENNReal.ofReal q := not_le.mp hnot
    have hvfinite : lelongNumber (n := m + 1) P x ≠ ⊤ :=
      ne_top_of_lt hvlt
    have hvq : (lelongNumber (n := m + 1) P x).toReal < q :=
      (ENNReal.lt_ofReal_iff_toReal_lt hvfinite).mp hvlt
    let b : ℝ := ((lelongNumber (n := m + 1) P x).toReal + q) / 2
    have hvb : (lelongNumber (n := m + 1) P x).toReal < b := by dsimp only [b]; linarith
    have hb : 0 < b := lt_of_le_of_lt ENNReal.toReal_nonneg hvb
    have hbq : b < q := by dsimp only [b]; linarith
    obtain ⟨k, K, hk, hbK, hKq⟩ := exists_eligible_grid (m + 1) hb hbq
    have hν := ((hcrit k hk K).mpr (hjets k hk K hKq)).trans (hupper k hk)
    have hble : ENNReal.ofReal b ≤ lelongNumber (n := m + 1) P x :=
      (ENNReal.ofReal_le_ofReal hbK).trans hν
    exact (not_lt_of_ge hble) ((ENNReal.lt_ofReal_iff_toReal_lt hvfinite).mpr hvb)

end

end SGPT.Foundations.Analysis.Pending.RawLelongBergmanJetEquations

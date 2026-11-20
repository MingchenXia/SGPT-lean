import SGPT.AlmostSemigroup.OkounkovExtension
import Mathlib.Data.Set.Card

/-! Actual slice counts in a common finite superset determine distance and body equality.
Blueprint: common-superset-comparison.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.AlmostSemigroup
open Filter Class OkounkovExtension
open scoped Topology

/-- A common finite superset bounds the actual symmetric difference. -/
theorem discrepancy_le_common_superset {α : Type*} [DecidableEq α]
    (A B Q : Finset α) (hA : A ⊆ Q) (hB : B ⊆ Q) :
    (discrepancy A B : ℝ) ≤ 2 * Q.card - A.card - B.card := by
  have ha := discrepancy_formula A Q
  have hb := discrepancy_formula Q B
  rw [Finset.inter_eq_left.mpr hA] at ha
  rw [Finset.inter_eq_right.mpr hB] at hb
  have har : (discrepancy A Q : ℝ) + 2 * A.card = A.card + Q.card := by
    exact_mod_cast ha
  have hbr : (discrepancy Q B : ℝ) + 2 * B.card = Q.card + B.card := by
    exact_mod_cast hb
  have ht : (discrepancy A B : ℝ) ≤ discrepancy A Q + discrepancy Q B := by
    exact_mod_cast discrepancy_triangle A Q B
  linarith

/-- Equal actual normalized counts in a common finite superset give vanishing discrepancy. -/
theorem tendsto_normalizedDiscrepancy_zero_of_common_superset
    {α : Type*} [DecidableEq α] (n : ℕ) (A B Q : ℕ → Finset α) {a : ℝ}
    (hAQ : ∀ᶠ m : ℕ in atTop, A m ⊆ Q m) (hBQ : ∀ᶠ m : ℕ in atTop, B m ⊆ Q m)
    (hA : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ ^ n * (A m).card) atTop (𝓝 a))
    (hB : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ ^ n * (B m).card) atTop (𝓝 a))
    (hQ : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ ^ n * (Q m).card) atTop (𝓝 a)) :
    Tendsto (normalizedDiscrepancy n A B) atTop (𝓝 0) := by
  have hup : Tendsto (fun m : ℕ => 2 * ((m : ℝ)⁻¹ ^ n * (Q m).card) -
      (m : ℝ)⁻¹ ^ n * (A m).card - (m : ℝ)⁻¹ ^ n * (B m).card) atTop (𝓝 0) := by
    have hzero : 2 * a - a - a = 0 := by ring
    simpa only [hzero] using ((hQ.const_mul 2).sub hA).sub hB
  apply squeeze_zero' (Eventually.of_forall (normalizedDiscrepancy_nonneg n A B)) _ hup
  filter_upwards [hAQ, hBQ] with m hmA hmB
  have h := mul_le_mul_of_nonneg_left (discrepancy_le_common_superset (A m) (B m) (Q m) hmA hmB)
    (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) n)
  simpa only [normalizedDiscrepancy, mul_sub, mul_left_comm] using h

/-- The containing sets may lie outside the cone and need not be additive. -/
theorem dist_eq_zero_of_common_superset {n : ℕ} {C : AdmissibleCone n}
    (S T : ConeSubset C) (Q : ℕ → Set (Fin n → ℤ)) (hQ : ∀ m, (Q m).Finite) {a : ℝ}
    (hSQ : ∀ᶠ m : ℕ in atTop, slice S.val (m : ℤ) ⊆ Q m)
    (hTQ : ∀ᶠ m : ℕ in atTop, slice T.val (m : ℤ) ⊆ Q m)
    (hS : Tendsto S.normalizedCardinality atTop (𝓝 a))
    (hT : Tendsto T.normalizedCardinality atTop (𝓝 a))
    (hcount : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ ^ n * (Nat.card (Q m) : ℝ)) atTop (𝓝 a)) :
    dist S T = 0 := by
  classical
  let q : ℕ → Finset (Fin n → ℤ) := fun m : ℕ => (hQ m).toFinset
  have hsq : ∀ᶠ m : ℕ in atTop, S.slices m ⊆ q m := by
    filter_upwards [hSQ] with m hm
    intro x hx
    exact (hQ m).mem_toFinset.mpr (hm ((S.mem_slices m x).mp hx))
  have htq : ∀ᶠ m : ℕ in atTop, T.slices m ⊆ q m := by
    filter_upwards [hTQ] with m hm
    intro x hx
    exact (hQ m).mem_toFinset.mpr (hm ((T.mem_slices m x).mp hx))
  have hc : ∀ m, (q m).card = Nat.card (Q m) := by
    intro m
    exact ((Set.ncard_eq_toFinset_card (Q m) (hQ m)).trans (by rfl)).symm
  have hq : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ ^ n * (q m).card) atTop (𝓝 a) := by
    simpa only [hc] using hcount
  have hd := tendsto_normalizedDiscrepancy_zero_of_common_superset n S.slices T.slices q
    hsq htq hS hT hq
  exact hd.limsup_eq

/-- Genuine continuous Okounkov extension identifies the distance-zero pair. -/
theorem bodyExtension_eq_of_common_superset {n : ℕ} {C : AdmissibleCone n}
    (S T : AlmostSpace C) (Q : ℕ → Set (Fin n → ℤ)) (hQ : ∀ m, (Q m).Finite) {a : ℝ}
    (hSQ : ∀ᶠ m : ℕ in atTop, slice S.val.val (m : ℤ) ⊆ Q m)
    (hTQ : ∀ᶠ m : ℕ in atTop, slice T.val.val (m : ℤ) ⊆ Q m)
    (hS : Tendsto S.val.normalizedCardinality atTop (𝓝 a))
    (hT : Tendsto T.val.normalizedCardinality atTop (𝓝 a))
    (hcount : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ ^ n * (Nat.card (Q m) : ℝ)) atTop (𝓝 a)) :
    bodyExtension S = bodyExtension T := by
  have hzero : dist S T = 0 := dist_eq_zero_of_common_superset S.val T.val Q hQ hSQ hTQ hS hT hcount
  exact ((Metric.inseparable_iff.mpr hzero).map (continuous_bodyExtension C)).eq

end SGPT.AlmostSemigroup

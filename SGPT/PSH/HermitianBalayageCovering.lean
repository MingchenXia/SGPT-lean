import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Finite coverings with uniform overlap for frozen local estimates

A maximal separated net supplies the centers. Rescaling the centers whose
outer balls contain one point places them in a fixed compact ball with
fixed separation. Its finite packing number bounds the overlap before the
compact set and the radius are chosen.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric Classical
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- A compact set has finite positive-radius packing number. -/
theorem packingNumber_ne_top_of_isCompact {K : Set E} (hK : IsCompact K)
    {ε : ℝ≥0} (hε : ε ≠ 0) : Metric.packingNumber ε K ≠ ⊤ := by
  obtain ⟨T, _, hTfin, hTcover⟩ := Metric.exists_finite_isCover_of_isCompact
    (ε := (ε / 2 : ℝ≥0)) (div_ne_zero hε (by norm_num)) hK
  have hp : Metric.packingNumber ε K ≤ T.encard := by
    calc
      Metric.packingNumber ε K = Metric.packingNumber (2 * (ε / 2)) K := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε / 2) K :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) K
      _ ≤ T.encard := hTcover.externalCoveringNumber_le_encard
  exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hTfin) hp

/-- Compact sets admit finite inner-ball covers with a uniform finite
bound on the multiplicity of the larger balls. The bound depends only on
the ambient normed space, not on the set, its location or the radius. -/
theorem exists_finite_ball_cover_bounded_overlap :
    ∃ N : ℕ, ∀ (K : Set E), IsCompact K → ∀ (r : ℝ), 0 < r →
      ∃ S : Finset E, (↑S : Set E) ⊆ K ∧
        (∀ x ∈ K, ∃ a ∈ S, x ∈ ball a (r / 4)) ∧
        ∀ x : E, (S.filter (fun a => x ∈ ball a r)).card ≤ N := by
  classical
  have hunit := packingNumber_ne_top_of_isCompact (isCompact_closedBall (0 : E) 8)
    (ε := 1) (by norm_num)
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hunit
  refine ⟨N, ?_⟩
  intro K hK r hr
  let ε : ℝ≥0 := ⟨r / 8, by positivity⟩
  have hε : ε ≠ 0 := by
    intro h
    have hc := congrArg (fun t : ℝ≥0 => (t : ℝ)) h
    change r / 8 = 0 at hc
    linarith
  have hp := packingNumber_ne_top_of_isCompact hK hε
  let A := Metric.maximalSeparatedSet ε K
  have hA : A.Finite := Set.encard_ne_top_iff.mp (by
    rw [Metric.encard_maximalSeparatedSet hp]
    exact hp)
  let S := hA.toFinset
  have hSA : (↑S : Set E) = A := by simp [S]
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hSA]
    exact Metric.maximalSeparatedSet_subset
  · intro x hx
    have hcover := Metric.isCover_maximalSeparatedSet hp
    obtain ⟨a, ha, hxa⟩ := hcover hx
    refine ⟨a, by simpa [S] using ha, ?_⟩
    change edist x a ≤ (ε : ℝ≥0∞) at hxa
    rw [edist_dist, ENNReal.ofReal_le_coe] at hxa
    change dist x a < r / 4
    change dist x a ≤ r / 8 at hxa
    linarith
  · intro x
    let F := S.filter (fun a => x ∈ ball a r)
    let f : E → E := fun a => (8 / r) • (a - x)
    have hf : Function.Injective f := by
      intro a b hab
      have hs : (8 / r : ℝ) ≠ 0 := div_ne_zero (by norm_num) hr.ne'
      exact sub_left_injective (smul_right_injective _ hs hab)
    have himage : (↑(F.image f) : Set E) ⊆ closedBall (0 : E) 8 := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      have hax : dist a x < r := by
        simpa only [F, Finset.mem_filter, mem_ball, dist_comm] using (Finset.mem_filter.mp ha).2
      simp only [mem_closedBall, dist_zero_right]
      dsimp [f]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 8) hr), ← dist_eq_norm]
      have hscale : (8 / r) * r = (8 : ℝ) := div_mul_cancel₀ _ hr.ne'
      nlinarith [mul_lt_mul_of_pos_left hax (div_pos (by norm_num : (0 : ℝ) < 8) hr)]
    have hsep : Metric.IsSeparated (1 : ℝ≥0∞) (↑(F.image f) : Set E) := by
      intro y hy z hz hyz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      have hab : a ≠ b := fun h => hyz (congrArg f h)
      have haA : a ∈ A := by simpa [S] using (Finset.mem_filter.mp ha).1
      have hbA : b ∈ A := by simpa [S] using (Finset.mem_filter.mp hb).1
      have hdist := Metric.isSeparated_maximalSeparatedSet (ε := ε) (A := K) haA hbA hab
      change (ε : ℝ≥0∞) < edist a b at hdist
      rw [edist_dist] at hdist
      have hdist' : r / 8 < dist a b := by
        exact ENNReal.coe_lt_ofReal.mp hdist
      rw [edist_dist]
      apply ENNReal.one_lt_ofReal.mpr
      dsimp [f]
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hr), dist_sub_right]
      have hscale : (8 / r) * (r / 8) = (1 : ℝ) := by field_simp
      nlinarith [mul_lt_mul_of_pos_left hdist' (div_pos (by norm_num : (0 : ℝ) < 8) hr)]
    have hcard := hsep.encard_le_packingNumber himage
    rw [Set.encard_coe_eq_coe_finsetCard, ← hN] at hcard
    have hcard' : (F.image f).card ≤ N := ENat.natCast_le_natCast.mp hcard
    rw [Finset.card_image_of_injective F hf] at hcard'
    exact hcard'

end SGPT.PSH.HermitianBalayage

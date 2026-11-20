import SGPT.Foundations.Analysis.Pending.HolomorphicIdealPowerGeneratorBound
import SGPT.Foundations.Analysis.Pending.HolomorphicGermNoetherian
import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace SGPT.PSH

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

noncomputable section

variable {n N : ℕ}

/-- The actual norm-bounded holomorphic germs for the original finite family. -/
def canonicalGrowthGermSet (G : Fin N → ComplexModel n → ℂ) :
    Set (HolGerm (ComplexModel n)) :=
  {h | ∃ (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (C : ℝ),
    0 ≤ C ∧ HolGerm.mk F hF = h ∧
    ∀ᶠ z in 𝓝 0, ‖F z‖ ≤ C * ∑ i, ‖G i z‖}

/-- The canonical ideal is an actual span, without a closure certificate. -/
def canonicalGrowthGermIdeal (G : Fin N → ComplexModel n → ℂ) :
    Ideal (HolGerm (ComplexModel n)) := Ideal.span (canonicalGrowthGermSet G)

private theorem original_mem_growth (G : Fin N → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z) (i : Fin N) :
    HolGerm.mk (G i) (hG i) ∈ canonicalGrowthGermIdeal G := by
  apply Ideal.subset_span
  refine ⟨G i, hG i, 1, zero_le_one, rfl, ?_⟩
  exact Eventually.of_forall fun z => by
    simpa only [one_mul] using
      Finset.single_le_sum (fun j _ => norm_nonneg (G j z)) (Finset.mem_univ i)

private theorem finite_norm_sum_sq_bound {m : ℕ} (F : Fin m → ℂ) :
    (∑ i, ‖F i‖) ^ 2 ≤ (m : ℝ) * ∑ i, ‖F i‖ ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin m => (1 : ℝ)) (fun i => ‖F i‖)

/-- Noetherian finite subset selection and the accepted ideal-power estimate
internally give actual canonical generators and the same squared-norm growth.
This is a fixed-centre result; uniform generation on a neighbourhood is separate. -/
theorem exists_finite_canonical_growth_germ_presentation
    (G : Fin N → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z) :
    ∃ (m : ℕ) (F : Fin m → ComplexModel n → ℂ)
      (hF : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (F j) z),
      Ideal.span (range fun j => HolGerm.mk (F j) (hF j)) = canonicalGrowthGermIdeal G ∧
      (∀ H : ComplexModel n → ℂ,
        ∀ hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z,
        HolGerm.mk H hH ∈ canonicalGrowthGermIdeal G ↔
          ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 0, ‖H z‖ ≤ C * ∑ i, ‖G i z‖) ∧
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ z in 𝓝 0,
        a * generatorNormSq G z ≤ generatorNormSq F z ∧
          generatorNormSq F z ≤ b * generatorNormSq G z := by
  classical
  let : IsNoetherianRing (HolGerm (ComplexModel n)) :=
    isNoetherianRing_holGerm_euclidean n
  have hfg : (Ideal.span (canonicalGrowthGermSet G)).FG :=
    (Ideal.span (canonicalGrowthGermSet G)).fg_of_isNoetherianRing
  obtain ⟨T, hT, hspanT⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (canonicalGrowthGermSet G)).mp hfg
  let m := T.card
  let v : Fin m → HolGerm (ComplexModel n) := fun j => T.equivFin.symm j
  have hv (j : Fin m) : v j ∈ canonicalGrowthGermSet G := hT (T.equivFin.symm j).2
  choose F hF C hC heq hbound using hv
  have hrange : (T : Set (HolGerm (ComplexModel n))) = range v := by
    ext h
    constructor
    · intro hh
      exact ⟨T.equivFin ⟨h, hh⟩, by simp [v]⟩
    · rintro ⟨j, rfl⟩
      exact (T.equivFin.symm j).2
  have hspan : Ideal.span (range fun j => HolGerm.mk (F j) (hF j)) =
      canonicalGrowthGermIdeal G := by
    simp_rw [heq]
    change Submodule.span _ (range v) = Submodule.span _ (canonicalGrowthGermSet G)
    rw [← hrange, ← hspanT]
  have hmem (H : ComplexModel n → ℂ)
      (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) :
      HolGerm.mk H hH ∈ canonicalGrowthGermIdeal G ↔
        ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ z in 𝓝 0, ‖H z‖ ≤ D * ∑ i, ‖G i z‖ := by
    constructor
    · intro hh
      have hh' : HolGerm.mk H hH ∈
          (Ideal.span (range fun j => HolGerm.mk (F j) (hF j))) ^ 1 := by
        simpa only [pow_one, hspan] using hh
      obtain ⟨D, hD, hb⟩ :=
        HolomorphicIdealPowerGeneratorBound.exists_norm_bound_of_mem_span_pow F hF H hH 1 hh'
      refine ⟨D * ∑ j, C j, mul_nonneg hD (Finset.sum_nonneg fun j _ => hC j), ?_⟩
      filter_upwards [hb, eventually_all.mpr hbound] with z hz hzb
      calc ‖H z‖ ≤ D * ∑ j, ‖F j z‖ := by simpa only [pow_one] using hz
        _ ≤ D * ∑ j, C j * ∑ i, ‖G i z‖ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hzb j) hD
        _ = _ := by rw [← Finset.sum_mul]; ring
    · rintro ⟨D, hD, hb⟩
      exact Ideal.subset_span ⟨H, hH, D, hD, rfl, hb⟩
  have hrev (i : Fin N) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ z in 𝓝 0, ‖G i z‖ ≤ D * ∑ j, ‖F j z‖ := by
    have hh : HolGerm.mk (G i) (hG i) ∈
        (Ideal.span (range fun j => HolGerm.mk (F j) (hF j))) ^ 1 := by
      simpa only [pow_one, hspan] using original_mem_growth G hG i
    obtain ⟨D, hD, hb⟩ :=
      HolomorphicIdealPowerGeneratorBound.exists_norm_bound_of_mem_span_pow F hF (G i) (hG i) 1 hh
    exact ⟨D, hD, by simpa only [pow_one] using hb⟩
  choose D hD hrevbound using hrev
  let A : ℝ := (∑ i, D i ^ 2) * m + 1
  let B : ℝ := (∑ j, C j ^ 2) * N + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨m, F, hF, hspan, hmem, A⁻¹, B, inv_pos.mpr hA, hB, ?_⟩
  filter_upwards [eventually_all.mpr hbound, eventually_all.mpr hrevbound] with z hzF hzG
  have upper : generatorNormSq F z ≤
      ((∑ j, C j ^ 2) * N) * generatorNormSq G z := by
    have hterm (j : Fin m) : ‖F j z‖ ^ 2 ≤
        C j ^ 2 * ((N : ℝ) * generatorNormSq G z) := by
      calc ‖F j z‖ ^ 2 ≤ (C j * ∑ i, ‖G i z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hzF j) 2
        _ = C j ^ 2 * (∑ i, ‖G i z‖) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (finite_norm_sum_sq_bound (G · z)) (sq_nonneg _)
    calc generatorNormSq F z ≤ ∑ j, C j ^ 2 * ((N : ℝ) * generatorNormSq G z) :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = _ := by rw [← Finset.sum_mul]; ring
  have lower : generatorNormSq G z ≤
      ((∑ i, D i ^ 2) * m) * generatorNormSq F z := by
    have hterm (i : Fin N) : ‖G i z‖ ^ 2 ≤
        D i ^ 2 * ((m : ℝ) * generatorNormSq F z) := by
      calc ‖G i z‖ ^ 2 ≤ (D i * ∑ j, ‖F j z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hzG i) 2
        _ = D i ^ 2 * (∑ j, ‖F j z‖) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (finite_norm_sum_sq_bound (F · z)) (sq_nonneg _)
    calc generatorNormSq G z ≤ ∑ i, D i ^ 2 * ((m : ℝ) * generatorNormSq F z) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by rw [← Finset.sum_mul]; ring
  constructor
  · have hle : generatorNormSq G z ≤ A * generatorNormSq F z := by
      dsimp [A]
      nlinarith [generatorNormSq_nonneg F z]
    calc A⁻¹ * generatorNormSq G z ≤ A⁻¹ * (A * generatorNormSq F z) :=
        mul_le_mul_of_nonneg_left hle (inv_pos.mpr hA).le
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
  · dsimp [B]
    nlinarith [generatorNormSq_nonneg G z]

/-- Genuine two-sided growth comparisons identify the actual canonical ideals,
without claiming equality of the original raw generated ideals. -/
theorem canonicalGrowthGermIdeal_eq_of_norm_comparison {M : ℕ}
    (G : Fin N → ComplexModel n → ℂ) (H : Fin M → ComplexModel n → ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomp : ∀ᶠ z in 𝓝 0,
      a * ∑ i, ‖G i z‖ ≤ ∑ j, ‖H j z‖ ∧
        ∑ j, ‖H j z‖ ≤ b * ∑ i, ‖G i z‖) :
    canonicalGrowthGermIdeal G = canonicalGrowthGermIdeal H := by
  unfold canonicalGrowthGermIdeal
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨F, hF, C, hC, heq, hbound⟩
    refine ⟨F, hF, C / a, div_nonneg hC ha.le, heq, ?_⟩
    filter_upwards [hbound, hcomp] with z hz hc
    have hl : ∑ i, ‖G i z‖ ≤ (∑ j, ‖H j z‖) / a :=
      (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hc.1)
    calc ‖F z‖ ≤ C * ∑ i, ‖G i z‖ := hz
      _ ≤ C * ((∑ j, ‖H j z‖) / a) := mul_le_mul_of_nonneg_left hl hC
      _ = _ := by ring
  · rintro ⟨F, hF, C, hC, heq, hbound⟩
    refine ⟨F, hF, C * b, mul_nonneg hC hb.le, heq, ?_⟩
    filter_upwards [hbound, hcomp] with z hz hc
    calc ‖F z‖ ≤ C * ∑ j, ‖H j z‖ := hz
      _ ≤ C * (b * ∑ i, ‖G i z‖) := mul_le_mul_of_nonneg_left hc.2 hC
      _ = _ := by ring

end
end SGPT.PSH

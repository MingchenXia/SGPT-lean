import SGPT.BBJ.CantorProbabilityFamily
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

set_option autoImplicit false

/-! # Genuine bounded neighborhoods of the Cantor potential off its poles

Compactness of the actual parameter space gives common bounds for all
probability averages.  Extended kernel values are proved finite before
using their real readback.
-/

noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory Metric TopologicalSpace SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending PatchLocalBoundedMeasure
open scoped Topology ENNReal Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- A compact set away from the actual code set has one real kernel bound
for every actual parameter, before choosing a probability. -/
theorem exists_cantorLogKernel_compact_lower (j : Bool)
    {S : Set (ComplexModel 1)} (hS : IsCompact S)
    (hSK : ∀ z ∈ S, (projectiveModelChart j).symm z ∉ projectiveCantorSet) :
    ∃ L : ℝ, L ≤ 0 ∧ ∀ z ∈ S, ∀ b : ℕ → Bool,
      (L : EReal) ≤ movingProjectiveSectionPotential (cantorCode b)
        ((projectiveModelChart j).symm z) := by
  let H := fun q : (ℕ → Bool) × ComplexModel 1 =>
    movingProjectiveSectionPotential (cantorCode q.1) ((projectiveModelChart j).symm q.2)
  have hbot (q : (ℕ → Bool) × ComplexModel 1) (hq : q.2 ∈ S) : H q ≠ ⊥ := by
    obtain ⟨L, _, hL⟩ := movingProjectiveSectionPotential_code_uniform_lower _ (hSK _ hq)
    exact ne_of_gt ((EReal.bot_lt_coe L).trans_le (hL q.1))
  have htop (q : (ℕ → Bool) × ComplexModel 1) : H q ≠ ⊤ :=
    ne_of_lt ((movingProjectiveSectionPotential_nonpos _ _).trans_lt EReal.zero_lt_top)
  have hc : ContinuousOn (fun q => (H q).toReal) (univ ×ˢ S) := by
    apply EReal.continuousOn_toReal.comp (continuous_cantorLogKernel j).continuousOn
    intro q hq
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hbot q hq.2, htop q⟩
  obtain ⟨C, hC⟩ := (isCompact_univ.prod hS).exists_bound_of_continuousOn hc
  refine ⟨-max C 0, neg_nonpos.mpr (le_max_right _ _), fun z hz b => ?_⟩
  have hbound := hC (b,z) ⟨mem_univ _,hz⟩
  have hreal : -max C 0 ≤ (H (b,z)).toReal := by
    simpa only [Real.norm_eq_abs] using
      (neg_le_neg (le_max_left C 0)).trans ((neg_le_neg hbound).trans (neg_abs_le _))
  have hcoe := EReal.coe_toReal (htop (b,z)) (hbot (b,z) hz)
  exact (EReal.coe_le_coe_iff.mpr hreal).trans_eq hcoe

/-- The compact bound applies uniformly to every actual parameter probability. -/
theorem exists_cantorProbabilityLogPotential_compact_bounds (j : Bool)
    {S : Set (ComplexModel 1)} (hS : IsCompact S)
    (hSK : ∀ z ∈ S, (projectiveModelChart j).symm z ∉ projectiveCantorSet) :
    ∃ L : ℝ, L ≤ 0 ∧ ∀ (σ : Measure (ℕ → Bool)), IsProbabilityMeasure σ →
      ∀ z ∈ S, (L : EReal) ≤ cantorProbabilityLogPotential σ ((projectiveModelChart j).symm z) ∧
        cantorProbabilityLogPotential σ ((projectiveModelChart j).symm z) ≤ 0 := by
  obtain ⟨L, hL, hkernel⟩ := exists_cantorLogKernel_compact_lower j hS hSK
  refine ⟨L, hL, fun σ hσ z hz => ?_⟩
  have := hσ
  refine ⟨?_, cantorProbabilityLogPotential_nonpos _ _⟩
  have hdeficit (b : ℕ → Bool) :
      cantorLogDeficit b ((projectiveModelChart j).symm z) ≤ ENNReal.ofReal (-L) := by
    have he := EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hkernel z hz b))
    simpa only [cantorLogDeficit, ← EReal.coe_neg, EReal.real_coe_toENNReal] using he
  have hI := lintegral_mono (μ := σ) hdeficit
  simp only [lintegral_const, measure_univ, mul_one] at hI
  change cantorProbabilityLogIntegral σ ((projectiveModelChart j).symm z) ≤
    ENNReal.ofReal (-L) at hI
  have he : (cantorProbabilityLogIntegral σ ((projectiveModelChart j).symm z) : EReal) ≤
      (ENNReal.ofReal (-L) : EReal) := by exact_mod_cast hI
  have hneg := EReal.neg_le_neg_iff.mpr he
  simpa only [cantorProbabilityLogPotential, EReal.coe_ennreal_ofReal, max_eq_left (neg_nonneg.mpr hL),
    ← EReal.coe_neg, neg_neg] using hneg

/-- Every actual point off the code set has one open neighborhood and one
real bound that work for every parameter probability, including at infinity. -/
theorem exists_cantorProbabilityLogPotential_bounded_neighborhood
    (p : P1) (hp : p ∉ projectiveCantorSet) :
    ∃ O : Set P1, IsOpen O ∧ p ∈ O ∧ O ⊆ projectiveCantorSetᶜ ∧
      ∃ L : ℝ, L ≤ 0 ∧ ∀ (σ : Measure (ℕ → Bool)), IsProbabilityMeasure σ →
        ∀ q ∈ O, (L : EReal) ≤ cantorProbabilityLogPotential σ q ∧
          cantorProbabilityLogPotential σ q ≤ 0 := by
  obtain ⟨j, hj⟩ := projectiveLineAtlas.cover p
  change Bool at j
  let z := projectiveModelChart j p
  let D := (projectiveModelChart j).target ∩
    (projectiveModelChart j).symm ⁻¹' projectiveCantorSetᶜ
  have hz : z ∈ D := ⟨(projectiveModelChart j).map_source hj, by
    change (projectiveModelChart j).symm ((projectiveModelChart j) p) ∈ projectiveCantorSetᶜ
    rwa [(projectiveModelChart j).left_inv hj]⟩
  have hD : IsOpen D := (projectiveModelChart j).isOpen_inter_preimage_symm
    isClosed_projectiveCantorSet.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hz)
  have hclosed : closedBall z (r/2) ⊆ D :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨L, hL, hbound⟩ := exists_cantorProbabilityLogPotential_compact_bounds j
    (isCompact_closedBall z (r/2)) (fun w hw => (hclosed hw).2)
  let O := (projectiveModelChart j).source ∩
    (projectiveModelChart j) ⁻¹' ball z (r/2)
  have hO : IsOpen O := (projectiveModelChart j).isOpen_inter_preimage isOpen_ball
  have hpO : p ∈ O := ⟨hj, mem_ball_self (by linarith)⟩
  have hback (q : P1) (hq : q ∈ O) :
      (projectiveModelChart j).symm ((projectiveModelChart j) q) = q :=
    (projectiveModelChart j).left_inv hq.1
  refine ⟨O, hO, hpO, ?_, L, hL, ?_⟩
  · intro q hq
    have hk := (hclosed (ball_subset_closedBall hq.2)).2
    change (projectiveModelChart j).symm ((projectiveModelChart j) q) ∈ projectiveCantorSetᶜ at hk
    rwa [hback q hq] at hk
  · intro σ hσ q hq
    simpa only [hback q hq] using
      hbound σ hσ ((projectiveModelChart j) q) (ball_subset_closedBall hq.2)

/-- The SAME original Cantor potential has a genuine native bounded-on
neighborhood at every point outside its actual poles. -/
theorem exists_bounded_cantorLogPotential_neighborhood
    (p : P1) (hp : p ∉ projectiveCantorSet) :
    ∃ O : Set P1, IsOpen O ∧ p ∈ O ∧ O ⊆ projectiveCantorSetᶜ ∧
      IsBoundedPotentialOn cantorLogPotential O := by
  obtain ⟨O, hO, hpO, hOK, L, _, hbound⟩ :=
    exists_cantorProbabilityLogPotential_bounded_neighborhood p hp
  refine ⟨O, hO, hpO, hOK, L, 0, fun q hq => ?_⟩
  simpa only [cantorProbabilityLogPotential_cantorBitProbability, EReal.coe_zero] using
    hbound cantorBitProbability inferInstance q hq

end SGPT.BBJ

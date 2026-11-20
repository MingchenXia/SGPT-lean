import SGPT.BBJ.CantorProbabilityFamily
import SGPT.Foundations.Analysis.Pending.UniformLelongBound
import SGPT.Foundations.Analysis.Pending.ActualLelongAdditivity
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import SGPT.Foundations.Analysis.FirstPass.LelongNumberPole
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import Mathlib.Topology.Clopen

set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory Metric TopologicalSpace SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- Positive mixtures of the actual parameter measures give the literal extended potential sum. -/
theorem cantorProbabilityLogPotential_positive_mixture
    (σ τ : Measure (ℕ → Bool)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    cantorProbabilityLogPotential (ENNReal.ofReal a • σ+ENNReal.ofReal b • τ) =
      fun p => (a : EReal)*cantorProbabilityLogPotential σ p+
        (b : EReal)*cantorProbabilityLogPotential τ p := by
  funext p
  simp only [cantorProbabilityLogPotential, cantorProbabilityLogIntegral,
    lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]
  rw [EReal.coe_ennreal_add,
    EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _)) (.inr (EReal.coe_ennreal_ne_bot _))]
  simp only [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
    max_eq_left ha.le, max_eq_left hb.le, mul_neg, sub_eq_add_neg]

/-- A genuine finite bit cylinder is clopen in the actual compact product space. -/
theorem isClopen_cantorCylinder (I : Finset ℕ) (b : ℕ → Bool) :
    IsClopen (cantorCylinder I b) := by
  have heq : cantorCylinder I b = ⋂ i ∈ I, {d : ℕ → Bool | d i = b i} := by
    ext d
    simp only [cantorCylinder, Set.mem_pi, Finset.mem_coe, mem_singleton_iff, mem_iInter,
      mem_ofPred_eq]
  rw [heq]
  apply isClopen_biInter_finset
  intro i _
  exact (show IsClopen ({b i} : Set Bool) from
    ⟨isClosed_singleton, isOpen_discrete _⟩).preimage (continuous_apply i)

private def cantorNearWeight (n : ℕ) : ℝ := (1/2 : ℝ)^(n+1)

private theorem cantorNearWeight_pos (n : ℕ) : 0 < cantorNearWeight n :=
  pow_pos (by norm_num) _

private theorem cantorNearWeight_lt_one (n : ℕ) : cantorNearWeight n < 1 :=
  pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)

private theorem cantorFarWeight_pos (n : ℕ) : 0 < 1-cantorNearWeight n :=
  sub_pos.mpr (cantorNearWeight_lt_one n)

private theorem cantorCylinder_mass (b : ℕ → Bool) (n : ℕ) :
    cantorBitProbability (cantorCylinder (Finset.range (n+1)) b) =
      ENNReal.ofReal (cantorNearWeight n) := by
  rw [cantorBitProbability_cylinder, Finset.card_range]
  unfold cantorNearWeight
  rw [ENNReal.ofReal_pow (by norm_num)]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

private theorem cantorCylinder_compl_mass (b : ℕ → Bool) (n : ℕ) :
    cantorBitProbability (cantorCylinder (Finset.range (n+1)) b)ᶜ =
      ENNReal.ofReal (1-cantorNearWeight n) := by
  rw [measure_compl (measurableSet_cantorCylinder _ _) (measure_ne_top _ _),
    measure_univ, cantorCylinder_mass, ENNReal.ofReal_sub 1 (cantorNearWeight_pos n).le,
    ENNReal.ofReal_one]

/-- The literal probability obtained by restricting to the matching first n+1 bits. -/
def cantorNearProbability (b : ℕ → Bool) (n : ℕ) : Measure (ℕ → Bool) :=
  (ENNReal.ofReal (cantorNearWeight n))⁻¹ •
    cantorBitProbability.restrict (cantorCylinder (Finset.range (n+1)) b)

/-- The literal probability obtained by restricting to the complementary cylinder. -/
def cantorFarProbability (b : ℕ → Bool) (n : ℕ) : Measure (ℕ → Bool) :=
  (ENNReal.ofReal (1-cantorNearWeight n))⁻¹ •
    cantorBitProbability.restrict (cantorCylinder (Finset.range (n+1)) b)ᶜ

instance cantorNearProbability_probability (b : ℕ → Bool) (n : ℕ) :
    IsProbabilityMeasure (cantorNearProbability b n) where
  measure_univ := by
    rw [cantorNearProbability, Measure.smul_apply, Measure.restrict_apply_univ,
      smul_eq_mul, cantorCylinder_mass]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (cantorNearWeight_pos n)).ne'
      ENNReal.ofReal_ne_top

instance cantorFarProbability_probability (b : ℕ → Bool) (n : ℕ) :
    IsProbabilityMeasure (cantorFarProbability b n) where
  measure_univ := by
    rw [cantorFarProbability, Measure.smul_apply, Measure.restrict_apply_univ,
      smul_eq_mul, cantorCylinder_compl_mass]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (cantorFarWeight_pos n)).ne'
      ENNReal.ofReal_ne_top

/-- The exact fair measure split, with both coefficients strictly positive for every n. -/
theorem cantorBitProbability_cylinder_split (b : ℕ → Bool) (n : ℕ) :
    ENNReal.ofReal (cantorNearWeight n) • cantorNearProbability b n+
      ENNReal.ofReal (1-cantorNearWeight n) • cantorFarProbability b n =
        cantorBitProbability := by
  rw [cantorNearProbability, cantorFarProbability, smul_smul, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (cantorNearWeight_pos n)).ne'
      ENNReal.ofReal_ne_top,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (cantorFarWeight_pos n)).ne'
      ENNReal.ofReal_ne_top, one_smul, one_smul,
    Measure.restrict_add_restrict_compl (measurableSet_cantorCylinder _ _)]

/-- The actual far-cylinder average is finite at the original root point. -/
theorem cantorFarProbability_potential_ne_bot (b : ℕ → Bool) (n : ℕ) :
    cantorProbabilityLogPotential (cantorFarProbability b n) (projectiveCantorCode b) ≠ ⊥ := by
  let C := cantorCylinder (Finset.range (n+1)) b
  let F : Set ℂ := (fun d : ℕ → Bool => (cantorCode d : ℂ)) '' Cᶜ
  have hC : IsClopen C := isClopen_cantorCylinder _ _
  have hFcompact : IsCompact F := hC.compl.isClosed.isCompact.image
    (Complex.continuous_ofReal.comp continuous_cantorCode)
  have hbC : b ∈ C := fun _ _ => rfl
  have hflip : cantorFlip b 0 ∈ Cᶜ := by
    intro hd
    have h0 : cantorFlip b 0 0 = b 0 := hd 0 (Finset.mem_range.mpr (Nat.succ_pos n))
    cases hb : b 0 <;> simp [cantorFlip, hb] at h0
  have hFnonempty : F.Nonempty := ⟨_, cantorFlip b 0, hflip, rfl⟩
  have hbF : (cantorCode b : ℂ) ∉ F := by
    rintro ⟨d, hd, hdb⟩
    have heq : d = b := cantorCode_injective (Complex.ofReal_injective hdb)
    exact hd (heq.symm ▸ hbC)
  let r := Metric.infDist (cantorCode b : ℂ) F
  have hr : 0 < r := (hFcompact.isClosed.notMem_iff_infDist_pos hFnonempty).mp hbF
  let B := Real.log (r^2)-Real.log (1+Complex.normSq (cantorCode b : ℂ))-Real.log 2
  let L := min 0 B
  have hkernel (d : ℕ → Bool) (hd : d ∈ Cᶜ) :
      (L : EReal) ≤ movingProjectiveSectionPotential (cantorCode d) (projectiveCantorCode b) := by
    have hgap : r ≤ dist (cantorCode b : ℂ) (cantorCode d : ℂ) :=
      Metric.infDist_le_dist_of_mem (⟨d, hd, rfl⟩ : (cantorCode d : ℂ) ∈ F)
    rw [dist_eq_norm] at hgap
    have hne : (cantorCode b : ℂ)-(cantorCode d : ℂ) ≠ 0 :=
      norm_pos_iff.mp (hr.trans_le hgap)
    have hlog := Real.log_le_log (sq_pos_of_pos hr)
      (pow_le_pow_left₀ hr.le hgap 2)
    have hc0 := cantorCode_nonneg d
    have hc1 := cantorCode_lt_half d
    have hClog : Real.log (1+(cantorCode d)^2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by nlinarith)
    apply le_trans (EReal.coe_le_coe_iff.mpr (min_le_right 0 B))
    change (B : EReal) ≤ movingProjectiveSectionPotential (cantorCode d)
      (projectiveLineHomeomorph ((cantorCode b : ℂ) : OnePoint ℂ))
    rw [movingProjectiveSectionPotential_finite, logNormSq_of_ne_zero hne,
      ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    dsimp only [B]
    linarith
  have hmem : ∀ᵐ d ∂cantorFarProbability b n, d ∈ Cᶜ :=
    Measure.ae_smul_measure
      (ae_restrict_mem (μ := cantorBitProbability) (measurableSet_cantorCylinder _ _).compl)
      ((ENNReal.ofReal (1-cantorNearWeight n))⁻¹)
  have hdeficit : ∀ᵐ d ∂cantorFarProbability b n,
      cantorLogDeficit d (projectiveCantorCode b) ≤ ENNReal.ofReal (-L) := by
    filter_upwards [hmem] with d hd
    have he := EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hkernel d hd))
    simpa only [cantorLogDeficit, ← EReal.coe_neg, EReal.real_coe_toENNReal] using he
  have hI := lintegral_mono_ae hdeficit
  simp only [lintegral_const, measure_univ, mul_one] at hI
  change cantorProbabilityLogIntegral (cantorFarProbability b n) (projectiveCantorCode b) ≤
    ENNReal.ofReal (-L) at hI
  intro hbot
  have ht : (cantorProbabilityLogIntegral (cantorFarProbability b n)
      (projectiveCantorCode b) : EReal) = ⊤ := EReal.neg_eq_bot_iff.mp hbot
  exact (hI.trans_lt ENNReal.ofReal_lt_top).ne (EReal.coe_ennreal_eq_top_iff.mp ht)

private theorem cantorProbability_zero_lelong_of_ne_bot
    (σ : Measure (ℕ → Bool)) [IsProbabilityMeasure σ] (p : P1)
    (hp : cantorProbabilityLogPotential σ p ≠ ⊥) :
    NonKahlerLocus.lelongNumber (n := 1) (cantorProbabilityLogPotential σ) p = 0 := by
  apply le_antisymm _ zero_le
  by_contra h
  exact hp (NonKahlerLocus.eq_bot_of_lelongNumber_pos (by norm_num)
    (isThetaPshPotential_cantorProbabilityLogPotential σ).1 (lt_of_not_ge h))

/-- Every actual native point Lelong number of the literal Cantor logarithmic average is zero. -/
theorem lelongNumber_cantorLogPotential (p : P1) :
    NonKahlerLocus.lelongNumber (n := 1) cantorLogPotential p = 0 := by
  by_cases hp : p ∈ projectiveCantorSet
  · obtain ⟨b, rfl⟩ := hp
    obtain ⟨N, hN⟩ := UniformLelongBound.hasUniformLelongBound
      (n := 1) (by norm_num) projectiveNativeFSBackground.form
    have hbound (n : ℕ) :
        NonKahlerLocus.lelongNumber (n := 1) cantorLogPotential (projectiveCantorCode b) ≤
          (1/2 : ℝ≥0∞)^(n+1)*ENNReal.ofReal (max N 0) := by
      have hnear := isThetaPshPotential_cantorProbabilityLogPotential (cantorNearProbability b n)
      have hfar := isThetaPshPotential_cantorProbabilityLogPotential (cantorFarProbability b n)
      have hqnear := (GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
        (γ := projectiveNativeFSBackground.form) (cantorNearWeight_pos n) hnear.1).quasiPlurisubharmonic
      have hqfar := (GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
        (γ := projectiveNativeFSBackground.form) (cantorFarWeight_pos n) hfar.1).quasiPlurisubharmonic
      have hzero := cantorProbability_zero_lelong_of_ne_bot (cantorFarProbability b n)
        (projectiveCantorCode b) (cantorFarProbability_potential_ne_bot b n)
      have hblend := cantorProbabilityLogPotential_positive_mixture
        (cantorNearProbability b n) (cantorFarProbability b n)
        (cantorNearWeight n) (1-cantorNearWeight n)
        (cantorNearWeight_pos n) (cantorFarWeight_pos n)
      rw [cantorBitProbability_cylinder_split,
        cantorProbabilityLogPotential_cantorBitProbability] at hblend
      rw [hblend, ActualLelongAdditivity.lelongNumber_add_eq hqnear hqfar,
        ActualLelongPositiveScaling.lelongNumber_smul_eq (cantorNearWeight_pos n),
        ActualLelongPositiveScaling.lelongNumber_smul_eq (cantorFarWeight_pos n),
        hzero, mul_zero, add_zero]
      have hweight : ENNReal.ofReal (cantorNearWeight n) = (1/2 : ℝ≥0∞)^(n+1) := by
        rw [← cantorCylinder_mass b n, cantorBitProbability_cylinder, Finset.card_range]
      rw [← hweight]
      gcongr
      exact (hN _ hnear (projectiveCantorCode b)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left N 0))
    have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop :=
      tendsto_atTop.mpr fun k => eventually_atTop.mpr ⟨k, fun n hn => hn.trans (Nat.le_succ n)⟩
    have hpower := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1/2 : ℝ≥0∞) < 1)).comp hshift
    have hlimit := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal (max N 0)) hpower
      (Or.inr ENNReal.ofReal_ne_top)
    apply le_antisymm _ zero_le
    exact ge_of_tendsto' (by simpa only [Function.comp_apply, zero_mul] using hlimit) hbound
  · simpa only [cantorProbabilityLogPotential_cantorBitProbability] using
      cantorProbability_zero_lelong_of_ne_bot cantorBitProbability p
        (cantorLogPotential_ne_bot_off p hp)

end SGPT.BBJ

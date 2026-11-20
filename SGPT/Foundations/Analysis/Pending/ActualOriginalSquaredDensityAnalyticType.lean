import SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityDyadicConvergence
import SGPT.Foundations.Analysis.Pending.DemaillyApproximationAnalyticType
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

set_option autoImplicit false

/-! # Exact original multiplier-ideal type of the SAME squared density

The actual core branch and the original multiplier ideal's finite Nadel
generators give a bounded residual for the literal squared sum. This supplies
the analytic type and strict multiplier fields for that SAME sequence.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal Classical
namespace SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityAnalyticType
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  FirstPass.QuasiEquisingularApproximation
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  BergmanKernelSmooth BergmanSupWeight GlobalTubeFunction
  ActualGlobalSquaredBergmanDensity ActualSquaredBergmanDensityUniformRatios
  ActualOriginalSquaredDensityThetaPsh ActualOriginalSquaredDensityDyadicConvergence
  MultiplierIdealBergmanNadelManifold DemaillyApproximationAnalyticType

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem core_sandwich (F : FixedChartCover n X)
    (θ : ClosedRealOneOneForm n X) (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {m : ℕ} (hm : 0 < m) (i : F.t) {x : X} (hx : x ∈ F.cover.U i) :
    localDensity F ρ u m i x ≤ density F ρ u m x ∧
      density F ρ u m x ≤ ((Fintype.card F.t : ℝ) + 1) * Real.exp F.CB *
        localDensity F ρ u m i x := by
  classical
  have hVi := F.cover.U_subset_V i hx
  have hterm0 : ∀ j : F.t, 0 ≤ bumpExtend (F.cover.V j)
      (fun y => F.cover.χ j y * F.cover.χ j y) (localDensity F ρ u m j) x :=
    fun j => bumpExtend_nonneg (fun y => mul_self_nonneg (F.cover.χ j y))
      (fun _ => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) x
  have hlower := Finset.single_le_sum (fun j _ => hterm0 j) (Finset.mem_univ i)
  refine ⟨?_, ?_⟩
  · simpa only [density, bumpExtend_of_mem hVi, F.cover.χ_eq_one i x hx,
      one_mul] using hlower
  · have hterm : ∀ j : F.t, bumpExtend (F.cover.V j)
        (fun y => F.cover.χ j y * F.cover.χ j y) (localDensity F ρ u m j) x ≤
        Real.exp F.CB * localDensity F ρ u m i x := by
      intro j
      by_cases hj : x ∈ F.cover.V j
      · rw [bumpExtend_of_mem hj]
        have hχ0 := F.cover.χ_nonneg j x
        have hχ1 := F.χ_le_one j x
        have hχsq : F.cover.χ j x * F.cover.χ j x ≤ 1 := by nlinarith
        have hDj : 0 ≤ localDensity F ρ u m j x :=
          mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
        calc _ ≤ localDensity F ρ u m j x := by nlinarith
          _ ≤ _ := localDensity_le_exp_CB_mul F θ ρ hρ hu hm j i ⟨hj, hVi⟩
      · rw [bumpExtend_of_notMem hj]
        exact mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset F.t)) => hterm j
    have hsum' : density F ρ u m x ≤ (Fintype.card F.t : ℝ) *
        (Real.exp F.CB * localDensity F ρ u m i x) := by
      simpa only [density, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
    have hnonneg : 0 ≤ Real.exp F.CB * localDensity F ρ u m i x :=
      mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
    calc _ ≤ (Fintype.card F.t : ℝ) *
        (Real.exp F.CB * localDensity F ρ u m i x) := hsum'
      _ ≤ ((Fintype.card F.t : ℝ) + 1) *
        (Real.exp F.CB * localDensity F ρ u m i x) :=
        mul_le_mul_of_nonneg_right (by linarith) hnonneg
      _ = _ := by ring

private theorem scaled_log_localDensity_eq_branch (F : FixedChartCover n X)
    (θ : ClosedRealOneOneForm n X) (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {m : ℕ} (hm : 0 < m) (j : F.t) {x : X} (hx : x ∈ F.cover.V j) :
    (((m : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (localDensity F ρ u m j x)) =
      F.branch ρ u m j x := by
  let B := ball (F.center j) (F.bergmanRadius j)
  let P := correctedWeight (F.chart j) (ρ j) u
  have hP : PlurisubharmonicOn P B :=
    (F.plurisubharmonicOn_correctedWeight hρ hu.1 j).mono
      (ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le)
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hK : bergmanSup B (fun z => multiplierWeight (m : ℝ) (P z))
      ((F.chart j).val x) ≠ ⊤ :=
    BergmanSubadditivity.bergmanSup_multiplierWeight_ne_top isOpen_ball hP hmR
      (F.V_subset_chartPatch j hx).2
  rw [F.branch_of_mem (F.V_subset_chartPatch j hx)]
  dsimp only [localDensity]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hK,
    ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (inv_nonneg.mpr hmR.le))
      (EReal.coe_ne_top _), ← EReal.coe_mul]
  have hmul : (m : ℝ)⁻¹ * (-(m : ℝ) * ρ j ((F.chart j).val x)) =
      -ρ j ((F.chart j).val x) := by field_simp
  rw [hmul, EReal.coe_neg, sub_eq_add_neg, add_comm]
  rfl

private theorem originalWeight_core_bounds (F : FixedChartCover n X)
    (θ : ClosedRealOneOneForm n X) (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {m : ℕ} (hm : 0 < m) (i : F.t) {x : X} (hx : x ∈ F.cover.U i) :
    F.branch ρ u m i x ≤ originalWeight F ρ u m x ∧
      originalWeight F ρ u m x ≤ F.branch ρ u m i x +
        (((m : ℝ)⁻¹ * Real.log (((Fintype.card F.t : ℝ) + 1) * Real.exp F.CB) : ℝ) : EReal) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  let B : ℝ := ((Fintype.card F.t : ℝ) + 1) * Real.exp F.CB
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨hlo, hup⟩ := core_sandwich F θ ρ hρ hu hm i hx
  have heq := scaled_log_localDensity_eq_branch F θ ρ hρ hu hm i
    (F.cover.U_subset_V i hx)
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact mul_le_mul_of_nonneg_left
      (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hlo))
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr hmR.le))
  · have hlog := ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hup)
    rw [ENNReal.ofReal_mul hB.le, ENNReal.log_mul_add,
      ENNReal.log_ofReal_of_pos hB] at hlog
    have hs := mul_le_mul_of_nonneg_left hlog
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr hmR.le))
    rw [EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr hmR.le)) (EReal.coe_ne_top _),
      ← EReal.coe_mul, heq, add_comm] at hs
    exact hs

/-- Actual original ideal generators give the exact type of the SAME original
squared sum, including at every common zero. -/
theorem hasAnalyticSingularitiesOfType_originalWeight (hn : 0 < n)
    (F : FixedChartCover n X) (θ : ClosedRealOneOneForm n X)
    (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u) {m : ℕ} (hm : 0 < m) :
    HasAnalyticSingularitiesOfType (n := n) (originalWeight F ρ u m) ((m : ℚ)⁻¹)
      (multiplierIdeal (n := n) (m : ℝ) u) := by
  classical
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hc : 0 < (m : ℚ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hm)
  have hcR : (((m : ℚ)⁻¹ : ℚ) : ℝ) = (m : ℝ)⁻¹ := by push_cast; rfl
  have hcoh := isCoherent_multiplierIdeal_of_pos hn hu.1 hmR
  refine ⟨hc, hcoh, fun x => ?_⟩
  obtain ⟨U₀, hU₀, hxU₀, N, g, hgd, hgen⟩ := hcoh x
  have hgx : ∀ h, (multiplierIdeal (n := n) (m : ℝ) u).mem x h →
      IsInSpanAt (n := n) (· ∈ range g) x h :=
    fun h hh => (hgen x hxU₀ h).mp hh
  have hgmem : ∀ i, (multiplierIdeal (n := n) (m : ℝ) u).mem x (g i) := by
    intro i
    refine (hgen x hxU₀ (g i)).mpr ⟨?_, 1, fun _ => g i, fun _ _ => 1,
      fun _ => ⟨i, rfl⟩, fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const, ?_⟩
    · filter_upwards [hU₀.mem_nhds hxU₀] with y hy
      exact (hgd i y hy).mdifferentiableAt (hU₀.mem_nhds hy)
    · exact Eventually.of_forall fun y => by simp
  obtain ⟨i, hxi⟩ := F.cover.cover x
  have hxVi := F.cover.U_subset_V i hxi
  obtain ⟨C₁, hC₁⟩ := F.exists_const_eventually_le_branch hn hρ hu.1 hm i hxVi hgmem
  obtain ⟨C₂, hC₂⟩ := exists_branch_le F hρ hu.1 hm i (subset_closure hxVi) hgx
  let b : ℝ := (m : ℝ)⁻¹ * Real.log (((Fintype.card F.t : ℝ) + 1) * Real.exp F.CB)
  let K : ℝ := |C₁| + |C₂| + |b|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC₁K : C₁ ≤ K := by
    dsimp [K]
    linarith [le_abs_self C₁, abs_nonneg C₂, abs_nonneg b]
  have hC₂K : C₂ + b ≤ K := by
    dsimp [K]
    linarith [abs_nonneg C₁, le_abs_self C₂, le_abs_self b]
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U₀ ∧
      (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (K : EReal) ≤
        originalWeight F ρ u m y ∧
      originalWeight F ρ u m y ≤
        (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (K : EReal) := by
    filter_upwards [hU₀.mem_nhds hxU₀, (F.cover.isOpen_U i).mem_nhds hxi, hC₁, hC₂]
      with y hy₀ hyi hy₁ hy₂
    obtain ⟨hlo, hhi⟩ := originalWeight_core_bounds F θ ρ hρ hu hm i hyi
    refine ⟨hy₀, ?_, ?_⟩
    · apply le_trans _ (hy₁.trans hlo)
      rw [sub_eq_add_neg, sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_neg]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (neg_le_neg hC₁K))
    · calc originalWeight F ρ u m y ≤ F.branch ρ u m i y + (b : EReal) := hhi
        _ ≤ ((((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (C₂ : EReal)) +
            (b : EReal) := add_le_add hy₂ le_rfl
        _ = (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + ((C₂ + b : ℝ) : EReal) := by
          rw [EReal.coe_add, add_assoc]
        _ ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (K : EReal) :=
          add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hC₂K)
  obtain ⟨U, hUev, hUo, hxU⟩ := _root_.eventually_nhds_iff.mp hev
  let R : X → ℝ := fun y => if generatorLog g y = ⊥ then 0 else
    (originalWeight F ρ u m y).toReal - (m : ℝ)⁻¹ * (generatorLog g y).toReal
  refine ⟨U, hUo, hxU, N, g, fun j => (hgd j).mono fun y hy => (hUev y hy).1,
    fun y hy h => hgen y (hUev y hy).1 h, R, K, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨-, hlo, hhi⟩ := hUev y hy
    by_cases hg0 : generatorLog g y = ⊥
    · simpa only [R, if_pos hg0, abs_zero] using hK
    · obtain ⟨t, ht⟩ : ∃ t : ℝ, generatorLog g y = (t : EReal) :=
        ⟨(generatorLog g y).toReal, (EReal.coe_toReal (generatorLog_ne_top g y) hg0).symm⟩
      rw [ht, ← EReal.coe_mul] at hlo hhi
      have hb := (eq_coe_of_bounds hlo hhi).2
      simpa only [R, if_neg hg0, ht, EReal.toReal_coe] using hb
  · obtain ⟨-, hlo, hhi⟩ := hUev y hy
    rw [hcR]
    by_cases hg0 : generatorLog g y = ⊥
    · rw [hg0, EReal.coe_mul_bot_of_pos (inv_pos.mpr hmR), EReal.bot_add] at hhi ⊢
      exact le_bot_iff.mp hhi
    · obtain ⟨t, ht⟩ : ∃ t : ℝ, generatorLog g y = (t : EReal) :=
        ⟨(generatorLog g y).toReal, (EReal.coe_toReal (generatorLog_ne_top g y) hg0).symm⟩
      rw [ht, ← EReal.coe_mul] at hlo hhi
      have hw := (eq_coe_of_bounds hlo hhi).1
      simp only [R, if_neg hg0, ht, EReal.toReal_coe]
      nth_rewrite 1 [hw]
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
      ring

/-- Adding an actual finite constant retains the SAME original ideal and
generators, with the bounded remainder constructed from the SAME sum. -/
theorem hasAnalyticSingularitiesOfType_originalWeight_add_const (hn : 0 < n)
    (F : FixedChartCover n X) (θ : ClosedRealOneOneForm n X)
    (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u) {m : ℕ} (hm : 0 < m) (a : ℝ) :
    HasAnalyticSingularitiesOfType (n := n)
      (fun x => originalWeight F ρ u m x + (a : EReal)) ((m : ℚ)⁻¹)
      (multiplierIdeal (n := n) (m : ℝ) u) := by
  obtain ⟨hc, hcoh, hloc⟩ := hasAnalyticSingularitiesOfType_originalWeight hn F θ ρ hρ hu hm
  refine ⟨hc, hcoh, fun x => ?_⟩
  obtain ⟨U, hU, hxU, N, g, hgd, hgen, R, C, hRC, heq⟩ := hloc x
  refine ⟨U, hU, hxU, N, g, hgd, hgen, fun y => R y + a, C + |a|,
    fun y hy => (abs_add_le _ _).trans (add_le_add (hRC y hy) le_rfl), fun y hy => ?_⟩
  dsimp only
  rw [heq y hy, EReal.coe_add, add_assoc]

/-- Uniform correction chosen internally from genuine doubling. The SAME
sequence has the exact original ideal at every level and the strict
multiplier field; antitonicity and the original limit are retained literally. -/
theorem exists_uniform_original_density_multiplier_inclusion (hn : 0 < n)
    (F : FixedChartCover n X) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (θ : ClosedRealOneOneForm n X)
      (ρ : F.t → ComplexModel n → ℝ),
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) →
      ∀ (u : X → EReal), IsThetaPshPotential θ.val u →
        (∀ x : X, Antitone (fun ℓ : ℕ => originalWeight F ρ u (2 ^ ℓ) x +
            ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) ∧
          Tendsto (fun ℓ : ℕ => originalWeight F ρ u (2 ^ ℓ) x +
            ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) atTop (𝓝 (u x))) ∧
        (∀ ℓ : ℕ, HasAnalyticSingularitiesOfType (n := n)
          (fun x => originalWeight F ρ u (2 ^ ℓ) x +
            ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) (((2 ^ ℓ : ℕ) : ℚ)⁻¹)
          (multiplierIdeal (n := n) ((2 ^ ℓ : ℕ) : ℝ) u)) ∧
        ∀ c d : ℝ, 0 < c → c < d → ∀ᶠ ℓ : ℕ in atTop,
          MultiplierIdealIncluded (n := n)
            (fun x => originalWeight F ρ u (2 ^ ℓ) x +
              ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) d u c := by
  obtain ⟨E, hE, hconv⟩ := exists_uniform_original_density_dyadic_convergence F
  refine ⟨E, hE, ?_⟩
  intro θ ρ hρ u hu
  have htype : ∀ ℓ : ℕ, HasAnalyticSingularitiesOfType (n := n)
      (fun x => originalWeight F ρ u (2 ^ ℓ) x +
        ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) (((2 ^ ℓ : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((2 ^ ℓ : ℕ) : ℝ) u) := fun ℓ =>
    hasAnalyticSingularitiesOfType_originalWeight_add_const hn F θ ρ hρ hu
      (pow_pos (by norm_num : 0 < (2 : ℕ)) _) _
  refine ⟨hconv θ ρ hρ u hu, htype, ?_⟩
  intro c d hc hcd
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hlevels : Tendsto (fun ℓ : ℕ => ((2 ^ ℓ : ℕ) : ℝ)) atTop atTop := by
    have hp := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
    exact hp.congr fun ℓ => by push_cast; rfl
  filter_upwards [hlevels.eventually_ge_atTop (c * d / (d - c))] with ℓ hℓ
  have hmcd : c * d ≤ ((2 ^ ℓ : ℕ) : ℝ) * (d - c) := (div_le_iff₀ hdc).mp hℓ
  have hle : ∀ x, u x ≤ originalWeight F ρ u (2 ^ ℓ) x +
      ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal) := by
    intro x
    obtain ⟨ha, ht⟩ := hconv θ ρ hρ u hu x
    exact ha.le_of_tendsto ht ℓ
  exact QuasiEquisingularApproximationDemailly.multiplierIdealIncluded_of_hasAnalyticSingularitiesOfType
    hu.1.quasiPlurisubharmonic hle (by positivity) (htype ℓ) hc hcd hmcd

end SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityAnalyticType

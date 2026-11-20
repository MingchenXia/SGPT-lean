import SGPT.Foundations.Analysis.Pending.ActualFixedAtlasHolomorphicKernelGauges

set_option autoImplicit false

/-! # Uniform actual overlap ratios for the SAME squared Bergman density -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal Classical
namespace SGPT.Foundations.Analysis.Pending.ActualSquaredBergmanDensityUniformRatios
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  BergmanKernelSmooth BergmanSupWeight GlobalTubeFunction
  ActualGlobalSquaredBergmanDensity ActualFixedAtlasHolomorphicKernelGauges

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem scaled_inv_log_sub (k : ℕ) (hk : 0 < k) (L : EReal) (r : ℝ) :
    (k : ℝ) * ((((k : ℝ)⁻¹ : ℝ) : EReal) * L - (r : EReal)) =
      L + (-(k : ℝ) * r : ℝ) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  rw [EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hkR.le)
    (EReal.coe_ne_top _), ← mul_assoc, ← EReal.coe_mul,
    mul_inv_cancel₀ hkR.ne', EReal.coe_one, one_mul, ← EReal.coe_mul,
    sub_eq_add_neg, ← EReal.coe_neg]
  congr 1
  congr 1
  ring

private theorem scaled_add (k : ℕ) (hk : 0 < k) (L : EReal) (C : ℝ) :
    (k : ℝ) * (L + (C / (k : ℝ) : ℝ)) = (k : ℝ) * L + (C : EReal) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hkR.le)
    (EReal.coe_ne_top _), ← EReal.coe_mul]
  congr 1
  congr 1
  field_simp

private theorem exp_scaled_branch (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) {k : ℕ} (hk : 0 < k)
    (j : F.t) {y : X} (hy : y ∈ F.cover.V j) :
    EReal.exp ((k : ℝ) * F.branch ρ u k j y) =
      ENNReal.ofReal (Real.exp (-(k : ℝ) * ρ j ((F.chart j).val y))) *
        bergmanSup (ball (F.center j) (F.bergmanRadius j))
          (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z))
          ((F.chart j).val y) := by
  rw [F.branch_of_mem (F.V_subset_chartPatch j hy)]
  rw [scaled_inv_log_sub k hk, EReal.exp_add, EReal.exp_coe, bergmanLog,
    ENNReal.exp_log, mul_comm]

/-- Genuine branch comparisons exponentiate to uniform real kernel bounds,
including common zeros; the constant is independent of u and k. -/
theorem localDensity_le_exp_CB_mul (F : FixedChartCover n X)
    (θ : ClosedRealOneOneForm n X) (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {k : ℕ} (hk : 0 < k) (j l : F.t) {y : X}
    (hy : y ∈ F.cover.V j ∩ F.cover.V l) :
    localDensity F ρ u k j y ≤ Real.exp F.CB * localDensity F ρ u k l y := by
  obtain ⟨i, _, r, g, _, _, _, _, hlevels⟩ :=
    all_level_holomorphic_kernel_gauges F θ ρ hρ y
  obtain ⟨hBw, _, _⟩ := hlevels u hu k hk
  have hK : bergmanSup (ball (F.center l) (F.bergmanRadius l))
      (fun z => multiplierWeight k (correctedWeight (F.chart l) (ρ l) u z))
      ((F.chart l).val y) ≠ ⊤ :=
    BergmanKernelSmooth.bergmanSup_ne_top (hBw l) (F.V_subset_chartPatch l hy.2).2
  have hbranch := F.branch_le_branch_add hρ hu.1 hk j l hy
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hscale := mul_le_mul_of_nonneg_left hbranch (EReal.coe_nonneg.mpr hkR.le)
  rw [scaled_add k hk] at hscale
  have h := EReal.exp_monotone hscale
  rw [EReal.exp_add, EReal.exp_coe, exp_scaled_branch F ρ u hk j hy.1,
    exp_scaled_branch F ρ u hk l hy.2] at h
  have hright :
      (ENNReal.ofReal (Real.exp (-(k : ℝ) * ρ l ((F.chart l).val y))) *
        bergmanSup (ball (F.center l) (F.bergmanRadius l))
          (fun z => multiplierWeight k (correctedWeight (F.chart l) (ρ l) u z))
          ((F.chart l).val y) * ENNReal.ofReal (Real.exp F.CB)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK) ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono hright h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hr
  simpa only [localDensity, mul_comm, mul_left_comm, mul_assoc] using hr

private theorem term_nonneg (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (k : ℕ) (j : F.t) (y : X) :
    0 ≤ bumpExtend (F.cover.V j) (fun z => F.cover.χ j z * F.cover.χ j z)
      (localDensity F ρ u k j) y :=
  bumpExtend_nonneg (fun z => mul_self_nonneg (F.cover.χ j z))
    (fun _ => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) y

/-- Every active original kernel is bounded by exp(CB) times the literal
original squared density, with the core index selected internally. -/
theorem localDensity_le_exp_CB_mul_density (F : FixedChartCover n X)
    (θ : ClosedRealOneOneForm n X) (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {k : ℕ} (hk : 0 < k) (j : F.t) {y : X} (hy : y ∈ F.cover.V j) :
    0 ≤ localDensity F ρ u k j y ∧
      localDensity F ρ u k j y ≤ Real.exp F.CB * density F ρ u k y := by
  classical
  refine ⟨mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg, ?_⟩
  obtain ⟨i, hi⟩ := F.cover.cover y
  have hsum := Finset.single_le_sum (fun l _ => term_nonneg F ρ u k l y)
    (Finset.mem_univ i)
  have hcore : localDensity F ρ u k i y ≤ density F ρ u k y := by
    simpa only [density, bumpExtend_of_mem (F.cover.U_subset_V i hi),
      F.cover.χ_eq_one i y hi, one_mul] using hsum
  exact (localDensity_le_exp_CB_mul F θ ρ hρ hu hk j i
    ⟨hy, F.cover.U_subset_V i hi⟩).trans
      (mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le)

end SGPT.Foundations.Analysis.Pending.ActualSquaredBergmanDensityUniformRatios

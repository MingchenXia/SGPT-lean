import SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityThetaPsh
import SGPT.Foundations.Analysis.Pending.BergmanSubadditivity
import SGPT.Foundations.Analysis.Pending.DemaillyChartBranchLimit

set_option autoImplicit false

/-! # Doubling and convergence of the SAME original squared Bergman sum

The real kernel subadditivity and actual overlap ratios produce a uniform
doubling bound. A fixed core branch gives a true pointwise squeeze, including
poles. The density and its prescribed potentials are never replaced by type.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal Classical
namespace SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityDyadicConvergence
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  BergmanKernelSmooth BergmanSupWeight GlobalTubeFunction
  ActualGlobalSquaredBergmanDensity ActualSquaredBergmanDensityUniformRatios
  ActualOriginalSquaredDensityThetaPsh

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem density_nonneg (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (k : ℕ) (x : X) :
    0 ≤ density F ρ u k x := by
  apply Finset.sum_nonneg
  intro j _
  exact bumpExtend_nonneg (fun y => mul_self_nonneg (F.cover.χ j y))
    (fun _ => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) x

private theorem exists_uniform_local_doubling (F : FixedChartCover n X) :
    ∃ D : ℝ, 0 < D ∧ ∀ (θ : ClosedRealOneOneForm n X)
      (ρ : F.t → ComplexModel n → ℝ),
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) →
      ∀ (u : X → EReal), IsThetaPshPotential θ.val u →
      ∀ m : ℕ, 0 < m → ∀ j : F.t, ∀ x ∈ F.cover.V j,
        localDensity F ρ u (2 * m) j x ≤ D * localDensity F ρ u m j x ^ 2 := by
  classical
  have hchoose : ∀ j : F.t, ∃ C : ℝ, 0 < C ∧
      ∀ B : Set (ComplexModel n), IsOpen B → Convex ℝ B →
        (∀ z ∈ B, ‖z‖ < ‖F.center j‖ + F.bergmanRadius j) →
      ∀ P : ComplexModel n → EReal, PlurisubharmonicOn P B →
      ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ → ∀ y ∈ B,
        bergmanSup B (fun z => multiplierWeight (c₁ + c₂) (P z)) y ≤
          ENNReal.ofReal C * bergmanSup B (fun z => multiplierWeight c₁ (P z)) y *
            bergmanSup B (fun z => multiplierWeight c₂ (P z)) y := by
    intro j
    exact BergmanSubadditivity.bergmanSup_add_le' (d := n)
      (add_pos_of_nonneg_of_pos (norm_nonneg _) (F.bergmanRadius_pos j))
  choose C hC hsub using hchoose
  let D : ℝ := (∑ j : F.t, C j) + 1
  have hsum : 0 ≤ ∑ j : F.t, C j := Finset.sum_nonneg fun j _ => (hC j).le
  have hD : 0 < D := add_pos_of_nonneg_of_pos hsum zero_lt_one
  refine ⟨D, hD, ?_⟩
  intro θ ρ hρ u hu m hm j x hx
  let B := ball (F.center j) (F.bergmanRadius j)
  let P := correctedWeight (F.chart j) (ρ j) u
  have hP : PlurisubharmonicOn P B :=
    (F.plurisubharmonicOn_correctedWeight hρ hu.1 j).mono
      (ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le)
  have hmem : (F.chart j).val x ∈ B := (F.V_subset_chartPatch j hx).2
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hcast : ((2 * m : ℕ) : ℝ) = (m : ℝ) + (m : ℝ) := by push_cast; ring
  have h := hsub j B isOpen_ball (convex_ball _ _)
    (fun z hz => DemaillyChartBranchLimit.norm_lt_of_mem_ball hz)
    P hP (m : ℝ) (m : ℝ) hmR hmR ((F.chart j).val x) hmem
  rw [← hcast] at h
  have hK : bergmanSup B (fun z => multiplierWeight (m : ℝ) (P z))
      ((F.chart j).val x) ≠ ⊤ :=
    BergmanSubadditivity.bergmanSup_multiplierWeight_ne_top isOpen_ball hP hmR hmem
  have hright : ENNReal.ofReal (C j) *
      bergmanSup B (fun z => multiplierWeight (m : ℝ) (P z)) ((F.chart j).val x) *
      bergmanSup B (fun z => multiplierWeight (m : ℝ) (P z)) ((F.chart j).val x) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK) hK
  have hr := ENNReal.toReal_mono hright h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hC j).le] at hr
  have hexp : Real.exp (-((2 * m : ℕ) : ℝ) * ρ j ((F.chart j).val x)) =
      Real.exp (-(m : ℝ) * ρ j ((F.chart j).val x)) ^ 2 := by
    rw [pow_two, ← Real.exp_add, hcast]
    congr 1
    ring
  have hlocal : localDensity F ρ u (2 * m) j x ≤ C j * localDensity F ρ u m j x ^ 2 := by
    dsimp only [localDensity]
    rw [hexp]
    calc _ ≤ Real.exp (-(m : ℝ) * ρ j ((F.chart j).val x)) ^ 2 *
        (C j * (bergmanSup B (fun z => multiplierWeight (m : ℝ) (P z))
          ((F.chart j).val x)).toReal * (bergmanSup B
          (fun z => multiplierWeight (m : ℝ) (P z)) ((F.chart j).val x)).toReal) :=
      mul_le_mul_of_nonneg_left hr (sq_nonneg _)
      _ = _ := by dsimp [B, P]; ring
  have hCD : C j ≤ D := by
    have hj := Finset.single_le_sum (fun l _ => (hC l).le) (Finset.mem_univ j)
    change C j ≤ (∑ l : F.t, C l) + 1
    linarith
  exact hlocal.trans (mul_le_mul_of_nonneg_right hCD (sq_nonneg _))

/-- The original finite squared sum doubles uniformly before all original
potentials and levels, including every common zero. -/
theorem exists_uniform_original_density_doubling (F : FixedChartCover n X) :
    ∃ A : ℝ, 0 < A ∧ ∀ (θ : ClosedRealOneOneForm n X)
      (ρ : F.t → ComplexModel n → ℝ),
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) →
      ∀ (u : X → EReal), IsThetaPshPotential θ.val u →
      ∀ m : ℕ, 0 < m → ∀ x : X,
        density F ρ u (2 * m) x ≤ A * density F ρ u m x ^ 2 := by
  classical
  obtain ⟨D, hD, hd⟩ := exists_uniform_local_doubling F
  let b := Real.exp F.CB
  let N : ℝ := Fintype.card F.t + 1
  let A : ℝ := N * D * b ^ 2
  have hb : 0 < b := Real.exp_pos _
  have hN : 0 < N := by dsimp [N]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro θ ρ hρ u hu m hm x
  have hS := density_nonneg F ρ u m x
  have hterm : ∀ j : F.t, bumpExtend (F.cover.V j)
      (fun y => F.cover.χ j y * F.cover.χ j y) (localDensity F ρ u (2 * m) j) x ≤
      D * b ^ 2 * density F ρ u m x ^ 2 := by
    intro j
    by_cases hx : x ∈ F.cover.V j
    · rw [bumpExtend_of_mem hx]
      have hχ0 := F.cover.χ_nonneg j x
      have hχ1 := F.χ_le_one j x
      have hχsq : F.cover.χ j x * F.cover.χ j x ≤ 1 := by nlinarith
      have hDj2 : 0 ≤ localDensity F ρ u (2 * m) j x :=
        mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
      have hfirst : F.cover.χ j x * F.cover.χ j x * localDensity F ρ u (2 * m) j x ≤
          localDensity F ρ u (2 * m) j x := by nlinarith
      obtain ⟨hDj, hratio⟩ := localDensity_le_exp_CB_mul_density F θ ρ hρ hu hm j hx
      have hsquare := mul_self_le_mul_self hDj hratio
      calc _ ≤ localDensity F ρ u (2 * m) j x := hfirst
        _ ≤ D * localDensity F ρ u m j x ^ 2 := hd θ ρ hρ u hu m hm j x hx
        _ ≤ D * (b * density F ρ u m x) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hD.le
          simpa only [pow_two] using hsquare
        _ = _ := by ring
    · rw [bumpExtend_of_notMem hx]
      positivity
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset F.t)) => hterm j
  have hsum' : density F ρ u (2 * m) x ≤
      (Fintype.card F.t : ℝ) * (D * b ^ 2 * density F ρ u m x ^ 2) := by
    simpa only [density, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  have hDN : 0 ≤ D * b ^ 2 * density F ρ u m x ^ 2 := by positivity
  calc _ ≤ (Fintype.card F.t : ℝ) * (D * b ^ 2 * density F ρ u m x ^ 2) := hsum'
    _ ≤ N * (D * b ^ 2 * density F ρ u m x ^ 2) :=
      mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) hDN
    _ = _ := by dsimp [A]; ring

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

/-- A true fixed-core squeeze recovers the SAME original potential at every
point, including poles, from the literal original squared sum. -/
theorem tendsto_originalWeight (F : FixedChartCover n X)
    (θ : ClosedRealOneOneForm n X) (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u) (x : X) :
    Tendsto (fun m : ℕ => originalWeight F ρ u m x) atTop (𝓝 (u x)) := by
  obtain ⟨i, hi⟩ := F.cover.cover x
  have hbranch : Tendsto (fun m : ℕ => F.branch ρ u m i x) atTop (𝓝 (u x)) := by
    exact DemaillyChartBranchLimit.tendsto_chartBergmanBranch hu.1 (hρ i)
      (ball_subset_ball (F.bergmanRadius_lt_potentialRadius i).le)
      (F.V_subset_chartPatch i (F.cover.U_subset_V i hi))
  let B : ℝ := ((Fintype.card F.t : ℝ) + 1) * Real.exp F.CB
  have hsmall : Tendsto (fun m : ℕ => (((m : ℝ)⁻¹ * Real.log B : ℝ) : EReal))
      atTop (𝓝 ((0 : ℝ) : EReal)) := by
    apply (continuous_coe_real_ereal.tendsto _).comp
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (Real.log B)
    simpa only [Function.comp_def, zero_mul] using h
  have hadd := (EReal.continuousAt_add (p := (u x, ((0 : ℝ) : EReal)))
    (Or.inr (EReal.coe_ne_bot 0)) (Or.inr (EReal.coe_ne_top 0))).tendsto.comp
      (hbranch.prodMk_nhds hsmall)
  simp only [EReal.coe_zero, add_zero] at hadd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hbranch hadd
    (by filter_upwards [eventually_ge_atTop 1] with m hm
        exact (originalWeight_core_bounds F θ ρ hρ hu (by omega) i hi).1)
    (by filter_upwards [eventually_ge_atTop 1] with m hm
        exact (originalWeight_core_bounds F θ ρ hρ hu (by omega) i hi).2)

private theorem originalWeight_two_mul_le (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) {m : ℕ} (hm : 0 < m)
    {A : ℝ} (hA : 0 < A) (x : X)
    (hd : density F ρ u (2 * m) x ≤ A * density F ρ u m x ^ 2) :
    originalWeight F ρ u (2 * m) x ≤ originalWeight F ρ u m x +
      ((((2 * (m : ℝ))⁻¹ * Real.log A : ℝ)) : EReal) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  by_cases hzero : density F ρ u (2 * m) x = 0
  · simp only [originalWeight, hzero, ENNReal.ofReal_zero, ENNReal.log_zero]
    rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr (inv_pos.mpr (by rw [h2m]; positivity)))]
    exact bot_le
  · have h2 : 0 < density F ρ u (2 * m) x :=
      lt_of_le_of_ne (density_nonneg F ρ u (2 * m) x) (Ne.symm hzero)
    have h1 : 0 < density F ρ u m x := by
      by_contra h
      have hz : density F ρ u m x = 0 :=
        le_antisymm (le_of_not_gt h) (density_nonneg F ρ u m x)
      rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hd
      exact not_le_of_gt h2 hd
    have hlog := Real.log_le_log h2 hd
    rw [Real.log_mul hA.ne' (pow_pos h1 2).ne', Real.log_pow] at hlog
    simp only [originalWeight, ENNReal.log_ofReal_of_pos h2,
      ENNReal.log_ofReal_of_pos h1, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    rw [h2m]
    calc (2 * (m : ℝ))⁻¹ * Real.log (density F ρ u (2 * m) x)
        ≤ (2 * (m : ℝ))⁻¹ * (Real.log A + 2 * Real.log (density F ρ u m x)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by field_simp; ring

/-- The SAME sum has a uniform finite correction whose dyadic sequence is
antitone and converges to the SAME original potential, even at its poles. -/
theorem exists_uniform_original_density_dyadic_convergence (F : FixedChartCover n X) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (θ : ClosedRealOneOneForm n X)
      (ρ : F.t → ComplexModel n → ℝ),
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) →
      ∀ (u : X → EReal), IsThetaPshPotential θ.val u → ∀ x : X,
        Antitone (fun ℓ : ℕ => originalWeight F ρ u (2 ^ ℓ) x +
          ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) ∧
        Tendsto (fun ℓ : ℕ => originalWeight F ρ u (2 ^ ℓ) x +
          ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal)) atTop (𝓝 (u x)) := by
  obtain ⟨A, hA, hdouble⟩ := exists_uniform_original_density_doubling F
  refine ⟨max (Real.log A) 0, le_max_right _ _, ?_⟩
  intro θ ρ hρ u hu x
  refine ⟨?_, ?_⟩
  · refine antitone_nat_of_succ_le fun ℓ => ?_
    let E : ℝ := max (Real.log A) 0
    have hm : 0 < (2 : ℕ) ^ ℓ := pow_pos (by norm_num) _
    have h := originalWeight_two_mul_le F ρ u hm hA x
      (hdouble θ ρ hρ u hu (2 ^ ℓ) hm x)
    have hpow : (2 : ℕ) * 2 ^ ℓ = 2 ^ (ℓ + 1) := by ring
    rw [hpow] at h
    have hcast : ((2 ^ ℓ : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by push_cast; ring
    rw [hcast] at h
    have hlogE : (2 * (2 : ℝ) ^ ℓ)⁻¹ * Real.log A ≤ (2 * (2 : ℝ) ^ ℓ)⁻¹ * E :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have hsplit : E * ((2 : ℝ) ^ ℓ)⁻¹ =
        (2 * (2 : ℝ) ^ ℓ)⁻¹ * E + E * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by
      rw [pow_succ]
      field_simp
      ring
    calc originalWeight F ρ u (2 ^ (ℓ + 1)) x + ((E * ((2 : ℝ) ^ (ℓ + 1))⁻¹ : ℝ) : EReal)
        ≤ (originalWeight F ρ u (2 ^ ℓ) x +
            (((2 * (2 : ℝ) ^ ℓ)⁻¹ * Real.log A : ℝ) : EReal)) +
            ((E * ((2 : ℝ) ^ (ℓ + 1))⁻¹ : ℝ) : EReal) := by gcongr
      _ ≤ (originalWeight F ρ u (2 ^ ℓ) x +
            (((2 * (2 : ℝ) ^ ℓ)⁻¹ * E : ℝ) : EReal)) +
            ((E * ((2 : ℝ) ^ (ℓ + 1))⁻¹ : ℝ) : EReal) := by gcongr
      _ = originalWeight F ρ u (2 ^ ℓ) x + ((E * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal) := by
        rw [hsplit, EReal.coe_add, add_assoc]
  · have hw : Tendsto (fun ℓ : ℕ => originalWeight F ρ u (2 ^ ℓ) x) atTop (𝓝 (u x)) :=
      (tendsto_originalWeight F θ ρ hρ hu x).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
    have he : Tendsto (fun ℓ : ℕ => ((max (Real.log A) 0 * ((2 : ℝ) ^ ℓ)⁻¹ : ℝ) : EReal))
        atTop (𝓝 ((0 : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      have h := (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).const_mul
          (max (Real.log A) 0)
      simpa only [Function.comp_def, mul_zero] using h
    have hadd := (EReal.continuousAt_add (p := (u x, ((0 : ℝ) : EReal)))
      (Or.inr (EReal.coe_ne_bot 0)) (Or.inr (EReal.coe_ne_top 0))).tendsto.comp
        (hw.prodMk_nhds he)
    simpa only [Function.comp_def, EReal.coe_zero, add_zero] using hadd

end SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityDyadicConvergence

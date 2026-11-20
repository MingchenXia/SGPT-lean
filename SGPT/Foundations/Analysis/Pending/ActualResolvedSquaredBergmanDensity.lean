import SGPT.Foundations.Analysis.Pending.ActualGlobalSquaredBergmanDensity
import SGPT.Foundations.Analysis.Pending.ActualSimultaneousPrincipalizedAtlasKernels

set_option autoImplicit false

/-! # Smooth strictly positive resolved remainder of the actual squared density -/
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal
universe u
namespace SGPT.Foundations.Analysis.Pending.ActualResolvedSquaredBergmanDensity
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  NormalCrossings HironakaAdmissibleSequence BergmanKernelSmooth
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  ActualGlobalSquaredBergmanDensity GlobalTubeFunction

private def adaptedInverse {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)) :
    ComplexModel n → Y := fun z => (complexChartAt (n := n) y).val.symm (Φ.invFun z)

private theorem adaptedInverse_zero {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0) :
    adaptedInverse y Φ 0 = y := by
  dsimp only [adaptedInverse]
  rw [← h0, Φ.left_inv _ Φ.center_mem_source]
  exact (complexChartAt (n := n) y).val.left_inv (mem_complexChartAt_source y)

private theorem adaptedInverse_tendsto {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] (y : Y)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0) :
    Tendsto (adaptedInverse y Φ) (𝓝 0) (𝓝 y) := by
  have ht : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  have hcont := ((complexChartAt (n := n) y).val.continuousAt_symm
    (hsrc (Φ.mapsTo_invFun ht))).comp
    ((Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds ht)).continuousAt)
  have ht' : Tendsto (adaptedInverse y Φ) (𝓝 0) (𝓝 (adaptedInverse y Φ 0)) := hcont.tendsto
  simpa only [adaptedInverse_zero y Φ h0] using ht'

private theorem atlas_pullback_holomorphic {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {f : Y → X} (y : Y)
    (hf : ∀ t, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f t)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)
    (e : ComplexChart n X) (hx : f y ∈ e.val.source) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ
      (fun z => e.val (f (adaptedInverse y Φ z))) z := by
  have ht : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  have hT := adaptedInverse_tendsto y Φ hsrc h0
  have hnear : ∀ᶠ z in 𝓝 0, f (adaptedInverse y Φ z) ∈ e.val.source :=
    ((hf y).continuousAt.tendsto.comp hT).eventually (e.val.open_source.mem_nhds hx)
  filter_upwards [Φ.isOpen_target.mem_nhds ht, hnear] with z hz hzX
  have hdInv := (Φ.invFun_holomorphic.differentiableAt
    (Φ.isOpen_target.mem_nhds hz)).mdifferentiableAt
  have hdT := (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm
    (hsrc (Φ.mapsTo_invFun hz))).comp z hdInv
  have hdf := ((hf (adaptedInverse y Φ z)).mdifferentiableAt (by simp)).comp z hdT
  exact ((mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n))
    e.property hzX).comp z hdf).differentiableAt

private theorem exists_atlas_smooth_ball {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {f : Y → X} (y : Y)
    (hf : ∀ t, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f t)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)
    (e : ComplexChart n X) (hx : f y ∈ e.val.source) :
    ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ ∞ (fun z => e.val (f (adaptedInverse y Φ z))) (ball 0 r) ∧
      ∀ z ∈ ball 0 r, f (adaptedInverse y Φ z) ∈ e.val.source := by
  have hD := atlas_pullback_holomorphic y hf Φ hsrc h0 e hx
  have hnear : ∀ᶠ z in 𝓝 0, f (adaptedInverse y Φ z) ∈ e.val.source :=
    ((hf y).continuousAt.tendsto.comp (adaptedInverse_tendsto y Φ hsrc h0)).eventually
      (e.val.open_source.mem_nhds hx)
  obtain ⟨r, hr, hcond⟩ := Metric.eventually_nhds_iff_ball.mp (hD.and hnear)
  have hd : DifferentiableOn ℂ
      (fun z => e.val (f (adaptedInverse y Φ z))) (ball 0 r) :=
    fun z hz => (hcond z hz).1.differentiableWithinAt
  exact ⟨r, hr, contDiffOn_real_of_differentiableOn_complex hd isOpen_ball,
    fun z hz => (hcond z hz).2⟩

private theorem resolved_factor_at_point {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (F : FixedChartCover n X) {θ : ClosedRealOneOneForm n X}
    (ρ : F.t → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    (u : X → EReal) (k : ℕ) {f : Y → X} (y : Y)
    (hf : ∀ t, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f t)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0) (g : Y → ℂ)
    (hkernel : ∀ j : {j : F.t // f y ∈ closure (F.cover.V j)},
      ∃ hBw : BergmanWeight (ball (F.center j.val) (F.bergmanRadius j.val))
        (fun z => multiplierWeight k (correctedWeight (F.chart j.val) (ρ j.val) u z)),
        ∃ (Q : ComplexModel n → StrongDual ℂ
          (bergmanSubspace (ball (F.center j.val) (F.bergmanRadius j.val))
            (fun z => multiplierWeight k (correctedWeight (F.chart j.val) (ρ j.val) u z))))
          (r : ℝ), 0 < r ∧ ContDiffOn ℝ ∞ (fun z => ‖Q z‖ ^ 2) (ball 0 r) ∧
          ∀ z ∈ ball 0 r, 0 < ‖Q z‖ ^ 2 ∧
            ‖evalCLM hBw ((F.chart j.val).val (f (adaptedInverse y Φ z)))‖ ^ 2 =
              ‖g (adaptedInverse y Φ z)‖ ^ 2 * ‖Q z‖ ^ 2) :
    ∃ (H : ComplexModel n → ℝ) (r : ℝ), 0 < r ∧
      ContDiffOn ℝ ∞ H (ball 0 r) ∧ ContDiffOn ℝ ∞ (fun z => Real.log (H z)) (ball 0 r) ∧
      ∀ z ∈ ball 0 r, 0 < H z ∧
        density F ρ u k (f (adaptedInverse y Φ z)) =
          ‖g (adaptedInverse y Φ z)‖ ^ 2 * H z := by
  classical
  let J := {j : F.t // f y ∈ closure (F.cover.V j)}
  choose hBw Q r hr hQ hfactor using hkernel
  let T := adaptedInverse y Φ
  let H : ComplexModel n → ℝ := fun z => ∑ j : J,
    (F.cover.χ j.val (f (T z))) ^ 2 *
      Real.exp (-(k : ℝ) * ρ j.val ((F.chart j.val).val (f (T z)))) * ‖Q j z‖ ^ 2
  have hT := adaptedInverse_tendsto y Φ hsrc h0
  have hTf : Tendsto (fun z => f (T z)) (𝓝 0) (𝓝 (f y)) :=
    (hf y).continuousAt.tendsto.comp hT
  let e := complexChartAt (n := n) (f y)
  obtain ⟨b, hb, hβ, hβsrc⟩ := exists_atlas_smooth_ball y hf Φ hsrc h0 e
    (mem_complexChartAt_source (f y))
  have hχ (j : F.t) : ContDiffOn ℝ ∞ (fun z => F.cover.χ j (f (T z))) (ball 0 b) := by
    have hcomp := (F.cover.χ_smooth j e).comp hβ (fun z hz => e.val.map_source (hβsrc z hz))
    exact hcomp.congr fun z hz => by
      simp only [Function.comp_apply, T, e.val.left_inv (hβsrc z hz)]
  have hactive (j : J) : ∀ᶠ z in 𝓝 0,
      ContDiffAt ℝ ∞ (fun z =>
        (F.cover.χ j.val (f (T z))) ^ 2 *
          Real.exp (-(k : ℝ) * ρ j.val ((F.chart j.val).val (f (T z)))) * ‖Q j z‖ ^ 2) z ∧
      bumpExtend (F.cover.V j.val) (fun x => F.cover.χ j.val x * F.cover.χ j.val x)
        (localDensity F ρ u k j.val) (f (T z)) =
        ‖g (T z)‖ ^ 2 * ((F.cover.χ j.val (f (T z))) ^ 2 *
          Real.exp (-(k : ℝ) * ρ j.val ((F.chart j.val).val (f (T z)))) * ‖Q j z‖ ^ 2) := by
    have hx := F.closure_V_subset_chartPatch j.val j.property
    obtain ⟨a, ha, hα, _⟩ := exists_atlas_smooth_ball y hf Φ hsrc h0 (F.chart j.val) hx.1
    have hK : ∀ᶠ z in 𝓝 0,
        (F.chart j.val).val (f (T z)) ∈ ball (F.center j.val) (F.bergmanRadius j.val) := by
      have ht := ((F.chart j.val).val.continuousAt hx.1).tendsto.comp hTf
      exact ht.eventually (isOpen_ball.mem_nhds hx.2)
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hb),
      isOpen_ball.mem_nhds (mem_ball_self ha),
      isOpen_ball.mem_nhds (mem_ball_self (hr j)), hK] with z hzB hzA hzR hzK
    have hzΩ := ball_subset_ball (F.bergmanRadius_lt_potentialRadius j.val).le hzK
    have hp := ((hρ j.val).2.2.1.contDiffAt (isOpen_ball.mem_nhds hzΩ)).comp z
      (hα.contDiffAt (isOpen_ball.mem_nhds hzA))
    refine ⟨(((hχ j.val).contDiffAt (isOpen_ball.mem_nhds hzB)).pow 2).mul
      ((contDiffAt_const.mul hp).exp) |>.mul
      ((hQ j).contDiffAt (isOpen_ball.mem_nhds hzR)), ?_⟩
    by_cases hzV : f (T z) ∈ F.cover.V j.val
    · rw [bumpExtend_of_mem hzV]
      dsimp only [localDensity]
      rw [bergmanSup_eq_ofReal_norm_evalCLM_sq (hBw j) hzK,
        ENNReal.toReal_ofReal (sq_nonneg _), (hfactor j z hzR).2]
      ring
    · have hzχ : F.cover.χ j.val (f (T z)) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hzV (F.cover.tsupport_χ_subset j.val h))
      rw [bumpExtend_of_notMem hzV, hzχ]
      simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero]
  have hinactive (j : F.t) (hj : f y ∉ closure (F.cover.V j)) :
      ∀ᶠ z in 𝓝 0,
        bumpExtend (F.cover.V j) (fun x => F.cover.χ j x * F.cover.χ j x)
          (localDensity F ρ u k j) (f (T z)) = 0 := by
    filter_upwards [hTf.eventually (isClosed_closure.isOpen_compl.mem_nhds hj)] with z hz
    exact bumpExtend_of_notMem (fun h => hz (subset_closure h))
  have hsm : ∀ᶠ z in 𝓝 0, ContDiffAt ℝ ∞ H z := by
    filter_upwards [Filter.eventually_all.mpr (fun j : J => (hactive j).mono fun _ h => h.1)]
      with z hz
    exact ContDiffAt.sum fun j _ => hz j
  have heq : ∀ᶠ z in 𝓝 0, density F ρ u k (f (T z)) = ‖g (T z)‖ ^ 2 * H z := by
    have hall : ∀ j : F.t, ∀ᶠ z in 𝓝 0,
        bumpExtend (F.cover.V j) (fun x => F.cover.χ j x * F.cover.χ j x)
          (localDensity F ρ u k j) (f (T z)) =
        if hj : f y ∈ closure (F.cover.V j) then
          ‖g (T z)‖ ^ 2 * ((F.cover.χ j (f (T z))) ^ 2 *
            Real.exp (-(k : ℝ) * ρ j ((F.chart j).val (f (T z)))) * ‖Q ⟨j, hj⟩ z‖ ^ 2)
        else 0 := by
      intro j
      by_cases hj : f y ∈ closure (F.cover.V j)
      · simpa only [dif_pos hj] using (hactive ⟨j, hj⟩).mono fun _ h => h.2
      · simpa only [dif_neg hj] using hinactive j hj
    filter_upwards [Filter.eventually_all.mpr hall] with z hz
    dsimp only [density, H]
    simp_rw [hz]
    rw [Finset.sum_dite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [← Finset.mul_sum]
    congr 1
    exact (Equiv.subtypeEquivRight (by simp)).sum_comp fun j : J =>
      (F.cover.χ j.val (f (T z))) ^ 2 *
        Real.exp (-(k : ℝ) * ρ j.val ((F.chart j.val).val (f (T z)))) * ‖Q j z‖ ^ 2
  have hH0 : 0 < H 0 := by
    obtain ⟨j, hj⟩ := F.cover.cover (f y)
    have hjV := F.cover.U_subset_V j hj
    let j0 : J := ⟨j, subset_closure hjV⟩
    have hpos := (hfactor j0 0 (mem_ball_self (hr j0))).1
    have hle := Finset.single_le_sum (f := fun l : J =>
      (F.cover.χ l.val (f (T 0))) ^ 2 *
        Real.exp (-(k : ℝ) * ρ l.val ((F.chart l.val).val (f (T 0)))) * ‖Q l 0‖ ^ 2)
      (fun l _ => mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (sq_nonneg _))
      (Finset.mem_univ j0)
    have hcore : F.cover.χ j (f (T 0)) = 1 := by
      rw [show T 0 = y from adaptedInverse_zero y Φ h0]
      exact F.cover.χ_eq_one j (f y) hj
    have hposTerm : 0 < (F.cover.χ j0.val (f (T 0))) ^ 2 *
        Real.exp (-(k : ℝ) * ρ j0.val ((F.chart j0.val).val (f (T 0)))) * ‖Q j0 0‖ ^ 2 := by
      dsimp only [j0]
      rw [hcore, one_pow, one_mul]
      exact mul_pos (Real.exp_pos _) hpos
    exact hposTerm.trans_le hle
  have hp : ∀ᶠ z in 𝓝 0, 0 < H z :=
    hsm.self_of_nhds.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds hH0)
  obtain ⟨a, ha, hall⟩ := Metric.eventually_nhds_iff_ball.mp (hsm.and (hp.and heq))
  have hSmooth : ContDiffOn ℝ ∞ H (ball 0 a) := fun z hz =>
    (hall z hz).1.contDiffWithinAt
  exact ⟨H, a, ha, hSmooth, hSmooth.log (fun z hz => (hall z hz).2.1.ne'),
    fun z hz => (hall z hz).2⟩

/-- The original fixed squared density has an internally constructed smooth
strictly positive resolved factor on whole adapted balls, including poles. -/
theorem exists_fixed_cover_resolved_smooth_positive_density {m : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X] [CompactSpace X] :
    ∃ F : FixedChartCover (m + 1) X,
      ∀ (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal),
        IsThetaPshPotential θ.val u →
        ∃ ρ : F.t → ComplexModel (m + 1) → ℝ,
          (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
            (ball (F.center j) (F.potentialRadius j)) (ρ j)) ∧
          ∀ k : ℕ, 0 < k → ChartSmooth (n := m + 1) (density F ρ u k) ∧
            ∃ (Y : Type u) (_ : TopologicalSpace Y)
              (_ : ChartedSpace (ComplexModel (m + 1)) Y) (_ : IsComplexManifold (m + 1) Y)
              (f : Y → X) (D : EffectiveDivisor (m + 1) Y) (E : List (Set Y)),
              IsAdmissibleBlowupSequence (m + 1) X []
                (multiplierIdeal (n := m + 1) k u).zeroLocus Y f E ∧
              GermIdeal.pullback (m := m + 1) f (multiplierIdeal (n := m + 1) k u) = D.ideal ∧
              IsSNCDivisor (m + 1) E ∧ D.support = ⋃ A ∈ E, A ∧
              D.support = f ⁻¹' (multiplierIdeal (n := m + 1) k u).zeroLocus ∧
              IsIsomorphismOver (m + 1) f (multiplierIdeal (n := m + 1) k u).zeroLocusᶜ ∧
              ∀ y : Y,
                ∃ Φ : LocalHolomorphicEquivAt (n := m + 1)
                    ((complexChartAt (n := m + 1) y).val y),
                  Φ.source ⊆ (complexChartAt (n := m + 1) y).val.target ∧
                  Φ.toFun ((complexChartAt (n := m + 1) y).val y) = 0 ∧
                  ∃ g : Y → ℂ, HolomorphicAt (m + 1) g y ∧
                    (∀ a : Y → ℂ, D.ideal.mem y a ↔ IsInSpanAt (n := m + 1) (· = g) y a) ∧
                    let T : ComplexModel (m + 1) → Y := fun z =>
                      (complexChartAt (n := m + 1) y).val.symm (Φ.invFun z)
                    ∃ (H : ComplexModel (m + 1) → ℝ) (r : ℝ), 0 < r ∧
                      ContDiffOn ℝ ∞ H (ball 0 r) ∧
                      ContDiffOn ℝ ∞ (fun z => Real.log (H z)) (ball 0 r) ∧
                      ∀ z ∈ ball 0 r, 0 < H z ∧
                        density F ρ u k (f (T z)) = ‖g (T z)‖ ^ 2 * H z := by
  classical
  obtain ⟨F, hF⟩ := exists_fixed_cover_smooth_squared_kernel_densities
    (n := m + 1) (X := X) (Nat.zero_lt_succ m)
  refine ⟨F, fun θ u hu => ?_⟩
  obtain ⟨ρ, hρ, hlevels⟩ := hF θ u hu
  refine ⟨ρ, hρ, fun k hk => ?_⟩
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  obtain ⟨Y, tY, chY, cmY, f, D, E, hπ, hpb, hE, hsupp, hzero, hiso, hall⟩ :=
    ActualSimultaneousPrincipalizedAtlasKernels.exists_principalization_all_atlas_smooth_positive_kernels
      hu hkR
  let := tY
  let := chY
  let := cmY
  refine ⟨(hlevels k hk).2.1, Y, tY, chY, cmY, f, D, E,
    hπ, hpb, hE, hsupp, hzero, hiso, ?_⟩
  intro y
  obtain ⟨S, Φ, hsrc, h0, _, _, _, g, hgy, hgen, hkernel⟩ := hall y
  refine ⟨Φ, hsrc, h0, g, hgy, hgen, ?_⟩
  have hf := fun t => hπ.isBlowupSequence.contMDiff t
  apply resolved_factor_at_point F ρ hρ u k y hf Φ hsrc h0 g
  intro j
  have hx := F.closure_V_subset_chartPatch j.val j.property
  let a := (F.bergmanRadius j.val + F.potentialRadius j.val) / 2
  have hβa : F.bergmanRadius j.val < a := by
    dsimp only [a]; linarith [F.bergmanRadius_lt_potentialRadius j.val]
  have haP : a < F.potentialRadius j.val := by
    dsimp only [a]; linarith [F.bergmanRadius_lt_potentialRadius j.val]
  obtain ⟨hBw, Q, r, hr, _, hQ, heq⟩ := hkernel (F.chart j.val) hx.1
    (ball (F.center j.val) (F.potentialRadius j.val)) (ρ j.val) (hρ j.val)
    (ball (F.center j.val) a) isOpen_ball (convex_ball _ _) isBounded_ball
    (closure_ball_subset_closedBall.trans (closedBall_subset_ball haP))
    (ball (F.center j.val) (F.bergmanRadius j.val)) isOpen_ball
    (closure_ball_subset_closedBall.trans (closedBall_subset_ball hβa)) hx.2
  exact ⟨hBw, Q, r, hr, hQ, fun z hz => ⟨(heq z hz).1, (heq z hz).2.2⟩⟩

end SGPT.Foundations.Analysis.Pending.ActualResolvedSquaredBergmanDensity

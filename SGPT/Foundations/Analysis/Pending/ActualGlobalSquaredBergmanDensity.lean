import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationFixedCover
import SGPT.Foundations.Analysis.Pending.BergmanKernelSmooth
import SGPT.Foundations.Analysis.Pending.DemaillyApproximation
import SGPT.Foundations.Analysis.Pending.GlobalTubeFunction

set_option autoImplicit false

/-! # Natural global squared-cutoff Bergman densities

A fixed cover is chosen before every original background, potential and level.
The actual weighted kernels, their entire smooth square norms and genuine
support-zero extensions give a global smooth density, including all poles.
This is the density axis of gentle gluing, not a QEA or curvature certificate.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualGlobalSquaredBergmanDensity

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  BergmanKernelSmooth BergmanSupWeight GlobalTubeFunction

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The actual diagonal kernel with its smooth theta-potential gauge. -/
def localDensity (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (k : ℕ) (j : F.t) : X → ℝ :=
  fun x => Real.exp (-(k : ℝ) * ρ j ((F.chart j).val x)) *
    (bergmanSup (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z))
      ((F.chart j).val x)).toReal

/-- A finite sum of the actual squared-cutoff kernels, extended by zero. -/
def density (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (k : ℕ) : X → ℝ :=
  fun x => ∑ j : F.t, bumpExtend (F.cover.V j)
    (fun y => F.cover.χ j y * F.cover.χ j y) (localDensity F ρ u k j) x

private theorem original_bergmanWeight (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {k : ℕ} (hk : 0 < k) (j : F.t) :
    BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z)) := by
  let B := ball (F.center j) (F.bergmanRadius j)
  let Ω := ball (F.center j) (F.potentialRadius j)
  let Ψ := correctedWeight (F.chart j) (ρ j) u
  have hBΩ : B ⊆ Ω := ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le
  have hΨ : PlurisubharmonicOn Ψ Ω := F.plurisubharmonicOn_correctedWeight hρ hu.1 j
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  refine ⟨isOpen_ball, DemaillyApproximation.aemeasurable_multiplierWeight_restrict
    isOpen_ball (hΨ.upperSemicontinuousOn.mono hBΩ) hkR.ne', ?_⟩
  intro z hz
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  have hcb : closedBall z (ε / 2) ⊆ B :=
    (closedBall_subset_ball (by linarith)).trans hεB
  obtain ⟨C, _, hC⟩ := hΨ.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z (ε / 2)) (hcb.trans hBΩ)
  refine ⟨Real.exp (-(k * C)), Real.exp_pos _, ε / 2, by positivity, hcb, fun t ht => ?_⟩
  rw [← multiplierWeight_coe]
  exact multiplierWeight_antitone hkR.le (hC t ht)

private theorem localDensity_chartSmoothOn (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} {k : ℕ} (j : F.t)
    (hBw : BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z))) :
    ChartSmoothOn n (localDensity F ρ u k j) (F.cover.V j) := by
  intro e z hz
  have hpatch := F.V_subset_chartPatch j hz.2
  have hzt : z ∈ (chartTransition e (F.chart j)).source := ⟨hz.1, hpatch.1⟩
  have hzB : chartTransition e (F.chart j) z ∈
      ball (F.center j) (F.bergmanRadius j) := hpatch.2
  have hzΩ : chartTransition e (F.chart j) z ∈
      ball (F.center j) (F.potentialRadius j) :=
    ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le hzB
  have ht := chartTransition_contDiffAt_real e (F.chart j) hzt
  have hr := ((hρ j).2.2.1.contDiffAt (isOpen_ball.mem_nhds hzΩ)).comp z ht
  have hK := ((contDiffOn_toReal_bergmanSup hBw).contDiffAt
    (isOpen_ball.mem_nhds hzB)).comp z ht
  exact (((contDiffAt_const.mul hr).exp).mul hK).contDiffWithinAt

private theorem term_nonneg (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (k : ℕ) (j : F.t) (x : X) :
    0 ≤ bumpExtend (F.cover.V j) (fun y => F.cover.χ j y * F.cover.χ j y)
      (localDensity F ρ u k j) x :=
  bumpExtend_nonneg (fun y => mul_self_nonneg (F.cover.χ j y))
    (fun _ => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) x

private theorem smooth_density (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} {k : ℕ}
    (hBw : ∀ j, BergmanWeight (ball (F.center j) (F.bergmanRadius j))
      (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z))) :
    ChartSmooth (n := n) (density F ρ u k) := by
  have hterm : ∀ j : F.t, ChartSmooth (n := n)
      (bumpExtend (F.cover.V j) (fun y => F.cover.χ j y * F.cover.χ j y)
        (localDensity F ρ u k j)) := by
    intro j
    apply chartSmooth_bumpExtend (F.cover.isOpen_V j)
      (fun e => (F.cover.χ_smooth j e).mul (F.cover.χ_smooth j e))
      (localDensity_chartSmoothOn F hρ j (hBw j))
    exact tsupport_mul_subset_left.trans (F.cover.tsupport_χ_subset j)
  intro e
  exact ContDiffOn.sum fun j _ => hterm j e

private theorem core_lower (F : FixedChartCover n X)
    (ρ : F.t → ComplexModel n → ℝ) (u : X → EReal) (k : ℕ) (x : X) :
    ∃ j : F.t, x ∈ F.cover.U j ∧ localDensity F ρ u k j x ≤ density F ρ u k x := by
  classical
  obtain ⟨j, hj⟩ := F.cover.cover x
  refine ⟨j, hj, ?_⟩
  have hv := F.cover.U_subset_V j hj
  have ht := Finset.single_le_sum (fun l _ => term_nonneg F ρ u k l x)
    (Finset.mem_univ j)
  simpa only [density, bumpExtend_of_mem hv, F.cover.χ_eq_one j x hj,
    one_mul] using ht

private theorem localDensity_pos_of_finite (F : FixedChartCover n X)
    {θ : ClosedRealOneOneForm n X} {ρ : F.t → ComplexModel n → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential θ.val (F.chart j)
      (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    {k : ℕ} (hk : 0 < k) (j : F.t) {x : X} (hx : x ∈ F.cover.U j)
    (hux : u x ≠ ⊥) : 0 < localDensity F ρ u k j x := by
  let B := ball (F.center j) (F.bergmanRadius j)
  let Ψ := correctedWeight (F.chart j) (ρ j) u
  have hpatch := F.V_subset_chartPatch j (F.cover.U_subset_V j hx)
  have hΨ : PlurisubharmonicOn Ψ B :=
    (F.plurisubharmonicOn_correctedWeight hρ hu.1 j).mono
      (ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le)
  have hfinite : Ψ ((F.chart j).val x) ≠ ⊥ := by
    simpa only [Ψ, correctedWeight, chartFunction, (F.chart j).val.left_inv hpatch.1]
      using (by
        rw [← EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hux,
          ← EReal.coe_add]
        exact EReal.coe_ne_bot _ :
          u x + (ρ j ((F.chart j).val x) : EReal) ≠ ⊥)
  let R := ‖F.center j‖ + F.bergmanRadius j + 1
  have hR : 0 < R := by dsimp [R]; linarith [norm_nonneg (F.center j), F.bergmanRadius_pos j]
  obtain ⟨C, hC, hOT⟩ := exists_one_le_mul_bergmanSup n R hR
  have hbounded : ∀ z ∈ B, ‖z‖ < R := by
    intro z hz
    have hz' : ‖z - F.center j‖ < F.bergmanRadius j := by simpa only [B, mem_ball, dist_eq_norm] using hz
    have hn := norm_le_norm_sub_add z (F.center j)
    dsimp [R]; linarith
  have hpos := (hOT B isOpen_ball (convex_ball _ _) hbounded Ψ hΨ k
    (Nat.cast_pos.mpr hk) ((F.chart j).val x) hpatch.2 hfinite).2.1
  have hpos' : 0 < bergmanSup B (fun z => multiplierWeight k (Ψ z)) ((F.chart j).val x) := by
    rw [QuantitativeRegularizationBergmanInstanceTransport.bergmanSup_congr_instance
      (inferInstance : MeasurableSpace (ComplexModel n)) inferInstance
      (borel (ComplexModel n))
      (@BorelSpace.mk (ComplexModel n) _ (borel (ComplexModel n)) rfl)]
    exact hpos
  have hBw := original_bergmanWeight F hρ hu hk j
  exact mul_pos (Real.exp_pos _) (ENNReal.toReal_pos hpos'.ne'
    (bergmanSup_ne_top hBw hpatch.2))

/-- The fixed geometry and original PSH data internally produce entire smooth
squared-cutoff kernels before every level, including all common zeros. -/
theorem exists_fixed_cover_smooth_squared_kernel_densities (hn : 0 < n) [CompactSpace X] :
    ∃ F : FixedChartCover n X,
      ∀ (θ : ClosedRealOneOneForm n X) (u : X → EReal), IsThetaPshPotential θ.val u →
        ∃ ρ : F.t → ComplexModel n → ℝ,
          (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
            (ball (F.center j) (F.potentialRadius j)) (ρ j)) ∧
          ∀ k : ℕ, 0 < k →
            (∀ j, BergmanWeight (ball (F.center j) (F.bergmanRadius j))
              (fun z => multiplierWeight k (correctedWeight (F.chart j) (ρ j) u z))) ∧
            ChartSmooth (n := n) (density F ρ u k) ∧
            (∀ x, 0 ≤ density F ρ u k x) ∧
            (∀ x, ∃ j : F.t, x ∈ F.cover.U j ∧
              localDensity F ρ u k j x ≤ density F ρ u k x) ∧
            ∀ x, u x ≠ ⊥ → 0 < density F ρ u k x := by
  obtain ⟨F⟩ := exists_fixedChartCover (Z := X) hn
  refine ⟨F, fun θ u hu => ?_⟩
  obtain ⟨ρ, hρ⟩ := F.exists_potentials θ
  refine ⟨ρ, hρ, fun k hk => ?_⟩
  have hBw := fun j => original_bergmanWeight F hρ hu hk j
  refine ⟨hBw, smooth_density F hρ hBw, ?_, core_lower F ρ u k, ?_⟩
  · exact fun x => Finset.sum_nonneg fun j _ => term_nonneg F ρ u k j x
  · intro x hux
    obtain ⟨j, hj, hle⟩ := core_lower F ρ u k x
    exact (localDensity_pos_of_finite F hρ hu hk j hj hux).trans_le hle

end SGPT.Foundations.Analysis.Pending.ActualGlobalSquaredBergmanDensity

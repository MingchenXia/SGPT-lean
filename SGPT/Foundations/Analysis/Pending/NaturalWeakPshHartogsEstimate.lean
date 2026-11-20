import SGPT.Foundations.Analysis.Pending.NaturalPshHartogsBallEstimate
import SGPT.Foundations.Analysis.Pending.NaturalHartogsFixedCutoff

/-!
# Weak native tests yield uniform moving-center Hartogs upper bounds

Only one genuinely constructed fixed native test is used to choose the
convergence event. This event belongs to the original nontrivial filter;
an ultrafilter event is not substituted by a natural-number tail.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace Function
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalWeakPshHartogsEstimate

open NaturalPshHartogsBallEstimate NaturalHartogsFixedCutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- The same native test deficit is controlled by the original singular finite-center submean. -/
theorem test_deficit_le_ball_center {u : E → EReal}
    (hu : PlurisubharmonicOn u Ω) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hΩ : IsPreconnected (Ω : Set E)) (hne : ∃ a ∈ Ω, u a ≠ ⊥)
    (y : E) {R C : ℝ} (hR : 0 < R) (hB : closedBall y R ⊆ Ω)
    (hy : u y ≠ ⊥) (hC : ∀ z ∈ ball y R, u z ≤ (C : EReal))
    (φ : 𝓓(Ω, ℝ)) (hφ : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : tsupport φ ⊆ ball y R) :
    (∫ z, φ z * (C - (u z).toReal) ∂μ) ≤
      (μ (ball y R)).toReal * (C - (u y).toReal) := by
  have hui := hu.locallyIntegrableOn_toReal μ hΩ hne
  have hi : IntegrableOn (fun z => (u z).toReal) (ball y R) μ :=
    (hui.integrableOn_compact_subset hB (isCompact_closedBall y R)).mono_set
      ball_subset_closedBall
  let _ : IsFiniteMeasure (μ.restrict (ball y R)) := ⟨by simpa using (measure_ball_lt_top (μ := μ) (x := y) (r := R))⟩
  have hc : IntegrableOn (fun _ : E => C) (ball y R) μ := integrable_const C
  have hpi : Integrable (fun z => φ z * (u z).toReal) μ := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hui
  have hφi : Integrable (fun z => φ z) μ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hdi : Integrable (fun z => φ z * (C - (u z).toReal)) μ := by
    exact ((hφi.mul_const C).sub hpi).congr (Eventually.of_forall (fun z => by
      change φ z * C - φ z * (u z).toReal = φ z * (C - (u z).toReal)
      ring))
  have haereal : ∀ᵐ z ∂μ.restrict (ball y R), (u z).toReal ≤ C := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (ball_subset_closedBall.trans hB) (hu.ae_coe_toReal μ hΩ hne),
      ae_restrict_mem measurableSet_ball] with z huz hz
    exact EReal.coe_le_coe_iff.mp (huz.le.trans (hC z hz))
  have hweighted : (∫ z, φ z * (C - (u z).toReal) ∂μ) ≤
      ∫ z in ball y R, C - (u z).toReal ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hsupp h)), zero_mul])]
    apply integral_mono_ae hdi.integrableOn (hc.sub hi)
    filter_upwards [haereal] with z hz
    exact mul_le_of_le_one_left (sub_nonneg.mpr hz) (hφ z).2
  have hread : (∫ z in ball y R, C - (u z).toReal ∂μ) =
      (μ (ball y R)).toReal * C - ∫ z in ball y R, (u z).toReal ∂μ := by
    rw [integral_sub hc hi]
    simp [measureReal_def]
  have hmean := real_ball_submean_of_ne_bot hu.discPshOn μ y hR hB hy
  rw [hread] at hweighted
  nlinarith

/-- The original pole-inclusive center is bounded by this actual fixed test deficit. -/
theorem original_center_le_of_test_deficit {u : E → EReal}
    (hu : PlurisubharmonicOn u Ω) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hΩ : IsPreconnected (Ω : Set E)) (hne : ∃ a ∈ Ω, u a ≠ ⊥)
    (y : E) {R C : ℝ} (hR : 0 < R) (hB : closedBall y R ⊆ Ω)
    (hC : ∀ z ∈ ball y R, u z ≤ (C : EReal))
    (φ : 𝓓(Ω, ℝ)) (hφ : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1)
    (hsupp : tsupport φ ⊆ ball y R) :
    u y ≤ ((C - (∫ z, φ z * (C - (u z).toReal) ∂μ) /
      (μ (ball y R)).toReal : ℝ) : EReal) := by
  by_cases hy : u y = ⊥
  · rw [hy]
    exact bot_le
  have hyt : u y ≠ ⊤ := (hu y (hB (mem_closedBall_self hR.le))).ne_top
  have hm : 0 < (μ (ball y R)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos μ y hR).ne' measure_ball_ne_top
  have hd := test_deficit_le_ball_center hu μ hΩ hne y hR hB hy hC φ hφ hsupp
  have hdiv : (∫ z, φ z * (C - (u z).toReal) ∂μ) / (μ (ball y R)).toReal ≤
      C - (u y).toReal := (div_le_iff₀ hm).mpr (by simpa only [mul_comm] using hd)
  rw [← EReal.coe_toReal hyt hy, EReal.coe_le_coe_iff]
  linarith

/-- One event of the actual weak convergence filter controls all nearby moving centers. -/
theorem eventually_le_on_ball_of_weak_tests
    {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → E → EReal} {v : E → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (hv : PlurisubharmonicOn v Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsPreconnected (Ω : Set E))
    (hnu : ∀ i, ∃ a ∈ Ω, u i a ≠ ⊥) (hnv : ∃ a ∈ Ω, v a ≠ ⊥)
    (hlim : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ z, φ z * (u i z).toReal ∂μ) l
        (𝓝 (∫ z, φ z * (v z).toReal ∂μ)))
    (x : E) {R A C δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hK : closedBall x (3 * R) ⊆ Ω)
    (hC : ∀ i z, z ∈ closedBall x (3 * R) → u i z ≤ (C : EReal))
    (hA : ∀ z ∈ closedBall x (3 * R), v z ≤ (A : EReal)) (hAC : A < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ i in l, ∀ y ∈ ball x ε, u i y ≤ ((A + δ : ℝ) : EReal) := by
  let m : ℝ := (μ (ball x R)).toReal
  have hm : 0 < m := ENNReal.toReal_pos
    (Metric.measure_ball_pos μ x hR).ne' measure_ball_ne_top
  let η : ℝ := δ / (2 * (C - A))
  have hη : 0 < η := div_pos hδ (mul_pos (by norm_num) (sub_pos.mpr hAC))
  have hsmall : closedBall x R ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith : R ≤ 3 * R)).trans hK
  obtain ⟨φ, hφ, hmass, ε₀, hε₀, hsupp⟩ :=
    exists_testFunction_mass_ge_and_moving_support μ x hR hη hsmall
  have hsuppx : tsupport φ ⊆ closedBall x (3 * R) :=
    (hsupp x (mem_ball_self hε₀)).trans
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hφi : Integrable (fun z => φ z) μ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hread : ∀ (w : E → EReal), LocallyIntegrableOn (fun z => (w z).toReal) Ω μ →
      (∫ z, φ z * (C - (w z).toReal) ∂μ) =
        C * (∫ z, φ z ∂μ) - ∫ z, φ z * (w z).toReal ∂μ := by
    intro w hwi
    have hpi : Integrable (fun z => φ z * (w z).toReal) μ := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hwi
    simp_rw [mul_sub]
    rw [integral_sub (hφi.mul_const C) hpi, integral_mul_const, mul_comm (∫ z, φ z ∂μ)]
  let D : ι → ℝ := fun i => ∫ z, φ z * (C - (u i z).toReal) ∂μ
  let d : ℝ := ∫ z, φ z * (C - (v z).toReal) ∂μ
  have hui : ∀ i, LocallyIntegrableOn (fun z => (u i z).toReal) Ω μ :=
    fun i => (hu i).locallyIntegrableOn_toReal μ hΩ (hnu i)
  have hvi := hv.locallyIntegrableOn_toReal μ hΩ hnv
  have hD : Tendsto D l (𝓝 d) := by
    have ht := (tendsto_const_nhds (x := C * ∫ z, φ z ∂μ)).sub (hlim φ)
    have hfun : D = fun i => C * (∫ z, φ z ∂μ) - ∫ z, φ z * (u i z).toReal ∂μ :=
      funext (fun i => hread (u i) (hui i))
    rw [hfun, show d = C * (∫ z, φ z ∂μ) - ∫ z, φ z * (v z).toReal ∂μ from hread v hvi]
    exact ht
  have hdlower : (C - A) * (∫ z, φ z ∂μ) ≤ d := by
    have hpi : Integrable (fun z => φ z * (v z).toReal) μ := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hvi
    have hdi : Integrable (fun z => φ z * (C - (v z).toReal)) μ := by
      exact ((hφi.mul_const C).sub hpi).congr (Eventually.of_forall (fun z => by
        change φ z * C - φ z * (v z).toReal = φ z * (C - (v z).toReal)
        ring))
    rw [show (C - A) * (∫ z, φ z ∂μ) = ∫ z, φ z * (C - A) ∂μ by
      rw [integral_mul_const, mul_comm]]
    apply integral_mono_ae (hφi.mul_const (C - A)) hdi
    have hva := (ae_restrict_iff' Ω.isOpen.measurableSet).mp (hv.ae_coe_toReal μ hΩ hnv)
    filter_upwards [hva] with z hvz
    by_cases hz : z ∈ tsupport φ
    · have hreal : (v z).toReal ≤ A := EReal.coe_le_coe_iff.mp
        ((hvz (φ.tsupport_subset hz)).le.trans (hA z (hsuppx hz)))
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left hreal C) (hφ z).1
    · rw [image_eq_zero_of_notMem_tsupport hz]
      simp
  have hdlower' : (C - A) * ((1 - η) * m) ≤ d :=
    (mul_le_mul_of_nonneg_left hmass (sub_pos.mpr hAC).le).trans hdlower
  have hthreshold : d - δ * m / 2 < d := by nlinarith
  have hevent := hD.eventually (Ioi_mem_nhds hthreshold)
  refine ⟨min ε₀ R, lt_min hε₀ hR, ?_⟩
  filter_upwards [hevent] with i hi
  intro y hy
  have hy₀ : y ∈ ball x ε₀ := (ball_subset_ball (min_le_left _ _)) hy
  have hyR : dist y x < R := (ball_subset_ball (min_le_right _ _)) hy
  have hballK : closedBall y R ⊆ closedBall x (3 * R) := by
    intro z hz
    have hzR : dist z y ≤ R := hz
    show dist z x ≤ 3 * R
    exact (dist_triangle z y x).trans (by linarith)
  have hmoving : (μ (ball y R)).toReal = m := by
    dsimp [m]
    rw [μ.addHaar_ball_center y R, μ.addHaar_ball_center x R]
  have hcenter := original_center_le_of_test_deficit (hu i) μ hΩ (hnu i) y hR
    (hballK.trans hK) (fun z hz => hC i z (hballK (ball_subset_closedBall hz)))
    φ hφ (hsupp y hy₀)
  rw [hmoving] at hcenter
  have hηeq : (C - A) * η = δ / 2 := by
    dsimp [η]
    field_simp [(sub_pos.mpr hAC).ne']
  have hreal : C - D i / m ≤ A + δ := by
    have hDlower : (C - A) * ((1 - η) * m) - δ * m / 2 ≤ D i := by
      dsimp [D] at hi
      linarith
    have hquot : C - (A + δ) ≤ D i / m := (le_div_iff₀ hm).mpr (by
      nlinarith [congrArg (fun t : ℝ => t * m) hηeq])
    linarith
  exact hcenter.trans (EReal.coe_le_coe_iff.mpr hreal)

end SGPT.Foundations.Analysis.Pending.NaturalWeakPshHartogsEstimate

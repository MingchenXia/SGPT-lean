import SGPT.Foundations.Analysis.Pending.NaturalWeakPshHartogsEstimate

/-!
# Actual weak tests under finite potential correction and local Hartogs recovery

All convergence events remain in the original nontrivial filter. Pole sets
are retained in the corrected functions until original PSH almost-everywhere
finiteness identifies their actual real representatives.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalWeakPotentialHartogs

open NaturalWeakPshHartogsEstimate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- Adding one continuous finite potential preserves the actual native weak tests. -/
theorem weak_tests_tendsto_corrected_of_continuous_potential
    {ι : Type*} {l : Filter ι} [NeBot l] {f : ι → E → EReal} {v : E → EReal}
    {ρ : E → ℝ} (hρ : ContinuousOn ρ Ω)
    (hf : ∀ i, PlurisubharmonicOn (fun z => f i z + (ρ z : EReal)) Ω)
    (hv : PlurisubharmonicOn (fun z => v z + (ρ z : EReal)) Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsPreconnected (Ω : Set E))
    (hnf : ∀ i, ∃ z ∈ Ω, f i z + (ρ z : EReal) ≠ ⊥)
    (hnv : ∃ z ∈ Ω, v z + (ρ z : EReal) ≠ ⊥)
    (hlim : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ z, φ z * (f i z).toReal ∂μ) l
        (𝓝 (∫ z, φ z * (v z).toReal ∂μ))) :
    ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ z, φ z * (f i z + (ρ z : EReal)).toReal ∂μ) l
        (𝓝 (∫ z, φ z * (v z + (ρ z : EReal)).toReal ∂μ)) := by
  have hρi : LocallyIntegrableOn ρ Ω μ := hρ.locallyIntegrableOn Ω.isOpen.measurableSet
  have hread : ∀ (g : E → EReal),
      PlurisubharmonicOn (fun z => g z + (ρ z : EReal)) Ω →
      (∃ z ∈ Ω, g z + (ρ z : EReal) ≠ ⊥) →
      ∀ φ : 𝓓(Ω, ℝ),
      (∫ z, φ z * (g z + (ρ z : EReal)).toReal ∂μ) =
        (∫ z, φ z * (g z).toReal ∂μ) + ∫ z, φ z * ρ z ∂μ := by
    intro g hg hng φ
    have hgi := hg.locallyIntegrableOn_toReal μ hΩ hng
    have hfinite := hg.ae_finite μ hΩ hng
    have heq : ∀ᵐ z ∂μ.restrict Ω,
        (g z + (ρ z : EReal)).toReal = (g z).toReal + ρ z := by
      filter_upwards [hfinite] with z hz
      have hgt : g z ≠ ⊤ := by
        intro h
        simpa [h] using hz.1
      have hgb : g z ≠ ⊥ := by
        intro h
        simpa [h] using hz.2
      simp only [EReal.toReal_add hgt hgb (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_coe]
    have hraw : LocallyIntegrableOn (fun z => (g z).toReal) Ω μ :=
      (hgi.sub hρi).congr (heq.mono (fun z hz => by
        change (g z + (ρ z : EReal)).toReal - ρ z = (g z).toReal
        linarith))
    have hrawφ : Integrable (fun z => φ z * (g z).toReal) μ := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hraw
    have hρφ : Integrable (fun z => φ z * ρ z) μ := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hρi
    have heq' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp heq
    calc
      _ = ∫ z, φ z * (g z).toReal + φ z * ρ z ∂μ := by
        apply integral_congr_ae
        filter_upwards [heq'] with z hz
        by_cases hzΩ : z ∈ Ω
        · rw [hz hzΩ, mul_add]
        · rw [image_eq_zero_of_notMem_tsupport (fun h => hzΩ (φ.tsupport_subset h))]
          simp
      _ = _ := integral_add hrawφ hρφ
  intro φ
  have h := (hlim φ).add (tendsto_const_nhds (x := ∫ z, φ z * ρ z ∂μ))
  simpa only [← hread v hv hnv φ, ← hread (f _) (hf _) (hnf _) φ] using h

/-- Weak original PSH tests produce one upper event on an actual neighborhood, including poles. -/
theorem eventually_locally_le_of_weak_tests
    {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → E → EReal} {v : E → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (hv : PlurisubharmonicOn v Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsPreconnected (Ω : Set E))
    (hnu : ∀ i, ∃ z ∈ Ω, u i z ≠ ⊥) (hnv : ∃ z ∈ Ω, v z ≠ ⊥)
    (hlim : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ z, φ z * (u i z).toReal ∂μ) l
        (𝓝 (∫ z, φ z * (v z).toReal ∂μ)))
    {C : ℝ} (hC : ∀ i z, z ∈ Ω → u i z ≤ (C : EReal))
    (x : E) (hx : x ∈ Ω) {a : ℝ} (ha : v x < (a : EReal)) :
    ∃ ε : ℝ, 0 < ε ∧ ball x ε ⊆ Ω ∧
      ∀ᶠ i in l, ∀ y ∈ ball x ε, u i y ≤ (a : EReal) := by
  obtain ⟨b, hvb, hba⟩ := EReal.exists_rat_btwn_of_lt ha
  have hbaR : (b : ℝ) < a := EReal.coe_lt_coe_iff.mp hba
  have hvupper : ∀ᶠ y in 𝓝 x, v y < ((b : ℝ) : EReal) := by
    have h := hv.upperSemicontinuousOn x hx ((b : ℝ) : EReal) hvb
    rw [nhdsWithin_eq_nhds.mpr (Ω.isOpen.mem_nhds hx)] at h
    exact h
  have hnbhd : {y | y ∈ Ω ∧ v y < ((b : ℝ) : EReal)} ∈ 𝓝 x := by
    filter_upwards [Ω.isOpen.mem_nhds hx, hvupper] with y hy hyb
    exact ⟨hy, hyb⟩
  obtain ⟨t, ht, hlocal⟩ := Metric.mem_nhds_iff.mp hnbhd
  have hBt : ball x t ⊆ Ω := fun y hy => (hlocal hy).1
  by_cases hCb : C ≤ (b : ℝ)
  · refine ⟨t, ht, hBt, Eventually.of_forall (fun i y hy => ?_)⟩
    exact (hC i y (hBt hy)).trans (EReal.coe_le_coe_iff.mpr (hCb.trans hbaR.le))
  let R : ℝ := t / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hKBt : closedBall x (3 * R) ⊆ ball x t :=
    closedBall_subset_ball (by dsimp [R]; linarith)
  obtain ⟨ε, hε, hevent⟩ := eventually_le_on_ball_of_weak_tests hu hv μ hΩ hnu hnv hlim
    x hR (sub_pos.mpr hbaR) (hKBt.trans hBt)
    (fun i y hy => hC i y (hBt (hKBt hy)))
    (fun y hy => (hlocal (hKBt hy)).2.le) (lt_of_not_ge hCb)
  refine ⟨min ε R, lt_min hε hR, ?_, ?_⟩
  · exact ((ball_subset_ball (min_le_right _ _)).trans
      (ball_subset_ball (by dsimp [R]; linarith))).trans hBt
  · filter_upwards [hevent] with i hi
    intro y hy
    have h := hi y ((ball_subset_ball (min_le_left _ _)) hy)
    simpa only [add_sub_cancel] using h

end SGPT.Foundations.Analysis.Pending.NaturalWeakPotentialHartogs

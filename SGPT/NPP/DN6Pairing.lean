import SGPT.NPP.DN6Taylor
import SGPT.NPP.DN6Adjoint
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The generator of a fibrewise average, paired with a test function (chart form)

Lane DN6 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 7, proof of
`eq:chern-smoothing-generator`).  In a chart: `G : E × E → E` smooth with `G(z, 0) = z`, a smooth
weight `k(z, ξ)`, even in `ξ`, vanishing for `‖ξ‖ > R` and of mass one near `z₀`, and the fibrewise
average `Ψ_g(z, t) = ∫ g(G(z, tξ)) k(z, ξ) dξ` (`fibreAverage`).  For every smooth `ψ` supported
near `z₀` there are a compact set `C` and a continuous `φ` vanishing off `C` such that, **for every
measurable `g` integrable on `C`**,
`(∫ Ψ_g(z, t) ψ(z) dz - ∫ g ψ) / t² → ∫ g φ` as `t → 0⁺` (`exists_tendsto_pairing`).

Proof (FPT): Fubini and the change of variables `y = G(z, tξ)` (`DN6Adjoint`) give
`∫ Ψ_g(·, t) ψ = ∫ g(y) Ψ*_t(y) dy` with `Ψ*_t(y) = ∫ Â((y, tξ), ξ) dξ`,
`Â((y, η), ξ) = A(y, η) k(G(·, η)⁻¹ y, ξ)` (`adjWeight`), `∫ Â((y, 0), ξ) dξ = ψ(y)`; the uniform
even expansion (`DN6Taylor`) gives `(Ψ*_t - ψ)/t² → φ := Q_Â` uniformly.  The pointwise companion
`tendstoUniformlyOn_fibreAverage` expands `Ψ_g` itself for smooth `g`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN6

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The fibrewise average `Ψ_g(z, t) = ∫ g(G(z, tξ)) k(z, ξ) dξ` with a weight `k(z, ξ)`. -/
def fibreAverage (G : E × E → E) (k : E × E → ℝ) (g : E → ℝ) (z : E) (t : ℝ) : ℝ :=
  ∫ ξ, g (G (z, t • ξ)) * k (z, ξ) ∂μ

/-- The adjoint weight `Â((y, η), ξ) = A(y, η) k(G(·, η)⁻¹(y), ξ)`. -/
def adjWeight (A : E × E → ℝ) (inv : E × E → E) (k : E × E → ℝ) : (E × E) × E → ℝ :=
  fun q => A q.1 * k (inv q.1, q.2)

variable {μ}

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Products with a bounded measurable function vanishing off `C` are integrable. -/
theorem integrable_mul_of_vanish {g h : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    (hg : IntegrableOn g C μ) (hh : AEStronglyMeasurable h μ) {M : ℝ} (hM : ∀ y, |h y| ≤ M)
    (hvan : ∀ y ∉ C, h y = 0) : Integrable (fun y => g y * h y) μ := by
  have hgi : Integrable (C.indicator g) μ := (integrable_indicator_iff hC).mpr hg
  have h1 := hgi.bdd_mul (c := M) hh (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hM y)
  refine h1.congr (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ C
  · simp [indicator_of_mem hy, mul_comm]
  · simp [indicator_of_notMem hy, hvan y hy]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Uniform convergence on `C` of multipliers vanishing off `C` passes to the pairing with a
function integrable on `C`. -/
theorem tendsto_integral_mul_of_tendstoUniformlyOn {l : Filter ℝ} {g : E → ℝ} {C : Set E}
    (hC : MeasurableSet C) (hg : IntegrableOn g C μ) {D : ℝ → E → ℝ} {φ : E → ℝ}
    (hD : TendstoUniformlyOn D φ l C) (hDv : ∀ t, ∀ y ∉ C, D t y = 0) (hφv : ∀ y ∉ C, φ y = 0)
    (hDi : ∀ᶠ t in l, Integrable (fun y => g y * D t y) μ)
    (hφi : Integrable (fun y => g y * φ y) μ) :
    Tendsto (fun t => ∫ y, g y * D t y ∂μ) l (𝓝 (∫ y, g y * φ y ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set I := ∫ y in C, |g y| ∂μ with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg hC fun _ _ => abs_nonneg _
  have hev := Metric.tendstoUniformlyOn_iff.mp hD (ε / (2 * (I + 1))) (by positivity)
  filter_upwards [hev, hDi] with t ht hti
  rw [Real.dist_eq, ← integral_sub hti hφi]
  have hb : ∀ y, ‖g y * D t y - g y * φ y‖ ≤ ε / (2 * (I + 1)) * C.indicator (fun y => |g y|) y := by
    intro y
    by_cases hy : y ∈ C
    · rw [indicator_of_mem hy, ← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
      have h := ht y hy
      rw [Real.dist_eq, abs_sub_comm] at h
      exact mul_le_mul_of_nonneg_right h.le (abs_nonneg _)
    · rw [indicator_of_notMem hy, hDv t y hy, hφv y hy]; simp
  have hbi : Integrable (fun y => ε / (2 * (I + 1)) * C.indicator (fun y => |g y|) y) μ :=
    ((integrable_indicator_iff hC).mpr hg.abs).const_mul _
  calc |∫ y, g y * D t y - g y * φ y ∂μ| = ‖∫ y, g y * D t y - g y * φ y ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ε / (2 * (I + 1)) * C.indicator (fun y => |g y|) y ∂μ :=
        norm_integral_le_of_norm_le hbi (Eventually.of_forall hb)
    _ = ε / (2 * (I + 1)) * I := by
        rw [integral_const_mul, integral_indicator hC]
    _ < ε := by
        have h1 : ε / (2 * (I + 1)) * I ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

/-- The second derivative of a function vanishing near a point vanishes there. -/
theorem fderiv_fderiv_eq_zero_of_eventually {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : F → ℝ} {p : F} (h : A =ᶠ[𝓝 p] fun _ => 0) : fderiv ℝ (fderiv ℝ A) p = 0 := by
  have h1 : fderiv ℝ A =ᶠ[𝓝 p] fun _ => 0 := by
    obtain ⟨U, hU, hUo, hpU⟩ := (_root_.eventually_nhds_iff.mp h)
    filter_upwards [hUo.mem_nhds hpU] with q hq
    have hq' : A =ᶠ[𝓝 q] fun _ => 0 := _root_.eventually_nhds_iff.mpr ⟨U, hU, hUo, hq⟩
    rw [hq'.fderiv_eq]
    exact fderiv_const_apply 0
  rw [h1.fderiv_eq]
  exact fderiv_const_apply 0

/-! ### Fubini and the change of variables -/

section Main

variable {G : E × E → E} {k : E × E → ℝ}

/-- **The adjoint identity** `∫ Ψ_g(·, t) ψ = ∫ g Ψ*_t`, with `Ψ*_t(y) = ∫ Â((y, tξ), ξ) dξ`, and
the integrability of the right side. -/
theorem integral_fibreAverage_mul_eq {ψ : E → ℝ} {t₀ : ℝ} {C : Set E} {A : E × E → ℝ}
    {inv : E × E → E} (hA : IsAdjointDensity μ G ψ t₀ C A)
    (hI : IsAdjointInverse μ G ψ t₀ A inv) (hG : Continuous G) (hk : Continuous k) {R : ℝ}
    (hks : ∀ z ξ, R < ‖ξ‖ → k (z, ξ) = 0) (hÂ : Continuous (adjWeight A inv k))
    {g : E → ℝ} (hgm : StronglyMeasurable g) (hg : IntegrableOn g C μ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t * R < t₀) :
    ∫ z, fibreAverage μ G k g z t * ψ z ∂μ =
        ∫ y, g y * weightAverage μ (adjWeight A inv k) y t ∂μ ∧
      Integrable (fun y => g y * weightAverage μ (adjWeight A inv k) y t) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hCm : MeasurableSet C := hA.isCompact.isClosed.measurableSet
  set Â := adjWeight A inv k with hÂdef
  have hsmall : ∀ ξ : E, ‖ξ‖ ≤ R → ‖t • ξ‖ < t₀ := by
    intro ξ hξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_left hξ ht0).trans_lt ht
  have hÂs : ∀ q : (E × E) × E, R < ‖q.2‖ → Â q = 0 := fun q hq => by
    simp [hÂdef, adjWeight, hks _ _ hq]
  have hÂC : ∀ q : (E × E) × E, q.1.1 ∉ C → Â q = 0 := fun q hq => by
    simp [hÂdef, adjWeight, hA.vanish q.1 hq]
  have hÂcs : HasCompactSupport Â := by
    obtain ⟨K₁, hK₁, hK₁s⟩ : ∃ K₁ : Set (E × E), IsCompact K₁ ∧ tsupport A ⊆ K₁ :=
      ⟨_, hA.hasCompactSupport, subset_rfl⟩
    refine HasCompactSupport.intro (hK₁.prod (isCompact_closedBall (0 : E) R)) fun q hq => ?_
    simp only [mem_prod, mem_closedBall, dist_zero_right, not_and_or, not_le] at hq
    rcases hq with hq | hq
    · simp [hÂdef, adjWeight, image_eq_zero_of_notMem_tsupport fun h => hq (hK₁s h)]
    · exact hÂs q hq
  obtain ⟨M, hM⟩ := hÂ.bounded_above_of_compact_support hÂcs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ((0, 0), 0))
  set B := ∫ y in C, |g y| ∂μ with hB
  have hB0 : 0 ≤ B := setIntegral_nonneg hCm fun _ _ => abs_nonneg _
  have hψc : Continuous ψ := by
    have h : Continuous fun y : E => A (y, 0) :=
      hA.contDiff.continuous.comp (continuous_id.prodMk (continuous_const (y := (0 : E))))
    have he : (fun y => A (y, 0)) = ψ := funext hA.eq_zero
    rwa [he] at h
  have hgÂ : ∀ η ξ : E, Integrable (fun y => g y * Â ((y, η), ξ)) μ := fun η ξ =>
    integrable_mul_of_vanish hCm hg
      (hÂ.comp ((continuous_id.prodMk continuous_const).prodMk continuous_const)).aestronglyMeasurable
      (fun y => by simpa using hM ((y, η), ξ)) fun y hy => hÂC ((y, η), ξ) hy
  -- the first integrand, in the variables `(ξ, z)`
  set f₁ : E × E → ℝ := fun q => g (G (q.2, t • q.1)) * k (q.2, q.1) * ψ q.2 with hf₁
  have hf₁m : StronglyMeasurable f₁ := by
    have h1 : StronglyMeasurable fun q : E × E => g (G (q.2, t • q.1)) :=
      hgm.comp_measurable
        (hG.comp (continuous_snd.prodMk (continuous_const.smul continuous_fst))).measurable
    exact (h1.mul (hk.comp (continuous_snd.prodMk continuous_fst)).stronglyMeasurable).mul
      (hψc.comp continuous_snd).stronglyMeasurable
  -- the fibre identity
  have hfib : ∀ ξ : E, ‖ξ‖ ≤ R → ∀ F : E → ℝ,
      ∫ z, F (G (z, t • ξ)) * k (z, ξ) * ψ z ∂μ =
        ∫ y, F y * Â ((y, t • ξ), ξ) ∂μ := by
    intro ξ hξ F
    have h := hA.integral_eq (t • ξ) (hsmall ξ hξ) (fun y => F y * k (inv (y, t • ξ), ξ))
    refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).trans
      (h.trans (integral_congr_ae (Eventually.of_forall fun y => ?_)))
    · by_cases hz : ψ z = 0
      · rw [hz, mul_zero, mul_zero]
      · rw [hI.apply z (subset_tsupport ψ hz) (t • ξ) (hsmall ξ hξ)]
    · simp only [hÂdef, adjWeight]; ring
  have hf₁i : Integrable f₁ (μ.prod μ) := by
    refine (integrable_prod_iff hf₁m.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
    · by_cases hξ : ‖ξ‖ ≤ R
      · have h := hI.integrable (t • ξ) (hsmall ξ hξ) (fun y => g y * k (inv (y, t • ξ), ξ))
          ((hgÂ (t • ξ) ξ).congr (Eventually.of_forall fun y => by
            simp only [hÂdef, adjWeight]; ring))
        refine h.congr (Eventually.of_forall fun z => ?_)
        simp only [hf₁]
        by_cases hz : ψ z = 0
        · rw [hz, mul_zero, mul_zero]
        · rw [hI.apply z (subset_tsupport ψ hz) (t • ξ) (hsmall ξ hξ)]
      · have h0 : (fun z => f₁ (ξ, z)) = fun _ => 0 := by
          funext z; simp [hf₁, hks z ξ (not_le.mp hξ)]
        rw [h0]; exact integrable_zero _ _ _
    · have hbi : Integrable ((closedBall (0 : E) R).indicator fun _ => M * B) μ :=
        (integrable_indicator_iff measurableSet_closedBall).mpr
          (integrableOn_const (isCompact_closedBall (0 : E) R).measure_lt_top.ne)
      refine Integrable.mono' hbi hf₁m.aestronglyMeasurable.norm.integral_prod_right'
        (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      by_cases hξ : ‖ξ‖ ≤ R
      · rw [indicator_of_mem (by simpa using hξ)]
        have e1 : (fun z => ‖f₁ (ξ, z)‖) = fun z => (fun y => |g y|) (G (z, t • ξ)) *
            |k (z, ξ)| * |ψ z| := by
          funext z; simp only [hf₁, Real.norm_eq_abs, abs_mul]
        have h := hA.integral_abs_eq (t • ξ) (hsmall ξ hξ)
          (fun y => |g y| * |k (inv (y, t • ξ), ξ)|)
        have e2 : ∫ z, (fun y => |g y|) (G (z, t • ξ)) * |k (z, ξ)| * |ψ z| ∂μ =
            ∫ y, |g y| * |Â ((y, t • ξ), ξ)| ∂μ := by
          refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).trans
            (h.trans (integral_congr_ae (Eventually.of_forall fun y => ?_)))
          · simp only
            by_cases hz : ψ z = 0
            · rw [hz, abs_zero, mul_zero, mul_zero]
            · rw [hI.apply z (subset_tsupport ψ hz) (t • ξ) (hsmall ξ hξ)]
          · simp only [hÂdef, adjWeight, abs_mul]; ring
        rw [e1, e2]
        have hbi' : Integrable (fun y => M * C.indicator (fun y => |g y|) y) μ :=
          ((integrable_indicator_iff hCm).mpr hg.abs).const_mul _
        calc ∫ y, |g y| * |Â ((y, t • ξ), ξ)| ∂μ
            ≤ ∫ y, M * C.indicator (fun y => |g y|) y ∂μ := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) hbi'
                (Eventually.of_forall fun y => ?_)
              simp only
              by_cases hy : y ∈ C
              · rw [indicator_of_mem hy, mul_comm M]
                exact mul_le_mul_of_nonneg_left (by simpa using hM ((y, t • ξ), ξ)) (abs_nonneg _)
              · rw [hÂC ((y, t • ξ), ξ) hy]; simp [indicator_of_notMem hy]
          _ = M * B := by rw [integral_const_mul, integral_indicator hCm]
      · rw [indicator_of_notMem (by simpa using hξ)]
        have h0 : (fun z => ‖f₁ (ξ, z)‖) = fun _ => 0 := by
          funext z; simp [hf₁, hks z ξ (not_le.mp hξ)]
        rw [h0, integral_zero]
  -- the second integrand, in the variables `(y, ξ)`
  set f₂ : E × E → ℝ := fun q => g q.1 * Â ((q.1, t • q.2), q.2) with hf₂
  have hf₂i : Integrable f₂ (μ.prod μ) := by
    have hm : AEStronglyMeasurable f₂ (μ.prod μ) :=
      ((hgm.comp_measurable measurable_fst).mul
        (hÂ.comp ((continuous_fst.prodMk (continuous_const.smul continuous_snd)).prodMk
          continuous_snd)).stronglyMeasurable).aestronglyMeasurable
    have hbi : Integrable (fun q : E × E => C.indicator (fun y => |g y|) q.1 *
        (closedBall (0 : E) R).indicator (fun _ => M) q.2) (μ.prod μ) :=
      ((integrable_indicator_iff hCm).mpr hg.abs).mul_prod
        ((integrable_indicator_iff measurableSet_closedBall).mpr
          (integrableOn_const (isCompact_closedBall (0 : E) R).measure_lt_top.ne))
    refine hbi.mono' hm (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, hf₂]
    simp only [abs_mul]
    by_cases hy : q.1 ∈ C
    · by_cases hξ : ‖q.2‖ ≤ R
      · rw [indicator_of_mem hy, indicator_of_mem (by simpa using hξ)]
        exact mul_le_mul_of_nonneg_left (by simpa using hM ((q.1, t • q.2), q.2)) (abs_nonneg _)
      · rw [hÂs ((q.1, t • q.2), q.2) (not_le.mp hξ), abs_zero, mul_zero]
        exact mul_nonneg (indicator_nonneg (fun _ _ => abs_nonneg _) _)
          (indicator_nonneg (fun _ _ => hM0) _)
    · rw [hÂC ((q.1, t • q.2), q.2) hy, abs_zero, mul_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => abs_nonneg _) _)
        (indicator_nonneg (fun _ _ => hM0) _)
  refine ⟨?_, ?_⟩
  · calc ∫ z, fibreAverage μ G k g z t * ψ z ∂μ = ∫ z, ∫ ξ, f₁ (ξ, z) ∂μ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [fibreAverage, hf₁]
          rw [← integral_mul_const]
      _ = ∫ ξ, ∫ z, f₁ (ξ, z) ∂μ ∂μ :=
          (integral_integral_swap (f := fun ξ z => f₁ (ξ, z)) hf₁i).symm
      _ = ∫ ξ, ∫ y, f₂ (y, ξ) ∂μ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          by_cases hξ : ‖ξ‖ ≤ R
          · exact hfib ξ hξ g
          · have h1 : (fun z => f₁ (ξ, z)) = fun _ => 0 := by
              funext z; simp [hf₁, hks z ξ (not_le.mp hξ)]
            have h2 : (fun y => f₂ (y, ξ)) = fun _ => 0 := by
              funext y; simp [hf₂, hÂs ((y, t • ξ), ξ) (not_le.mp hξ)]
            simp only [h1, h2]
      _ = ∫ y, ∫ ξ, f₂ (y, ξ) ∂μ ∂μ :=
          (integral_integral_swap (f := fun y ξ => f₂ (y, ξ)) hf₂i).symm
      _ = ∫ y, g y * weightAverage μ Â y t ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [hf₂, weightAverage]
          rw [integral_const_mul]
  · refine hf₂i.integral_prod_left.congr (Eventually.of_forall fun y => ?_)
    simp only [hf₂, weightAverage]
    rw [integral_const_mul]

/-- The adjoint weight of a smooth weight is smooth. -/
theorem contDiff_adjWeight {A : E × E → ℝ} (hA : ContDiff ℝ ∞ A) {inv : E × E → E}
    {T : Set (E × E)} (hT : IsOpen T) (hAT : tsupport A ⊆ T) (hinv : ContDiffOn ℝ ∞ inv T)
    (hk : ContDiff ℝ ∞ k) : ContDiff ℝ ∞ (adjWeight A inv k) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.1 ∈ T
  · have hi : ContDiffAt ℝ ∞ (fun q : (E × E) × E => inv q.1) q :=
      (hinv.contDiffAt (hT.mem_nhds hq)).comp q contDiffAt_fst
    exact (hA.contDiffAt.comp q contDiffAt_fst).mul
      (hk.contDiffAt.comp q (hi.prodMk contDiffAt_snd))
  · have hnot : q.1 ∉ tsupport A := fun h => hq (hAT h)
    have hev0 := (notMem_tsupport_iff_eventuallyEq).mp hnot
    have hev : adjWeight A inv k =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto q).eventually hev0] with q' hq'
      simp [adjWeight, hq']
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **The pairing of the generator with a test function, in a chart** (FPT
`eq:chern-smoothing-generator`, adjoint form): for smooth `ψ` supported near `z₀` there are a
compact `C ⊆ W` and a continuous `φ` vanishing off `C` with
`(∫ Ψ_g(·, t) ψ - ∫ g ψ)/t² → ∫ g φ` for every measurable `g` integrable on `C`. -/
theorem exists_tendsto_pairing (hG : ContDiff ℝ ∞ G) (hG0 : ∀ z, G (z, 0) = z)
    (hk : ContDiff ℝ ∞ k) {R : ℝ} (hR : 0 < R) (hks : ∀ z ξ, R < ‖ξ‖ → k (z, ξ) = 0)
    (hke : ∀ z ξ, k (z, -ξ) = k (z, ξ)) (z₀ : E) {W : Set E} (hW : IsOpen W) (hz₀W : z₀ ∈ W)
    (hk1 : ∀ z ∈ W, ∫ ξ, k (z, ξ) ∂μ = 1) :
    ∃ ε > 0, ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ ball z₀ ε →
      ∃ (t₀ : ℝ) (C : Set E) (φ : E → ℝ), 0 < t₀ ∧ IsCompact C ∧ C ⊆ W ∧ Continuous φ ∧
        (∀ y ∉ C, φ y = 0) ∧ (∀ y ∉ C, ψ y = 0) ∧
        (∀ z ∈ tsupport ψ, ∀ η : E, ‖η‖ < t₀ → G (z, η) ∈ C) ∧
        ∀ g : E → ℝ, StronglyMeasurable g → IntegrableOn g C μ →
          Tendsto (fun t => (∫ z, fibreAverage μ G k g z t * ψ z ∂μ - ∫ z, g z * ψ z ∂μ) / t ^ 2)
            (𝓝[>] 0) (𝓝 (∫ y, g y * φ y ∂μ)) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨ε, hε, hεψ⟩ := exists_adjointDensity μ hG hG0 z₀ hW hz₀W
  refine ⟨ε, hε, fun ψ hψ hψs => ?_⟩
  obtain ⟨t₀, C, A, inv, hA, hCW, hI⟩ := hεψ ψ hψ hψs
  obtain ⟨T, hT, hAT, hinvT⟩ := hI.smooth
  have hCm : MeasurableSet C := hA.isCompact.isClosed.measurableSet
  set Â := adjWeight A inv k with hÂdef
  have hÂs : ContDiff ℝ ∞ Â := contDiff_adjWeight hA.contDiff hT hAT hinvT hk
  have hÂ2 : ContDiff ℝ 2 Â := hÂs.of_le (WithTop.coe_le_coe.mpr le_top)
  have hÂsupp : ∀ p ξ, R < ‖ξ‖ → Â (p, ξ) = 0 := fun p ξ hξ => by
    simp [hÂdef, adjWeight, hks _ _ hξ]
  have hÂe : ∀ p ξ, Â (p, -ξ) = Â (p, ξ) := fun p ξ => by
    simp [hÂdef, adjWeight, hke]
  set φ := weightSecondCoeff μ Â with hφdef
  have hφc : Continuous φ := continuous_weightSecondCoeff hÂ2 hÂsupp
  have hφv : ∀ y ∉ C, φ y = 0 := by
    intro y hy
    have hzero : ∀ ξ : E, pD2 Â (y, 0) ξ = 0 := by
      intro ξ
      have hev : (fun p => Â (p, ξ)) =ᶠ[𝓝 (y, 0)] fun _ => 0 := by
        have ho : IsOpen (Cᶜ ×ˢ (univ : Set E)) :=
          hA.isCompact.isClosed.isOpen_compl.prod isOpen_univ
        filter_upwards [ho.mem_nhds ⟨hy, mem_univ _⟩] with p hp
        simp [hÂdef, adjWeight, hA.vanish p hp.1]
      exact fderiv_fderiv_eq_zero_of_eventually hev
    simp [hφdef, weightSecondCoeff, hzero]
  have hψv : ∀ y ∉ C, ψ y = 0 := fun y hy => by
    rw [← hA.eq_zero y]; exact hA.vanish (y, 0) hy
  have hψc : Continuous ψ := hψ.continuous
  -- the zeroth-order term
  have hzeroth : ∀ y, ∫ ξ, Â ((y, 0), ξ) ∂μ = ψ y := by
    intro y
    by_cases hy : ψ y = 0
    · simp [hÂdef, adjWeight, hA.eq_zero, hy]
    · have hA0 : A (y, 0) ≠ 0 := by rwa [hA.eq_zero]
      have hyC : y ∈ C := by by_contra h; exact hy (hψv y h)
      simp only [hÂdef, adjWeight, hI.zero y hA0, hA.eq_zero]
      rw [integral_const_mul, hk1 y (hCW hyC), mul_one]
  refine ⟨t₀, C, φ, hA.pos, hA.isCompact, hCW, hφc, hφv, hψv, hA.mapsTo, fun g hgm hg => ?_⟩
  set D : ℝ → E → ℝ := fun t y => (weightAverage μ Â y t - ∫ ξ, Â ((y, 0), ξ) ∂μ) / t ^ 2
    with hDdef
  have hD : TendstoUniformlyOn D φ (𝓝[>] 0) C :=
    tendstoUniformlyOn_weightAverage hÂ2 hR hÂsupp hÂe hA.isCompact
  have hDv : ∀ t, ∀ y ∉ C, D t y = 0 := by
    intro t y hy
    have h1 : ∀ ξ : E, Â ((y, t • ξ), ξ) = 0 := fun ξ => by
      simp [hÂdef, adjWeight, hA.vanish (y, t • ξ) hy]
    simp [hDdef, weightAverage, h1, hzeroth, hψv y hy]
  have hψb : ∃ Mψ, ∀ y, |ψ y| ≤ Mψ := by
    obtain ⟨Mψ, h⟩ := hψc.bounded_above_of_compact_support
      (HasCompactSupport.intro hA.isCompact fun y hy => hψv y hy)
    exact ⟨Mψ, fun y => by simpa using h y⟩
  obtain ⟨Mψ, hMψ⟩ := hψb
  have hgψ : Integrable (fun y => g y * ψ y) μ :=
    integrable_mul_of_vanish hCm hg hψc.aestronglyMeasurable hMψ hψv
  have hφb : ∃ Mφ, ∀ y, |φ y| ≤ Mφ := by
    obtain ⟨Mφ, h⟩ := hφc.bounded_above_of_compact_support
      (HasCompactSupport.intro hA.isCompact fun y hy => hφv y hy)
    exact ⟨Mφ, fun y => by simpa using h y⟩
  obtain ⟨Mφ, hMφ⟩ := hφb
  have hφi : Integrable (fun y => g y * φ y) μ :=
    integrable_mul_of_vanish hCm hg hφc.aestronglyMeasurable hMφ hφv
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < t₀ / R := Ioo_mem_nhdsGT (div_pos hA.pos hR)
  have hmain : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∫ z, fibreAverage μ G k g z t * ψ z ∂μ - ∫ z, g z * ψ z ∂μ) / t ^ 2 =
        ∫ y, g y * D t y ∂μ ∧ Integrable (fun y => g y * D t y) μ := by
    filter_upwards [hev] with t ⟨ht0, ht⟩
    have htR : t * R < t₀ := by rwa [lt_div_iff₀ hR] at ht
    obtain ⟨h1, h2⟩ := integral_fibreAverage_mul_eq hA hI hG.continuous hk.continuous hks
      hÂs.continuous hgm hg ht0.le htR
    have e : (fun y => g y * D t y) =
        fun y => (g y * weightAverage μ Â y t - g y * ψ y) / t ^ 2 := by
      funext y; simp only [hDdef, hzeroth]; ring
    refine ⟨?_, ?_⟩
    · rw [e, integral_div, integral_sub h2 hgψ, h1]
    · rw [e]; exact (h2.sub hgψ).div_const _
  refine Tendsto.congr' (hmain.mono fun t ht => ht.1.symm) ?_
  exact tendsto_integral_mul_of_tendstoUniformlyOn hCm hg hD hDv hφv
    (hmain.mono fun t ht => ht.2) hφi

/-- The smooth weighted integrand `(z, η, ξ) ↦ g(G(z, η)) k(z, ξ)`. -/
def compWeight (G : E × E → E) (k : E × E → ℝ) (g : E → ℝ) : (E × E) × E → ℝ :=
  fun q => g (G q.1) * k (q.1.1, q.2)

/-- **The pointwise expansion for smooth `g`**: `(Ψ_g(z, t) - g(z))/t² → Q(z)` uniformly on
compact sets where the weight has mass one. -/
theorem tendstoUniformlyOn_fibreAverage {g : E → ℝ} (hg : ContDiff ℝ 2 g)
    (hG : ContDiff ℝ 2 G) (hG0 : ∀ z, G (z, 0) = z) (hk : ContDiff ℝ 2 k) {R : ℝ} (hR : 0 < R)
    (hks : ∀ z ξ, R < ‖ξ‖ → k (z, ξ) = 0) (hke : ∀ z ξ, k (z, -ξ) = k (z, ξ))
    {K : Set E} (hK : IsCompact K) (hk1 : ∀ z ∈ K, ∫ ξ, k (z, ξ) ∂μ = 1) :
    TendstoUniformlyOn (fun t z => (fibreAverage μ G k g z t - g z) / t ^ 2)
      (weightSecondCoeff μ (compWeight G k g)) (𝓝[>] 0) K := by
  have hA : ContDiff ℝ 2 (compWeight G k g) :=
    (hg.comp (hG.comp contDiff_fst)).mul (hk.comp ((contDiff_fst.comp contDiff_fst).prodMk
      contDiff_snd))
  have h := tendstoUniformlyOn_weightAverage (μ := μ) hA hR
    (fun p ξ hξ => by simp [compWeight, hks _ _ hξ]) (fun p ξ => by simp [compWeight, hke]) hK
  refine h.congr (Eventually.of_forall fun t z hz => ?_)
  simp only [weightAverage, fibreAverage, compWeight, hG0]
  rw [integral_const_mul, hk1 z hz, mul_one]

end Main

end SGPT.NPP.DN6

import SGPT.Okounkov.TranscendentalWNLegendreBoundedLocal

/-!
# The locally bounded case on a ball: the identity on test functions (package WN-LEG)

Blueprint `claude-tok-wn-leg`, nodes `tok-wn-leg:tight` and `tok-wn-leg:bounded-case` (second
part).  In the setting of `TranscendentalWNLegendreBoundedLocal` (`IsBoundedLegendreData
(ball z₀ r) u a b C`, approximants `F_k` on `D`, `W = ball z₀ (r/8)`), for every continuous
compactly supported `0 ≤ φ ≤ 1` with `tsupport φ ⊆ W`:

* `λ ↦ ∫ φ dν_{k,λ}` agrees on `(a, b)` with a Borel function
  (`exists_measurable_lintegral_approxTransform`), and `1_{(a,b)}(λ) ∫ φ dν_λ` is Borel
  (`measurable_indicator_lintegral`);
* **tightness** (`lintegral_tail_le`): `∫ φ(z)(1 - χ_L(τ)) dμ_k ≤ (N + 1) M · 2η` uniformly in
  `k` once `K/L < η` (the band formula of the smooth case and the slope bounds);
* **the test-function identity** (`lintegral_test_eq`):
  `∫ φ(z) d MA(u)(z, τ) = (N + 1) ∫_a^b ∫ φ d MA(û_λ) dλ`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
  SGPT.Foundations.Analysis.Pending.PshRadialRegularization

variable {N : ℕ} {u : ComplexModel N → ℂ → EReal} {a b C : ℝ} {z₀ : ComplexModel N} {r : ℝ}
  {ρ : ComplexModel (N + 1) → ℝ}

namespace IsBoundedLegendreData

variable (h : IsBoundedLegendreData (ball z₀ r) u a b C) (hρ : IsRadialKernel ρ) (hr : 0 < r)
include h hρ hr

/-! ### Measurability in `λ` -/

/-- **`λ ↦ ∫ φ dν_{k,λ}` is Borel on `(a, b)`** (it is `∫_D φ(z) · schur density at
`(z, Y_k(z, λ))`, jointly measurable). -/
theorem exists_measurable_lintegral_approxTransform (k : ℕ) {φ : ComplexModel N → ℝ}
    (hφ : Continuous φ)
    (hf : ∀ lam, PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
      (approxDomain (ball z₀ r) (localScale r))) :
    ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ ∀ lam ∈ Ioo a b,
      g lam = ∫⁻ z, ENNReal.ofReal (φ z) ∂(MongeAmpere.truncationLimitMeasure
        (approxDomain (ball z₀ r) (localScale r))
        (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
        (hf lam)) := by
  classical
  set D := approxDomain (ball z₀ r) (localScale r)
  set F := approxProfile ρ u a b C (localScale r) k
  have hD := h.localData hρ hr k
  set S : Set (ℝ × ComplexModel N) := Ioo a b ×ˢ (D : Set (ComplexModel N))
  have hS : IsOpen S := isOpen_Ioo.prod D.isOpen
  set G : ℝ × ComplexModel N → ComplexModel N × ℝ :=
    S.piecewise (fun p => (p.2, legendreArg F p.2 p.1)) (fun _ => (0, 0))
  have hcont : ContinuousOn (fun p : ℝ × ComplexModel N => (p.2, legendreArg F p.2 p.1)) S := by
    intro p hp
    have h1 := (hD.contDiffAt_legendreArg hp.2 hp.1).continuousAt
    have h2 : ContinuousAt (fun p : ℝ × ComplexModel N => legendreArg F p.2 p.1) p :=
      ContinuousAt.comp (g := fun q : ComplexModel N × ℝ => legendreArg F q.1 q.2)
        (f := fun p : ℝ × ComplexModel N => (p.2, p.1)) h1 continuous_swap.continuousAt
    exact (continuous_snd.continuousAt.prodMk h2).continuousWithinAt
  have hG : Measurable G := hcont.measurable_piecewise continuousOn_const hS.measurableSet
  set H : ℝ × ComplexModel N → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (schurDensity F (G p)) * ENNReal.ofReal (φ p.2)
  have hH : Measurable H :=
    ((measurable_schurDensity F).comp hG).ennreal_ofReal.mul
      (hφ.measurable.comp measurable_snd).ennreal_ofReal
  refine ⟨fun lam => ∫⁻ z, H (lam, z) ∂(volume.restrict (D : Set (ComplexModel N))),
    hH.lintegral_prod_right', fun lam hlam => ?_⟩
  rw [h.truncationLimitMeasure_approxTransform_eq_smooth hρ hr k hlam, smoothMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_smoothDensity _).ennreal_ofReal
      hφ.measurable.ennreal_ofReal]
  refine setLIntegral_congr_fun D.isOpen.measurableSet fun z hz => ?_
  have hGp : G (lam, z) = (z, legendreArg F z lam) := by
    simp only [G]
    rw [piecewise_eq_of_mem _ _ _ (show (lam, z) ∈ S from ⟨hlam, hz⟩)]
  simp only [H, hGp, Pi.mul_apply]
  rw [hD.smoothDensity_legendreValue (D := D) hz hlam]

/-! ### The test-function identity -/

omit h hρ hr in
theorem lintegral_le_measure_ball {μ : Measure (ComplexModel N)} {φ : ComplexModel N → ℝ}
    (hφW : tsupport φ ⊆ ball z₀ (r / 8)) (hφ1 : ∀ z, φ z ≤ 1) :
    ∫⁻ z, ENNReal.ofReal (φ z) ∂μ ≤ μ (ball z₀ (r / 8)) := by
  rw [← lintegral_indicator_one measurableSet_ball]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ ball z₀ (r / 8)
  · rw [indicator_of_mem hz, Pi.one_apply]
    exact ENNReal.ofReal_le_one.mpr (hφ1 z)
  · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport (fun h' => hz (hφW h')),
      ENNReal.ofReal_zero]

/-- **`1_{(a,b)}(λ) ∫ φ dν_λ` is Borel** (a pointwise limit of Borel functions). -/
theorem measurable_indicator_lintegral
    (hû : ∀ lam, PlurisubharmonicOn (partialLegendre u lam)
      (approxDomain (ball z₀ r) (localScale r)))
    {φ : ComplexModel N → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφW : tsupport φ ⊆ ball z₀ (r / 8)) (hφ0 : ∀ z, 0 ≤ φ z) :
    Measurable ((Ioo a b).indicator fun lam => ∫⁻ z, ENNReal.ofReal (φ z) ∂(
      MongeAmpere.truncationLimitMeasure (approxDomain (ball z₀ r) (localScale r))
        (partialLegendre u lam) (hû lam))) := by
  set D := approxDomain (ball z₀ r) (localScale r)
  have hfl : ∀ k lam, PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam) D :=
    fun k lam => plurisubharmonicOn_partialLegendre D.isOpen (h.localPsh hρ hr k)
      (isCircleInvariant_logRadialFunction _) lam
  choose g hgm hg using fun k => h.exists_measurable_lintegral_approxTransform hρ hr k hφ (hfl k)
  refine measurable_of_tendsto_metrizable (f := fun k => (Ioo a b).indicator (g k))
    (fun k => (hgm k).indicator measurableSet_Ioo) (tendsto_pi_nhds.mpr fun lam => ?_)
  by_cases hlam : lam ∈ Ioo a b
  · simp only [indicator_of_mem hlam]
    refine (h.tendsto_lintegral_approxTransform hρ hr hlam (hû lam) (fun k => hfl k lam) hφ hφc
      (hφW.trans (ball_eighth_subset_approxDomain hr)) hφ0).congr fun k => (hg k lam hlam).symm
  · simp only [indicator_of_notMem hlam]
    exact tendsto_const_nhds

omit h hρ hr in
theorem ae_mem_of_truncationLimitMeasure {n : ℕ} {Ω : Opens (ComplexModel n)}
    {f : ComplexModel n → EReal} (hf : PlurisubharmonicOn f Ω) :
    ∀ᵐ x ∂(MongeAmpere.truncationLimitMeasure Ω f hf), x ∈ Ω :=
  ae_iff.mpr (MongeAmpere.truncationLimitMeasure_compl hf)

omit h hρ hr in
theorem volume_Ioo_diff_Icc_le {η : ℝ} (hη : 0 < η) :
    volume (Ioo a b \ Icc (a + η) (b - η)) ≤ ENNReal.ofReal (2 * η) := by
  have hsub : Ioo a b \ Icc (a + η) (b - η) ⊆ Ioo a (a + η) ∪ Ioo (b - η) b := by
    rintro x ⟨⟨hax, hxb⟩, hx⟩
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hax, hx⟩
    · exact Or.inr ⟨hx, hxb⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith) (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Tightness** (`tok-wn-leg:tight`): the mass of `μ_k` near `τ = 0` and `τ = ∞`, weighted by
`φ`, is at most `(N + 1) M · 2η` once `K/L < η`, uniformly in `k`. -/
theorem lintegral_tail_le (k : ℕ)
    (hfu : PlurisubharmonicOn
      (productModelFunction (logRadialFunction (approxProfile ρ u a b C (localScale r) k)))
      (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r))))
    {φ : ComplexModel N → ℝ} (hφ : Continuous φ) (hφ01 : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1)
    (hφW : tsupport φ ⊆ ball z₀ (r / 8)) {M : ℝ≥0∞}
    (hM : ∀ lam ∈ Ioo a b, ∀ hf : PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
      (approxDomain (ball z₀ r) (localScale r)),
      MongeAmpere.truncationLimitMeasure (approxDomain (ball z₀ r) (localScale r))
        (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam) hf
        (ball z₀ (r / 8)) ≤ M)
    {η : ℝ} (hη : 0 < η) {L : ℕ} (hL : 0 < L) (hKL : approxSlack a b C / L < η) :
    ∫⁻ q, ENNReal.ofReal (φ (stripModelEquiv N q).1 * (1 - tauCutoff L (stripModelEquiv N q).2))
        ∂(MongeAmpere.truncationLimitMeasure
          (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r)))
          (productModelFunction (logRadialFunction (approxProfile ρ u a b C (localScale r) k)))
          hfu) ≤ ((N + 1 : ℕ) : ℝ≥0∞) * (M * ENNReal.ofReal (2 * η)) := by
  set D := approxDomain (ball z₀ r) (localScale r)
  set F := approxProfile ρ u a b C (localScale r) k
  have hD := h.localData hρ hr k
  have hp := h.localPsh hρ hr k
  have hfl : ∀ lam, PlurisubharmonicOn (partialLegendre (logRadialFunction F) lam) D :=
    fun lam => plurisubharmonicOn_partialLegendre D.isOpen hp
      (isCircleInvariant_logRadialFunction _) lam
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set gL : ComplexModel N × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (φ p.1 * (1 - logCutoff L p.2))
  have hgL : Measurable gL :=
    ((hφ.measurable.comp measurable_fst).mul (measurable_const.sub
      ((continuous_logCutoff (L : ℝ)).measurable.comp measurable_snd))).ennreal_ofReal
  have hgL_le : ∀ p, gL p ≤ ENNReal.ofReal (φ p.1) := fun p =>
    ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (hφ01 _).1
      (by linarith [logCutoff_nonneg (L : ℝ) p.2]))
  have step1 : ∫⁻ q, ENNReal.ofReal (φ (stripModelEquiv N q).1 *
        (1 - tauCutoff L (stripModelEquiv N q).2))
        ∂(MongeAmpere.truncationLimitMeasure (puncturedProductOpens D)
          (productModelFunction (logRadialFunction F)) hfu) =
      ∫⁻ q, gL ((stripModelEquiv N q).1, logNormSq (stripModelEquiv N q).2)
        ∂(MongeAmpere.truncationLimitMeasure (puncturedProductOpens D)
          (productModelFunction (logRadialFunction F)) hfu) := by
    refine lintegral_congr_ae ((ae_mem_of_truncationLimitMeasure hfu).mono fun q hq => ?_)
    simp only [gL]
    rw [tauCutoff_of_ne hq.2]
  rw [step1, hD.lintegral_truncationLimitMeasure_logRadial hp hfu hfl hgL]
  refine mul_le_mul_right ?_ _
  calc ∫⁻ lam in Ioo a b, ∫⁻ z, gL (z, legendreArg F z lam)
        ∂(MongeAmpere.truncationLimitMeasure D (partialLegendre (logRadialFunction F) lam)
          (hfl lam))
      ≤ ∫⁻ lam in Ioo a b, (Ioo a b \ Icc (a + η) (b - η)).indicator (fun _ => M) lam := by
        refine setLIntegral_mono' measurableSet_Ioo fun lam hlam => ?_
        by_cases hlam' : lam ∈ Icc (a + η) (b - η)
        · rw [indicator_of_notMem (fun h' => h'.2 hlam')]
          have hz0 : ∀ᵐ z ∂(MongeAmpere.truncationLimitMeasure D
              (partialLegendre (logRadialFunction F) lam) (hfl lam)),
              gL (z, legendreArg F z lam) = 0 := by
            refine (ae_mem_of_truncationLimitMeasure (hfl lam)).mono fun z hz => ?_
            have h1 := h.legendreArg_approxProfile_lt hρ isPreconnected_ball' (localScale_pos hr)
              (localScale_le_half r) hz k hLr hlam (by linarith [hlam'.2])
            have h2 := h.neg_lt_legendreArg_approxProfile hρ isPreconnected_ball'
              (localScale_pos hr) (localScale_le_half r) hz k hLr hlam (by linarith [hlam'.1])
            simp only [gL]
            rw [logCutoff_eq_one (abs_le.mpr ⟨h2.le, h1.le⟩), sub_self, mul_zero,
              ENNReal.ofReal_zero]
          rw [lintegral_congr_ae hz0, lintegral_zero]
        · rw [indicator_of_mem (show lam ∈ Ioo a b \ Icc (a + η) (b - η) from ⟨hlam, hlam'⟩)]
          calc ∫⁻ z, gL (z, legendreArg F z lam)
                ∂(MongeAmpere.truncationLimitMeasure D (partialLegendre (logRadialFunction F) lam)
                  (hfl lam))
              ≤ ∫⁻ z, ENNReal.ofReal (φ z)
                ∂(MongeAmpere.truncationLimitMeasure D (partialLegendre (logRadialFunction F) lam)
                  (hfl lam)) := lintegral_mono fun z => hgL_le _
            _ ≤ _ := lintegral_le_measure_ball hφW (fun z => (hφ01 z).2)
            _ ≤ M := hM lam hlam (hfl lam)
    _ = M * volume (Ioo a b \ Icc (a + η) (b - η)) := by
        rw [lintegral_indicator_const (measurableSet_Ioo.diff measurableSet_Icc),
          Measure.restrict_apply (measurableSet_Ioo.diff measurableSet_Icc),
          inter_eq_left.mpr sdiff_subset]
    _ ≤ M * ENNReal.ofReal (2 * η) := mul_le_mul_right (volume_Ioo_diff_Icc_le hη) _

/-- **The test-function identity** (`tok-wn-leg:bounded-case`, main step): for continuous
compactly supported `0 ≤ φ ≤ 1` with `tsupport φ ⊆ ball z₀ (r/8)`,
`∫ φ(z) d MA(u) = (N + 1) ∫_a^b ∫ φ d MA(û_λ) dλ` (measures on `D × ℂ*` and `D`). -/
theorem lintegral_test_eq
    (hu : PlurisubharmonicOn (productModelFunction u)
      (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r))))
    (hû : ∀ lam, PlurisubharmonicOn (partialLegendre u lam)
      (approxDomain (ball z₀ r) (localScale r)))
    {φ : ComplexModel N → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφW : tsupport φ ⊆ ball z₀ (r / 8)) (hφ01 : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1) :
    ∫⁻ q, ENNReal.ofReal (φ (stripModelEquiv N q).1)
        ∂(MongeAmpere.truncationLimitMeasure
          (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r)))
          (productModelFunction u) hu) =
      ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo a b, ∫⁻ z, ENNReal.ofReal (φ z)
        ∂(MongeAmpere.truncationLimitMeasure (approxDomain (ball z₀ r) (localScale r))
          (partialLegendre u lam) (hû lam)) := by
  set D := approxDomain (ball z₀ r) (localScale r)
  set P := puncturedProductOpens D
  set F := fun k => approxProfile ρ u a b C (localScale r) k
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (hφ01 z).1
  have hφD : tsupport φ ⊆ D := hφW.trans (ball_eighth_subset_approxDomain hr)
  have hD := fun k => h.localData hρ hr k
  have hp := fun k => h.localPsh hρ hr k
  have hfu : ∀ k, PlurisubharmonicOn (productModelFunction (logRadialFunction (F k))) P :=
    fun k => ((hD k).isSmoothPshOn_uTilde (D := D) (hp k)).2.1
  have hfl : ∀ k lam, PlurisubharmonicOn (partialLegendre (logRadialFunction (F k)) lam) D :=
    fun k lam => plurisubharmonicOn_partialLegendre D.isOpen (hp k)
      (isCircleInvariant_logRadialFunction _) lam
  set μk := fun k => MongeAmpere.truncationLimitMeasure P
    (productModelFunction (logRadialFunction (F k))) (hfu k)
  set μ := MongeAmpere.truncationLimitMeasure P (productModelFunction u) hu
  set Jk := fun k lam => ∫⁻ z, ENNReal.ofReal (φ z)
    ∂(MongeAmpere.truncationLimitMeasure D (partialLegendre (logRadialFunction (F k)) lam)
      (hfl k lam))
  set J := fun lam => ∫⁻ z, ENNReal.ofReal (φ z)
    ∂(MongeAmpere.truncationLimitMeasure D (partialLegendre u lam) (hû lam))
  set Ik := fun k => ∫⁻ q, ENNReal.ofReal (φ (stripModelEquiv N q).1) ∂(μk k)
  set LHS := ∫⁻ q, ENNReal.ofReal (φ (stripModelEquiv N q).1) ∂μ
  obtain ⟨M, hMt, hM⟩ := h.exists_cln_bound hρ hr
  have hJk_le : ∀ k, ∀ lam ∈ Ioo a b, Jk k lam ≤ M := fun k lam hlam =>
    (lintegral_le_measure_ball hφW fun z => (hφ01 z).2).trans (hM k lam hlam (hfl k lam))
  -- the smooth identity for every `k`
  have hIk : ∀ k, Ik k = ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo a b, Jk k lam := fun k =>
    (hD k).lintegral_truncationLimitMeasure_logRadial (D := D) (hp k) (hfu k) (hfl k)
      (g := fun p => ENNReal.ofReal (φ p.1)) (hφ.measurable.comp measurable_fst).ennreal_ofReal
  -- the right side converges
  have hJk_meas : ∀ k, AEMeasurable (Jk k) (volume.restrict (Ioo a b)) := by
    intro k
    obtain ⟨g, hgm, hg⟩ := h.exists_measurable_lintegral_approxTransform hρ hr k hφ (hfl k)
    exact hgm.aemeasurable.congr ((ae_restrict_mem measurableSet_Ioo).mono fun lam hlam =>
      hg lam hlam)
  have hRHS : Tendsto (fun k => ∫⁻ lam in Ioo a b, Jk k lam) atTop
      (𝓝 (∫⁻ lam in Ioo a b, J lam)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun _ => M) hJk_meas
      (fun k => (ae_restrict_mem measurableSet_Ioo).mono fun lam hlam => hJk_le k lam hlam) ?_
      ((ae_restrict_mem measurableSet_Ioo).mono fun lam hlam =>
        h.tendsto_lintegral_approxTransform hρ hr hlam (hû lam) (fun k => hfl k lam) hφ hφc hφD
          hφ0)
    rw [setLIntegral_const, Real.volume_Ioo]
    exact ENNReal.mul_ne_top hMt.ne ENNReal.ofReal_ne_top
  set T := ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo a b, J lam
  have hI : Tendsto Ik atTop (𝓝 T) := by
    have := ENNReal.Tendsto.const_mul hRHS (Or.inr (ENNReal.natCast_ne_top (N + 1)))
    exact this.congr fun k => (hIk k).symm
  -- the cut-off test functions
  have hΦconv : ∀ L : ℕ, Tendsto (fun k => ∫⁻ q, ENNReal.ofReal (productCutoff φ L q) ∂(μk k))
      atTop (𝓝 (∫⁻ q, ENNReal.ofReal (productCutoff φ L q) ∂μ)) := fun L =>
    h.tendsto_lintegral_approxProfile hρ hr hu hfu (continuous_productCutoff hφ L)
      (hasCompactSupport_productCutoff hφc L) (tsupport_productCutoff_subset_punctured hφD L)
      (productCutoff_nonneg hφ0 L)
  -- upper bound (Fatou)
  have hupper : ∀ L : ℕ, ∫⁻ q, ENNReal.ofReal (productCutoff φ L q) ∂μ ≤ T := fun L =>
    le_of_tendsto_of_tendsto' (hΦconv L) hI fun k =>
      lintegral_mono fun q => ENNReal.ofReal_le_ofReal (productCutoff_le hφ0 L q)
  have hLHS_le : LHS ≤ T := by
    have hlim : ∀ᵐ q ∂μ, Tendsto (fun L : ℕ => ENNReal.ofReal (productCutoff φ L q)) atTop
        (𝓝 (ENNReal.ofReal (φ (stripModelEquiv N q).1))) := by
      refine (ae_mem_of_truncationLimitMeasure hu).mono fun q hq => ?_
      have h1 := (tendsto_tauCutoff hq.2).const_mul (φ (stripModelEquiv N q).1)
      rw [mul_one] at h1
      exact (ENNReal.continuous_ofReal.tendsto _).comp h1
    calc LHS = ∫⁻ q, liminf (fun L : ℕ => ENNReal.ofReal (productCutoff φ L q)) atTop ∂μ :=
          lintegral_congr_ae (hlim.mono fun q hq => hq.liminf_eq.symm)
      _ ≤ liminf (fun L : ℕ => ∫⁻ q, ENNReal.ofReal (productCutoff φ L q) ∂μ) atTop :=
          lintegral_liminf_le fun L => (continuous_productCutoff hφ L).measurable.ennreal_ofReal
      _ ≤ T := liminf_le_of_frequently_le' (Frequently.of_forall hupper)
  -- lower bound (tightness)
  set c := ((N + 1 : ℕ) : ℝ≥0∞) * M
  have hc : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hMt.ne
  have hlower : ∀ η : ℝ, 0 < η → T ≤ LHS + c * ENNReal.ofReal (2 * η) := by
    intro η hη
    obtain ⟨L, hL⟩ := exists_nat_gt (max (approxSlack a b C / η) 0)
    have hL0 : 0 < L := by exact_mod_cast (le_max_right _ _).trans_lt hL
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
    have hKL : approxSlack a b C / L < η := by
      rw [div_lt_iff₀ hLr]
      have := (le_max_left _ _).trans_lt hL
      rw [div_lt_iff₀ hη] at this
      linarith
    have hsplit : ∀ k, Ik k ≤ ∫⁻ q, ENNReal.ofReal (productCutoff φ L q) ∂(μk k) +
        c * ENNReal.ofReal (2 * η) := by
      intro k
      have heq : Ik k = ∫⁻ q, ENNReal.ofReal (productCutoff φ L q) ∂(μk k) +
          ∫⁻ q, ENNReal.ofReal (φ (stripModelEquiv N q).1 *
            (1 - tauCutoff L (stripModelEquiv N q).2)) ∂(μk k) := by
        rw [← lintegral_add_left (continuous_productCutoff hφ L).measurable.ennreal_ofReal]
        refine lintegral_congr fun q => ?_
        rw [← ENNReal.ofReal_add (productCutoff_nonneg hφ0 L q)
          (mul_nonneg (hφ0 _) (by linarith [tauCutoff_le_one (L : ℝ) (stripModelEquiv N q).2]))]
        congr 1
        simp only [productCutoff]
        ring
      rw [heq, mul_assoc]
      exact add_le_add_right (h.lintegral_tail_le hρ hr k (hfu k) hφ hφ01 hφW
        (fun lam hlam hf => hM k lam hlam hf) hη hL0 hKL) _
    have h1 : Tendsto (fun k => ∫⁻ q, ENNReal.ofReal (productCutoff φ L q) ∂(μk k) +
        c * ENNReal.ofReal (2 * η)) atTop
        (𝓝 (∫⁻ q, ENNReal.ofReal (productCutoff φ L q) ∂μ + c * ENNReal.ofReal (2 * η))) :=
      (hΦconv L).add tendsto_const_nhds
    refine (le_of_tendsto_of_tendsto' hI h1 hsplit).trans (add_le_add_left ?_ _)
    exact lintegral_mono fun q => ENNReal.ofReal_le_ofReal (productCutoff_le hφ0 L q)
  have hT_le : T ≤ LHS := by
    have hlim : Tendsto (fun m : ℕ => LHS + c * ENNReal.ofReal (2 * (1 / ((m : ℝ) + 1)))) atTop
        (𝓝 (LHS + c * ENNReal.ofReal (2 * 0))) := by
      refine tendsto_const_nhds.add (ENNReal.Tendsto.const_mul ?_ (Or.inr hc))
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2)
    rw [mul_zero, ENNReal.ofReal_zero, mul_zero, add_zero] at hlim
    exact ge_of_tendsto' hlim fun m => hlower _ (by positivity)
  exact le_antisymm hLHS_le hT_le

end IsBoundedLegendreData

end SGPT.Okounkov.TranscendentalWN

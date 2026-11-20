import SGPT.Envelopes.MADirichlet4FixedMeasure

/-!
# Self-integral convergence for the convolution approximants

Xia, *Foundations of pluripotential theory* (FPT), `thm:canonical-grid-self-integral-convergence`,
in the convolution variant of lanes MA-DIR2/MA-DIR3 and for truncated functions.

Let `α` be a finite measure carried by a compact `K`, with `cthickening (2r) K ⊆ D` and
`α ≤ (ddᶜw)ⁿ` on `D` for a bounded plurisubharmonic `w`, and let `gⱼ = α ∗ ρⱼ`
(`convDensity α r hr j`, `ρⱼ` TN's radial kernels). If plurisubharmonic `f_k` with `|f_k| ≤ T`
converge in `L¹_loc(D)` to `b` and `s_k → ∞`, then

  `∫_D |f_k - b| g_{s_k} dV → 0`   (`tendsto_lintegral_convDensity_abs_sub`).

Applied to the truncations `f_k = max(U_{s_k}, -T)` of a convergent subsequence of the
approximants `U_j` of `exists_convolution_approximants` and `b = max(u, -T)`, this is the
second convergence of FPT's theorem (the error term `cₙ (j+1)⁻¹ χⁿ` of the densities is
`O(1/j)`); truncating at a fixed level keeps every function bounded, which replaces FPT's
`L²(μ)` bound by `e₂`.

*Proof* (FPT, with the convolution in place of cube averages). By Tonelli,
`∫_D φ gⱼ dV = ∫ Aⱼφ dα` with `Aⱼφ(t) = ∫ φ(x) ρⱼ(x - t) dx` (`lintegral_convDensity_mul_eq`).
For `t ∈ K` with `f_k(t) → b(t)`: `|f_k - b| = 2(f_k - b)₊ - (f_k - b)`; the sub-mean inequality
gives `A f_k(t) ≥ f_k(t)`, the radial regularizations of `b` converge, `Aⱼb(t) → b(t)`
(`tendsto_integral_mul_explicitRadialKernel_of_psh`), and by upper semicontinuity of `b` and
Hartogs' lemma `(f_k - b)₊ ≤ c - b` on the shrinking supports for every `c > b(t)`; hence
`A_{s_k}|f_k - b|(t) → 0` (`tendsto_integral_abs_sub_mul_kernel`). By
`lem:bounded-psh-fixed-measure-continuity` (`tendsto_integral_abs_sub_of_localL1`), every
subsequence has a further subsequence along which `f_k → b` `α`-almost everywhere, and dominated
convergence concludes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor SGPT.Foundations.Analysis.Pending.HolomorphicPullback

variable {n : ℕ}

/-- **The radial regularizations converge**: if `u` is locally bounded plurisubharmonic on `Ω`
and `B̄(z, 2r) ⊆ Ω`, then `∫ u(x) ρⱼ(x - z) dx → u(z)`. -/
theorem tendsto_integral_mul_explicitRadialKernel_of_psh {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {r : ℝ} (hr : 0 < r)
    {z : ComplexModel n} (hz : closedBall z (2 * r) ⊆ Ω) :
    Tendsto (fun j => ∫ x, u x * explicitRadialKernel r hr j (x - z)) atTop (𝓝 (u z)) := by
  set N : Set (ComplexModel n) := ball z r with hNdef
  set Kc : Set (ComplexModel n) := closedBall z (2 * r) with hKcdef
  have hNΩ : N ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hz)
  have hball : ∀ x ∈ N, closedBall x r ⊆ Kc := fun x hx =>
    closedBall_subset_closedBall' (by rw [mem_ball] at hx; linarith)
  obtain ⟨S, hSk⟩ := exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh hu hr
    isOpen_ball hNΩ (isCompact_closedBall z (2 * r)) hz hball
  have hpL : LocallyIntegrableOn u Ω volume := locallyIntegrableOn_of_plurisubharmonicOn_real hu.1
  have hpLevi := hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hu.1
  set f : ℕ → ComplexModel n → ℝ := fun j =>
    translationPairing volume (Kc.indicator u) (S.kernel j) with hfdef
  have hfPsh : ∀ j, PlurisubharmonicOn (fun x => (f j x : EReal))
      ((⟨N, isOpen_ball⟩ : Opens (ComplexModel n)) : Set (ComplexModel n)) := fun j =>
    (discPshOn_translationPairing_indicator hpL hpLevi (S.kernel_hasCompactSupport j)
      (S.kernel_contDiff j) (S.kernel_nonneg j) (isCompact_closedBall _ _) hz
      (S.translated_tsupport j)).plurisubharmonicOn isOpen_ball
  have hpoint := tendsto_everywhere_of_ae_of_antitone_psh (U := ⟨N, isOpen_ball⟩)
    (hu.1.mono hNΩ) hfPsh (fun x hx => S.antitone_pairing x hx) S.ae_tendsto_pairing
  have hzN : z ∈ N := mem_ball_self hr
  have heq : ∀ j, f j z = ∫ x, u x * explicitRadialKernel r hr j (x - z) := by
    intro j
    simp only [hfdef, translationPairing, hSk]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : explicitRadialKernel r hr j (x - z) = 0
    · simp [hx]
    · have hxs : x - z ∈ closedBall (0 : ComplexModel n) (r / ((j : ℝ) + 1)) := by
        rw [← explicitRadialKernel_tsupport r hr j]
        exact subset_tsupport _ hx
      have hxz : x ∈ Kc := by
        rw [hKcdef, mem_closedBall, dist_eq_norm]
        rw [mem_closedBall, dist_zero_right] at hxs
        have h1 : r / ((j : ℝ) + 1) ≤ r := div_le_self hr.le (by linarith [j.cast_nonneg (α := ℝ)])
        linarith
      simp [indicator_of_mem hxz]
  simpa only [← heq] using hpoint z hzN

/-- The kernel `ρⱼ(· - t)` vanishes outside `B̄(t, r/(j+1))`. -/
theorem explicitRadialKernel_sub_eq_zero_of_lt {r : ℝ} (hr : 0 < r) (j : ℕ)
    {x t : ComplexModel n} (h : r / ((j : ℝ) + 1) < ‖x - t‖) :
    explicitRadialKernel r hr j (x - t) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  rw [explicitRadialKernel_tsupport r hr j, mem_closedBall, dist_zero_right] at hmem
  linarith

/-- If `B̄(t, r) ⊆ D`, multiplying by `ρⱼ(· - t)` does not see the values off `D`. -/
theorem indicator_mul_kernel_eq {D : Opens (ComplexModel n)} {r : ℝ} (hr : 0 < r) (j : ℕ)
    {t : ComplexModel n} (ht : closedBall t r ⊆ D) (ψ : ComplexModel n → ℝ) :
    (fun x => (D : Set (ComplexModel n)).indicator ψ x * explicitRadialKernel r hr j (x - t)) =
      fun x => ψ x * explicitRadialKernel r hr j (x - t) := by
  funext x
  by_cases hx : x ∈ (D : Set (ComplexModel n))
  · rw [indicator_of_mem hx]
  · have hρ : explicitRadialKernel r hr j (x - t) = 0 := by
      refine explicitRadialKernel_sub_eq_zero_of_lt hr j ?_
      have hxr : r < ‖x - t‖ := by
        by_contra h
        exact hx (ht (by rw [mem_closedBall, dist_eq_norm]; linarith))
      have h1 : r / ((j : ℝ) + 1) ≤ r := div_le_self hr.le (by linarith [j.cast_nonneg (α := ℝ)])
      linarith
    rw [hρ, mul_zero, mul_zero]

/-- Bounded measurable functions times `ρⱼ(· - t)` are integrable. -/
theorem integrable_mul_kernel {ψ : ComplexModel n → ℝ} (hψ : Measurable ψ) {B : ℝ}
    (hB : ∀ x, |ψ x| ≤ B) {r : ℝ} (hr : 0 < r) (j : ℕ) (t : ComplexModel n) :
    Integrable (fun x => ψ x * explicitRadialKernel r hr j (x - t)) := by
  have hk : Integrable (fun x => explicitRadialKernel (n := n) r hr j (x - t)) :=
    ((explicitRadialKernel_contDiff r hr j).continuous.integrable_of_hasCompactSupport
      (explicitRadialKernel_hasCompactSupport r hr j)).comp_sub_right t
  refine hk.bdd_mul hψ.aestronglyMeasurable (c := B) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hB x

/-- **Hartogs' lemma on balls**: if `v_j → v` in `L¹_loc(D)` and `v(x) < c`, then `v_j ≤ c` on a
fixed ball around `x` for all large `j`. -/
theorem eventually_le_on_ball_of_localL1 {D : Opens (ComplexModel n)}
    {f : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hf : ∀ j, IsLocallyBoundedPshOn D (f j)) (hv : IsLocallyBoundedPshOn D v)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) atTop (𝓝 0))
    {x : ComplexModel n} (hx : x ∈ D) {c : ℝ} (hc : v x < c) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ j in atTop, ∀ y ∈ ball x R, f j y ≤ c := by
  set A : ℝ := (v x + c) / 2 with hAdef
  have husc : ∀ᶠ y in 𝓝 x, v y < A ∧ y ∈ (D : Set (ComplexModel n)) := by
    refine Eventually.and ?_ (D.isOpen.mem_nhds hx)
    have h := upperSemicontinuousOn_of_isLocallyBoundedPshOn hv x hx A (by rw [hAdef]; linarith)
    rwa [nhdsWithin_eq_nhds.mpr (D.isOpen.mem_nhds hx)] at h
  obtain ⟨ρ0, hρ0, hρ0b⟩ := Metric.eventually_nhds_iff.mp husc
  set R : ℝ := ρ0 / 4 with hRdef
  have hR : 0 < R := by positivity
  have hsub : closedBall x (3 * R) ⊆ ball x ρ0 := closedBall_subset_ball (by rw [hRdef]; linarith)
  have hballD : ball x ρ0 ⊆ D := fun y hy => (hρ0b hy).2
  have hlim' : Tendsto (fun j => ∫⁻ z in closedBall x (3 * R),
      canonicalERealAbsDiff (f j z : EReal) (v z : EReal)) atTop (𝓝 0) := by
    simpa only [canonicalERealAbsDiff_coe_coe] using
      hlim _ (isCompact_closedBall x _) (hsub.trans hballD)
  have hev := NaturalPshHartogsBallEstimate.eventually_le_on_ball_of_lintegral_canonical_tendsto
    (U := ball x ρ0) (fun j => (hf j).1.mono hballD) (hv.1.mono hballD)
    (convex_ball x ρ0).isPreconnected (fun j => ⟨x, mem_ball_self hρ0, EReal.coe_ne_bot _⟩)
    ⟨x, mem_ball_self hρ0, EReal.coe_ne_bot _⟩ volume x hR hsub
    (fun z hz => EReal.coe_le_coe_iff.mpr (hρ0b (hsub hz)).1.le) hlim'
    (δ := (c - v x) / 2) (by linarith)
  refine ⟨R, hR, hev.mono fun j hj y hy => ?_⟩
  have := EReal.coe_le_coe_iff.mp (hj y hy)
  rw [hAdef] at this
  linarith

/-- **Pointwise convergence of the convolution averages** (FPT, Steps 2 and 3 of the proof of
`thm:canonical-grid-self-integral-convergence`, convolution variant): if `f_k → b` in `L¹_loc(D)`,
`f_k(t) → b(t)`, `B̄(t, 2r) ⊆ D` and `s_k → ∞`, then `∫ |f_k - b|(x) ρ_{s_k}(x - t) dx → 0`. -/
theorem tendsto_integral_abs_sub_mul_kernel {D : Opens (ComplexModel n)}
    {f : ℕ → ComplexModel n → ℝ} {b : ComplexModel n → ℝ}
    (hf : ∀ k, IsLocallyBoundedPshOn D (f k)) (hb : IsLocallyBoundedPshOn D b) {T : ℝ}
    (hfT : ∀ k, ∀ z ∈ D, |f k z| ≤ T) (hbT : ∀ z ∈ D, |b z| ≤ T)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun k => ∫⁻ x in K, ENNReal.ofReal |f k x - b x|) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) {t : ComplexModel n} (ht : closedBall t (2 * r) ⊆ D)
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) (hft : Tendsto (fun k => f k t) atTop (𝓝 (b t))) :
    Tendsto (fun k => ∫ x, |f k x - b x| * explicitRadialKernel r hr (s k) (x - t)) atTop
      (𝓝 0) := by
  set ρ : ℕ → ComplexModel n → ℝ := fun k x => explicitRadialKernel r hr (s k) (x - t) with hρdef
  have hρ0 : ∀ k x, 0 ≤ ρ k x := fun k x => explicitRadialKernel_nonneg r hr (s k) _
  have hρ1 : ∀ k, ∫ x, ρ k x = 1 := fun k => by
    simp only [hρdef]
    rw [integral_sub_right_eq_self (fun x => explicitRadialKernel (n := n) r hr (s k) x) t,
      explicitRadialKernel_integral_one]
  have htD : t ∈ (D : Set (ComplexModel n)) := ht (mem_closedBall_self (by linarith))
  have htr : closedBall t r ⊆ D := (closedBall_subset_closedBall (by linarith)).trans ht
  -- integrability through the measurable indicators
  have hint : ∀ (ψ : ComplexModel n → ℝ), Measurable ((D : Set (ComplexModel n)).indicator ψ) →
      ∀ B : ℝ, (∀ z ∈ D, |ψ z| ≤ B) → ∀ k, Integrable (fun x => ψ x * ρ k x) := by
    intro ψ hψ B hB k
    have h := integrable_mul_kernel hψ (B := max B 0) (fun x => by
      by_cases hx : x ∈ (D : Set (ComplexModel n))
      · rw [indicator_of_mem hx]; exact (hB x hx).trans (le_max_left _ _)
      · rw [indicator_of_notMem hx, abs_zero]; exact le_max_right _ _) hr (s k) t
    rwa [indicator_mul_kernel_eq hr (s k) htr ψ] at h
  have hfm : ∀ k, Measurable ((D : Set (ComplexModel n)).indicator (f k)) := fun k =>
    measurable_indicator_of_plurisubharmonicOn (hf k).1
  have hbm : Measurable ((D : Set (ComplexModel n)).indicator b) :=
    measurable_indicator_of_plurisubharmonicOn hb.1
  have hind : ∀ (g : ℝ → ℝ → ℝ), g 0 0 = 0 → ∀ k,
      (D : Set (ComplexModel n)).indicator (fun x => g (f k x) (b x)) =
        fun x => g ((D : Set (ComplexModel n)).indicator (f k) x)
          ((D : Set (ComplexModel n)).indicator b x) := by
    intro g hg k
    funext x
    by_cases hx : x ∈ (D : Set (ComplexModel n))
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, hg]
  have hIf : ∀ k, Integrable (fun x => f k x * ρ k x) := fun k => hint _ (hfm k) T (hfT k) k
  have hIb : ∀ k, Integrable (fun x => b x * ρ k x) := fun k => hint _ hbm T hbT k
  have hIp : ∀ k, Integrable (fun x => max (f k x - b x) 0 * ρ k x) := by
    intro k
    refine hint _ ?_ (2 * T) (fun z hz => ?_) k
    · rw [hind (fun a c => max (a - c) 0) (by simp) k]
      exact ((hfm k).sub hbm).max measurable_const
    · rw [abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (by linarith [(abs_nonneg (b z)).trans (hbT z hz)])
      linarith [(abs_le.mp (hfT k z hz)).2, (abs_le.mp (hbT z hz)).1]
  -- the decomposition `|f - b| = 2 (f - b)₊ - (f - b)`
  have hid : ∀ k, ∫ x, |f k x - b x| * ρ k x =
      2 * (∫ x, max (f k x - b x) 0 * ρ k x) - ((∫ x, f k x * ρ k x) - ∫ x, b x * ρ k x) := by
    intro k
    have hd : Integrable (fun x => f k x * ρ k x - b x * ρ k x) := (hIf k).sub (hIb k)
    have h2 : Integrable (fun x => 2 * (max (f k x - b x) 0 * ρ k x)) := (hIp k).const_mul 2
    calc ∫ x, |f k x - b x| * ρ k x
        = ∫ x, (2 * (max (f k x - b x) 0 * ρ k x) - (f k x * ρ k x - b x * ρ k x)) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          rcases le_total 0 (f k x - b x) with h0 | h0
          · simp only [abs_of_nonneg h0, max_eq_left h0]; ring
          · simp only [abs_of_nonpos h0, max_eq_right h0]; ring
      _ = _ := by rw [integral_sub h2 hd, integral_const_mul, integral_sub (hIf k) (hIb k)]
  have hsubmean : ∀ k, f k t ≤ ∫ x, f k x * ρ k x := fun k =>
    le_integral_mul_explicitRadialKernel (hf k) hr ht (s k)
  have hbconv : Tendsto (fun k => ∫ x, b x * ρ k x) atTop (𝓝 (b t)) :=
    (tendsto_integral_mul_explicitRadialKernel_of_psh hb hr ht).comp hs
  -- the positive part is controlled near `t`
  have hpos : ∀ c : ℝ, b t < c →
      ∀ᶠ k in atTop, ∫ x, max (f k x - b x) 0 * ρ k x ≤ c - ∫ x, b x * ρ k x := by
    intro c hc
    have husc : ∀ᶠ y in 𝓝 t, b y < c := by
      have h := upperSemicontinuousOn_of_isLocallyBoundedPshOn hb t htD c hc
      rwa [nhdsWithin_eq_nhds.mpr (D.isOpen.mem_nhds htD)] at h
    obtain ⟨R0, hR0, hR0b⟩ := Metric.eventually_nhds_iff.mp husc
    obtain ⟨R1, hR1, hev⟩ := eventually_le_on_ball_of_localL1 hf hb hlim htD hc
    have hrad : ∀ᶠ k in atTop, r / ((s k : ℝ) + 1) < min R0 R1 := by
      have h0 : Tendsto (fun k => r / ((s k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1
          (tendsto_natCast_atTop_atTop.comp hs))
      exact (tendsto_order.1 h0).2 _ (lt_min hR0 hR1)
    filter_upwards [hev, hrad] with k hk hkr
    have hle : ∀ x, max (f k x - b x) 0 * ρ k x ≤ (c - b x) * ρ k x := by
      intro x
      by_cases hx : ρ k x = 0
      · rw [hx, mul_zero, mul_zero]
      · have hxt : ‖x - t‖ ≤ r / ((s k : ℝ) + 1) := by
          by_contra h
          exact hx (explicitRadialKernel_sub_eq_zero_of_lt hr (s k) (not_le.mp h))
        have hx0 : dist x t < R0 := by
          rw [dist_eq_norm]; exact hxt.trans_lt (hkr.trans_le (min_le_left _ _))
        have hx1 : x ∈ ball t R1 := by
          rw [mem_ball, dist_eq_norm]; exact hxt.trans_lt (hkr.trans_le (min_le_right _ _))
        have h1 := hk x hx1
        have h2 := hR0b hx0
        exact mul_le_mul_of_nonneg_right (max_le (by linarith) (by linarith)) (hρ0 k x)
    have hc' : Integrable (fun x => c * ρ k x) := (integrable_mul_kernel measurable_const
      (B := |c|) (fun _ => le_rfl) hr (s k) t)
    calc ∫ x, max (f k x - b x) 0 * ρ k x ≤ ∫ x, (c - b x) * ρ k x :=
          integral_mono (hIp k) ((hc'.sub (hIb k)).congr
            (Eventually.of_forall fun x => by
              show c * ρ k x - b x * ρ k x = (c - b x) * ρ k x
              ring)) hle
      _ = c - ∫ x, b x * ρ k x := by
          rw [show (fun x => (c - b x) * ρ k x) = fun x => c * ρ k x - b x * ρ k x by
              funext x; ring, integral_sub hc' (hIb k), integral_const_mul, hρ1, mul_one]
  -- conclusion
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k => ha.trans_le ?_, fun a ha => ?_⟩
  · exact integral_nonneg fun x => mul_nonneg (abs_nonneg _) (hρ0 k x)
  · filter_upwards [hpos (b t + a / 8) (by linarith),
      (tendsto_order.1 hbconv).1 (b t - a / 8) (by linarith),
      (tendsto_order.1 hft).1 (b t - a / 8) (by linarith)] with k hk1 hk2 hk3
    rw [hid k]
    linarith [hsubmean k]

/-- **The pairing of `α ∗ ρⱼ` with a function** (Tonelli): for `φ ≥ 0` bounded on `D` with
measurable restriction, `∫_D φ (α ∗ ρⱼ) dV = ∫ (∫ φ̃(x) ρⱼ(x - t) dx) dα(t)`, `φ̃ = 𝟙_D φ`. -/
theorem lintegral_convDensity_mul_eq {D : Opens (ComplexModel n)} (α : Measure (ComplexModel n))
    [IsFiniteMeasure α] {r : ℝ} (hr : 0 < r) {φ : ComplexModel n → ℝ}
    (hφm : Measurable ((D : Set (ComplexModel n)).indicator φ)) {B : ℝ} (hφ0 : ∀ x, 0 ≤ φ x)
    (hφB : ∀ z ∈ D, φ z ≤ B) (j : ℕ) :
    ∫⁻ x in (D : Set (ComplexModel n)),
        ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (φ x) =
      ∫⁻ t, ENNReal.ofReal (∫ x, (D : Set (ComplexModel n)).indicator φ x *
        explicitRadialKernel r hr j (x - t)) ∂α := by
  set φ' : ComplexModel n → ℝ := (D : Set (ComplexModel n)).indicator φ with hφ'def
  have hDm : MeasurableSet (D : Set (ComplexModel n)) := D.isOpen.measurableSet
  set ρ := explicitRadialKernel (n := n) r hr j with hρdef
  have hρc : Continuous ρ := (explicitRadialKernel_contDiff r hr j).continuous
  have hφ'0 : ∀ x, 0 ≤ φ' x := fun x => by
    by_cases hx : x ∈ (D : Set (ComplexModel n))
    · rw [hφ'def, indicator_of_mem hx]; exact hφ0 x
    · rw [hφ'def, indicator_of_notMem hx]
  have hφ'B : ∀ x, |φ' x| ≤ max B 0 := fun x => by
    by_cases hx : x ∈ (D : Set (ComplexModel n))
    · rw [hφ'def, indicator_of_mem hx, abs_of_nonneg (hφ0 x)]; exact (hφB x hx).trans (le_max_left _ _)
    · rw [hφ'def, indicator_of_notMem hx, abs_zero]; exact le_max_right _ _
  have hL : ∫⁻ x in (D : Set (ComplexModel n)),
      ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (φ x) =
      ∫⁻ x, ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (φ' x) := by
    rw [← lintegral_indicator hDm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ (D : Set (ComplexModel n))
    · simp [hφ'def, indicator_of_mem hx]
    · simp [hφ'def, indicator_of_notMem hx]
  have hdens : ∀ x, ENNReal.ofReal (convDensity α r hr j x) = ∫⁻ t, ENNReal.ofReal (ρ (x - t)) ∂α :=
    fun x => ofReal_integral_eq_lintegral_ofReal (integrable_explicitRadialKernel_sub α hr j x)
      (Eventually.of_forall fun t => explicitRadialKernel_nonneg r hr j _)
  have hmeas : AEMeasurable (Function.uncurry fun (x t : ComplexModel n) =>
      ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal (φ' x)) (volume.prod α) :=
    ((ENNReal.measurable_ofReal.comp (hρc.measurable.comp (measurable_fst.sub measurable_snd))).mul
      (ENNReal.measurable_ofReal.comp (hφm.comp measurable_fst))).aemeasurable
  rw [hL]
  calc ∫⁻ x, ENNReal.ofReal (convDensity α r hr j x) * ENNReal.ofReal (φ' x)
      = ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal (φ' x) ∂α := by
        refine lintegral_congr fun x => ?_
        rw [hdens, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (ρ (x - t)) * ENNReal.ofReal (φ' x) ∂volume ∂α :=
        lintegral_lintegral_swap hmeas
    _ = _ := by
        refine lintegral_congr fun t => ?_
        rw [ofReal_integral_eq_lintegral_ofReal (integrable_mul_kernel hφm (hφ'B) hr j t)
          (Eventually.of_forall fun x => mul_nonneg (hφ'0 x) (explicitRadialKernel_nonneg r hr j _))]
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_mul (hφ'0 x), mul_comm]

/-- **Self-integral convergence for the convolution approximants** (FPT
`thm:canonical-grid-self-integral-convergence`, second convergence, convolution variant, for
functions bounded by `T`): if plurisubharmonic `f_k` with `|f_k| ≤ T` converge to `b` in
`L¹_loc(D)` and `s_k → ∞`, then `∫_D |f_k - b| (α ∗ ρ_{s_k}) dV → 0`. -/
theorem tendsto_lintegral_convDensity_abs_sub {D : Opens (ComplexModel n)}
    (α : Measure (ComplexModel n)) [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hαK : α Kᶜ = 0) {r : ℝ} (hr : 0 < r) (hKD : cthickening (2 * r) K ⊆ D)
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn D w) {a M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ D, a ≤ w z ∧ w z ≤ a + M)
    (hα : α.restrict D ≤ canonicalBedfordTaylorMeasure D w hw)
    {f : ℕ → ComplexModel n → ℝ} {b : ComplexModel n → ℝ}
    (hf : ∀ k, IsLocallyBoundedPshOn D (f k)) (hb : IsLocallyBoundedPshOn D b) {T : ℝ}
    (hfT : ∀ k, ∀ z ∈ D, |f k z| ≤ T)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun k => ∫⁻ x in K, ENNReal.ofReal |f k x - b x|) atTop (𝓝 0))
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) :
    Tendsto (fun k => ∫⁻ x in (D : Set (ComplexModel n)),
      ENNReal.ofReal (convDensity α r hr (s k) x) * ENNReal.ofReal |f k x - b x|) atTop (𝓝 0) := by
  have hbT := abs_le_of_localL1 hf hb hfT hlim
  have hKsub : K ⊆ D := (self_subset_cthickening K).trans hKD
  have hαK' : ∀ᵐ t ∂α, t ∈ K :=
    (measure_eq_zero_iff_ae_notMem.mp hαK).mono fun t ht => by simpa using ht
  have hαD : α.restrict D = α :=
    Measure.restrict_eq_self_of_ae_mem (hαK'.mono fun t ht => hKsub ht)
  set φ : ℕ → ComplexModel n → ℝ := fun k x => |f k x - b x| with hφdef
  have hφm : ∀ k, Measurable ((D : Set (ComplexModel n)).indicator (φ k)) := by
    intro k
    have h : (D : Set (ComplexModel n)).indicator (φ k) =
        fun x => |(D : Set (ComplexModel n)).indicator (f k) x -
          (D : Set (ComplexModel n)).indicator b x| := by
      funext x
      by_cases hx : x ∈ (D : Set (ComplexModel n))
      · simp [hφdef, indicator_of_mem hx]
      · simp [hφdef, indicator_of_notMem hx]
    rw [h]
    exact continuous_abs.measurable.comp ((measurable_indicator_of_plurisubharmonicOn (hf k).1).sub
      (measurable_indicator_of_plurisubharmonicOn hb.1))
  have hφB : ∀ k, ∀ z ∈ D, φ k z ≤ 2 * |T| := fun k z hz => by
    calc |f k z - b z| ≤ |f k z| + |b z| := abs_sub _ _
      _ ≤ |T| + |T| := add_le_add ((hfT k z hz).trans (le_abs_self T)) ((hbT z hz).trans (le_abs_self T))
      _ = 2 * |T| := by ring
  set I : ℕ → ComplexModel n → ℝ := fun k t => ∫ x, (D : Set (ComplexModel n)).indicator (φ k) x *
    explicitRadialKernel r hr (s k) (x - t) with hIdef
  have hrw : (fun k => ∫⁻ x in (D : Set (ComplexModel n)),
      ENNReal.ofReal (convDensity α r hr (s k) x) * ENNReal.ofReal |f k x - b x|) =
      fun k => ∫⁻ t, ENNReal.ofReal (I k t) ∂α := by
    funext k
    exact lintegral_convDensity_mul_eq α hr (hφm k) (fun x => abs_nonneg _) (hφB k) (s k)
  rw [hrw]
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hP2 := tendsto_integral_abs_sub_of_localL1 (fun k => hf (ns k)) hb (fun k => hfT (ns k))
    (fun K hK hKD => (hlim K hK hKD).comp hns) (capacityNull_of_le_ma hw hM hwb hα) (ν := α)
  rw [hαD] at hP2
  have hTIM : TendstoInMeasure α (fun k => f (ns k)) atTop b := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hcheb : ∀ k, α {x | ε ≤ dist (f (ns k) x) (b x)} ≤
        ENNReal.ofReal (ε⁻¹ * ∫ x, |f (ns k) x - b x| ∂α) := by
      intro k
      have hi : Integrable (fun x => |f (ns k) x - b x|) α := by
        rw [← hαD]
        exact ((integrable_of_isLocallyBoundedPshOn (ν := α) (hf (ns k)) (hfT (ns k))).sub
          (integrable_of_isLocallyBoundedPshOn (ν := α) hb hbT)).abs
      have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun x => abs_nonneg
        (f (ns k) x - b x)) hi ε
      rw [← ofReal_measureReal (measure_ne_top α _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_inv_mul_iff₀ hε]
      simpa only [Real.dist_eq] using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hcheb
    simpa using ENNReal.tendsto_ofReal (hP2.const_mul ε⁻¹)
  obtain ⟨ms, hms, hae⟩ := hTIM.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hsub : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
  have hDCT := tendsto_lintegral_of_dominated_convergence (μ := α)
    (F := fun k t => ENNReal.ofReal (I (ns (ms k)) t)) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal (2 * |T|))
    (fun k => by
      refine ENNReal.measurable_ofReal.comp ?_
      have hmeas : Measurable (Function.uncurry fun (t x : ComplexModel n) =>
          (D : Set (ComplexModel n)).indicator (φ (ns (ms k))) x *
            explicitRadialKernel r hr (s (ns (ms k))) (x - t)) :=
        ((hφm _).comp measurable_snd).mul
          ((explicitRadialKernel_contDiff r hr _).continuous.measurable.comp
            (measurable_snd.sub measurable_fst))
      exact hmeas.stronglyMeasurable.integral_prod_right.measurable)
    (fun k => Eventually.of_forall fun t => by
      refine ENNReal.ofReal_le_ofReal ?_
      calc I (ns (ms k)) t ≤ ∫ x, 2 * |T| * explicitRadialKernel r hr (s (ns (ms k))) (x - t) := by
            refine integral_mono (integrable_mul_kernel (hφm _) (B := 2 * |T|) (fun x => by
              by_cases hx : x ∈ (D : Set (ComplexModel n))
              · rw [indicator_of_mem hx, abs_of_nonneg (abs_nonneg _)]; exact hφB _ x hx
              · rw [indicator_of_notMem hx, abs_zero]; positivity) hr _ t)
              (integrable_mul_kernel measurable_const (B := abs (2 * |T|)) (fun _ => le_rfl) hr _ t)
              fun x => mul_le_mul_of_nonneg_right ?_ (explicitRadialKernel_nonneg r hr _ _)
            by_cases hx : x ∈ (D : Set (ComplexModel n))
            · rw [indicator_of_mem hx]; exact hφB _ x hx
            · rw [indicator_of_notMem hx]; positivity
        _ = 2 * |T| := by
            rw [integral_const_mul, integral_sub_right_eq_self
              (fun x => explicitRadialKernel (n := n) r hr (s (ns (ms k))) x) t,
              explicitRadialKernel_integral_one, mul_one])
    (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top α _))
    (by
      filter_upwards [hae, hαK'] with t ht htK
      have ht2 : closedBall t (2 * r) ⊆ D := (closedBall_subset_cthickening htK _).trans hKD
      have htr : closedBall t r ⊆ D := (closedBall_subset_closedBall (by linarith)).trans ht2
      have hpt := tendsto_integral_abs_sub_mul_kernel (fun k => hf (ns (ms k))) hb
        (fun k => hfT (ns (ms k))) hbT (fun K hK hKD => (hlim K hK hKD).comp hsub) hr ht2
        (hs.comp hsub) ht
      have heq : ∀ k, I (ns (ms k)) t = ∫ x, |f (ns (ms k)) x - b x| *
          explicitRadialKernel r hr (s (ns (ms k))) (x - t) := fun k => by
        simp only [hIdef]
        rw [indicator_mul_kernel_eq hr _ htr]
      simp only [heq]
      simpa using ENNReal.tendsto_ofReal hpt)
  simpa using hDCT

end SGPT.Envelopes.MADirichlet

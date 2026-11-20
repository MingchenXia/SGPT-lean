import SGPT.Okounkov.TranscendentalRelGenDivisibility
import SGPT.Foundations.Analysis.Pending.RiemannExtensionThin
import SGPT.Foundations.Analysis.Pending.HiepSliceLemma
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# `L²` Riemann extension across a hypersurface

Plan `tok/RELGEN2/PLAN.md`, step P4 (blueprint `l2:l2-riemann-extension`, chapter
`claude-tok-l2`).

Let `U ⊆ ℂᵈ` be open, `k` holomorphic on `U` and not identically zero near any point of `U`, and
`F` holomorphic on `U \ {k = 0}` and square integrable near every point of `U`. Then `F` extends
holomorphically to `U` (`exists_extension_of_locally_sq_integrable`; Demailly, *Complex analytic
and differential geometry*, VIII.7.3 for `L²` functions; Riemann's theorem for bounded ones).

Proof: by the sub-mean value inequality on balls `B(y, ρ)` avoiding `{k = 0}` and the Lipschitz
bound `|k(w) - k(y)| ≤ L |w - y|`, the radius `ρ` can be taken `≥ c |k(y)|`, so
`|k(y)|^N |F(y)|² ≤ C` (`N = dim_ℝ`): `H = F k^N` is bounded near `{k = 0}` and extends
(`RiemannExtensionThin.exists_extension_of_thin`). Then `∫ |H|² / |k|^{2N} = ∫ |F|² < ∞`, so
`H = a k^N` near every point (`l2DivisibilityStatement`, `𝓘(N log |k|²) = (k^N)`), i.e. `F = a` off
`{k = 0}`: `F` is locally bounded near `{k = 0}` and extends by Riemann's theorem again.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

noncomputable section

namespace SGPT.Okounkov.TranscendentalL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {d : ℕ}

/-- **`k^N F` is bounded near the zero set of `k`** when `F` is square integrable: the
quantitative sub-mean value bound (plan P4, first step). -/
theorem exists_bound_mul_pow_of_lintegral_sq {U : Set (ComplexModel d)} (hU : IsOpen U)
    {k : ComplexModel d → ℂ} (hk : DifferentiableOn ℂ k U) {F : ComplexModel d → ℂ}
    (hF : DifferentiableOn ℂ F (U ∩ {x | k x ≠ 0})) {t : ComplexModel d} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hr₀U : ball t r₀ ⊆ U)
    (hA : ∫⁻ y in ball t r₀, ENNReal.ofReal (‖F y‖ ^ 2) ≠ ⊤) :
    ∃ C : ℝ, ∀ y ∈ ball t (r₀ / 4), k y ≠ 0 →
      ‖F y * k y ^ Module.finrank ℝ (ComplexModel d)‖ ≤ C := by
  rcases subsingleton_or_nontrivial (ComplexModel d) with hs | hnt
  · exact ⟨‖F t * k t ^ Module.finrank ℝ (ComplexModel d)‖, fun y _ _ ↦ by
      rw [Subsingleton.elim y t]⟩
  set N := Module.finrank ℝ (ComplexModel d) with hN
  set r := r₀ / 4 with hr
  have hr0 : 0 < r := by positivity
  set Kc := closedBall t (2 * r) with hKc
  have hKcU : Kc ⊆ U := fun w hw ↦ hr₀U (by
    rw [mem_closedBall] at hw; rw [mem_ball]; linarith)
  have hKcc : IsCompact Kc := isCompact_closedBall _ _
  have hkc : ContinuousOn k U := hk.continuousOn
  have hkd : ContDiffOn ℂ ∞ k U := contDiffOn_of_differentiableOn_complex hk hU
  have hfdc : ContinuousOn (fderiv ℂ k) U :=
    hkd.continuousOn_fderiv_of_isOpen hU (by simp)
  obtain ⟨L₀, hL₀⟩ := hKcc.exists_bound_of_continuousOn (hfdc.mono hKcU)
  obtain ⟨Mk₀, hMk₀⟩ := hKcc.exists_bound_of_continuousOn (hkc.mono hKcU)
  set L := max L₀ 0 + 1 with hL
  set Mk := max Mk₀ 0 + 1 with hMk
  have hL0 : 0 < L := by positivity
  have hMk0 : 0 < Mk := by positivity
  set c₁ := min (r / Mk) (1 / (2 * L)) with hc₁
  have hc₁0 : 0 < c₁ := lt_min (by positivity) (by positivity)
  set V₁ : ℝ≥0∞ := volume (ball (0 : ComplexModel d) 1) with hV₁
  have hV₁0 : V₁ ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hV₁top : V₁ ≠ ⊤ := measure_ball_lt_top.ne
  set A := ∫⁻ y in ball t r₀, ENNReal.ofReal (‖F y‖ ^ 2) with hAdef
  set B : ℝ := (A / V₁).toReal with hB
  refine ⟨Real.sqrt (Mk ^ N * B / c₁ ^ N), fun y hy hky ↦ ?_⟩
  have hyK : ‖k y‖ < Mk := by
    have := hMk₀ y (by rw [mem_closedBall]; rw [mem_ball] at hy; linarith)
    rw [hMk]; linarith [le_max_left Mk₀ 0]
  have hky0 : 0 < ‖k y‖ := norm_pos_iff.mpr hky
  set ρ := c₁ * ‖k y‖ with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ ≤ r := by
    have h1 : c₁ ≤ r / Mk := min_le_left _ _
    calc ρ = c₁ * ‖k y‖ := rfl
      _ ≤ r / Mk * Mk := mul_le_mul h1 hyK.le hky0.le (by positivity)
      _ = r := by field_simp
  have hρL : L * ρ ≤ ‖k y‖ / 2 := by
    have h1 : c₁ ≤ 1 / (2 * L) := min_le_right _ _
    calc L * ρ = L * c₁ * ‖k y‖ := by ring
      _ ≤ L * (1 / (2 * L)) * ‖k y‖ := by gcongr
      _ = ‖k y‖ / 2 := by field_simp
  -- the closed ball `B(y, ρ)` avoids `{k = 0}`
  have hball : closedBall y ρ ⊆ U ∩ {x | k x ≠ 0} := by
    intro w hw
    have hwK : w ∈ Kc := by
      rw [mem_closedBall] at hw ⊢; rw [mem_ball] at hy; linarith [dist_triangle w y t]
    have hyK' : y ∈ Kc := by rw [mem_closedBall]; rw [mem_ball] at hy; linarith
    refine ⟨hKcU hwK, ?_⟩
    have hlip : ‖k w - k y‖ ≤ L * ‖w - y‖ := by
      refine (convex_closedBall t (2 * r)).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz ↦ hk.differentiableAt (hU.mem_nhds (hKcU hz))) (fun z hz ↦ ?_) hyK' hwK
      exact (hL₀ z hz).trans (by rw [hL]; linarith [le_max_left L₀ 0])
    have hwy : ‖w - y‖ ≤ ρ := by rw [← dist_eq_norm]; exact hw
    have : ‖k y‖ - ‖k w‖ ≤ ‖k w - k y‖ := by
      have := norm_sub_norm_le (k y) (k w)
      rw [norm_sub_rev] at this; linarith [norm_sub_rev (k y) (k w)]
    have hkw : ‖k y‖ / 2 ≤ ‖k w‖ := by nlinarith
    intro hk0
    rw [hk0, norm_zero] at hkw
    linarith
  -- the sub-mean value inequality
  have hopen : IsOpen (U ∩ {x | k x ≠ 0}) :=
    hkc.isOpen_inter_preimage hU isOpen_compl_singleton
  have hmv := SGPT.Foundations.Analysis.Pending.lintegral_ball_normSq_ge hopen hF hρ0 hball
  have hsub : ball y ρ ⊆ ball t r₀ := fun w hw ↦ by
    rw [mem_ball] at hw hy ⊢; linarith [dist_triangle w y t]
  have hle : volume (ball y ρ) * ENNReal.ofReal (‖F y‖ ^ 2) ≤ A :=
    hmv.trans (lintegral_mono_set hsub)
  rw [Measure.addHaar_ball _ _ hρ0.le, mul_comm (ENNReal.ofReal _) V₁, mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)] at hle
  have hle' : ENNReal.ofReal (ρ ^ N * ‖F y‖ ^ 2) ≤ A / V₁ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hV₁0) (Or.inl hV₁top), mul_comm]
    exact hle
  have hBtop : A / V₁ ≠ ⊤ := ENNReal.div_ne_top hA hV₁0
  have hρF : ρ ^ N * ‖F y‖ ^ 2 ≤ B := (ENNReal.ofReal_le_iff_le_toReal hBtop).mp hle'
  -- conclusion
  rw [norm_mul, norm_pow]
  refine Real.le_sqrt_of_sq_le ?_
  have hkN : ‖k y‖ ^ N ≤ Mk ^ N := pow_le_pow_left₀ hky0.le hyK.le N
  have hρN : ρ ^ N = c₁ ^ N * ‖k y‖ ^ N := by rw [hρ, mul_pow]
  rw [hρN] at hρF
  have hc₁N : 0 < c₁ ^ N := pow_pos hc₁0 N
  rw [le_div_iff₀ hc₁N]
  calc (‖F y‖ * ‖k y‖ ^ N) ^ 2 * c₁ ^ N = ‖k y‖ ^ N * (c₁ ^ N * ‖k y‖ ^ N * ‖F y‖ ^ 2) := by
        ring
    _ ≤ Mk ^ N * B := by
        refine mul_le_mul hkN hρF (by positivity) (by positivity)

/-- **`L²` Riemann extension across a hypersurface** (plan P4, blueprint
`l2:l2-riemann-extension`). Let `U ⊆ ℂᵈ` be open, `k` holomorphic on `U` and not identically zero
near any point of `U`, and `F` holomorphic on `U \ {k = 0}` with `∫ |F|² < ∞` on a ball around
every point of `U`. Then `F` extends to a holomorphic function on `U`. -/
theorem exists_extension_of_locally_sq_integrable {U : Set (ComplexModel d)} (hU : IsOpen U)
    {k : ComplexModel d → ℂ} (hk : DifferentiableOn ℂ k U)
    (hkne : ∀ x ∈ U, ¬ ∀ᶠ y in 𝓝 x, k y = 0) {F : ComplexModel d → ℂ}
    (hF : DifferentiableOn ℂ F (U ∩ {x | k x ≠ 0}))
    (hL2 : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∫⁻ y in ball x r, ENNReal.ofReal (‖F y‖ ^ 2) ≠ ⊤) :
    ∃ G : ComplexModel d → ℂ, DifferentiableOn ℂ G U ∧ EqOn G F (U ∩ {x | k x ≠ 0}) := by
  set T := U ∩ {x | k x = 0} with hT
  have hUT : U \ T = U ∩ {x | k x ≠ 0} := by
    ext x
    constructor
    · intro h; exact ⟨h.1, fun h0 ↦ h.2 ⟨h.1, h0⟩⟩
    · intro h; exact ⟨h.1, fun hT ↦ h.2 hT.2⟩
  have hkc : ContinuousOn k U := hk.continuousOn
  have hUTo : IsOpen (U \ T) := by
    rw [hUT]; exact hkc.isOpen_inter_preimage hU isOpen_compl_singleton
  have hloc : ∀ t ∈ T, ∃ r > 0, ball t r ⊆ U ∧ ∃ h : ComplexModel d → ℂ,
      DifferentiableOn ℂ h (ball t r) ∧ (¬ ∀ᶠ z in 𝓝 t, h z = 0) ∧
        ∀ z ∈ ball t r, z ∈ T → h z = 0 := by
    intro t ht
    obtain ⟨r, hr, hrU, -⟩ := hL2 t ht.1
    exact ⟨r, hr, hrU, k, hk.mono hrU, hkne t ht.1, fun z _ hz ↦ hz.2⟩
  set N := Module.finrank ℝ (ComplexModel d) with hN
  -- Step 1: `H = F k^N` extends
  have hH : DifferentiableOn ℂ (fun x ↦ F x * k x ^ N) (U \ T) := by
    rw [hUT]
    exact hF.mul ((hk.mono inter_subset_left).pow N)
  have hHbdd : ∀ t ∈ T, ∃ V ∈ 𝓝 t, ∃ C, ∀ z ∈ V \ T, ‖F z * k z ^ N‖ ≤ C := by
    intro t ht
    obtain ⟨r₀, hr₀, hr₀U, hA⟩ := hL2 t ht.1
    obtain ⟨C, hC⟩ := exists_bound_mul_pow_of_lintegral_sq hU hk hF hr₀ hr₀U hA
    refine ⟨ball t (r₀ / 4), ball_mem_nhds t (by positivity), C, fun z hz ↦ ?_⟩
    have hzU : z ∈ U := hr₀U (ball_subset_ball (by linarith) hz.1)
    exact hC z hz.1 fun h0 ↦ hz.2 ⟨hzU, h0⟩
  obtain ⟨H, hHd, hHeq⟩ := RiemannExtensionThin.exists_extension_of_thin hUTo hH hloc hHbdd
  -- Step 2: `H = a k^N` near every point, so `F` is locally bounded
  have hFbdd : ∀ t ∈ T, ∃ V ∈ 𝓝 t, ∃ C, ∀ z ∈ V \ T, ‖F z‖ ≤ C := by
    intro t ht
    obtain ⟨r, hr, hrU, hA⟩ := hL2 t ht.1
    have hfreq : ∀ w ∈ ball t r, ∃ᶠ v in 𝓝 w, k v ≠ 0 := fun w hw ↦ by
      have := hkne w (hrU hw)
      rw [not_eventually] at this
      exact this
    have hae : ∀ᵐ w ∂(volume.restrict (ball t r)), k w ≠ 0 :=
      LelongPoincareDivisor.ae_ne_zero isOpen_ball (hk.mono hrU) hfreq
    have hfin : (∫⁻ w in ball t r, ENNReal.ofReal (‖H w‖ ^ 2) /
        ENNReal.ofReal (‖k w‖ ^ (2 * N))) ≠ ⊤ := by
      refine ne_of_eq_of_ne (lintegral_congr_ae ?_) hA
      filter_upwards [hae, ae_restrict_mem measurableSet_ball] with w hkw hw
      have hwUT : w ∈ U \ T := hUT ▸ ⟨hrU hw, hkw⟩
      rw [hHeq hwUT, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm N 2,
        ENNReal.ofReal_mul (by positivity)]
      have hpos : 0 < ‖k w‖ ^ (2 * N) := pow_pos (norm_pos_iff.mpr hkw) _
      rw [ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top]
    obtain ⟨a, ha, haeq⟩ := TranscendentalRelGen.l2DivisibilityStatement d t r hr H k (hHd.mono hrU) (hk.mono hrU)
      (hkne t ht.1) N hfin
    have hac : ContinuousAt a t := ha.self_of_nhds.continuousAt
    obtain ⟨V, hV, hVa⟩ : ∃ V ∈ 𝓝 t, ∀ z ∈ V, ‖a z‖ ≤ ‖a t‖ + 1 ∧ H z = a z * k z ^ N ∧
        z ∈ U := by
      refine ⟨_, (hac.eventually (Metric.ball_mem_nhds (a t) one_pos)).and
        (haeq.and (hU.mem_nhds ht.1)), fun z hz ↦ ⟨?_, hz.2.1, hz.2.2⟩⟩
      have h1 : dist (a z) (a t) < 1 := hz.1
      have := norm_sub_norm_le (a z) (a t)
      rw [← dist_eq_norm] at this
      linarith
    refine ⟨V, hV, ‖a t‖ + 1, fun z hz ↦ ?_⟩
    obtain ⟨hz1, hz2, hz3⟩ := hVa z hz.1
    have hkz : k z ≠ 0 := fun h0 ↦ hz.2 ⟨hz3, h0⟩
    have hzUT : z ∈ U \ T := ⟨hz3, hz.2⟩
    have hFz : F z = a z := by
      have h1 := hHeq hzUT
      rw [hz2] at h1
      exact (mul_right_cancel₀ (pow_ne_zero N hkz) h1).symm
    rw [hFz]; exact hz1
  obtain ⟨G, hG, hGeq⟩ := RiemannExtensionThin.exists_extension_of_thin hUTo
    (hUT ▸ hF) hloc hFbdd
  exact ⟨G, hG, hUT ▸ hGeq⟩

end SGPT.Okounkov.TranscendentalL2

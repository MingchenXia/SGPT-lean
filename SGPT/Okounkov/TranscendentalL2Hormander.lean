import SGPT.Foundations.Analysis.Pending.HormanderL2Theorem

/-!
# Hörmander's `L²` estimate on open sets with a strictly plurisubharmonic exhaustion

Plan `tok/RELGEN2/PLAN.md`, step P1 (blueprint `l2:hormander-exhaustion`, chapter
`claude-tok-l2`).

The workspace proves Hörmander's estimate for `∂̄` on **bounded convex** domains
(`SGPT.Foundations.Analysis.Pending.Hormander.hormanderL2Estimate`). Convexity enters that proof only
through one smooth strictly convex function `s` with `{s ≤ 1}` a compact subset of the domain and
`s ≤ 1/2` on the compact set `K` (`exists_smooth_convex_exhaustion`): the cut-offs are `θ_k ∘ s` and
the auxiliary weights are functions of `s`. The Bochner--Kodaira a priori estimate, the density
of test forms (Hörmander's Lemma 4.1.3) and the Hilbert space argument hold on every open set.

Here the convex function is replaced by an arbitrary smooth function `s` which is strictly
plurisubharmonic on `{s < 1}` (`ε ‖v‖² ≤ Levi s (v)`), with `{s ≤ 1}` compact inside the open set
`D` and `s ≤ 1/2` on `K`. This is Hörmander's setting of a pseudoconvex domain with a smooth
strictly plurisubharmonic exhaustion function (Hörmander, *An introduction to complex analysis in
several variables*, Theorems 4.2.2 and 5.2.10; Demailly, *Complex analytic and differential
geometry*, VIII.6.5), localized to a compact set as in the convex case.

* `exists_cutoffData_of_exhaustion`: the cut-off and weight data of Hörmander's three-weight
  method from such an `s` (TN `exists_hormanderCutoffData`, with the convex exhaustion replaced
  by `s`).
* `hormanderL2_of_exhaustion`: the estimate (TN `hormanderL2Estimate_of_density`, whose proof
  is reused verbatim apart from convexity), in the form of `HormanderL2Estimate` without the
  convexity of the subdomain `D'`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Metric Complex
open scoped Topology ContDiff ComplexConjugate InnerProductSpace

noncomputable section

namespace SGPT.Okounkov.TranscendentalL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending.CauchyGreen

variable {n : ℕ}

/-- **Cut-off and weight data from a strictly plurisubharmonic exhaustion** (plan P1;
TN `exists_hormanderCutoffData` with the convex exhaustion replaced by `s`). Let `s` be smooth,
`ε ‖v‖² ≤ Levi s (v)` on `{s < 1}`, `{s ≤ 1}` compact and contained in `L`, and `s ≤ 1/2` on `K`.
There are an open `L' ⋐ L`, an open `U₀` with `K ⊆ U₀ ⊆ L'`, cut-offs `η k` compactly supported
in `L'` and eventually `1` near every point of `L'`, and weights `ψ₀ ≥ 0`, `χ` vanishing on `U₀`,
with `|∇η_k|² ≤ e^{ψ₀}`, `2ψ₀ ≤ χ` and `A |∇ψ₀|² |ξ|² ≤ Levi χ (ξ)` on `L'`. -/
theorem exists_cutoffData_of_exhaustion {L K : Set (ComplexModel n)} (A : ℝ)
    {s : ComplexModel n → ℝ} {ε : ℝ} (hε : 0 < ε) (hscd : ContDiff ℝ ∞ s)
    (hScpt : IsCompact {x | s x ≤ 1}) (hsL : {x | s x ≤ 1} ⊆ L) (hsK : ∀ x ∈ K, s x ≤ 1 / 2)
    (hslevi : ∀ x, s x < 1 → ∀ v, ε * ‖v‖ ^ 2 ≤ leviForm s x v) :
    ∃ (L' : Set (ComplexModel n)) (U₀ : Set (ComplexModel n)) (η : ℕ → ComplexModel n → ℝ)
      (ψ₀ χ : ComplexModel n → ℝ),
      IsOpen L' ∧ closure L' ⊆ L ∧ IsCompact (closure L') ∧ IsOpen U₀ ∧ K ⊆ U₀ ∧ U₀ ⊆ L' ∧
      (∀ k, ContDiff ℝ ∞ (η k) ∧ HasCompactSupport (η k) ∧ tsupport (η k) ⊆ L' ∧
        ∀ x, 0 ≤ η k x ∧ η k x ≤ 1) ∧
      (∀ x ∈ L', ∀ᶠ k in Filter.atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1) ∧
      ContDiffOn ℝ ∞ ψ₀ L' ∧ ContDiffOn ℝ ∞ χ L' ∧
      (∀ k, ∀ x ∈ L', ‖fderiv ℝ (η k) x‖ ^ 2 ≤ Real.exp (ψ₀ x)) ∧
      (∀ x, 0 ≤ ψ₀ x) ∧ (∀ x ∈ U₀, ψ₀ x = 0 ∧ χ x = 0) ∧
      (∀ x ∈ L', 2 * ψ₀ x ≤ χ x) ∧
      (∀ x ∈ L', ∀ ξ, A * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤ leviForm χ x ξ) ∧
      (∀ x ∈ L', ∀ ξ, 0 ≤ leviForm χ x ξ) := by
  have hsc : Continuous s := hscd.continuous
  obtain ⟨G₀, hG₀⟩ := hScpt.exists_bound_of_continuousOn
    (hscd.continuous_fderiv (by norm_cast)).continuousOn
  set G : ℝ := max G₀ 0 with hGdef
  have hG0 : 0 ≤ G := le_max_right _ _
  have hG : ∀ x, s x < 1 → ‖fderiv ℝ s x‖ ≤ G := fun x hx ↦
    (hG₀ x (show s x ≤ 1 from hx.le)).trans (le_max_left _ _)
  obtain ⟨M, hM⟩ := exists_abs_deriv_smoothTransition_le
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- the weight profile `φ`
  have hg₁ : ∀ t < (1 : ℝ), BddAbove ((fun t ↦ (2 * M * G) ^ 2 / (1 - t) ^ 2) ''
      Icc ((4 / 5 + 1) / 2) t) := fun t ht ↦ by
    refine isCompact_Icc.bddAbove_image (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    intro u hu
    have : u < 1 := hu.2.trans_lt ht
    exact pow_ne_zero 2 (by linarith)
  obtain ⟨φ, hφcd, hφ0, hφzero, -, hφbig⟩ :=
    exists_smooth_convex_majorant (by norm_num : (4 / 5 : ℝ) < 1) _ hg₁
  have hφd0 : ∀ t < (4 / 5 : ℝ), deriv φ t = 0 := fun t ht ↦ by
    have : φ =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds ht] with u hu using hφzero u hu.le
    rw [this.deriv_eq]
    simp
  -- the convex profile `χ₀`
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hg₂ : ∀ t < (1 : ℝ), BddAbove ((fun t ↦ max (2 * φ t) (A' * G ^ 2 * deriv φ t ^ 2 / ε)) ''
      Icc ((3 / 5 + 1) / 2) t) := fun t ht ↦ by
    have hsub : Icc ((3 / 5 + 1) / 2) t ⊆ Iio 1 := fun u hu ↦ hu.2.trans_lt ht
    have h1 := (hφcd.continuousOn).mono hsub
    have h2 := (hφcd.continuousOn_deriv_of_isOpen isOpen_Iio (by norm_cast)).mono hsub
    have h3 : ContinuousOn (fun t ↦ 2 * φ t) (Icc ((3 / 5 + 1) / 2) t) :=
      continuousOn_const.mul h1
    have h4 : ContinuousOn (fun t ↦ A' * G ^ 2 * deriv φ t ^ 2 / ε) (Icc ((3 / 5 + 1) / 2) t) :=
      (continuousOn_const.mul (h2.pow 2)).div_const ε
    exact isCompact_Icc.bddAbove_image (h3.sup h4)
  obtain ⟨χ₀, hχcd, hχ0, hχzero, hχd, hχbig⟩ :=
    exists_smooth_convex_majorant (by norm_num : (3 / 5 : ℝ) < 1) _ hg₂
  have hχat : ∀ t < (1 : ℝ), ContDiffAt ℝ 2 χ₀ t := fun t ht ↦
    (hχcd.contDiffAt (Iio_mem_nhds ht)).of_le (by norm_cast)
  have hsat : ∀ x, ContDiffAt ℝ 2 s x := fun x ↦ (hscd.of_le (by norm_cast)).contDiffAt
  have hlevi : ∀ x, s x < 1 → ∀ ξ,
      deriv χ₀ (s x) * (ε * ‖ξ‖ ^ 2) ≤ leviForm (fun y ↦ χ₀ (s y)) x ξ := fun x hx ξ ↦
    (mul_le_mul_of_nonneg_left (hslevi x hx ξ) (hχd _ hx).1).trans
      (le_leviForm_comp_real (hχat _ hx) (hsat x) (hχd _ hx).2 ξ)
  refine ⟨{x | s x < 1}, {x | s x < 3 / 5}, fun k x ↦ cutoffProfile k (s x),
    fun x ↦ φ (s x), fun x ↦ χ₀ (s x), isOpen_lt hsc continuous_const,
    (closure_lt_subset_le hsc continuous_const).trans hsL,
    hScpt.of_isClosed_subset isClosed_closure (closure_lt_subset_le hsc continuous_const),
    isOpen_lt hsc continuous_const,
    fun x hx ↦ (hsK x hx).trans_lt (by norm_num),
    fun x (hx : s x < 3 / 5) ↦ show s x < 1 by linarith, fun k ↦ ?_, fun x hx ↦ ?_,
    hφcd.comp hscd.contDiffOn fun x hx ↦ hx, hχcd.comp hscd.contDiffOn fun x hx ↦ hx,
    fun k x hx ↦ ?_, fun x ↦ hφ0 _, fun x (hx : s x < 3 / 5) ↦
      ⟨hφzero _ (by linarith), hχzero _ hx.le⟩, fun x hx ↦ ?_, fun x hx ξ ↦ ?_,
    fun x hx ξ ↦ ?_⟩
  · -- the cutoffs
    have hw := cutoffWidth_pos k
    have hsupp : tsupport (fun x ↦ cutoffProfile k (s x)) ⊆ {x | s x ≤ 1 - cutoffWidth k} := by
      refine closure_minimal (fun x hx ↦ ?_) (isClosed_le hsc continuous_const)
      by_contra h
      exact hx (cutoffProfile_of_ge (not_le.mp h).le)
    refine ⟨(contDiff_cutoffProfile k).comp hscd,
      hScpt.of_isClosed_subset (isClosed_tsupport _) fun x hx ↦ ?_, fun x hx ↦ ?_,
      fun x ↦ ⟨cutoffProfile_nonneg _ _, cutoffProfile_le_one _ _⟩⟩
    · exact (show s x ≤ 1 - cutoffWidth k from hsupp hx).trans (by linarith)
    · exact (show s x ≤ 1 - cutoffWidth k from hsupp hx).trans_lt (by linarith)
  · -- the cutoffs are eventually `1` near each point
    have hx' : s x < 1 := hx
    obtain ⟨k₀, hk₀⟩ := exists_two_mul_cutoffWidth_lt (sub_pos.mpr hx')
    filter_upwards [eventually_ge_atTop k₀] with k hk
    have hlt : s x < 1 - 2 * cutoffWidth k := by linarith [hk₀ k hk]
    filter_upwards [(isOpen_lt hsc continuous_const).mem_nhds hlt] with y hy
    exact cutoffProfile_of_le (le_of_lt hy)
  · -- the gradient bound for the cutoffs
    have hx' : s x < 1 := hx
    have hn : ‖fderiv ℝ (fun y ↦ cutoffProfile k (s y)) x‖ ≤
        |deriv (cutoffProfile k) (s x)| * G :=
      (norm_fderiv_comp_real_le (((contDiff_cutoffProfile k).differentiable
        (by norm_num)) _) (hscd.differentiable (by norm_num) x)).trans
        (mul_le_mul_of_nonneg_left (hG x hx') (abs_nonneg _))
    rcases lt_or_ge (s x) ((4 / 5 + 1) / 2) with h | h
    · rw [deriv_cutoffProfile_of_lt (by linarith [two_mul_cutoffWidth_le k]), abs_zero,
        zero_mul] at hn
      have : ‖fderiv ℝ (fun y ↦ cutoffProfile k (s y)) x‖ = 0 :=
        le_antisymm hn (norm_nonneg _)
      rw [this]
      simpa using (Real.exp_pos _).le
    · have hb := abs_deriv_cutoffProfile_le hM k hx'
      have h1 : 0 < 1 - s x := sub_pos.mpr hx'
      have hsq : ‖fderiv ℝ (fun y ↦ cutoffProfile k (s y)) x‖ ^ 2 ≤
          (2 * M * G) ^ 2 / (1 - s x) ^ 2 := by
        have h2 : ‖fderiv ℝ (fun y ↦ cutoffProfile k (s y)) x‖ ≤ 2 * M / (1 - s x) * G :=
          hn.trans (mul_le_mul_of_nonneg_right hb hG0)
        calc _ ≤ (2 * M / (1 - s x) * G) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
          _ = _ := by field_simp
      have := (hφbig (s x) ⟨h, hx'⟩).1
      linarith [Real.add_one_le_exp (φ (s x))]
  · -- `2 ψ₀ ≤ χ`
    have hx' : s x < 1 := hx
    rcases lt_or_ge (s x) ((3 / 5 + 1) / 2) with h | h
    · show 2 * φ (s x) ≤ χ₀ (s x)
      rw [hφzero _ (by linarith), mul_zero]
      exact hχ0 _
    · exact (le_max_left _ _).trans (hχbig (s x) ⟨h, hx'⟩).1
  · -- the Levi form bound
    have hx' : s x < 1 := hx
    have hn : ‖fderiv ℝ (fun y ↦ φ (s y)) x‖ ≤ |deriv φ (s x)| * G :=
      (norm_fderiv_comp_real_le ((hφcd.differentiableOn (by norm_num)).differentiableAt
        (Iio_mem_nhds hx')) (hscd.differentiable (by norm_num) x)).trans
        (mul_le_mul_of_nonneg_left (hG x hx') (abs_nonneg _))
    have hn2 : ‖fderiv ℝ (fun y ↦ φ (s y)) x‖ ^ 2 ≤ deriv φ (s x) ^ 2 * G ^ 2 := by
      calc _ ≤ (|deriv φ (s x)| * G) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = _ := by rw [mul_pow, sq_abs]
    have hkey : A' * (deriv φ (s x) ^ 2 * G ^ 2) ≤ deriv χ₀ (s x) * ε := by
      rcases lt_or_ge (s x) ((3 / 5 + 1) / 2) with h | h
      · rw [hφd0 _ (by linarith)]
        simpa using mul_nonneg (hχd _ hx').1 hε.le
      · have := (le_max_right _ _).trans (hχbig (s x) ⟨h, hx'⟩).2
        rw [div_le_iff₀ hε] at this
        linarith
    have hA : A * ‖fderiv ℝ (fun y ↦ φ (s y)) x‖ ^ 2 ≤ A' * (deriv φ (s x) ^ 2 * G ^ 2) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hn2 hA'0)
    calc A * ‖fderiv ℝ (fun y ↦ φ (s y)) x‖ ^ 2 * ‖ξ‖ ^ 2
        ≤ deriv χ₀ (s x) * ε * ‖ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hA.trans hkey) (by positivity)
      _ = deriv χ₀ (s x) * (ε * ‖ξ‖ ^ 2) := by ring
      _ ≤ _ := hlevi x hx' ξ
  · exact (mul_nonneg (hχd _ hx).1 (by positivity)).trans (hlevi x hx ξ)


/-- **Hörmander's `L²` estimate on an open set with a strictly plurisubharmonic exhaustion**
(plan P1, blueprint `l2:hormander-exhaustion`). Let `D` be open, `K` a set, and `s` smooth with
`ε ‖v‖² ≤ Levi s (v)` on `{s < 1}`, `{s ≤ 1}` compact and contained in `D`, `s ≤ 1/2` on `K`; let
`t > 0`. There are an open `D'` with compact closure inside `D`, an open `U` with `K ⊆ U ⊆ D'` and continuous shifts
`0 ≤ lam₁ ≤ lam₂` of the weight on `D'`, vanishing on `U`, such that for every weight `Φ` smooth
and plurisubharmonic on `D`: every `∂̄`-closed `f ∈ L²(D', e^{-Φ-lam₂})` with a pointwise Levi
bound `|⟨f, ξ⟩|² ≤ g · Levi Φ (ξ)`, `∫ g e^{-Φ-lam₁} < ∞`, is `∂̄ u` with `u ∈ L²(D', e^{-Φ-lam₁})`
orthogonal to the `L²` holomorphic functions, and every such `u` satisfies
`∫ |u|² e^{-Φ-lam₁} ≤ (1 + t) ∫ g e^{-Φ-lam₁}`. -/
theorem hormanderL2_of_exhaustion {D K : Set (ComplexModel n)}
    {s : ComplexModel n → ℝ} {ε : ℝ} (hε : 0 < ε) (hscd : ContDiff ℝ ∞ s)
    (hScpt : IsCompact {x | s x ≤ 1}) (hsD : {x | s x ≤ 1} ⊆ D) (hsK : ∀ x ∈ K, s x ≤ 1 / 2)
    (hslevi : ∀ x, s x < 1 → ∀ v, ε * ‖v‖ ^ 2 ≤ leviForm s x v) {t : ℝ} (ht : 0 < t) :
    ∃ (D' U : Set (ComplexModel n)) (lam₁ lam₂ : ComplexModel n → ℝ),
      IsOpen D' ∧ closure D' ⊆ D ∧ IsCompact (closure D') ∧ IsOpen U ∧ K ⊆ U ∧ U ⊆ D' ∧
      ContinuousOn lam₁ D' ∧ ContinuousOn lam₂ D' ∧
      (∀ x ∈ D', 0 ≤ lam₁ x ∧ lam₁ x ≤ lam₂ x) ∧ (∀ x ∈ U, lam₁ x = 0 ∧ lam₂ x = 0) ∧
      ∀ Φ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ Φ D → (∀ x ∈ D, ∀ ξ, 0 ≤ leviForm Φ x ξ) →
      ∀ f : Fin n → ComplexModel n → ℂ,
        (∀ j, MemLp (f j) 2 (weightedVolume D' fun x ↦ Φ x + lam₂ x)) → WeakDbarClosed D' f →
      ∀ g : ComplexModel n → ℝ, (∀ x ∈ D', 0 ≤ g x) →
        (∀ x ∈ D', ∀ ξ : Fin n → ℂ,
          ‖∑ j, conj (ξ j) * f j x‖ ^ 2 ≤ g x * leviForm Φ x (∑ j, ξ j • coordVec j)) →
        Integrable (fun x ↦ g x * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') →
      (∃ u : ComplexModel n → ℂ, MemLp u 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) ∧
          WeakDbarEq D' u f ∧
          ∀ h : ComplexModel n → ℂ, MemLp h 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
            WeakDbarEq D' h 0 →
            ∫ x in D', conj (h x) * u x * Real.exp (-(Φ x + lam₁ x)) = 0) ∧
      ∀ u : ComplexModel n → ℂ, MemLp u 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
        WeakDbarEq D' u f →
        (∀ h : ComplexModel n → ℂ, MemLp h 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
            WeakDbarEq D' h 0 →
            ∫ x in D', conj (h x) * u x * Real.exp (-(Φ x + lam₁ x)) = 0) →
        ∫ x in D', ‖u x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x)) ≤
          (1 + t) * ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x)) := by
  have hdens := hormanderDensityStatement n
  obtain ⟨L', U₀, η, ψ₀, χ, hL'o, hL'D, hL'c, hU₀o, hKU₀, hU₀L', hη, hηev, hψs, hχs, hηgrad,
    hψ0, hU₀z, h2ψ, hLevi, -⟩ :=
    exists_cutoffData_of_exhaustion ((1 + 1 / t) * n) hε hscd hScpt hsD hsK hslevi
  refine ⟨L', U₀, fun x ↦ χ x - 2 * ψ₀ x, fun x ↦ χ x - ψ₀ x, hL'o, hL'D, hL'c, hU₀o, hKU₀,
    hU₀L', hχs.continuousOn.sub (continuousOn_const.mul hψs.continuousOn),
    hχs.continuousOn.sub hψs.continuousOn,
    fun x hx ↦ ⟨by linarith [h2ψ x hx], by linarith [hψ0 x]⟩,
    fun x hx ↦ by simp [(hU₀z x hx).1, (hU₀z x hx).2], ?_⟩
  intro Φ hΦ hpsh f hf hfc g hg0 hfg hgi
  simp only [← add_sub_assoc] at hf hgi ⊢
  have hΦ' : ContDiffOn ℝ ∞ Φ L' := hΦ.mono (subset_closure.trans hL'D)
  have hpsh' : ∀ x ∈ L', ∀ ξ, 0 ≤ leviForm Φ x ξ := fun x hx ↦ hpsh x (hL'D (subset_closure hx))
  have hw₃ : ContDiffOn ℝ ∞ (fun x ↦ Φ x + χ x) L' := hΦ'.add hχs
  have hw₂ : ContDiffOn ℝ ∞ (fun x ↦ (fun x ↦ Φ x + χ x) x - ψ₀ x) L' := hw₃.sub hψs
  have hw₁ : ContinuousOn (fun x ↦ (fun x ↦ Φ x + χ x) x - 2 * ψ₀ x) L' :=
    hw₃.continuousOn.sub (continuousOn_const.mul hψs.continuousOn)
  have h12 : ∀ x ∈ L', (fun x ↦ (fun x ↦ Φ x + χ x) x - ψ₀ x) x =
      (fun x ↦ (fun x ↦ Φ x + χ x) x - 2 * ψ₀ x) x + ψ₀ x := fun x _ ↦ by simp only; ring
  have : CompleteSpace (closedForms hL'o hw₂) :=
    (Submodule.isClosed_orthogonal _).completeSpace_coe
  set a := formToL2 hL'o hw₂.continuousOn
  set A := tstarToL2 hL'o hw₁ hw₂ hψs.continuousOn
  set F := (memLp_formVec_of_components hf).toLp (formVec f)
  set G := ∫ x in L', g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) with hGdef
  have hG0 : 0 ≤ G := setIntegral_nonneg hL'o.measurableSet fun x hx ↦
    mul_nonneg (hg0 x hx) (Real.exp_pos _).le
  have hM : 0 ≤ (1 + t) * G := mul_nonneg (by linarith) hG0
  have hFW : F ∈ closedForms hL'o hw₂ := by
    rw [mem_closedForms_iff]
    intro h hh j k
    rw [← hfc h hh j k]
    refine integral_congr_of_ae_weightedVolume hL'o hw₂.continuousOn (fun x hx ↦ ?_)
      (fun x hx ↦ ?_) ?_
    · have hxs : x ∉ tsupport h := fun h' ↦ hx (hh.2.2 h')
      simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
    · have hxs : x ∉ tsupport h := fun h' ↦ hx (hh.2.2 h')
      simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
    · filter_upwards [(memLp_formVec_of_components hf).coeFn_toLp] with x hx
      simp only [F]
      rw [hx, formVec_apply, formVec_apply]
  set Q : testForms L' → ℝ := fun α ↦
    ∫ x, (∑ p, ‖dbarForm (α : Fin n → ComplexModel n → ℂ) p x‖ ^ 2) * Real.exp (-(Φ x + χ x))
  have hest : ∀ α : testForms L', ‖⟪a α, F⟫_ℂ‖ ^ 2 ≤ (1 + t) * G * (‖A α‖ ^ 2 + Q α) := by
    intro α
    have hpair := norm_sq_pairing_le hL'o hΦ' hχs hψs hpsh' ht hLevi hf hg0 hfg hgi α.2
    have hinner : ⟪a α, F⟫_ℂ = ∑ j, ∫ x, conj ((α : Fin n → ComplexModel n → ℂ) j x) * f j x
        ∂(weightedVolume L' fun x ↦ Φ x + χ x - ψ₀ x) := by
      simp only [a, F]
      rw [inner_formToL2]
      refine Finset.sum_congr rfl fun j _ ↦ integral_congr_ae ?_
      filter_upwards [(memLp_formVec_of_components hf).coeFn_toLp] with x hx
      rw [hx, formVec_apply]
    have hnorm : ‖A α‖ ^ 2 = ∫ x, ‖tstarForm (fun x ↦ Φ x + χ x - ψ₀ x) ψ₀ α x‖ ^ 2
        ∂(weightedVolume L' fun x ↦ Φ x + χ x - 2 * ψ₀ x) :=
      norm_sq_toLp_eq_integral (memLp_tstarForm hL'o hw₁ hw₂ hψs.continuousOn α.2)
    rw [hinner, hnorm]
    exact hpair
  have happrox := fun α ↦ exists_approx_of_density hdens hL'o hw₃ hψs hψ0 hη hηev hηgrad hw₂ hw₁ α
  have hbound := norm_inner_le_of_approx' a A Q (closedForms hL'o hw₂) hFW hM hest happrox
  exact hormander_of_pairing_bound hL'o hw₁ hw₂ hψs.continuousOn h12 hf hM hbound


end SGPT.Okounkov.TranscendentalL2

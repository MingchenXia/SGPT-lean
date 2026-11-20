import SGPT.Foundations.Analysis.Pending.MongeAmpereHolder

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Openness of the `ε`-continuity path of Yau's theorem

The route agreed on I-0831 (C-0054..C-0057): for `ε ∈ (0, 1]` solve
`(A + ddᶜφ)^N = e^{tF + εφ} A^N` by continuity in `t ∈ [0, 1]`, then let `ε → 0`.  This module proves
the **openness** step in `C^{2,r}`:

* `exists_eq_smul_near` — the inverse function theorem along a line: if `f : E → F` (Banach) is
  strictly differentiable at `x₀` with bijective derivative and `f x₀ = t₀ • v`, then `f x = t • v`
  is solvable near `x₀` for all `t` near `t₀` (via `HasStrictFDerivAt.map_nhds_eq_of_equiv` for
  `(x, t) ↦ (f x - t • v, t)`).
* `exists_atlas_estimates` — summing `MongeAmpereHolder.exists_chart_estimates` over a Hölder atlas:
  near `Φ₀`, `ma a ψ ∈ C^{0,r}(M)` and `‖ma ψ₁ - ma ψ₂ - Δ_g(ψ₁ - ψ₂)‖ ≤ C (‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) ‖ψ₁ - ψ₂‖`,
  i.e. `ψ ↦ ma a ψ` is strictly differentiable at `Φ₀` with derivative `Δ_g`, `g = a + ddᶜΦ₀`.
* `exists_ma_eq_near` (**openness**, blueprint `bou:yau-openness`): if `ma a Φ₀ = t₀ F + ε Φ₀`
  (`ε > 0`), then for `t` near `t₀` there is `ψ ∈ C^{2,r}(M)` arbitrarily close to `Φ₀` with
  `ma a ψ = t F + ε ψ` — the derivative `Δ_g - ε` is an isomorphism
  (`KahlerLaplacianChart.bijective_laplacianCLM_sub`).
* `exists_ma_eq_near_of_smooth` — the same for a Kähler background `A` and a chart-smooth solution
  `φ₀` of the density equation `(A + ddᶜφ₀)^N = e^{t₀F + εφ₀} A^N` (`ma_eq_of_density`).

Not yet here: smoothness of the new solutions (bootstrap) and the positivity `A + ddᶜψ > 0` for `ψ`
`C^{2,r}`-close to `φ₀` (TN.4 B5, N1/N5).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.YauOpenness

open FirstPass FirstPass.MongeAmpere KahlerLaplacianChart MongeAmpereHolder

/-! ### The inverse function theorem along a line -/

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Solving `f x = t v` near a solution** (inverse function theorem): if `f` is strictly
differentiable at `x₀` with bijective derivative and `f x₀ = t₀ • v`, then for every `ρ > 0` and all
`t` close to `t₀` there is `x` with `‖x - x₀‖ < ρ` and `f x = t • v`. -/
theorem exists_eq_smul_near {f : E → F} {T : E →L[ℝ] F} {x₀ : E} (hf : HasStrictFDerivAt f T x₀)
    (hT : Function.Bijective T) (v : F) {t₀ : ℝ} (h₀ : f x₀ = t₀ • v) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ → ∃ x : E, ‖x - x₀‖ < ρ ∧ f x = t • v := by
  set G : E × ℝ → F × ℝ := fun p => (f p.1 - p.2 • v, p.2) with hGdef
  set G' : E × ℝ →L[ℝ] F × ℝ :=
    (T.comp (ContinuousLinearMap.fst ℝ E ℝ) -
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight v).prod (ContinuousLinearMap.snd ℝ E ℝ) with hG'def
  have hG : HasStrictFDerivAt G G' (x₀, t₀) := by
    have h1 : HasStrictFDerivAt (fun p : E × ℝ => f p.1) (T.comp (ContinuousLinearMap.fst ℝ E ℝ))
        (x₀, t₀) := hf.comp (x₀, t₀) hasStrictFDerivAt_fst
    have h2 : HasStrictFDerivAt (fun p : E × ℝ => p.2 • v)
        ((ContinuousLinearMap.snd ℝ E ℝ).smulRight v) (x₀, t₀) :=
      (hasStrictFDerivAt_snd).smul_const v
    exact (h1.sub h2).prodMk hasStrictFDerivAt_snd
  have hinj : Function.Injective G' := by
    intro p q hpq
    simp only [hG'def, ContinuousLinearMap.prod_apply, sub_apply,
      ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd', Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    rw [h2] at h1
    have := hT.1 (sub_left_injective h1)
    exact Prod.ext this h2
  have hsurj : Function.Surjective G' := by
    intro q
    obtain ⟨y, hy⟩ := hT.2 (q.1 + q.2 • v)
    refine ⟨(y, q.2), ?_⟩
    simp [hG'def, hy]
  set Geq : (E × ℝ) ≃L[ℝ] (F × ℝ) := ContinuousLinearEquiv.ofBijective G'
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj) with hGeq
  have hG2 : HasStrictFDerivAt G (Geq : E × ℝ →L[ℝ] F × ℝ) (x₀, t₀) := by
    rw [hGeq, ContinuousLinearEquiv.coe_ofBijective]; exact hG
  have hmap := hG2.map_nhds_eq_of_equiv
  have hG0 : G (x₀, t₀) = (0, t₀) := by simp [hGdef, h₀]
  rw [hG0] at hmap
  have hS : (ball x₀ ρ ×ˢ univ : Set (E × ℝ)) ∈ 𝓝 (x₀, t₀) :=
    prod_mem_nhds (ball_mem_nhds x₀ hρ) univ_mem
  have hGS : G '' (ball x₀ ρ ×ˢ univ) ∈ 𝓝 ((0 : F), t₀) := by
    rw [← hmap]; exact image_mem_map hS
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hGS
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hmem : ((0 : F), t) ∈ ball ((0 : F), t₀) δ := by
    rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    exact max_lt hδ ht
  obtain ⟨⟨x, t'⟩, ⟨hx, -⟩, hxt⟩ := hball hmem
  simp only [hGdef, Prod.mk.injEq] at hxt
  obtain ⟨h1, rfl⟩ := hxt
  refine ⟨x, by rwa [mem_ball, dist_eq_norm] at hx, ?_⟩
  exact sub_eq_zero.mp h1

end Abstract

/-! ### The Monge–Ampère operator near a solution -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Atlas-level estimates**: near `Φ₀`, `ma a ψ ∈ C^{0,r}(M)` and the remainder of the
linearisation `Δ_g` is quadratically small. -/
theorem exists_atlas_estimates {a g : SmoothRealForm n M 2} (ha : a.IsHermitian)
    (hg : g.IsHermitian) {A : HolderAtlas n M} {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1)
    (Φ₀ : A.HolderMap 2 r ℝ)
    (hgφ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      normalizedHermitianMatrix (g.coeff e z) =
        normalizedHermitianMatrix (a.coeff e z) + complexHessian (fun x => Φ₀ (e.val.symm x)) z) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (∀ ψ : A.HolderMap 2 r ℝ, ‖ψ - Φ₀‖ < ρ → ∃ G : A.HolderMap 0 r ℝ, ⇑G = ma a ⇑ψ) ∧
      (∀ (ψ₁ ψ₂ : A.HolderMap 2 r ℝ) (G₁ G₂ : A.HolderMap 0 r ℝ), ‖ψ₁ - Φ₀‖ < ρ →
        ‖ψ₂ - Φ₀‖ < ρ → ⇑G₁ = ma a ⇑ψ₁ → ⇑G₂ = ma a ⇑ψ₂ →
        ‖G₁ - G₂ - laplacianCLM hg A hr0 hr1 (ψ₁ - ψ₂)‖ ≤
          C * (‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) * ‖ψ₁ - ψ₂‖) := by
  choose ρs Cs hρs hCs hmem hrem using fun i => exists_chart_estimates ha hg hr0 hr1 Φ₀ hgφ i
  set ρ : ℝ := 1 / (1 + ∑ i, 1 / ρs i) with hρdef
  have hsum0 : 0 ≤ ∑ i, 1 / ρs i := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hρs i)).le
  have hρ0 : 0 < ρ := one_div_pos.mpr (by linarith)
  have hρle : ∀ i, ρ ≤ ρs i := by
    intro i
    have h1 : 1 / ρs i ≤ 1 + ∑ j, 1 / ρs j := by
      have := Finset.single_le_sum (f := fun j => 1 / ρs j)
        (fun j _ => (one_div_pos.mpr (hρs j)).le) (Finset.mem_univ i)
      linarith
    rw [hρdef, div_le_iff₀ (by linarith)]
    have := (div_le_iff₀ (hρs i)).mp h1
    linarith [mul_comm (ρs i) (1 + ∑ j, 1 / ρs j)]
  refine ⟨ρ, ∑ i, Cs i, hρ0, Finset.sum_nonneg fun i _ => hCs i, fun ψ hψ => ?_,
    fun ψ₁ ψ₂ G₁ G₂ h₁ h₂ hG₁ hG₂ => ?_⟩
  · exact ⟨⟨ma a ψ, fun i => hmem i ψ (hψ.trans_le (hρle i))⟩, rfl⟩
  · set u := G₁ - G₂ - laplacianCLM hg A hr0 hr1 (ψ₁ - ψ₂) with hudef
    have hu : ⇑u = fun y => ma a ⇑ψ₁ y - ma a ⇑ψ₂ y - laplacian g ⇑(ψ₁ - ψ₂) y := by
      funext y
      simp only [hudef, HolderAtlas.HolderMap.coe_sub, Pi.sub_apply, laplacianCLM_apply, hG₁, hG₂]
    rw [HolderAtlas.HolderMap.norm_def, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h, hh, hhn⟩ := hrem i ψ₁ ψ₂ (h₁.trans_le (hρle i)) (h₂.trans_le (hρle i))
    have hrep : u.rep i = h := by
      ext z
      show A.localRep i ⇑u z = h z
      rw [hu, hh]
    rw [hrep]
    exact hhn

/-- **Openness of the `ε`-continuity path** (`C^{2,r}` form; blueprint `bou:yau-openness`): let
`g = a + ddᶜΦ₀` be Hermitian and `Φ₀` solve `ma a Φ₀ = t₀ F + ε Φ₀` with `ε > 0`.  Then for every
`ρ > 0` and all `t` near `t₀` the equation `ma a ψ = t F + ε ψ` has a solution `ψ ∈ C^{2,r}(M)` with
`‖ψ - Φ₀‖ < ρ`.  (Inverse function theorem; the linearisation `Δ_g - ε` is an isomorphism
`C^{2,r}(M) → C^{0,r}(M)`, `KahlerLaplacianChart.bijective_laplacianCLM_sub`.) -/
theorem exists_ma_eq_near [CompactSpace M] {a g : SmoothRealForm n M 2} (ha : a.IsHermitian)
    (hg : g.IsHermitian) {A : HolderAtlas n M} {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1)
    (Φ₀ : A.HolderMap 2 r ℝ)
    (hgφ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      normalizedHermitianMatrix (g.coeff e z) =
        normalizedHermitianMatrix (a.coeff e z) + complexHessian (fun x => Φ₀ (e.val.symm x)) z)
    (F : A.HolderMap 0 r ℝ) {ε : ℝ} (hε : 0 < ε) {t₀ : ℝ}
    (h₀ : ∀ y, ma a ⇑Φ₀ y = t₀ * F y + ε * Φ₀ y) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ → ∃ ψ : A.HolderMap 2 r ℝ, ‖ψ - Φ₀‖ < ρ ∧
      ∀ y, ma a ⇑ψ y = t * F y + ε * ψ y := by
  classical
  obtain ⟨ρ₁, C, hρ₁, hC, hmem, hrem⟩ := exists_atlas_estimates ha hg hr0 hr1 Φ₀ hgφ
  choose G hG using hmem
  set f₀ : A.HolderMap 2 r ℝ → A.HolderMap 0 r ℝ :=
    fun ψ => if h : ‖ψ - Φ₀‖ < ρ₁ then G ψ h else 0 with hf₀def
  have hf₀ : ∀ ψ (h : ‖ψ - Φ₀‖ < ρ₁), f₀ ψ = G ψ h := fun ψ h => dif_pos h
  set ι := HolderAtlas.HolderMap.toZeroCLM (A := A) (F := ℝ) (k := 2) hr1.le (by norm_num)
    with hιdef
  set T := laplacianCLM hg A hr0 hr1 with hTdef
  have hstrict₀ : HasStrictFDerivAt f₀ T Φ₀ := by
    refine HasStrictFDerivAt.of_isLittleO ?_
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    set ρ' := min ρ₁ (c / (2 * C + 1)) with hρ'
    have hρ'0 : 0 < ρ' := lt_min hρ₁ (div_pos hc (by linarith))
    filter_upwards [ball_mem_nhds ((Φ₀, Φ₀) : A.HolderMap 2 r ℝ × A.HolderMap 2 r ℝ) hρ'0]
      with p hp
    rw [mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hp
    have hp1 : ‖p.1 - Φ₀‖ < ρ' := (le_max_left _ _).trans_lt hp
    have hp2 : ‖p.2 - Φ₀‖ < ρ' := (le_max_right _ _).trans_lt hp
    have h1 : ‖p.1 - Φ₀‖ < ρ₁ := hp1.trans_le (min_le_left _ _)
    have h2 : ‖p.2 - Φ₀‖ < ρ₁ := hp2.trans_le (min_le_left _ _)
    rw [hf₀ _ h1, hf₀ _ h2]
    refine (hrem p.1 p.2 _ _ h1 h2 (hG _ h1) (hG _ h2)).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have hs : ‖p.1 - Φ₀‖ + ‖p.2 - Φ₀‖ ≤ 2 * (c / (2 * C + 1)) := by
      have := min_le_right ρ₁ (c / (2 * C + 1))
      linarith
    calc C * (‖p.1 - Φ₀‖ + ‖p.2 - Φ₀‖) ≤ C * (2 * (c / (2 * C + 1))) :=
          mul_le_mul_of_nonneg_left hs hC
      _ ≤ c := by
          rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
  set f : A.HolderMap 2 r ℝ → A.HolderMap 0 r ℝ := fun ψ => f₀ ψ - ε • ι ψ with hfdef
  have hstrict : HasStrictFDerivAt f (T - ε • ι) Φ₀ :=
    hstrict₀.sub (ι.hasStrictFDerivAt.const_smul ε)
  have hbij : Function.Bijective (T - ε • ι) := bijective_laplacianCLM_sub hg A hr0 hr1 hε
  have hΦ₀ : ‖Φ₀ - Φ₀‖ < ρ₁ := by simpa using hρ₁
  have h0 : f Φ₀ = t₀ • F := by
    ext y
    simp only [hfdef, hf₀ Φ₀ hΦ₀, HolderAtlas.HolderMap.coe_sub, HolderAtlas.HolderMap.coe_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hG, hιdef, HolderAtlas.HolderMap.coe_toZeroCLM,
      h₀]
    ring
  obtain ⟨δ, hδ, hsol⟩ := exists_eq_smul_near hstrict hbij F h0 (lt_min hρ hρ₁)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨ψ, hψ, hfψ⟩ := hsol t ht
  have hψ₁ : ‖ψ - Φ₀‖ < ρ₁ := hψ.trans_le (min_le_right _ _)
  refine ⟨ψ, hψ.trans_le (min_le_left _ _), fun y => ?_⟩
  have := congrArg (fun w : A.HolderMap 0 r ℝ => w y) hfψ
  simp only [hfdef, hf₀ ψ hψ₁, HolderAtlas.HolderMap.coe_sub, HolderAtlas.HolderMap.coe_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hG, hιdef,
    HolderAtlas.HolderMap.coe_toZeroCLM] at this
  linarith

end Manifold

/-! ### The `ε`-path for a Kähler background -/

section Kahler

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

open ManifoldTubePositivity PositiveClasses

/-- The coefficient matrix of `A + ddᶜφ` is `H_A + complexHessian φ`. -/
theorem normalizedHermitianMatrix_add_ddc (A : ClosedRealOneOneForm N Y) {φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) {e : ComplexChart N Y} {z : ComplexModel N}
    (hz : z ∈ e.val.target) :
    normalizedHermitianMatrix ((A + ddcClosedForm φ hφ).val.coeff e z) =
      normalizedHermitianMatrix (A.val.coeff e z) + complexHessian (fun x => φ (e.val.symm x)) z := by
  have hsum : (A + ddcClosedForm φ hφ).val.coeff e z =
      A.val.coeff e z + (ddcClosedForm φ hφ).val.coeff e z := rfl
  rw [hsum, normalizedHermitianMatrix_add, ddcClosedForm_coeff,
    normalizedHermitianMatrix_smoothDDC
      (((hφ e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]

/-- The Monge–Ampère equation in density form gives `ma A φ = G`. -/
theorem ma_eq_of_density (A : KahlerBackground N Y) {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ)
    {G : Y → ℝ} (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z)) (y : Y) :
    ma A.form.val φ y = G y := by
  set e := complexChartAt (n := N) y with he
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  have h11 : IsOneOne ((A.form + ddcClosedForm φ hφ).val.coeff e (e.val y)) := (hK.1 e _ hz).1
  have hA11 : IsOneOne (A.form.val.coeff e (e.val y)) := (A.isKahler.1 e _ hz).1
  have hd := hdens e (e.val y) hz
  rw [ConcentrationMassComparison.actualTopPowerDensity_eq_det h11,
    ConcentrationMassComparison.actualTopPowerDensity_eq_det hA11,
    normalizedHermitianMatrix_add_ddc A.form hφ hz, e.val.left_inv (mem_complexChartAt_source y)]
    at hd
  have hpos : 0 < (normalizedHermitianMatrix (A.form.val.coeff e (e.val y))).det.re :=
    (Complex.pos_iff.mp (posDef_coeff A.isKahler.1 hz).det_pos).1
  have hc : (0 : ℝ) < N.factorial / Real.pi ^ N := by positivity
  have hdet : (normalizedHermitianMatrix (A.form.val.coeff e (e.val y)) +
      complexHessian (fun x => φ (e.val.symm x)) (e.val y)).det.re =
      Real.exp (G y) * (normalizedHermitianMatrix (A.form.val.coeff e (e.val y))).det.re := by
    have := hd
    field_simp at this
    nlinarith [this]
  simp only [ma, maChart, ← he]
  rw [hdet, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  ring

/-- **Openness of the `ε`-path at a smooth solution** (`C^{2,r}` solutions): if `φ₀` is chart-smooth,
`A + ddᶜφ₀` is Kähler and `(A + ddᶜφ₀)^N = e^{t₀F + εφ₀} A^N` (`ε > 0`, `F` chart-smooth), then for
every `ρ > 0` and all `t` near `t₀` there is `ψ ∈ C^{2,r}(Y)`, `ρ`-close to `φ₀`, with
`ma A ψ = tF + εψ`. -/
theorem exists_ma_eq_near_of_smooth [CompactSpace Y] (A : KahlerBackground N Y)
    (HA : HolderAtlas N Y) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) {ε : ℝ} (hε : 0 < ε) {t₀ : ℝ} {φ₀ : Y → ℝ}
    (hφ₀ : ChartSmooth (n := N) φ₀) (hK : (A.form + ddcClosedForm φ₀ hφ₀).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ₀ hφ₀).val.coeff e z) =
        Real.exp (t₀ * F (e.val.symm z) + ε * φ₀ (e.val.symm z)) *
          actualTopPowerDensity (A.form.val.coeff e z)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ → ∃ ψ : HA.HolderMap 2 r ℝ,
      ‖ψ - HolderAtlas.HolderMap.ofChartSmooth hr1.le φ₀ hφ₀‖ < ρ ∧
      ∀ y, ma A.form.val ⇑ψ y = t * F y + ε * ψ y := by
  set Φ₀ : HA.HolderMap 2 r ℝ := HolderAtlas.HolderMap.ofChartSmooth hr1.le φ₀ hφ₀ with hΦ₀
  have hgφ : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      normalizedHermitianMatrix ((A.form + ddcClosedForm φ₀ hφ₀).val.coeff e z) =
        normalizedHermitianMatrix (A.form.val.coeff e z) +
          complexHessian (fun x => Φ₀ (e.val.symm x)) z :=
    fun e z hz => normalizedHermitianMatrix_add_ddc A.form hφ₀ hz
  have h₀ : ∀ y, ma A.form.val ⇑Φ₀ y =
      t₀ * (HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 0) hr1.le F hF) y + ε * Φ₀ y :=
    fun y => ma_eq_of_density A hφ₀ hK (G := fun y => t₀ * F y + ε * φ₀ y) hdens y
  obtain ⟨δ, hδ, hsol⟩ := exists_ma_eq_near A.isKahler.1 hK.1 hr0 hr1 Φ₀ hgφ
    (HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 0) hr1.le F hF) hε h₀ hρ
  exact ⟨δ, hδ, fun t ht => hsol t ht⟩

end Kahler

end SGPT.Foundations.Analysis.Pending.YauOpenness

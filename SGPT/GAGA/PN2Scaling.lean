import SGPT.GAGA.PNInvariant
import SGPT.GAGA.CoreClosure
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Invariant coherent modules are invariant under pointwise rescaling

Infrastructure of lane SERRE-PN2 (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), plan node PN5 of `claude-serre-pn.tex`
(dehomogenization), key lemma.

Let `P ⊆ 𝒪^κ` be coherent on `ℂ^{N+1} ∖ 0` and invariant under `ℂ*`, let `y` be a point with
`y_i = 1` and `σ ∈ P_y`. Then **the germ of `z ↦ σ(z / z_i)` lies in `P_y`**
(`mem_comp_inv_coord_smul`). This is what makes `P` the pull-back of its restriction to the
affine chart `z_i = 1`.

Proof. Membership of germs spreads to nearby points (`eventually_mem_of_coherentAt`), so by
invariance `z ↦ σ(c z)` lies in `P_y` for all constants `c` with `|c - 1| ≤ R`
(`eventually_mem_smul`). For `z` near `y`, `λ(z) = 1/z_i` is close to `1`, and Cauchy's formula
in the variable `c` gives `σ(λ(z) z) = ∫_0^{2π} K(θ, z) dθ` with
`K(θ, z) = (2πi)⁻¹ (c(θ) - 1) i (c(θ) - λ(z))⁻¹ σ(c(θ) z)`, `c(θ) = 1 + R e^{iθ}`. The Riemann
sums of this integral are combinations of the members `σ(c(θ_m) ·)` of `P_y` with holomorphic
coefficients, and they converge uniformly near `y` (`tendstoUniformlyOn_riemann`, uniform
continuity on a compact set). The closure theorem of lane SERRE-CORE
(`GermModule.CoherentAt.mem_of_tendstoUniformlyOn`) concludes.

Blueprint: `claude-serre-pn2.tex`, node `claude-serre-pn2:scaling`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology Metric Complex MeasureTheory
open scoped Real
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

/-! ### Spreading of membership -/

section Spread

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {κ : Type} [Fintype κ]

/-- A germ in `M_y` lies in `M_{y'}` for all `y'` near `y` (`M` coherent at `y`). -/
theorem eventually_mem_of_coherentAt {M : GermModule X κ} {y : X} (hM : M.CoherentAt y)
    {a : κ → X → ℂ} (ha : M.mem y a) : ∀ᶠ y' in 𝓝 y, M.mem y' a := by
  obtain ⟨U, hU, hyU, μ, _, τ, hτ⟩ := hM
  obtain ⟨c, hc, hca⟩ := (hτ.2 y hyU a).1 ha
  have h1 : ∀ᶠ y' in 𝓝 y, ∀ k, HolAt (c k) y' := eventually_all.2 fun k => (hc k).eventually
  have h2 : ∀ᶠ y' in 𝓝 y, ∀ j, a j =ᶠ[𝓝 y'] fun x => ∑ k, c k x * τ k j x :=
    eventually_all.2 fun j => (hca j).eventuallyEq_nhds
  filter_upwards [h1, h2, hU.mem_nhds hyU] with y' h1 h2 hy'
  exact (hτ.2 y' hy' a).2 ⟨c, h1, h2⟩

end Spread

/-! ### Riemann sums with a parameter -/

/-- **Riemann sums converge uniformly in a parameter** ranging over a compact set. -/
theorem tendstoUniformlyOn_riemann {X : Type*} [MetricSpace X] {K : ℝ → X → ℂ} {T : ℝ}
    (hT : 0 < T) {C : Set X} (hC : IsCompact C)
    (hK : ContinuousOn (fun p : ℝ × X => K p.1 p.2) (Icc 0 T ×ˢ C)) :
    TendstoUniformlyOn
      (fun (M : ℕ) z => ∑ m ∈ Finset.range M, ((T / M : ℝ) : ℂ) * K (T * m / M) z)
      (fun z => ∫ θ in (0 : ℝ)..T, K θ z) atTop C := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have huc := (isCompact_Icc.prod hC).uniformContinuousOn_of_continuous hK
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηK⟩ := huc (ε / (2 * T)) (by positivity)
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (T / η)
  filter_upwards [eventually_ge_atTop (M₀ + 1)] with M hM z hz
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans (Nat.le_add_left 1 M₀) hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hTM : T / M < η := by
    rw [div_lt_iff₀ hMpos]
    have h1 : T / η < M := lt_of_lt_of_le hM₀ (by exact_mod_cast (Nat.le_succ M₀).trans hM)
    rw [div_lt_iff₀ hη] at h1
    linarith
  set a : ℕ → ℝ := fun m => T * m / M with hadef
  have ha_mono : ∀ m, a m ≤ a (m + 1) := fun m => by
    simp only [hadef]
    gcongr
    linarith
  have ha_mem : ∀ m ≤ M, a m ∈ Icc 0 T := fun m hm => by
    refine ⟨by positivity, ?_⟩
    rw [hadef, div_le_iff₀ hMpos]
    have : (m : ℝ) ≤ M := by exact_mod_cast hm
    nlinarith
  have hstep : ∀ m, a (m + 1) - a m = T / M := fun m => by
    simp only [hadef]
    push_cast
    ring
  have hcont : ContinuousOn (fun θ => K θ z) (Icc 0 T) :=
    hK.comp (continuousOn_id.prodMk continuousOn_const) fun θ hθ => ⟨hθ, hz⟩
  have hsub : ∀ m < M, uIcc (a m) (a (m + 1)) ⊆ Icc 0 T := fun m hm => by
    rw [uIcc_of_le (ha_mono m)]
    exact Icc_subset_Icc (ha_mem m hm.le).1 (ha_mem (m + 1) hm).2
  have hint : ∀ m < M, IntervalIntegrable (fun θ => K θ z) volume (a m) (a (m + 1)) :=
    fun m hm => (hcont.mono (hsub m hm)).intervalIntegrable
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [hadef]
  have haM : a M = T := by simp only [hadef]; field_simp
  rw [ha0, haM] at hsum
  rw [dist_eq_norm, ← hsum, ← Finset.sum_sub_distrib]
  have hterm : ∀ m ∈ Finset.range M,
      ‖(∫ θ in a m..a (m + 1), K θ z) - ((T / M : ℝ) : ℂ) * K (T * m / M) z‖ ≤
        ε / (2 * T) * (T / M) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hc : ((T / M : ℝ) : ℂ) * K (T * m / M) z = ∫ _θ in a m..a (m + 1), K (a m) z := by
      rw [intervalIntegral.integral_const, hstep, Complex.real_smul]
    rw [hc, ← intervalIntegral.integral_sub (hint m hm) intervalIntegrable_const]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / (2 * T))
      (f := fun θ => K θ z - K (a m) z) (a := a m) (b := a (m + 1)) fun θ hθ => by
        have hθ' : θ ∈ Icc (a m) (a (m + 1)) := by
          rw [uIoc_of_le (ha_mono m)] at hθ
          exact Ioc_subset_Icc_self hθ
        have h1 : (θ, z) ∈ Icc 0 T ×ˢ C :=
          ⟨hsub m hm (by rw [uIcc_of_le (ha_mono m)]; exact hθ'), hz⟩
        have h2 : (a m, z) ∈ Icc 0 T ×ˢ C := ⟨ha_mem m hm.le, hz⟩
        have hd : dist (θ, z) (a m, z) < η := by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq,
            abs_of_nonneg (by linarith [hθ'.1])]
          linarith [hθ'.2, hstep m]
        have h3 : dist (K θ z) (K (a m) z) < ε / (2 * T) := hηK _ h1 _ h2 hd
        rw [dist_eq_norm] at h3
        exact h3.le
    rwa [hstep, abs_of_pos (by positivity)] at h
  calc ‖∑ m ∈ Finset.range M,
        ((∫ θ in a m..a (m + 1), K θ z) - ((T / M : ℝ) : ℂ) * K (T * m / M) z)‖
      ≤ ∑ m ∈ Finset.range M,
        ‖(∫ θ in a m..a (m + 1), K θ z) - ((T / M : ℝ) : ℂ) * K (T * m / M) z‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range M, ε / (2 * T) * (T / M) := Finset.sum_le_sum hterm
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
    _ < ε := by linarith

/-! ### Cauchy's formula as an integral over `[0, 2π]` -/

theorem cauchy_formula_interval {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall 1 R)) {w : ℂ} (hw : w ∈ ball (1 : ℂ) R) :
    g w = ∫ θ in (0 : ℝ)..2 * π, (2 * π * I)⁻¹ * (circleMap 0 R θ * I) *
      ((circleMap 1 R θ - w)⁻¹ * g (circleMap 1 R θ)) := by
  have hd : DiffContOnCl ℂ g (ball 1 R) :=
    DifferentiableOn.diffContOnCl (by rwa [closure_ball 1 hR.ne'])
  have h := hd.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  rw [← h, circleIntegral, ← intervalIntegral.integral_smul]
  congr 1
  funext θ
  rw [deriv_circleMap]
  simp only [smul_eq_mul]
  ring

/-! ### The key lemma -/

variable {N : ℕ} {κ : Type} [Fintype κ]

/-- By invariance, `z ↦ σ(c z)` lies in `P_y` for all constants `c` near `1`. -/
theorem eventually_mem_smul {P : GermModule (ConeSpace N) κ} (hinv : IsConeInvariant P)
    {y : ConeSpace N} (hy : y ≠ 0) (hcoh : P.CoherentAt y) {σ : κ → ConeSpace N → ℂ}
    (hσ : P.mem y σ) : ∀ᶠ c in 𝓝 (1 : ℂ), P.mem y (fun j z => σ j (c • z)) := by
  have h1 : Tendsto (fun c : ℂ => c • y) (𝓝 1) (𝓝 y) := by
    have h : Tendsto (fun c : ℂ => c • y) (𝓝 1) (𝓝 ((1 : ℂ) • y)) := tendsto_id.smul_const y
    rwa [one_smul] at h
  filter_upwards [h1.eventually (eventually_mem_of_coherentAt hcoh hσ),
    eventually_ne_nhds one_ne_zero] with c hc hc0
  have := (hinv (c • y) (smul_ne_zero hc0 hy) c⁻¹ (inv_ne_zero hc0) σ).1 hc
  simpa [inv_smul_smul₀ hc0] using this

/-- **Key lemma.** Let `P` be coherent on `ℂ^{N+1} ∖ 0` and `ℂ*`-invariant, `y_i = 1` and
`σ ∈ P_y`. Then the germ of `z ↦ σ(z / z_i)` lies in `P_y`. -/
theorem mem_comp_inv_coord_smul {P : GermModule (ConeSpace N) κ}
    (hP : P.IsCoherentOn (puncture (ConeSpace N))) (hinv : IsConeInvariant P)
    {y : ConeSpace N} {i : Fin (N + 1)} (hyi : y i = 1) {σ : κ → ConeSpace N → ℂ}
    (hσ : P.mem y σ) : P.mem y (fun j z => σ j ((z i)⁻¹ • z)) := by
  classical
  have hy : y ≠ 0 := fun h => by simp [h] at hyi
  have hcoh := hP y hy
  -- `σ` is holomorphic on a ball `B(y, δ₀)`
  obtain ⟨V, hV, hyV, hσV⟩ := exists_isOpen_differentiableOn (hcoh.holTupleAt_of_mem hσ)
  obtain ⟨δ₀, hδ₀, hδ₀V⟩ := Metric.isOpen_iff.1 hV y hyV
  -- the rescalings `σ(c ·)`, `|c - 1| < R₀`, lie in `P_y`
  obtain ⟨R₀, hR₀, hR₀mem⟩ := Metric.eventually_nhds_iff.1 (eventually_mem_smul hinv hy hcoh hσ)
  set R : ℝ := min (min (R₀ / 2) (δ₀ / (4 * (‖y‖ + 1)))) (1 / 2) with hRdef
  have hR : 0 < R := by positivity
  have hRR₀ : R < R₀ := by
    have h1 : R ≤ R₀ / 2 := by
      rw [hRdef]
      exact (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hRy : R * (‖y‖ + 1) ≤ δ₀ / 4 := by
    have h1 : R ≤ δ₀ / (4 * (‖y‖ + 1)) :=
      (min_le_left _ _).trans (min_le_right (R₀ / 2) (δ₀ / (4 * (‖y‖ + 1))))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hR1 : R ≤ 1 / 2 := by
    rw [hRdef]
    exact min_le_right _ _
  -- `λ(z) = 1 / z_i` is close to `1` near `y`
  have hlam : Tendsto (fun z : ConeSpace N => (z i)⁻¹) (𝓝 y) (𝓝 1) := by
    have hc : ContinuousAt (fun z : ConeSpace N => (z i)⁻¹) y :=
      ((EuclideanSpace.proj i : ConeSpace N →L[ℂ] ℂ).continuous.continuousAt).inv₀
        (by simp [hyi])
    simpa [hyi] using hc.tendsto
  obtain ⟨δ₁, hδ₁, hδ₁lam⟩ := Metric.eventually_nhds_iff.1
    (hlam.eventually (ball_mem_nhds (1 : ℂ) (half_pos hR)))
  set δ : ℝ := min (min (δ₀ / 4) (δ₁ / 2)) 1 with hδdef
  have hδ : 0 < δ := by positivity
  have hδδ₁ : δ < δ₁ := by
    have h1 : δ ≤ δ₁ / 2 := by
      rw [hδdef]
      exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hδδ₀ : δ ≤ δ₀ / 4 := by
    rw [hδdef]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by
    rw [hδdef]
    exact min_le_right _ _
  -- the relevant estimates on `B̄(y, δ)`
  have hlamz : ∀ z ∈ closedBall y δ, (z i)⁻¹ ∈ ball (1 : ℂ) (R / 2) := fun z hz =>
    hδ₁lam (lt_of_le_of_lt (mem_closedBall.1 hz) hδδ₁)
  have hzi : ∀ z ∈ closedBall y δ, z i ≠ 0 := by
    intro z hz h0
    have := hlamz z hz
    rw [h0, inv_zero, mem_ball, dist_comm, dist_zero_right, norm_one] at this
    linarith
  have hcz : ∀ z ∈ closedBall y δ, ∀ c ∈ closedBall (1 : ℂ) R, c • z ∈ ball y δ₀ := by
    intro z hz c hc
    rw [mem_ball, dist_eq_norm]
    have hz' : ‖z - y‖ ≤ δ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hz
    have hc' : ‖c - 1‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hc
    have hzn : ‖z‖ ≤ ‖y‖ + 1 := by
      have := norm_le_insert' z y
      linarith
    calc ‖c • z - y‖ = ‖(c - 1) • z + (z - y)‖ := by
          congr 1
          rw [sub_smul, one_smul]
          abel
      _ ≤ ‖c - 1‖ * ‖z‖ + ‖z - y‖ := (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ R * (‖y‖ + 1) + δ := by gcongr
      _ < δ₀ := by linarith
  have hcθ : ∀ θ : ℝ, circleMap 1 R θ ∈ closedBall (1 : ℂ) R := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 1 hR.le θ)
  have hcθ₀ : ∀ θ : ℝ, circleMap 1 R θ ∈ ball (1 : ℂ) R₀ := fun θ =>
    closedBall_subset_ball hRR₀ (hcθ θ)
  have hden : ∀ θ : ℝ, ∀ z ∈ closedBall y δ, circleMap 1 R θ - (z i)⁻¹ ≠ 0 := by
    intro θ z hz h0
    have h1 := hlamz z hz
    rw [sub_eq_zero] at h0
    rw [← h0, mem_ball, dist_eq_norm, ← dist_eq_norm, dist_comm] at h1
    have h2 : dist (1 : ℂ) (circleMap 1 R θ) = R := by
      rw [dist_comm, ← mem_sphere]
      exact circleMap_mem_sphere 1 hR.le θ
    linarith
  -- the integrand
  set K : κ → ℝ → ConeSpace N → ℂ := fun j θ z =>
    (2 * π * I)⁻¹ * (circleMap 0 R θ * I) *
      ((circleMap 1 R θ - (z i)⁻¹)⁻¹ * σ j (circleMap 1 R θ • z)) with hKdef
  have hσdiff : ∀ j, ∀ w ∈ ball y δ₀, DifferentiableAt ℂ (σ j) w := fun j w hw =>
    (hσV j).differentiableAt (hV.mem_nhds (hδ₀V hw))
  -- Cauchy's formula
  have hcauchy : ∀ j, ∀ z ∈ closedBall y δ,
      σ j ((z i)⁻¹ • z) = ∫ θ in (0 : ℝ)..2 * π, K j θ z := by
    intro j z hz
    refine cauchy_formula_interval (g := fun c => σ j (c • z)) hR (fun c hc => ?_)
      (ball_subset_ball (by linarith) (hlamz z hz))
    exact ((hσdiff j _ (hcz z hz c hc)).comp c
      ((differentiableAt_id.smul_const z))).differentiableWithinAt
  -- continuity of the integrand
  have hKc : ∀ j, ContinuousOn (fun p : ℝ × ConeSpace N => K j p.1 p.2)
      (Icc 0 (2 * π) ×ˢ closedBall y δ) := by
    intro j
    have hcm : Continuous fun p : ℝ × ConeSpace N => circleMap 1 R p.1 :=
      (continuous_circleMap 1 R).comp continuous_fst
    have hinvc : ContinuousOn (fun p : ℝ × ConeSpace N => (p.2 i)⁻¹)
        (Icc 0 (2 * π) ×ˢ closedBall y δ) :=
      ((EuclideanSpace.proj i : ConeSpace N →L[ℂ] ℂ).continuous.comp
        continuous_snd).continuousOn.inv₀ fun p hp => hzi p.2 hp.2
    have hσc : ContinuousOn (fun p : ℝ × ConeSpace N => σ j (circleMap 1 R p.1 • p.2))
        (Icc 0 (2 * π) ×ˢ closedBall y δ) :=
      (hσV j).continuousOn.comp (hcm.smul continuous_snd).continuousOn fun p hp =>
        hδ₀V (hcz p.2 hp.2 _ (hcθ p.1))
    refine continuousOn_const.mul
      (((continuous_circleMap 0 R).comp continuous_fst).continuousOn.mul continuousOn_const)
      |>.mul ((hcm.continuousOn.sub hinvc).inv₀ (fun p hp => hden p.1 p.2 hp.2) |>.mul hσc)
  -- the Riemann sums and their limit
  set S : ℕ → κ → ConeSpace N → ℂ := fun M j z =>
    ∑ m ∈ Finset.range M, ((2 * π / M : ℝ) : ℂ) * K j (2 * π * m / M) z with hSdef
  have hlim : ∀ j, TendstoUniformlyOn (fun M => S M j) (fun z => σ j ((z i)⁻¹ • z)) atTop
      (ball y δ) := by
    intro j
    have h := tendstoUniformlyOn_riemann (by positivity) (isCompact_closedBall y δ) (hKc j)
    refine (h.congr_right fun z hz => (hcauchy j z hz).symm).mono ball_subset_closedBall
  -- the Riemann sums are combinations of members of `P_y`
  set coef : ℕ → ℕ → ConeSpace N → ℂ := fun M m z =>
    ((2 * π / M : ℝ) : ℂ) * ((2 * π * I)⁻¹ * (circleMap 0 R (2 * π * m / M) * I)) *
      (circleMap 1 R (2 * π * m / M) - (z i)⁻¹)⁻¹ with hcoefdef
  have hcoord : HolAt (fun z : ConeSpace N => z i) y := Eventually.of_forall fun _ =>
    (EuclideanSpace.proj i : ConeSpace N →L[ℂ] ℂ).differentiableAt
  have hholinv : HolAt (fun z : ConeSpace N => (z i)⁻¹) y := hcoord.inv (by simp [hyi])
  have hcoef : ∀ M m, HolAt (coef M m) y := by
    intro M m
    refine (holAt_const _ y).mul (HolAt.inv ((holAt_const _ y).sub hholinv) ?_)
    exact hden _ y (mem_closedBall_self hδ.le)
  have hmem : ∀ M, P.mem y (S M) := by
    intro M
    have h := hcoh.finset_sum_mem (Finset.range M) (a := fun m j z =>
      coef M m z * σ j (circleMap 1 R (2 * π * m / M) • z)) fun m _ =>
        hcoh.smul_mem (hcoef M m) (hR₀mem (hcθ₀ _))
    refine hcoh.congr_mem h fun j => Eventually.of_forall fun z => ?_
    simp only [hSdef, hKdef, hcoefdef]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  -- differentiability on `B(y, δ)`
  have hdiffK : ∀ j θ, DifferentiableOn ℂ (K j θ) (ball y δ) := by
    intro j θ z hz
    have hz' := ball_subset_closedBall hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_const _).mul ((((differentiableAt_const _).sub
      (((EuclideanSpace.proj i : ConeSpace N →L[ℂ] ℂ).differentiableAt).inv (hzi z hz'))).inv
        (hden θ z hz')).mul ?_)
    exact (hσdiff j _ (hcz z hz' _ (hcθ θ))).comp z
      ((differentiableAt_id.const_smul (circleMap 1 R θ)))
  have hdiffS : ∀ M j, DifferentiableOn ℂ (S M j) (ball y δ) := fun M j =>
    DifferentiableOn.fun_sum fun m _ => (hdiffK j _).const_mul _
  have hdiffb : ∀ j, DifferentiableOn ℂ (fun z => σ j ((z i)⁻¹ • z)) (ball y δ) := by
    intro j z hz
    have hz' := ball_subset_closedBall hz
    have hc : (z i)⁻¹ ∈ closedBall (1 : ℂ) R :=
      ball_subset_closedBall (ball_subset_ball (by linarith) (hlamz z hz'))
    have hf : DifferentiableAt ℂ (fun x : ConeSpace N => (x i)⁻¹ • x) z :=
      (((EuclideanSpace.proj i : ConeSpace N →L[ℂ] ℂ).differentiableAt).inv
        (hzi z hz')).smul differentiableAt_id
    exact (DifferentiableAt.comp (g := σ j) (f := fun x : ConeSpace N => (x i)⁻¹ • x) z
      (hσdiff j _ (hcz z hz' _ hc)) hf).differentiableWithinAt
  exact hcoh.mem_of_tendstoUniformlyOn hδ hdiffS hdiffb hmem hlim

end SGPT.GAGA.PN

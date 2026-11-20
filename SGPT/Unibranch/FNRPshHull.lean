import SGPT.Unibranch.FNRHullBasics
import SGPT.Foundations.Analysis.Pending.OhsawaTakegoshiPoint
import SGPT.Foundations.Analysis.Pending.AnalyticWeightedMeanValue
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.SmoothPlurisubharmonic

/-!
# Plurisubharmonic functions on polynomial hulls; sublevel sets are Runge

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), end of the proof of Lemma 5.2 and proof of Theorem 5.4 ("the well-known
fact" that `{ρ < c}` is Runge in `Δⁿ` (resp. `ℂᴺ`) for `ρ` plurisubharmonic); ingredient of
`thm:FN` (2) ⇒ (1) (`appendix_unibranch.tex`). Classical reference: Hörmander, *An
introduction to complex analysis in several variables*, Theorem 4.3.4 (`K̂_P = K̂_{PSH}`).

Main statement (`psh_le_on_polyHull`): if `K ⊆ ℂⁿ` is compact, `u` is plurisubharmonic on an open
`D ⊇ K̂` (`K̂` the polynomial hull) and `u ≤ c` on `K`, then `u ≤ c` on `K̂`.

Proof.
1. `D` bounded convex (`psh_le_on_polyHull_of_convex`). Suppose `u(z) > t > s ≥ sup_K u`. The
   Ohsawa–Takegoshi extension from the point `z` (TN `exists_extension_from_point`) with weight
   `m u` gives `F` holomorphic on `D` with `F(z) = 1` and `∫_D |F|² e^{-m u} ≤ C e^{-m t}`.
   On an `r`-neighbourhood of `K` we have `u < s`, so the holomorphic mean value inequality
   (TN `volume_mul_norm_sq_le_weighted_lintegral`) gives `|F|² ≤ C e^{-m(t-s)} / vol B_r ≤ 1/4` on
   `K` for `m` large. Oka–Weil (`norm_le_on_polyHull`) gives `1 = |F(z)| ≤ sup_K |F| ≤ 1/2`.
2. General `D` (`psh_le_on_polyHull`). A polynomial polyhedron barrier
   `ψ = ‖z‖²/R² + Σⱼ |pⱼ|^{2k}` (`exists_psh_barrier`): continuous, plurisubharmonic on `ℂⁿ`,
   `ψ ≤ 1/2` on `K̂`, `{ψ ≤ 1}` compact in `D`. Gluing `max(u, A + Mψ)` on `{ψ < 1}` with `A + Mψ`
   outside (TN `gluedMax_plurisubharmonic`) gives a function plurisubharmonic on `ℂⁿ` that is
   `≤ s` on `K` and `> t` at `z`; apply step 1 on a large ball.

Corollaries (FN80's Runge property of sublevel sets): `polyHull_subset_sublevel`,
`polydisc_sublevel_runge`, `univ_sublevel_runge`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNR

open E2Nov16FNPolynomialPolyhedron E2Nov16FNHolomorphicHullMaximum E2Nov16FNPolynomialGraphBox

variable {n : ℕ}

/-! ### Polynomial maps and their squared norms -/

theorem differentiable_polyMap {m : ℕ} (φ : Fin m → Poly n) : Differentiable ℂ (polyMap φ) :=
  fun z => differentiableAt_euclidean.2 fun i => (differentiable_polyEval (φ i)) z

theorem norm_sq_polyMap {m : ℕ} (φ : Fin m → Poly n) (z : ComplexModel n) :
    ‖polyMap φ z‖ ^ 2 = ∑ i, ‖polyEval (φ i) z‖ ^ 2 := by
  simp [polyMap, EuclideanSpace.norm_sq_eq]

/-- `z ↦ Σᵢ |φᵢ(z)|²` is plurisubharmonic on `ℂⁿ` for polynomials `φᵢ`. -/
theorem plurisubharmonicOn_sum_normSq_polyEval {m : ℕ} (φ : Fin m → Poly n) :
    PlurisubharmonicOn (fun z => ((∑ i, ‖polyEval (φ i) z‖ ^ 2 : ℝ) : EReal)) univ := by
  have h := Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    (u := fun y : ComplexModel m => ((‖y‖ ^ 2 : ℝ) : EReal)) isOpen_univ
    (differentiable_polyMap φ).differentiableOn (mapsTo_univ _ _)
    ((discPshOn_norm_sq univ).plurisubharmonicOn isOpen_univ)
  simpa only [norm_sq_polyMap] using h

/-- `z ↦ |P(z)|²` is plurisubharmonic on `ℂⁿ`. -/
theorem plurisubharmonicOn_normSq_polyEval (P : Poly n) :
    PlurisubharmonicOn (fun z => ((‖polyEval P z‖ ^ 2 : ℝ) : EReal)) univ := by
  simpa using plurisubharmonicOn_sum_normSq_polyEval (fun _ : Fin 1 => P)

/-! ### Sublevel sets -/

theorem isOpen_inter_lt_of_plurisubharmonicOn {u : ComplexModel n → EReal}
    {D : Set (ComplexModel n)} (hD : IsOpen D) (hu : PlurisubharmonicOn u D) (s : EReal) :
    IsOpen {y | y ∈ D ∧ u y < s} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyD, hys⟩
  have h1 : ∀ᶠ w in 𝓝 y, u w < s := (hu y hyD).upperSemicontinuousAt s hys
  filter_upwards [h1, hD.mem_nhds hyD] with w hw1 hw2 using ⟨hw2, hw1⟩

/-! ### Step 1: bounded convex domains, via Ohsawa–Takegoshi -/

/-- **Maximum principle for plurisubharmonic functions on polynomial hulls, convex case.**
`K` compact, `Ω` open convex bounded with `K̂ ⊆ Ω`, `u` plurisubharmonic on `Ω`, `u ≤ c` on `K`:
then `u ≤ c` on `K̂`. -/
theorem psh_le_on_polyHull_of_convex {K Ω : Set (ComplexModel n)} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) {R : ℝ} (hR : 0 < R) (hbd : ∀ z ∈ Ω, ‖z‖ < R)
    (hKΩ : polyHull K ⊆ Ω) {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    {c : EReal} (hc : ∀ x ∈ K, u x ≤ c) {z : ComplexModel n} (hz : z ∈ polyHull K) :
    u z ≤ c := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨s, hcs, hsz⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨t, hst, htz⟩ := EReal.lt_iff_exists_real_btwn.mp hsz
  have hst' : s < t := EReal.coe_lt_coe_iff.mp hst
  set O : Set (ComplexModel n) := {y | y ∈ Ω ∧ u y < s} with hOdef
  have hO : IsOpen O := isOpen_inter_lt_of_plurisubharmonicOn hΩ hu s
  have hKO : K ⊆ O := fun x hx => ⟨hKΩ (subset_polyHull K hx), (hc x hx).trans_lt hcs⟩
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_thickening_subset_open hO hKO
  set r : ℝ := δ / 2 with hr_def
  have hr : 0 < r := by positivity
  have hball : ∀ x ∈ K, closedBall x r ⊆ O := fun x hx =>
    (closedBall_subset_ball (by linarith : r < δ)).trans
      ((ball_subset_thickening hx δ).trans hδO)
  obtain ⟨C, hC, hOT⟩ :=
    SGPT.Foundations.Analysis.Pending.OhsawaTakegoshiPoint.exists_extension_from_point n R hR
  set V : ℝ := (volume (ball (0 : ComplexModel n) r)).toReal with hVdef
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume _ hr).ne' measure_ball_lt_top.ne
  obtain ⟨m, hm⟩ := exists_nat_gt (max (Real.log (4 * C / V) / (t - s)) 0)
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hsmall : C * Real.exp (-((m : ℝ) * (t - s))) < V / 4 := by
    have hts : 0 < t - s := sub_pos.mpr hst'
    have h1 : Real.log (4 * C / V) < m * (t - s) :=
      (div_lt_iff₀ hts).mp (lt_of_le_of_lt (le_max_left _ _) hm)
    have h2 : 4 * C / V < Real.exp (m * (t - s)) :=
      (Real.log_lt_iff_lt_exp (by positivity)).mp h1
    rw [div_lt_iff₀ hV] at h2
    have hex := Real.exp_pos ((m : ℝ) * (t - s))
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ hex]
    linarith
  obtain ⟨F, hFhol, hF1, hFint⟩ := hOT Ω hΩ hconv hbd u hu (m : ℝ) hm0 z (hKΩ hz)
  have hw : multiplierWeight (m : ℝ) (u z) ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * t))) := by
    rw [← multiplierWeight_coe]
    exact multiplierWeight_antitone hm0.le htz.le
  have hint : (∫⁻ y in Ω, ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (m : ℝ) (u y)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-((m : ℝ) * t))) :=
    hFint.trans (by gcongr)
  have hFK : ∀ x ∈ K, ‖F x‖ ≤ 1 / 2 := by
    intro x hx
    have hsub : closedBall x r ⊆ Ω := fun y hy => (hball x hx hy).1
    have hb : ∀ w ∈ ball x r, u w ≤ (s : EReal) :=
      fun w hw => (hball x hx (ball_subset_closedBall hw)).2.le
    have hmv := Pending.AnalyticWeightedMeanValue.volume_mul_norm_sq_le_weighted_lintegral
      hΩ hFhol hm0 hr hsub hb
    have hvol : volume (ball x r) = ENNReal.ofReal V := by
      rw [Measure.addHaar_ball_center, hVdef, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
    have key : ENNReal.ofReal V * ENNReal.ofReal (‖F x‖ ^ 2) ≤
        ENNReal.ofReal (C * Real.exp (-((m : ℝ) * (t - s)))) := by
      rw [← hvol]
      refine hmv.trans ?_
      calc _ ≤ ENNReal.ofReal (Real.exp (m * s)) *
            (ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-((m : ℝ) * t)))) := by gcongr
        _ = _ := by
          rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
    rw [← ENNReal.ofReal_mul hV.le] at key
    have key' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key
    have hsq : ‖F x‖ ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
  have h := norm_le_on_polyHull hK hΩ hKΩ F hFhol (1 / 2) hFK z hz
  rw [hF1, norm_one] at h
  norm_num at h

/-! ### Step 2: the polyhedron barrier and arbitrary open neighbourhoods -/

/-- A polynomial that is `≤ 1/2` on `K̂` and `> 1` at a given point outside `K̂`. -/
theorem exists_half_separator {K : Set (ComplexModel n)} {y : ComplexModel n}
    (hy : y ∉ polyHull K) :
    ∃ q : Poly n, (∀ z ∈ polyHull K, ‖polyEval q z‖ ≤ 1 / 2) ∧ 1 < ‖polyEval q y‖ := by
  rcases (polyHull K).eq_empty_or_nonempty with he | ⟨z₀, hz₀⟩
  · refine ⟨MvPolynomial.C 2, by simp [he], by norm_num [polyEval]⟩
  obtain ⟨p, C, hpK, hpy⟩ : ∃ (p : Poly n) (C : ℝ), (∀ x ∈ K, ‖polyEval p x‖ ≤ C) ∧
      C < ‖polyEval p y‖ := by
    by_contra h
    push Not at h
    exact hy fun p C hC => h p C hC
  have hpH : ∀ z ∈ polyHull K, ‖polyEval p z‖ ≤ C := fun z hz => hz p C hpK
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hpH z₀ hz₀)
  set a := ‖polyEval p y‖ with ha_def
  have ha : 0 < a := hC0.trans_lt hpy
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 4)
    ((div_lt_one ha).mpr hpy)
  set c : ℝ := 2 / a ^ N with hc_def
  have hcpos : 0 < c := by positivity
  have hEval (z : ComplexModel n) :
      ‖polyEval (MvPolynomial.C (c : ℂ) * p ^ N) z‖ = c * ‖polyEval p z‖ ^ N := by
    simp only [polyEval, map_mul, MvPolynomial.eval_C, map_pow, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hcpos.le]
  refine ⟨MvPolynomial.C (c : ℂ) * p ^ N, fun z hz => ?_, ?_⟩
  · rw [hEval]
    have h1 : ‖polyEval p z‖ ^ N ≤ C ^ N := pow_le_pow_left₀ (norm_nonneg _) (hpH z hz) N
    have h2 : c * C ^ N = 2 * (C / a) ^ N := by
      rw [hc_def, div_pow]; field_simp
    calc c * ‖polyEval p z‖ ^ N ≤ c * C ^ N := by gcongr
      _ = 2 * (C / a) ^ N := h2
      _ ≤ 1 / 2 := by linarith
  · rw [hEval, hc_def, ← ha_def, div_mul_cancel₀ _ (pow_pos ha N).ne']
    norm_num

/-- **Polyhedron barrier.** For `K` compact with `K̂` inside an open `D`, a continuous
plurisubharmonic `ψ : ℂⁿ → ℝ` with `ψ ≤ 1/2` on `K̂` and `{ψ ≤ 1}` a compact subset of `D`. -/
theorem exists_psh_barrier {K D : Set (ComplexModel n)} (hK : IsCompact K) (hD : IsOpen D)
    (hKD : polyHull K ⊆ D) :
    ∃ ψ : ComplexModel n → ℝ, Continuous ψ ∧ PlurisubharmonicOn (fun y => (ψ y : EReal)) univ ∧
      (∀ y ∈ polyHull K, ψ y ≤ 1 / 2) ∧ IsCompact {y | ψ y ≤ 1} ∧ {y | ψ y ≤ 1} ⊆ D := by
  classical
  obtain ⟨R₀, hR₀⟩ := (isCompact_polyHull hK).exists_bound_of_continuousOn
    (continuous_norm (E := ComplexModel n)).continuousOn
  set R : ℝ := 2 * max R₀ 0 + 1 with hR_def
  have hR : 0 < R := by positivity
  have hRK : ∀ y ∈ polyHull K, ‖y‖ ≤ R / 2 := fun y hy => by
    have h := hR₀ y hy
    rw [norm_norm] at h
    linarith [le_max_left R₀ 0]
  set E : Set (ComplexModel n) := closedBall 0 R \ D with hE_def
  have hE : IsCompact E := (isCompact_closedBall _ _).diff hD
  have hsep : ∀ y : E, ∃ q : Poly n, (∀ z ∈ polyHull K, ‖polyEval q z‖ ≤ 1 / 2) ∧
      1 < ‖polyEval q y.val‖ := fun y => exists_half_separator fun h => y.property.2 (hKD h)
  choose q hqK hqy using hsep
  obtain ⟨s, hs⟩ := hE.elim_finite_subcover (fun y : E => {x | 1 < ‖polyEval (q y) x‖})
    (fun y => isOpen_lt continuous_const (continuous_polyEval (q y)).norm)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hqy ⟨y, hy⟩⟩)
  set m : ℕ := Fintype.card s with hm_def
  let e : s ≃ Fin m := Fintype.equivFin s
  let p : Fin m → Poly n := fun j => q (e.symm j).val
  have hpK : ∀ j, ∀ z ∈ polyHull K, ‖polyEval (p j) z‖ ≤ 1 / 2 := fun j => hqK _
  have hpE : ∀ y ∈ E, ∃ j, 1 < ‖polyEval (p j) y‖ := by
    intro y hy
    obtain ⟨i, his, hi⟩ := mem_iUnion₂.mp (hs hy)
    refine ⟨e ⟨i, his⟩, ?_⟩
    simp only [p, Equiv.symm_apply_apply]
    exact hi
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (4 * (m + 1)))
    (by norm_num : (1 / 4 : ℝ) < 1)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, lt_div_iff₀ (by positivity)] at hk
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  let φ : Fin (n + m) → Poly n :=
    Fin.append (fun i : Fin n => MvPolynomial.C ((R : ℂ)⁻¹) * MvPolynomial.X i)
      (fun j : Fin m => p j ^ k)
  set ψ : ComplexModel n → ℝ := fun z => ∑ i, ‖polyEval (φ i) z‖ ^ 2 with hψ_def
  have hψ_eq : ∀ z, ψ z = ‖z‖ ^ 2 / R ^ 2 + ∑ j, (‖polyEval (p j) z‖ ^ 2) ^ k := by
    intro z
    simp only [hψ_def, Fin.sum_univ_add, φ, Fin.append_left, Fin.append_right]
    congr 1
    · rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [polyEval, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, norm_mul,
        norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
      field_simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [polyEval, map_pow, norm_pow]
      ring
  have hψc : Continuous ψ :=
    continuous_finsetSum _ fun i _ => ((continuous_polyEval (φ i)).norm).pow 2
  have hψpsh : PlurisubharmonicOn (fun y => (ψ y : EReal)) univ :=
    plurisubharmonicOn_sum_normSq_polyEval φ
  have hsum_nonneg : ∀ z, 0 ≤ ∑ j, (‖polyEval (p j) z‖ ^ 2) ^ k :=
    fun z => Finset.sum_nonneg fun j _ => by positivity
  have hψ_ge_norm : ∀ z, ‖z‖ ^ 2 / R ^ 2 ≤ ψ z := fun z => by
    rw [hψ_eq]; linarith [hsum_nonneg z]
  have hψ_ge_p : ∀ z j, (‖polyEval (p j) z‖ ^ 2) ^ k ≤ ψ z := fun z j => by
    rw [hψ_eq]
    have h1 := Finset.single_le_sum (f := fun j => (‖polyEval (p j) z‖ ^ 2) ^ k)
      (fun j _ => by positivity) (Finset.mem_univ j)
    have h2 : 0 ≤ ‖z‖ ^ 2 / R ^ 2 := by positivity
    linarith
  have hsubball : {y | ψ y ≤ 1} ⊆ closedBall 0 R := by
    intro y hy
    rw [mem_closedBall_zero_iff]
    have h1 := (hψ_ge_norm y).trans hy
    rw [div_le_one (by positivity)] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero).mp h1
  refine ⟨ψ, hψc, hψpsh, ?_, ?_, ?_⟩
  · intro y hy
    rw [hψ_eq]
    have h1 : ‖y‖ ^ 2 / R ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have := hRK y hy
      nlinarith [norm_nonneg y]
    have h2 : ∑ j, (‖polyEval (p j) y‖ ^ 2) ^ k ≤ ∑ _j : Fin m, (1 / 4 : ℝ) ^ k := by
      refine Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (by positivity) ?_ k
      have := hpK j y hy
      nlinarith [norm_nonneg (polyEval (p j) y)]
    have h3 : ∑ _j : Fin m, (1 / 4 : ℝ) ^ k ≤ 1 / 4 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hm1 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := mul_le_mul_of_nonneg_left hk.le hm1
      calc (m : ℝ) * (1 / 4) ^ k ≤ m * (1 / (4 * (m + 1))) := this
        _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
    linarith
  · exact (isCompact_closedBall (0 : ComplexModel n) R).of_isClosed_subset
      (isClosed_le hψc continuous_const) hsubball
  · intro y hy
    by_contra hyD
    obtain ⟨j, hj⟩ := hpE y ⟨hsubball hy, hyD⟩
    have h1 : 1 < (‖polyEval (p j) y‖ ^ 2) ^ k :=
      one_lt_pow₀ (one_lt_pow₀ hj two_ne_zero) hk0
    have h2 := hψ_ge_p y j
    have h3 : ψ y ≤ 1 := hy
    linarith

/-- **Maximum principle for plurisubharmonic functions on polynomial hulls**
(Hörmander, Theorem 4.3.4, the inclusion `K̂_P ⊆ K̂_{PSH}`). `K ⊆ ℂⁿ` compact, `D` open with
`K̂ ⊆ D`, `u` plurisubharmonic on `D`, `u ≤ c` on `K`: then `u ≤ c` on `K̂`. -/
theorem psh_le_on_polyHull {K D : Set (ComplexModel n)} (hK : IsCompact K) (hD : IsOpen D)
    (hKD : polyHull K ⊆ D) {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u D)
    {c : EReal} (hc : ∀ x ∈ K, u x ≤ c) {z : ComplexModel n} (hz : z ∈ polyHull K) :
    u z ≤ c := by
  by_contra hlt
  push Not at hlt
  obtain ⟨s, hcs, hsz⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨t, hst, htz⟩ := EReal.lt_iff_exists_real_btwn.mp hsz
  obtain ⟨ψ, hψc, hψpsh, hψK, hψcpt, hψD⟩ := exists_psh_barrier hK hD hKD
  have hzL : z ∈ {y | ψ y ≤ 1} := show ψ z ≤ 1 from (hψK z hz).trans (by norm_num)
  have huL : UpperSemicontinuousOn u {y | ψ y ≤ 1} := fun y hy =>
    ((hu y (hψD hy)).upperSemicontinuousAt).upperSemicontinuousWithinAt _
  obtain ⟨y₀, hy₀L, hy₀max⟩ := huL.exists_isMaxOn ⟨z, hzL⟩ hψcpt
  obtain ⟨B, hB, -⟩ := EReal.lt_iff_exists_real_btwn.mp
    (lt_top_iff_ne_top.mpr (hu y₀ (hψD hy₀L)).ne_top)
  set M : ℝ := 4 * |B - s| + 4 with hM_def
  have hM : 0 < M := by positivity
  set A : ℝ := s - M / 2 with hA_def
  set w : ComplexModel n → EReal := fun y => ((A + M * ψ y : ℝ) : EReal) with hw_def
  have hwpsh : PlurisubharmonicOn w univ := by
    have h1 := hψpsh.const_mul hM
    have h2 : PlurisubharmonicOn (fun _ : ComplexModel n => (A : EReal)) univ :=
      fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top A) x
    have h3 := h2.add h1
    have heq : (fun y => (fun _ : ComplexModel n => (A : EReal)) y +
        (M : EReal) * (ψ y : EReal)) = w := by
      funext y
      simp only [hw_def, EReal.coe_add, EReal.coe_mul]
    rwa [heq] at h3
  set U : Set (ComplexModel n) := {y | ψ y < 1} with hU_def
  have hU : IsOpen U := isOpen_lt hψc continuous_const
  have hcl : closure {y | ψ y < 3 / 4} ⊆ U := by
    refine (closure_minimal (fun y (hy : ψ y < 3 / 4) => (le_of_lt hy : ψ y ≤ 3 / 4))
      (isClosed_le hψc continuous_const)).trans ?_
    intro y (hy : ψ y ≤ 3 / 4)
    show ψ y < 1
    linarith
  have hcollar : ∀ y ∈ U \ {y | ψ y < 3 / 4}, u y ≤ w y := by
    rintro y ⟨hyU, hyU'⟩
    have hy34 : 3 / 4 ≤ ψ y := not_lt.mp hyU'
    have h1 : u y ≤ u y₀ := hy₀max (show ψ y ≤ 1 from le_of_lt (show ψ y < 1 from hyU))
    refine h1.trans (hB.le.trans ?_)
    simp only [hw_def]
    have hB' : B ≤ A + M * ψ y := by
      have := le_abs_self (B - s)
      nlinarith
    exact_mod_cast hB'
  have hv := gluedMax_plurisubharmonic hU hcl hcollar
    (hu.mono fun y (hy : ψ y < 1) => hψD (show ψ y ≤ 1 from le_of_lt hy)) hwpsh
  obtain ⟨R₁, hR₁⟩ := (isCompact_polyHull hK).isBounded.subset_ball (0 : ComplexModel n)
  have hR₁pos : 0 < R₁ := by
    have := hR₁ hz
    rw [mem_ball] at this
    exact (dist_nonneg).trans_lt this
  have hKs : ∀ x ∈ K, gluedMax U u w x ≤ (s : EReal) := by
    intro x hx
    have hxU : x ∈ U := show ψ x < 1 from
      lt_of_le_of_lt (hψK x (subset_polyHull K hx)) (by norm_num)
    rw [gluedMax_eq_max hxU]
    refine max_le ((hc x hx).trans hcs.le) ?_
    simp only [hw_def]
    have h1 := hψK x (subset_polyHull K hx)
    have h2 : A + M * ψ x ≤ s := by
      rw [hA_def]
      nlinarith
    exact_mod_cast h2
  have key := psh_le_on_polyHull_of_convex hK isOpen_ball (convex_ball 0 R₁) hR₁pos
    (fun y hy => mem_ball_zero_iff.mp hy) hR₁ (hv.mono (subset_univ _)) hKs hz
  have hzU : z ∈ U := show ψ z < 1 from lt_of_le_of_lt (hψK z hz) (by norm_num)
  rw [gluedMax_eq_max hzU] at key
  have := (le_max_left (u z) (w z)).trans key
  have : (t : EReal) < s := htz.trans_le this
  exact absurd (EReal.coe_lt_coe_iff.mp this) (not_lt.mpr (EReal.coe_lt_coe_iff.mp hst).le)

/-! ### Sublevel sets are Runge -/

/-- **Sublevel sets of plurisubharmonic functions are Runge**: for `u` plurisubharmonic on an
open `D`, `K` compact with `K̂ ⊆ D` and `K ⊆ {u < c}`, also `K̂ ⊆ {u < c}`. -/
theorem polyHull_subset_sublevel {K D : Set (ComplexModel n)} (hK : IsCompact K) (hD : IsOpen D)
    (hKD : polyHull K ⊆ D) {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u D)
    {c : EReal} (hKc : ∀ x ∈ K, u x < c) : polyHull K ⊆ {z | u z < c} := by
  rcases K.eq_empty_or_nonempty with he | hne
  · rw [he, polyHull_empty]; exact empty_subset _
  have huK : UpperSemicontinuousOn u K := fun y hy =>
    ((hu y (hKD (subset_polyHull K hy))).upperSemicontinuousAt).upperSemicontinuousWithinAt _
  obtain ⟨x₀, hx₀, hx₀max⟩ := huK.exists_isMaxOn hne hK
  intro z hz
  exact (psh_le_on_polyHull hK hD hKD hu (fun x hx => (hx₀max hx : u x ≤ u x₀)) hz).trans_lt
    (hKc x₀ hx₀)

/-- **FN80, Lemma 5.2 / Theorem 5.4 ("well-known fact")**: for `ρ` plurisubharmonic on a
polydisc `Δ` and `c ∈ [-∞, ∞]`, the sublevel set `{ρ < c}` is Runge in `Δ`: the polynomial hull
of a compact subset of `Δ ∩ {ρ < c}` lies in `Δ ∩ {ρ < c}`. -/
theorem polydisc_sublevel_runge {a : ComplexModel n} {r : Fin n → ℝ}
    {ρ : ComplexModel n → EReal}
    (hρ : PlurisubharmonicOn ρ {z : ComplexModel n | ∀ i, ‖z i - a i‖ < r i}) {c : EReal}
    {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKΔ : K ⊆ {z : ComplexModel n | ∀ i, ‖z i - a i‖ < r i}) (hKc : ∀ x ∈ K, ρ x < c) :
    polyHull K ⊆ {z : ComplexModel n | ∀ i, ‖z i - a i‖ < r i} ∩ {z | ρ z < c} := by
  have hH := polyHull_subset_polydisc hK fun x hx => hKΔ hx
  exact subset_inter hH (polyHull_subset_sublevel hK (isOpen_polydisc a r) hH hρ hKc)

/-- The same on `ℂⁿ`: for `ρ` plurisubharmonic on `ℂⁿ`, `{ρ < c}` is Runge in `ℂⁿ`. -/
theorem univ_sublevel_runge {ρ : ComplexModel n → EReal} (hρ : PlurisubharmonicOn ρ univ)
    {c : EReal} {K : Set (ComplexModel n)} (hK : IsCompact K) (hKc : ∀ x ∈ K, ρ x < c) :
    polyHull K ⊆ {z | ρ z < c} :=
  polyHull_subset_sublevel hK isOpen_univ (subset_univ _) hρ hKc

end SGPT.Unibranch.FNR

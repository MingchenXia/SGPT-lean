import SGPT.Trace.OTExt4Patch

/-!
# Thin shells around a coordinate plane: the residue estimate in flat coordinates

Blueprint `claude-ot-residue.tex`, node `claude-ot-residue:shell`.  Xia, *Foundations of
pluripotential theory*, q07, `lem:gentle-weighted-normal-residue` (the annular limit).

In `ℂ^{m+d} = ℂ^m × ℂ^d` with coordinates `z = (z', w)` and the projection `π(z', w) = (z', 0)`
(`tangProj`), let `K = {|z'| ≤ a, |w| ≤ b}` and let `r, g, ψ ≥ 0` be continuous on `K` with

* `r ≥ c_R |w|²` (the normal pole is comparable to `|w|²`),
* `g(z) ≤ g(π z) + L_g |w|`, `g ≤ M_g` (`g = |G|²_{h₀}` for a smooth section `G`),
* `ψ(π z) ≤ ψ(z) + L_ψ |w|` (`ψ = e^{Φ/c}` for a weight with gentle analytic singularities),
* the critical gain `∫_K g (r^d log² r)⁻¹ ψ^{-c(1+κ)} < ∞` (`κ > 0`),
* the Skoda bound `∫_{|z'| ≤ a} ψ(z', 0)^{-β} dz' < ∞` (`β > 0`).

Then (`limsup_shell_le`)

  `limsup_{ε → 0+} ∫_{K ∩ {ε/2 ≤ r ≤ ε}} g r^{-d} ψ^{-c} ≤ (2/c_R)^d vol(B^d) ∫_{|z'| ≤ a} g(z', 0) ψ(z', 0)^{-c} dz'`.

This replaces the log resolution of FPT's proof (which identifies the limit exactly) by an upper
bound with a constant depending only on `c_R` and `d`, which is all that FPT's
`thm:compact-submanifold-extension` uses.  Proof: put `t = ε/c_R`, `s = t^{θ/2}` with
`θ = 1/(2(c+1))`.  On the shell `|w|² ≤ t`.  Where `ψ(z', 0) ≥ s` ("good" points) the Lipschitz
bounds give `ψ(z) ≥ (1 - δ_ε) ψ(z', 0)` with `δ_ε = L_ψ t^{(1-θ)/2} → 0` and
`g(z) ψ(z', 0)^{-c} ≤ g(z', 0) ψ(z', 0)^{-c} + L_g t^{(1 - cθ)/2}`; Fubini over `ℂ^m × ℂ^d`
bounds the good part by `(1 - δ_ε)^{-c} (2/c_R)^d vol(B^d) (∫ g(z',0) ψ(z',0)^{-c} + o(1))`.
The "bad" points lie over `{ψ(z', 0) < s}`, whose measure is `≤ s^β ∫ ψ(z',0)^{-β}`; Hölder's
inequality with exponents `1 + κ` and `(1+κ)/κ` against the critical gain bounds the bad part by
`(log²(ε/2) · ∫ crit)^{1/(1+κ)} (C s^β)^{κ/(1+κ)} → 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTRes

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ProductComplexManifold
  SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
open SGPT.Trace.OTMargin (normalWeight normalWeight_nonneg normalWeight_eq_norm_snd
  fst_prodModelEquiv_symm finrank_real_complexModel')
open SGPT.Trace.OTExt4 (closedLocalDom)

/-! ### Elementary estimates -/

/-- `log² x ≤ (2/α²) x^{-α}` for `0 < x ≤ 1` and `α > 0`. -/
theorem log_sq_le_rpow {x α : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hα : 0 < α) :
    Real.log x ^ 2 ≤ 2 / α ^ 2 * x ^ (-α) := by
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hxa1 : x ^ α ≤ 1 := Real.rpow_le_one hx.le hx1 hα.le
  have h := SGPT.Trace.OTExt2.log_sq_le_two_inv hxa hxa1
  rw [Real.log_rpow hx, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le, mul_comm α (-1),
    neg_one_mul] at h
  have hα2 : 0 < α ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hα2]
  nlinarith [h]

/-- `x^γ → 0` as `x → 0+`, for `γ > 0`. -/
theorem tendsto_rpow_nhdsGT_zero {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun x : ℝ => x ^ γ) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto
  rw [Real.zero_rpow hγ.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `(x / C)^γ → 0` as `x → 0+`, for `γ > 0`. -/
theorem tendsto_div_rpow_nhdsGT_zero {γ C : ℝ} (hγ : 0 < γ) :
    Tendsto (fun x : ℝ => (x / C) ^ γ) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x / C) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_id.div_const C).tendsto (0 : ℝ))
    simp only [id, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto
  rw [Real.zero_rpow hγ.ne'] at h2
  exact h2.comp h

/-! ### The tangential projection -/

/-- `π(z', w) = (z', 0)`. -/
def tangProj (m d : ℕ) (z : ComplexModel (m + d)) : ComplexModel (m + d) :=
  coordinateInclusion (m + d) m (coordinateProjection (m + d) m z)

theorem continuous_tangProj (m d : ℕ) : Continuous (tangProj m d) :=
  (coordinateInclusion (m + d) m).continuous.comp (coordinateProjection (m + d) m).continuous

theorem coordinateProjection_tangProj (m d : ℕ) (z : ComplexModel (m + d)) :
    coordinateProjection (m + d) m (tangProj m d z) = coordinateProjection (m + d) m z :=
  coordinateProjection_coordinateInclusion (by omega) _

theorem norm_sub_tangProj_sq (m d : ℕ) (z : ComplexModel (m + d)) :
    ‖z - tangProj m d z‖ ^ 2 = normalWeight (m + d) m z := by
  rw [EuclideanSpace.norm_sq_eq, normalWeight]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i.1 < m + d := i.2
  by_cases h : i.1 < m
  · rw [if_neg (by omega)]
    simp [tangProj, coordinateInclusion_apply, coordinateProjection_apply, h, hi]
  · rw [if_pos (by omega)]
    simp [tangProj, coordinateInclusion_apply, h]

theorem norm_sub_tangProj (m d : ℕ) (z : ComplexModel (m + d)) :
    ‖z - tangProj m d z‖ = Real.sqrt (normalWeight (m + d) m z) := by
  rw [← norm_sub_tangProj_sq, Real.sqrt_sq (norm_nonneg _)]

theorem normalWeight_tangProj (m d : ℕ) (z : ComplexModel (m + d)) :
    normalWeight (m + d) m (tangProj m d z) = 0 := by
  rw [normalWeight]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h
  · simp [tangProj, coordinateInclusion_apply, not_lt.mpr h]
  · rfl

theorem tangProj_mem_closedLocalDom {m d : ℕ} {a b : ℝ} {z : ComplexModel (m + d)}
    (hz : z ∈ closedLocalDom (m + d) m a b) : tangProj m d z ∈ closedLocalDom (m + d) m a b := by
  refine ⟨?_, ?_⟩
  · have h1 := hz.1
    rw [SGPT.Trace.OTExt2.tanWeight_eq_norm_proj (by omega)] at h1 ⊢
    rwa [coordinateProjection_tangProj]
  · rw [normalWeight_tangProj]
    exact (normalWeight_nonneg _ _ z).trans hz.2

theorem tangProj_eq_coordinateInclusion (m d : ℕ) (z : ComplexModel (m + d)) :
    tangProj m d z = coordinateInclusion (m + d) m (((prodModelEquiv m d).symm z).1) := by
  rw [fst_prodModelEquiv_symm]; rfl

/-! ### Products of balls -/

theorem mem_image_prod_of_mem {m d : ℕ} {a b t : ℝ} {A : Set (ComplexModel m)}
    {z : ComplexModel (m + d)} (hz : z ∈ closedLocalDom (m + d) m a b) (ha : 0 ≤ a)
    (ht : normalWeight (m + d) m z ≤ t) (hA : coordinateProjection (m + d) m z ∈ A) :
    z ∈ prodModelEquiv m d '' ((A ∩ closedBall 0 a) ×ˢ closedBall 0 (Real.sqrt t)) := by
  refine ⟨(prodModelEquiv m d).symm z, ⟨⟨?_, ?_⟩, ?_⟩, (prodModelEquiv m d).apply_symm_apply z⟩
  · rw [fst_prodModelEquiv_symm]; exact hA
  · rw [fst_prodModelEquiv_symm, mem_closedBall_zero_iff]
    have h1 := hz.1
    rw [SGPT.Trace.OTExt2.tanWeight_eq_norm_proj (by omega)] at h1
    exact le_of_pow_le_pow_left₀ two_ne_zero ha h1
  · rw [mem_closedBall_zero_iff]
    refine Real.le_sqrt_of_sq_le ?_
    rw [← normalWeight_eq_norm_snd]; exact ht

theorem volume_closedBall_sqrt (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    volume (closedBall (0 : ComplexModel d) (Real.sqrt t)) =
      ENNReal.ofReal (t ^ d) * volume (ball (0 : ComplexModel d) 1) := by
  rw [Measure.addHaar_closedBall _ _ (Real.sqrt_nonneg t), finrank_real_complexModel', pow_mul,
    Real.sq_sqrt ht]

/-- **Fubini over `ℂ^m × ℂ^d`**: a function of the tangential coordinates, integrated over a set
inside `e(B × B̄(0, √t))`, is bounded by `(∫_B F) vol(B̄(0, √t))`. -/
theorem lintegral_proj_le {m d : ℕ} {t : ℝ} {B : Set (ComplexModel m)} {S : Set (ComplexModel (m + d))}
    (hS : S ⊆ prodModelEquiv m d '' (B ×ˢ closedBall 0 (Real.sqrt t)))
    (F : ComplexModel m → ℝ≥0∞) (hF : AEMeasurable F) :
    ∫⁻ z in S, F (coordinateProjection (m + d) m z) ≤
      (∫⁻ ζ in B, F ζ) * volume (closedBall (0 : ComplexModel d) (Real.sqrt t)) := by
  have h := SGPT.Trace.OTExt2.lintegral_image_prod m d (A := B)
    (B := closedBall (0 : ComplexModel d) (Real.sqrt t)) F (fun _ => 1) hF aemeasurable_const
  simp only [mul_one, setLIntegral_const, one_mul] at h
  calc ∫⁻ z in S, F (coordinateProjection (m + d) m z)
      ≤ ∫⁻ z in prodModelEquiv m d '' (B ×ˢ closedBall 0 (Real.sqrt t)),
          F (coordinateProjection (m + d) m z) := lintegral_mono_set hS
    _ = ∫⁻ z in prodModelEquiv m d '' (B ×ˢ closedBall 0 (Real.sqrt t)),
          F ((prodModelEquiv m d).symm z).1 := by
        refine lintegral_congr fun z => ?_
        rw [fst_prodModelEquiv_symm]
    _ = _ := h

/-! ### Limits -/

/-- `|log(x/2)|^{2/p} ((x/C)^{θ/2})^{β/q} → 0` as `x → 0+`: the bad part of the shell. -/
theorem tendsto_bad {p q θ β C : ℝ} (hp : 0 < p) (hq : 0 < q) (hθ : 0 < θ) (hβ : 0 < β)
    (hC : 0 < C) :
    Tendsto (fun x : ℝ => (Real.log (x / 2) ^ 2) ^ (1 / p) * (((x / C) ^ (θ / 2)) ^ β) ^ (1 / q))
      (𝓝[>] 0) (𝓝 0) := by
  set γ : ℝ := θ / 2 * β * (1 / q) with hγ
  have hγ0 : 0 < γ := by positivity
  set κ' : ℝ := γ * p / 2 with hκ'
  have hκ'0 : 0 < κ' := by positivity
  have h2 : Tendsto (fun x : ℝ => x / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.div_const (2 : ℝ)).tendsto (0 : ℝ))
      simp only [id, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      exact div_pos hx two_pos
  have hlog := ((tendsto_log_mul_rpow_nhdsGT_zero hκ'0).comp h2).abs
  rw [abs_zero] at hlog
  have hpow := (Real.continuousAt_rpow_const 0 (2 / p) (Or.inr (by positivity))).tendsto.comp hlog
  rw [Real.zero_rpow (by positivity)] at hpow
  have hfin := hpow.const_mul ((2 / C) ^ γ)
  rw [mul_zero] at hfin
  refine hfin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  have hx2 : 0 < x / 2 := div_pos hx two_pos
  simp only [Function.comp]
  have hl : (Real.log (x / 2) ^ 2) ^ (1 / p) = |Real.log (x / 2)| ^ (2 / p) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1; push_cast; ring
  have hs : (((x / C) ^ (θ / 2)) ^ β) ^ (1 / q) = (2 / C) ^ γ * (x / 2) ^ γ := by
    rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), ← Real.mul_rpow
      (by positivity) hx2.le]
    rw [hγ, mul_assoc]
    congr 1; field_simp
  rw [hl, hs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx2.le _),
    Real.mul_rpow (abs_nonneg _) (Real.rpow_nonneg hx2.le _), ← Real.rpow_mul hx2.le]
  have he : κ' * (2 / p) = γ := by rw [hκ']; field_simp
  rw [he]
  ring

/-- The good part of the shell: `(1 - δ_ε)^{-c} A (I + L_g (ε/c_R)^{(1-cθ)/2} Λ) → A I`. -/
theorem tendsto_good {c θ cR Lψ Lg A0 I0 Λ0 : ℝ} (h1 : 0 < 1 - θ) (h2 : 0 < 1 - c * θ) :
    Tendsto (fun ε : ℝ => (1 - Lψ * (ε / cR) ^ ((1 - θ) / 2)) ^ (-c) *
        (A0 * (I0 + Lg * (ε / cR) ^ ((1 - c * θ) / 2) * Λ0))) (𝓝[>] 0) (𝓝 (A0 * I0)) := by
  have hδ := (tendsto_div_rpow_nhdsGT_zero (C := cR) (half_pos h1)).const_mul Lψ
  rw [mul_zero] at hδ
  have h1δ := (tendsto_const_nhds (x := (1 : ℝ))).sub hδ
  rw [sub_zero] at h1δ
  have hpow := (Real.continuousAt_rpow_const 1 (-c) (Or.inl one_ne_zero)).tendsto.comp h1δ
  rw [Real.one_rpow] at hpow
  have hL := ((tendsto_div_rpow_nhdsGT_zero (C := cR) (half_pos h2)).const_mul Lg).mul_const Λ0
  rw [mul_zero, zero_mul] at hL
  have hsum := ((tendsto_const_nhds (x := I0)).add hL).const_mul A0
  rw [add_zero] at hsum
  have := hpow.mul hsum
  rw [one_mul] at this
  exact this

/-- The pointwise estimate at good points of the shell. -/
theorem good_pointwise {g gπ ψ ψπ r ε δ s ρ w Lg Lψ c T : ℝ} (d : ℕ)
    (hgL : g ≤ gπ + Lg * w) (hgπ : 0 ≤ gπ) (hs0 : 0 < s) (hsψ : s ≤ ψπ)
    (hψ : ψπ ≤ ψ + Lψ * w) (hw0 : 0 ≤ w) (hwρ : w ≤ ρ) (hδs : Lψ * ρ = δ * s) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 2) (hr : ε / 2 ≤ r) (hε : 0 < ε) (hLg : 0 ≤ Lg) (hLψ : 0 ≤ Lψ) (hc : 0 < c)
    (hρs : ρ * s ^ (-c) = T) :
    g * (r ^ d)⁻¹ * ψ ^ (-c) ≤ (1 - δ) ^ (-c) * (2 / ε) ^ d * (gπ * ψπ ^ (-c) + Lg * T) := by
  have hψπ : 0 < ψπ := hs0.trans_le hsψ
  have hδ1 : 0 < 1 - δ := by linarith
  have hψge : (1 - δ) * ψπ ≤ ψ := by
    have h1 : Lψ * w ≤ Lψ * ρ := mul_le_mul_of_nonneg_left hwρ hLψ
    have h2 : δ * s ≤ δ * ψπ := mul_le_mul_of_nonneg_left hsψ hδ0
    nlinarith
  have hpos : 0 < (1 - δ) * ψπ := mul_pos hδ1 hψπ
  have hw : ψ ^ (-c) ≤ (1 - δ) ^ (-c) * ψπ ^ (-c) := by
    rw [← Real.mul_rpow hδ1.le hψπ.le]
    exact Real.rpow_le_rpow_of_nonpos hpos hψge (by linarith)
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hrinv : (r ^ d)⁻¹ ≤ (2 / ε) ^ d := by
    rw [← inv_pow]
    refine pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) ?_ d
    calc r⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ (by positivity) hr
      _ = 2 / ε := by rw [inv_div]
  have hsc : ψπ ^ (-c) ≤ s ^ (-c) := Real.rpow_le_rpow_of_nonpos hs0 hsψ (by linarith)
  have hψc0 : 0 ≤ ψ ^ (-c) := Real.rpow_nonneg (le_trans hpos.le hψge) _
  have hψπc0 : 0 ≤ ψπ ^ (-c) := Real.rpow_nonneg hψπ.le _
  have hT : Lg * w * ψπ ^ (-c) ≤ Lg * T := by
    rw [← hρs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hLg
    exact mul_le_mul hwρ hsc hψπc0 (hw0.trans hwρ)
  calc g * (r ^ d)⁻¹ * ψ ^ (-c)
      ≤ (gπ + Lg * w) * (2 / ε) ^ d * ((1 - δ) ^ (-c) * ψπ ^ (-c)) := by
        gcongr
    _ = (1 - δ) ^ (-c) * (2 / ε) ^ d * (gπ * ψπ ^ (-c) + Lg * w * ψπ ^ (-c)) := by ring
    _ ≤ (1 - δ) ^ (-c) * (2 / ε) ^ d * (gπ * ψπ ^ (-c) + Lg * T) := by
        gcongr

/-- The pointwise estimate at bad points of the shell: `g r^{-d} ≤ log²(ε/2) g (r^d log² r)⁻¹`. -/
theorem bad_pointwise {g r ε : ℝ} (d : ℕ) (hg0 : 0 ≤ g) (hε1 : ε < 1) (hr : ε / 2 ≤ r)
    (hr1 : r ≤ ε) (hε : 0 < ε) :
    g * (r ^ d)⁻¹ ≤ Real.log (ε / 2) ^ 2 * (g * (r ^ d * Real.log r ^ 2)⁻¹) := by
  have hε2 : 0 < ε / 2 := by positivity
  have hr0 : 0 < r := hε2.trans_le hr
  have hlr : Real.log r < 0 := Real.log_neg hr0 (by linarith)
  have hle : Real.log (ε / 2) ≤ Real.log r := Real.log_le_log hε2 hr
  have hsq : Real.log r ^ 2 ≤ Real.log (ε / 2) ^ 2 := by nlinarith
  have hl2 : 0 < Real.log r ^ 2 := by nlinarith
  have hrd : 0 < r ^ d := pow_pos hr0 d
  have key : (r ^ d)⁻¹ ≤ Real.log (ε / 2) ^ 2 * (r ^ d * Real.log r ^ 2)⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_comm (Real.log (ε / 2) ^ 2), mul_assoc]
    refine le_mul_of_one_le_right (inv_nonneg.mpr hrd.le) ?_
    rw [← div_eq_mul_inv, one_le_div hl2]
    exact hsq
  calc g * (r ^ d)⁻¹ ≤ g * (Real.log (ε / 2) ^ 2 * (r ^ d * Real.log r ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left key hg0
    _ = Real.log (ε / 2) ^ 2 * (g * (r ^ d * Real.log r ^ 2)⁻¹) := by ring

/-! ### The shell estimate -/

/-- **The residue estimate in flat coordinates** (FPT `lem:gentle-weighted-normal-residue`, upper
bound form).  See the module docstring. -/
theorem limsup_shell_le {m d : ℕ} {a b : ℝ} (ha : 0 ≤ a)
    {r g ψ : ComplexModel (m + d) → ℝ} {c κ cR β Lg Lψ Mg : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hcR : 0 < cR) (hβ : 0 < β) (hLg : 0 ≤ Lg) (hLψ : 0 ≤ Lψ)
    (hrc : ContinuousOn r (closedLocalDom (m + d) m a b))
    (hgc : ContinuousOn g (closedLocalDom (m + d) m a b))
    (hψc : ContinuousOn ψ (closedLocalDom (m + d) m a b))
    (hr : ∀ z ∈ closedLocalDom (m + d) m a b, cR * normalWeight (m + d) m z ≤ r z)
    (hg0 : ∀ z ∈ closedLocalDom (m + d) m a b, 0 ≤ g z)
    (hgM : ∀ z ∈ closedLocalDom (m + d) m a b, g z ≤ Mg)
    (hgL : ∀ z ∈ closedLocalDom (m + d) m a b,
      g z ≤ g (tangProj m d z) + Lg * Real.sqrt (normalWeight (m + d) m z))
    (hψ0 : ∀ z ∈ closedLocalDom (m + d) m a b, 0 ≤ ψ z)
    (hψL : ∀ z ∈ closedLocalDom (m + d) m a b,
      ψ (tangProj m d z) ≤ ψ z + Lψ * Real.sqrt (normalWeight (m + d) m z))
    (hcrit : ∫⁻ z in closedLocalDom (m + d) m a b,
      ENNReal.ofReal (g z * (r z ^ d * Real.log (r z) ^ 2)⁻¹) *
        ENNReal.ofReal (ψ z) ^ (-(c * (1 + κ))) ≠ ⊤)
    (hsk : ∫⁻ ζ in closedBall (0 : ComplexModel m) a,
      ENNReal.ofReal (ψ (coordinateInclusion (m + d) m ζ)) ^ (-β) ≠ ⊤) :
    limsup (fun ε : ℝ => ∫⁻ z in closedLocalDom (m + d) m a b ∩ {z | ε / 2 ≤ r z ∧ r z ≤ ε},
        ENNReal.ofReal (g z * (r z ^ d)⁻¹) * ENNReal.ofReal (ψ z) ^ (-c)) (𝓝[>] 0) ≤
      ENNReal.ofReal ((2 / cR) ^ d) * volume (ball (0 : ComplexModel d) 1) *
        ∫⁻ ζ in closedBall (0 : ComplexModel m) a,
          ENNReal.ofReal (g (coordinateInclusion (m + d) m ζ)) *
            ENNReal.ofReal (ψ (coordinateInclusion (m + d) m ζ)) ^ (-c) := by
  classical
  set K := closedLocalDom (m + d) m a b with hKdef
  set ι := coordinateInclusion (m + d) m with hιdef
  set proj := coordinateProjection (m + d) m with hprojdef
  set vD : ℝ≥0∞ := volume (ball (0 : ComplexModel d) 1) with hvDdef
  set Λ : ℝ≥0∞ := volume (closedBall (0 : ComplexModel m) a) with hΛdef
  set I : ℝ≥0∞ := ∫⁻ ζ in closedBall (0 : ComplexModel m) a,
      ENNReal.ofReal (g (ι ζ)) * ENNReal.ofReal (ψ (ι ζ)) ^ (-c) with hIdef
  set Ic : ℝ≥0∞ := ∫⁻ z in K, ENNReal.ofReal (g z * (r z ^ d * Real.log (r z) ^ 2)⁻¹) *
      ENNReal.ofReal (ψ z) ^ (-(c * (1 + κ))) with hIcdef
  set J : ℝ≥0∞ := ∫⁻ ζ in closedBall (0 : ComplexModel m) a, ENNReal.ofReal (ψ (ι ζ)) ^ (-β)
    with hJdef
  have hKc : IsCompact K := SGPT.Trace.OTExt4.isCompact_closedLocalDom _ _ _ _
  have hKcl : IsClosed K := hKc.isClosed
  have hKm : MeasurableSet K := hKcl.measurableSet
  have hvD : vD ≠ ⊤ := measure_ball_lt_top.ne
  have hvD0 : vD ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hΛ : Λ ≠ ⊤ := measure_closedBall_lt_top.ne
  have hιK : ∀ ζ ∈ closedBall (0 : ComplexModel m) a, ι ζ ∈ K := by
    intro ζ hζ
    refine ⟨?_, ?_⟩
    · rw [SGPT.Trace.OTExt2.tanWeight_eq_norm_proj (by omega), hιdef,
        coordinateProjection_coordinateInclusion (by omega)]
      exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hζ) 2
    · have h0 : normalWeight (m + d) m (ι ζ) = 0 := by
        have := normalWeight_tangProj m d (ι ζ)
        rwa [tangProj, coordinateProjection_coordinateInclusion (by omega)] at this
      rw [h0]; positivity
  have hπK : ∀ z ∈ K, tangProj m d z ∈ K := fun z hz => tangProj_mem_closedLocalDom hz
  have hπι : ∀ z, tangProj m d z = ι (proj z) := fun z => rfl
  have hprojK : ∀ z ∈ K, proj z ∈ closedBall (0 : ComplexModel m) a := by
    intro z hz
    have h1 := hz.1
    rw [SGPT.Trace.OTExt2.tanWeight_eq_norm_proj (by omega)] at h1
    exact mem_closedBall_zero_iff.mpr (le_of_pow_le_pow_left₀ two_ne_zero ha h1)
  have hC0 : ENNReal.ofReal ((2 / cR) ^ d) * vD ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hvD0
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top hC0]; exact le_top
  -- measurability on `K`
  have hgm : AEMeasurable g (volume.restrict K) := hgc.aemeasurable hKm
  have hrm : AEMeasurable r (volume.restrict K) := hrc.aemeasurable hKm
  have hψm : AEMeasurable ψ (volume.restrict K) := hψc.aemeasurable hKm
  -- parameters
  set θ : ℝ := 1 / (2 * (c + 1)) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθ1 : 0 < 1 - θ := by
    rw [hθdef, sub_pos, div_lt_one (by positivity)]; linarith
  have hcθ : 0 < 1 - c * θ := by
    rw [hθdef, sub_pos, mul_one_div, div_lt_one (by positivity)]; linarith
  set p : ℝ := 1 + κ with hpdef
  set q : ℝ := (1 + κ) / κ with hqdef
  have hp0 : 0 < p := by positivity
  have hq0 : 0 < q := by positivity
  have hpq : p.HolderConjugate q := by
    refine Real.holderConjugate_iff.mpr ⟨by linarith, ?_⟩
    rw [hpdef, hqdef, inv_div]
    field_simp
  have hpq1 : 1 / p + 1 / q = 1 := by
    rw [one_div, one_div]; exact hpq.inv_add_inv_eq_one
  set Mg' : ℝ := max Mg 0 with hMg'
  set δ : ℝ → ℝ := fun ε => Lψ * (ε / cR) ^ ((1 - θ) / 2) with hδdef
  set A1 : ℝ → ℝ≥0∞ := fun ε => ENNReal.ofReal ((1 - δ ε) ^ (-c) *
      (((2 / cR) ^ d * vD.toReal) * (I.toReal + Lg * (ε / cR) ^ ((1 - c * θ) / 2) * Λ.toReal)))
    with hA1def
  set K3 : ℝ≥0∞ := Ic ^ (1 / p) * (ENNReal.ofReal (Mg' * (2 / cR) ^ d) * J * vD) ^ (1 / q)
    with hK3def
  set A2 : ℝ → ℝ≥0∞ := fun ε => K3 * ENNReal.ofReal ((Real.log (ε / 2) ^ 2) ^ (1 / p) *
      (((ε / cR) ^ (θ / 2)) ^ β) ^ (1 / q)) with hA2def
  have hK3 : K3 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hcrit)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_)
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsk) hvD
  -- the limit of the bound
  have hlim : Tendsto (fun ε => A1 ε + A2 ε) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((2 / cR) ^ d) * vD * I)) := by
    have h1 : Tendsto A1 (𝓝[>] 0) (𝓝 (ENNReal.ofReal (((2 / cR) ^ d * vD.toReal) * I.toReal))) :=
      ENNReal.tendsto_ofReal (tendsto_good hθ1 hcθ)
    have h2 : Tendsto A2 (𝓝[>] 0) (𝓝 (K3 * ENNReal.ofReal 0)) :=
      ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal (tendsto_bad hp0 hq0 hθ0 hβ hcR))
        (Or.inr hK3)
    have := h1.add h2
    rwa [ENNReal.ofReal_zero, mul_zero, add_zero, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hvD,
      ENNReal.ofReal_toReal hI] at this
  -- the pointwise bound, eventually
  have hδlim : Tendsto δ (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_div_rpow_nhdsGT_zero (C := cR) (half_pos hθ1)).const_mul Lψ
    rwa [mul_zero] at this
  have hbound : ∀ᶠ ε in 𝓝[>] 0,
      ∫⁻ z in K ∩ {z | ε / 2 ≤ r z ∧ r z ≤ ε},
        ENNReal.ofReal (g z * (r z ^ d)⁻¹) * ENNReal.ofReal (ψ z) ^ (-c) ≤ A1 ε + A2 ε := by
    have hlt1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, hlt1, (tendsto_order.1 hδlim).2 (1 / 2) (by norm_num)]
      with ε (hε0 : 0 < ε) hε1 hδε
    set t : ℝ := ε / cR with htdef
    have ht0 : 0 < t := div_pos hε0 hcR
    set s : ℝ := t ^ (θ / 2) with hsdef
    have hs0 : 0 < s := Real.rpow_pos_of_pos ht0 _
    set ρ : ℝ := Real.sqrt t with hρdef
    have hδ0 : 0 ≤ δ ε := mul_nonneg hLψ (Real.rpow_nonneg ht0.le _)
    have hδs : Lψ * ρ = δ ε * s := by
      simp only [hδdef, hsdef, hρdef]
      rw [mul_assoc, ← Real.rpow_add ht0, Real.sqrt_eq_rpow]
      congr 2; ring
    have hρs : ρ * s ^ (-c) = t ^ ((1 - c * θ) / 2) := by
      rw [hρdef, hsdef, Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le, ← Real.rpow_add ht0]
      congr 1; ring
    set S := K ∩ {z | ε / 2 ≤ r z ∧ r z ≤ ε} with hSdef
    have hSm : MeasurableSet S :=
      (hrc.preimage_isClosed_of_isClosed hKcl isClosed_Icc).measurableSet
    set Kg := K ∩ (fun z => ψ (tangProj m d z)) ⁻¹' Ici s with hKgdef
    have hKgm : MeasurableSet Kg :=
      ((hψc.comp (continuous_tangProj m d).continuousOn hπK).preimage_isClosed_of_isClosed hKcl
        isClosed_Ici).measurableSet
    have hSK : ∀ z ∈ S, normalWeight (m + d) m z ≤ t := by
      intro z hz
      have := hr z hz.1
      rw [htdef, le_div_iff₀ hcR]
      linarith [hz.2.2]
    have hvol : volume (closedBall (0 : ComplexModel d) (Real.sqrt t)) =
        ENNReal.ofReal (t ^ d) * vD := volume_closedBall_sqrt d ht0.le
    have hrinv : ∀ z ∈ S, (r z ^ d)⁻¹ ≤ (2 / ε) ^ d := by
      intro z hz
      have hr0 : 0 < r z := lt_of_lt_of_le (by positivity) hz.2.1
      rw [← inv_pow]
      refine pow_le_pow_left₀ (inv_nonneg.mpr hr0.le) ?_ d
      calc (r z)⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ (by positivity) hz.2.1
        _ = 2 / ε := by rw [inv_div]
    rw [← lintegral_inter_add_sdiff _ S hKgm]
    refine add_le_add ?_ ?_
    · -- the good part
      set H : ComplexModel m → ℝ≥0∞ := (closedBall (0 : ComplexModel m) a).indicator
        (fun ζ => ENNReal.ofReal (g (ι ζ)) * ENNReal.ofReal (ψ (ι ζ)) ^ (-c)) with hHdef
      have hHm : AEMeasurable H := by
        refine (aemeasurable_indicator_iff measurableSet_closedBall).mpr ?_
        have hc1 : ContinuousOn (fun ζ => g (ι ζ)) (closedBall 0 a) :=
          hgc.comp ι.continuous.continuousOn hιK
        have hc2 : ContinuousOn (fun ζ => ψ (ι ζ)) (closedBall 0 a) :=
          hψc.comp ι.continuous.continuousOn hιK
        exact (ENNReal.measurable_ofReal.comp_aemeasurable
          (hc1.aemeasurable measurableSet_closedBall)).mul
          ((ENNReal.measurable_ofReal.comp_aemeasurable
            (hc2.aemeasurable measurableSet_closedBall)).pow_const _)
      set C1 : ℝ := (1 - δ ε) ^ (-c) * (2 / ε) ^ d with hC1def
      set T1 : ℝ := t ^ ((1 - c * θ) / 2) with hT1def
      have hδ1 : 0 < 1 - δ ε := by linarith
      have hC10 : 0 ≤ C1 := by positivity
      have hT10 : 0 ≤ T1 := by positivity
      have hpt : ∀ z ∈ S ∩ Kg, ENNReal.ofReal (g z * (r z ^ d)⁻¹) * ENNReal.ofReal (ψ z) ^ (-c) ≤
          ENNReal.ofReal C1 * (H (proj z) + ENNReal.ofReal (Lg * T1)) := by
        intro z hz
        obtain ⟨⟨hzK, hz1, hz2⟩, -, hzg⟩ := hz
        have hzg' : s ≤ ψ (tangProj m d z) := hzg
        have hψπ : 0 < ψ (tangProj m d z) := hs0.trans_le hzg'
        have hw : Real.sqrt (normalWeight (m + d) m z) ≤ ρ :=
          Real.sqrt_le_sqrt (hSK z ⟨hzK, hz1, hz2⟩)
        have hreal := good_pointwise d (hgL z hzK) (hg0 _ (hπK z hzK)) hs0 hzg' (hψL z hzK)
          (Real.sqrt_nonneg _) hw hδs hδ0 hδε.le hz1 hε0 hLg hLψ hc hρs
        have hψz : 0 < ψ z := by
          have h1 : Lψ * Real.sqrt (normalWeight (m + d) m z) ≤ Lψ * ρ :=
            mul_le_mul_of_nonneg_left hw hLψ
          have h2 : δ ε * s ≤ δ ε * ψ (tangProj m d z) := mul_le_mul_of_nonneg_left hzg' hδ0
          have h3 := hψL z hzK
          nlinarith
        have hr0 : 0 < r z := lt_of_lt_of_le (by positivity) hz1
        rw [hHdef, indicator_of_mem (hprojK z hzK), ← hπι z, ENNReal.ofReal_rpow_of_pos hψz,
          ENNReal.ofReal_rpow_of_pos hψπ,
          ← ENNReal.ofReal_mul (mul_nonneg (hg0 z hzK) (by positivity)),
          ← ENNReal.ofReal_mul (hg0 _ (hπK z hzK)),
          ← ENNReal.ofReal_add (mul_nonneg (hg0 _ (hπK z hzK)) (Real.rpow_nonneg hψπ.le _))
            (mul_nonneg hLg hT10), ← ENNReal.ofReal_mul hC10]
        exact ENNReal.ofReal_le_ofReal hreal
      have hsub : S ∩ Kg ⊆ K ∩ {z | normalWeight (m + d) m z ≤ t} :=
        fun z hz => ⟨hz.1.1, hSK z hz.1⟩
      have himg : K ∩ {z | normalWeight (m + d) m z ≤ t} ⊆
          prodModelEquiv m d '' (closedBall (0 : ComplexModel m) a ×ˢ closedBall 0 (Real.sqrt t)) := by
        intro z hz
        have := mem_image_prod_of_mem (A := univ) hz.1 ha hz.2 (mem_univ _)
        rwa [univ_inter] at this
      have hint1 : ∫⁻ z in K ∩ {z | normalWeight (m + d) m z ≤ t}, H (proj z) ≤
          I * (ENNReal.ofReal (t ^ d) * vD) := by
        refine (lintegral_proj_le himg H hHm).trans (le_of_eq ?_)
        rw [hvol, hHdef, setLIntegral_indicator measurableSet_closedBall, inter_self]
      have hint2 : volume (K ∩ {z | normalWeight (m + d) m z ≤ t}) ≤
          Λ * (ENNReal.ofReal (t ^ d) * vD) := by
        have := lintegral_proj_le himg (fun _ => (1 : ℝ≥0∞)) aemeasurable_const
        simp only [setLIntegral_const, one_mul] at this
        rwa [hvol] at this
      calc ∫⁻ z in S ∩ Kg, ENNReal.ofReal (g z * (r z ^ d)⁻¹) * ENNReal.ofReal (ψ z) ^ (-c)
          ≤ ∫⁻ z in S ∩ Kg, ENNReal.ofReal C1 * (H (proj z) + ENNReal.ofReal (Lg * T1)) :=
            setLIntegral_mono' (hSm.inter hKgm) hpt
        _ ≤ ∫⁻ z in K ∩ {z | normalWeight (m + d) m z ≤ t},
              ENNReal.ofReal C1 * (H (proj z) + ENNReal.ofReal (Lg * T1)) := lintegral_mono_set hsub
        _ = ENNReal.ofReal C1 * ((∫⁻ z in K ∩ {z | normalWeight (m + d) m z ≤ t}, H (proj z)) +
              ENNReal.ofReal (Lg * T1) * volume (K ∩ {z | normalWeight (m + d) m z ≤ t})) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ ENNReal.ofReal C1 * (I * (ENNReal.ofReal (t ^ d) * vD) +
              ENNReal.ofReal (Lg * T1) * (Λ * (ENNReal.ofReal (t ^ d) * vD))) := by
            gcongr
        _ = A1 ε := by
            have key : ENNReal.ofReal ((2 / ε) ^ d) * ENNReal.ofReal (t ^ d) =
                ENNReal.ofReal ((2 / cR) ^ d) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, htdef]
              congr 2
              field_simp
            have h1 : 0 ≤ (1 - δ ε) ^ (-c) := Real.rpow_nonneg hδ1.le _
            simp only [hA1def]
            rw [← htdef, ← hT1def]
            conv_rhs => rw [ENNReal.ofReal_mul h1, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
              ENNReal.ofReal_mul (mul_nonneg hLg hT10), ENNReal.ofReal_toReal hvD,
              ENNReal.ofReal_toReal hI, ENNReal.ofReal_toReal hΛ, ← key]
            rw [hC1def, ENNReal.ofReal_mul h1]
            ring
    · -- the bad part: Hölder against the critical gain
      set u : ComplexModel (m + d) → ℝ := fun z => g z * (r z ^ d)⁻¹ with hudef
      set w : ComplexModel (m + d) → ℝ≥0∞ := fun z => ENNReal.ofReal (ψ z) ^ (-c) with hwdef
      set f1 : ComplexModel (m + d) → ℝ≥0∞ := fun z => ENNReal.ofReal (u z) ^ (1 / p) * w z
        with hf1def
      set f2 : ComplexModel (m + d) → ℝ≥0∞ := fun z => ENNReal.ofReal (u z) ^ (1 / q) with hf2def
      have hSb : S \ Kg ⊆ K := fun z hz => hz.1.1
      have hμle : volume.restrict (S \ Kg) ≤ volume.restrict K := Measure.restrict_mono hSb le_rfl
      have hum : AEMeasurable (fun z => ENNReal.ofReal (u z)) (volume.restrict K) :=
        ENNReal.measurable_ofReal.comp_aemeasurable (hgm.mul (hrm.pow_const d).inv)
      have hwm : AEMeasurable w (volume.restrict K) :=
        (ENNReal.measurable_ofReal.comp_aemeasurable hψm).pow_const _
      have hf1m : AEMeasurable f1 (volume.restrict (S \ Kg)) :=
        ((hum.pow_const _).mul hwm).mono_measure hμle
      have hf2m : AEMeasurable f2 (volume.restrict (S \ Kg)) :=
        (hum.pow_const _).mono_measure hμle
      have hF : ∀ z, ENNReal.ofReal (u z) * w z = (f1 * f2) z := by
        intro z
        simp only [Pi.mul_apply, hf1def, hf2def]
        rw [mul_right_comm, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hpq1,
          ENNReal.rpow_one]
      have hf1p : ∀ z, f1 z ^ p = ENNReal.ofReal (u z) * ENNReal.ofReal (ψ z) ^ (-(c * (1 + κ))) := by
        intro z
        simp only [hf1def, hwdef]
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div,
          inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one, hpdef]
        congr 2; ring
      have hf2q : ∀ z, f2 z ^ q = ENNReal.ofReal (u z) := by
        intro z
        simp only [hf2def]
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
      have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (S \ Kg)) hpq hf1m hf2m
      -- the critical factor
      have hB1 : ∫⁻ z in S \ Kg, f1 z ^ p ≤ ENNReal.ofReal (Real.log (ε / 2) ^ 2) * Ic := by
        simp_rw [hf1p]
        calc ∫⁻ z in S \ Kg, ENNReal.ofReal (u z) * ENNReal.ofReal (ψ z) ^ (-(c * (1 + κ)))
            ≤ ∫⁻ z in S \ Kg, ENNReal.ofReal (Real.log (ε / 2) ^ 2) *
                (ENNReal.ofReal (g z * (r z ^ d * Real.log (r z) ^ 2)⁻¹) *
                  ENNReal.ofReal (ψ z) ^ (-(c * (1 + κ)))) := by
              refine setLIntegral_mono' (hSm.diff hKgm) fun z hz => ?_
              obtain ⟨⟨hzK, hz1, hz2⟩, -⟩ := hz
              rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
              gcongr
              exact bad_pointwise d (hg0 z hzK) hε1 hz1 hz2 hε0
          _ ≤ ∫⁻ z in K, ENNReal.ofReal (Real.log (ε / 2) ^ 2) *
                (ENNReal.ofReal (g z * (r z ^ d * Real.log (r z) ^ 2)⁻¹) *
                  ENNReal.ofReal (ψ z) ^ (-(c * (1 + κ)))) := lintegral_mono_set hSb
          _ = ENNReal.ofReal (Real.log (ε / 2) ^ 2) * Ic :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      -- the volume factor
      set Bd : Set (ComplexModel m) := (fun ζ => ψ (ι ζ)) ⁻¹' Iio s ∩ closedBall 0 a with hBddef
      have hBdm : MeasurableSet Bd := by
        have hcl : IsClosed (closedBall (0 : ComplexModel m) a ∩ (fun ζ => ψ (ι ζ)) ⁻¹' Ici s) :=
          (hψc.comp ι.continuous.continuousOn hιK).preimage_isClosed_of_isClosed isClosed_closedBall
            isClosed_Ici
        have heq : Bd = closedBall (0 : ComplexModel m) a \
            (closedBall (0 : ComplexModel m) a ∩ (fun ζ => ψ (ι ζ)) ⁻¹' Ici s) := by
          ext ζ
          constructor
          · rintro ⟨hlt, hb⟩
            exact ⟨hb, fun h => absurd (show s ≤ ψ (ι ζ) from h.2) (not_le.mpr hlt)⟩
          · rintro ⟨hb, hn⟩
            exact ⟨show ψ (ι ζ) < s from not_le.mp fun h => hn ⟨hb, h⟩, hb⟩
        rw [heq]
        exact measurableSet_closedBall.diff hcl.measurableSet
      have hBd : volume Bd ≤ ENNReal.ofReal s ^ β * J := by
        calc volume Bd = ∫⁻ _ in Bd, (1 : ℝ≥0∞) := (setLIntegral_one _).symm
          _ ≤ ∫⁻ ζ in Bd, ENNReal.ofReal s ^ β * ENNReal.ofReal (ψ (ι ζ)) ^ (-β) := by
              refine setLIntegral_mono' hBdm fun ζ hζ => ?_
              obtain ⟨hlt, hζb⟩ := hζ
              have hlt' : ψ (ι ζ) < s := hlt
              have hψ0' := hψ0 _ (hιK ζ hζb)
              rcases hψ0'.eq_or_lt with h0 | hpos
              · rw [← h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
                  ENNReal.mul_top (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hs0)
                    ENNReal.ofReal_ne_top).ne']
                exact le_top
              · rw [ENNReal.ofReal_rpow_of_pos hs0, ENNReal.ofReal_rpow_of_pos hpos,
                  ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hpos _)]
                exact Real.rpow_le_rpow hpos.le hlt'.le hβ.le
          _ ≤ ∫⁻ ζ in closedBall (0 : ComplexModel m) a,
                ENNReal.ofReal s ^ β * ENNReal.ofReal (ψ (ι ζ)) ^ (-β) :=
              lintegral_mono_set inter_subset_right
          _ = ENNReal.ofReal s ^ β * J :=
              lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hβ.le ENNReal.ofReal_ne_top)
      have himgb : S \ Kg ⊆ prodModelEquiv m d '' (Bd ×ˢ closedBall 0 (Real.sqrt t)) := by
        intro z hz
        obtain ⟨⟨hzK, hz1, hz2⟩, hzg⟩ := hz
        refine mem_image_prod_of_mem hzK ha (hSK z ⟨hzK, hz1, hz2⟩) ?_
        show ψ (ι (proj z)) < s
        rw [← hπι]
        by_contra hcon
        exact hzg ⟨hzK, not_lt.mp hcon⟩
      have hvolb : volume (S \ Kg) ≤ volume Bd * (ENNReal.ofReal (t ^ d) * vD) := by
        have := lintegral_proj_le himgb (fun _ => (1 : ℝ≥0∞)) aemeasurable_const
        simp only [setLIntegral_const, one_mul] at this
        rwa [hvol] at this
      have hB2 : ∫⁻ z in S \ Kg, f2 z ^ q ≤ ENNReal.ofReal (Mg' * (2 / ε) ^ d) *
          (ENNReal.ofReal s ^ β * J * (ENNReal.ofReal (t ^ d) * vD)) := by
        simp_rw [hf2q]
        calc ∫⁻ z in S \ Kg, ENNReal.ofReal (u z)
            ≤ ∫⁻ _ in S \ Kg, ENNReal.ofReal (Mg' * (2 / ε) ^ d) := by
              refine setLIntegral_mono' (hSm.diff hKgm) fun z hz => ?_
              obtain ⟨⟨hzK, hz1, hz2⟩, -⟩ := hz
              refine ENNReal.ofReal_le_ofReal ?_
              exact mul_le_mul ((hgM z hzK).trans (le_max_left _ _)) (hrinv z ⟨hzK, hz1, hz2⟩)
                (inv_nonneg.mpr (pow_nonneg (le_trans (by positivity) hz1) _)) (le_max_right _ _)
          _ = ENNReal.ofReal (Mg' * (2 / ε) ^ d) * volume (S \ Kg) := setLIntegral_const _ _
          _ ≤ _ := by
              gcongr
              exact hvolb.trans (by gcongr)
      calc ∫⁻ z in S \ Kg, ENNReal.ofReal (g z * (r z ^ d)⁻¹) * ENNReal.ofReal (ψ z) ^ (-c)
          = ∫⁻ z, (f1 * f2) z ∂(volume.restrict (S \ Kg)) := lintegral_congr fun z => hF z
        _ ≤ _ := hHold
        _ ≤ (ENNReal.ofReal (Real.log (ε / 2) ^ 2) * Ic) ^ (1 / p) *
              (ENNReal.ofReal (Mg' * (2 / ε) ^ d) *
                (ENNReal.ofReal s ^ β * J * (ENNReal.ofReal (t ^ d) * vD))) ^ (1 / q) :=
            mul_le_mul' (ENNReal.rpow_le_rpow hB1 (by positivity))
              (ENNReal.rpow_le_rpow hB2 (by positivity))
        _ = A2 ε := by
            have key : ENNReal.ofReal (Mg' * (2 / ε) ^ d) * ENNReal.ofReal (t ^ d) =
                ENNReal.ofReal (Mg' * (2 / cR) ^ d) := by
              rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← mul_pow, htdef]
              congr 3
              field_simp
            have hY : ENNReal.ofReal (Mg' * (2 / ε) ^ d) *
                (ENNReal.ofReal s ^ β * J * (ENNReal.ofReal (t ^ d) * vD)) =
                (ENNReal.ofReal (Mg' * (2 / cR) ^ d) * J * vD) * ENNReal.ofReal s ^ β := by
              rw [← key]; ring
            simp only [hA2def, hK3def]
            rw [← htdef, ← hsdef, hY,
              ENNReal.ofReal_mul (show 0 ≤ (Real.log (ε / 2) ^ 2) ^ (1 / p) by positivity),
              ← ENNReal.ofReal_rpow_of_nonneg (sq_nonneg (Real.log (ε / 2)))
                (show (0 : ℝ) ≤ 1 / p by positivity),
              ← ENNReal.ofReal_rpow_of_nonneg (show 0 ≤ s ^ β by positivity)
                (show (0 : ℝ) ≤ 1 / q by positivity),
              ← ENNReal.ofReal_rpow_of_nonneg hs0.le hβ.le,
              ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / p by positivity),
              ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / q by positivity)]
            ring
  calc limsup (fun ε : ℝ => ∫⁻ z in K ∩ {z | ε / 2 ≤ r z ∧ r z ≤ ε},
        ENNReal.ofReal (g z * (r z ^ d)⁻¹) * ENNReal.ofReal (ψ z) ^ (-c)) (𝓝[>] 0)
      ≤ limsup (fun ε => A1 ε + A2 ε) (𝓝[>] 0) := limsup_le_limsup hbound
    _ = _ := hlim.limsup_eq

end SGPT.Trace.OTRes

import SGPT.Okounkov.TranscendentalWNRegLaplacian
import SGPT.Okounkov.TranscendentalWNRegStatement
import SGPT.Foundations.Analysis.Pending.BoundedIntegrationByParts
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation
import SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact

/-!
# Berman's Laplacian estimate for envelopes of smooth obstacles

Package WN-REG (`claude-tok-wn-reg`, nodes `tok-wn-reg:beta-envelope` and
`tok-wn-reg:berman-smooth`): the β-solutions converge uniformly to the envelope, and the uniform
Laplacian bound passes to the envelope.  This proves `BermanSmoothEnvelopeStatement`
(`tok-wn:berman` for smooth obstacles; WN21 Theorem 2.5 with `ψ` smooth).  Source: R. Berman,
arXiv:1307.3008v3, Proposition 2.4 (the maximum-principle proof of
`sup |u_β - P(F)| ≤ A log β / β`) and Proposition 2.7.

* `isThetaPshPotential_coe_sub` — a β-solution shifted by a constant is an `A`-psh competitor.
* `eventually_le_add_of_antitone` — Dini's lemma on a compact space for a decreasing sequence of
  continuous functions whose (not necessarily continuous) limit lies below a continuous function.
* `competitor_le_betaSolution` (lower bound of Prop. 2.4): every competitor `v` of the envelope
  `P_A(F)` satisfies `v ≤ u_β + (2B + N log β)/β` (`|F| ≤ B`, `β ≥ 1`).  Following Berman, `v`
  is replaced by `max(v, -B)`, regularized by TN's decreasing smooth approximation
  (`BoundedIntegrationByParts.exists_antitone_chartSmooth`, Demailly), and the smooth
  subsolutions `(1 - 1/β) t_k v_k` are compared with `u_β` by the maximum principle
  (`le_betaSolution_of_subsolution`).
* `envelope_bounds` — `u_β - N log(1+S)/β ≤ P_A(F) ≤ u_β + (2B + N log β)/β`.
* `bermanSmoothEnvelopeStatement` — the statement `BermanSmoothEnvelopeStatement`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Okounkov.TranscendentalWNReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### Smooth competitors -/

/-- A chart-smooth `φ` with `A + ddᶜφ` Kähler, shifted by a constant, is an `A`-psh potential. -/
theorem isThetaPshPotential_coe_sub (A : KahlerBackground N Y) {φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler) (c : ℝ) :
    IsThetaPshPotential A.form.val (fun x => ((φ x - c : ℝ) : EReal)) := by
  have hs : ChartSmooth (n := N) (fun x => φ x - c) := fun e => (hφ e).sub contDiffOn_const
  refine ⟨(LocalPotentials.thetaPlurisubharmonic_smooth_iff A.form _ hs).mpr
    fun e z hz v => ?_, fun x U _ hxU => ⟨x, hxU, EReal.coe_ne_bot _⟩⟩
  have hsub : smoothDDC (fun y => φ (e.val.symm y) - c) z = smoothDDC (fun y => φ (e.val.symm y)) z := by
    rw [PositiveClasses.smoothDDC_sub e.val.open_target (hφ e) contDiffOn_const hz,
      GlobalPotentialTransforms.smoothDDC_const, sub_zero]
  rw [hsub]
  have h := coefficientSemipositive_of_isKahler hK hz v
  rw [add_ddc_line, ddcClosedForm_coeff] at h
  exact h

/-! ### Dini's lemma -/

/-- **Dini's lemma, one-sided**: on a compact space, if continuous `u_k` decrease pointwise to
`g ≤ F` with `F` continuous, then for every `η > 0` eventually `u_k ≤ F + η` everywhere. -/
theorem eventually_le_add_of_antitone [CompactSpace Y] {uk : ℕ → Y → ℝ}
    (hc : ∀ k, Continuous (uk k)) (hanti : ∀ x, Antitone fun k => uk k x) {g F : Y → ℝ}
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (g x))) (hF : Continuous F)
    (hgF : ∀ x, g x ≤ F x) {η : ℝ} (hη : 0 < η) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ y, uk k y ≤ F y + η := by
  set K : ℕ → Set Y := fun k => {y | F y + η ≤ uk k y} with hKdef
  have hKc : ∀ k, IsClosed (K k) := fun k => isClosed_le (hF.add continuous_const) (hc k)
  have hempty : univ ∩ ⋂ k, K k = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_univ, mem_iInter, true_and, mem_empty_iff_false, iff_false]
    intro hy
    have h1 : F y + η ≤ g y := ge_of_tendsto (hlim y) (Eventually.of_forall fun k => hy k)
    linarith [hgF y]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subfamily_closed K hKc hempty
  refine ⟨t.sup id, fun k hk y => ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : y ∈ univ ∩ ⋂ i ∈ t, K i := by
    refine ⟨mem_univ y, mem_iInter₂.mpr fun i hi => ?_⟩
    have hik : i ≤ k := (Finset.le_sup (f := id) hi).trans hk
    exact le_trans hcon.le (hanti y hik)
  rw [ht] at hmem
  exact hmem

/-! ### The lower bound of Proposition 2.4 -/

section Lower

variable [CompactSpace Y]

/-- **Every competitor of the envelope lies below `u_β + (2B + N log β)/β`** (Berman 2019,
Proposition 2.4, lower bound): for `β ≥ 1`, `|F| ≤ B`, a β-solution `u_β` of `F`, and an `A`-psh
`v` with `v ≤ F` quasi-everywhere. -/
theorem competitor_le_betaSolution (A : KahlerBackground N Y) {β : ℝ} (hβ : 1 ≤ β)
    {F : Y → ℝ} (hF : ChartSmooth (n := N) F) {B : ℝ} (hB : ∀ y, |F y| ≤ B)
    (U : BetaSolution A β F) {v : Y → EReal} (hv : IsThetaPshPotential A.form.val v)
    (hqe : QuasiEverywhere (n := N) (fun x => v x ≤ ((F x : ℝ) : EReal))) (x : Y) :
    v x ≤ ((U.u x + (2 * B + N * Real.log β) / β : ℝ) : EReal) := by
  have hβpos : 0 < β := by linarith
  have hFc : Continuous F := YauUniformEstimate.continuous_of_chartSmooth hF
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  -- `v ≤ F` everywhere
  have hvF : ∀ y, v y ≤ ((F y : ℝ) : EReal) :=
    ContinuousObstacleEnvelopeContact.le_coe_of_ae_in_charts_le hv.1 hFc
      fun e => hqe.ae_in_chart e volume
  -- the truncation `g = max(v, -B)`
  set g : Y → EReal := fun y => max (v y) ((-B : ℝ) : EReal) with hgdef
  have hg : ThetaPlurisubharmonic A.form.val g :=
    BoundedGlobalProduct.thetaPlurisubharmonic_max_const A.isSemipositive hv.1 (-B)
  have hgle : ∀ y, g y ≤ ((F y : ℝ) : EReal) := fun y =>
    max_le (hvF y) (EReal.coe_le_coe_iff.mpr (by linarith [(abs_le.mp (hB y)).1]))
  have hgb : BoundedGlobalProduct.IsBoundedPotential g :=
    ⟨-B, B, fun y => ⟨le_max_right _ _, (hgle y).trans
      (EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hB y)))⟩⟩
  set gR : Y → ℝ := fun y => (g y).toReal with hgRdef
  have hgcoe : ∀ y, g y = ((gR y : ℝ) : EReal) := fun y =>
    (EReal.coe_toReal (hgb.ne_top y) (hgb.ne_bot y)).symm
  have hgRF : ∀ y, gR y ≤ F y := fun y => by
    have := hgle y; rw [hgcoe y] at this; exact EReal.coe_le_coe_iff.mp this
  have hgRB : ∀ y, -B ≤ gR y := fun y => by
    have : ((-B : ℝ) : EReal) ≤ g y := le_max_right _ _
    rw [hgcoe y] at this; exact EReal.coe_le_coe_iff.mp this
  -- Demailly's decreasing regularization
  obtain ⟨uk, huk, hukpsh, hanti, hlim⟩ :=
    BoundedIntegrationByParts.exists_antitone_chartSmooth A A.form hg hgb
  have hukc : ∀ k, Continuous (uk k) := fun k =>
    YauUniformEstimate.continuous_of_chartSmooth (huk k)
  have hukge : ∀ k y, gR y ≤ uk k y := fun k y =>
    (hanti y).le_of_tendsto (hlim y) k
  -- the constants
  set δ : ℝ := 1 / β with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hβpos]; exact hβ
  set s : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hsdef
  have hs0 : ∀ k, 0 ≤ s k := fun k => by positivity
  set t : ℕ → ℝ := fun k => (1 + s k)⁻¹ with htdef
  have ht0 : ∀ k, 0 < t k := fun k => inv_pos.mpr (by linarith [hs0 k])
  have ht1 : ∀ k, t k ≤ 1 := fun k => inv_le_one_of_one_le₀ (by linarith [hs0 k])
  have hts : ∀ k, t k * (1 + s k) = 1 := fun k => inv_mul_cancel₀ (by linarith [hs0 k])
  set c : ℕ → ℝ := fun k => (1 - δ) * t k with hcdef
  have hc0 : ∀ k, 0 ≤ c k := fun k => mul_nonneg (by linarith) (ht0 k).le
  have hc1 : ∀ k, c k ≤ 1 := fun k => by
    have : (1 - δ) * t k ≤ 1 * 1 :=
      mul_le_mul (by linarith) (ht1 k) (ht0 k).le zero_le_one
    simpa [hcdef] using this
  have hclim : Tendsto c atTop (𝓝 (1 - δ)) := by
    have hs : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto t atTop (𝓝 1) := by
      have h1 : Tendsto (fun k => 1 + s k) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hs
      rw [add_zero] at h1
      simpa using h1.inv₀ one_ne_zero
    simpa using ht.const_mul (1 - δ)
  -- for each `η > 0`, the comparison for large `k`
  have hkey : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      c k * gR x - (1 - c k) * B - η + N * Real.log δ / β ≤ U.u x := by
    intro η hη
    obtain ⟨k₀, hk₀⟩ := eventually_le_add_of_antitone hukc hanti hlim hFc hgRF hη
    refine eventually_atTop.mpr ⟨k₀, fun k hk => ?_⟩
    have hw : ChartSmooth (n := N) (fun y => c k * uk k y) := fun e =>
      contDiffOn_const.mul (huk k e)
    have hpsh := (LocalPotentials.thetaPlurisubharmonic_smooth_iff
      (A.form + s k • A.form) (uk k) (huk k)).mp (by simpa [hsdef] using hukpsh k)
    have hwδ : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ v : ComplexModel N, δ * A.form.val.coeff e z ![v, Complex.I • v] ≤
          (A.form + ddcClosedForm (fun y => c k * uk k y) hw).val.coeff e z
            ![v, Complex.I • v] := by
      intro e z hz v
      have h := hpsh e z hz v
      rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] at h
      simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul] at h
      rw [add_ddc_line, ddcClosedForm_coeff]
      have hsm := smoothDDC_smul e.val.open_target (huk k e) (c k) hz
      simp only [smul_eq_mul] at hsm
      rw [hsm]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      set a := A.form.val.coeff e z ![v, Complex.I • v]
      set D := smoothDDC (fun y => uk k (e.val.symm y)) z ![v, Complex.I • v]
      have ha : 0 ≤ a := coefficientSemipositive_of_isKahler A.isKahler hz v
      have h2 : -(1 + s k) * a ≤ D := by linarith
      have h3 : c k * (-(1 + s k) * a) ≤ c k * D := mul_le_mul_of_nonneg_left h2 (hc0 k)
      have h4 : c k * (-(1 + s k) * a) = -((1 - δ) * a) := by
        simp only [hcdef]
        have := hts k
        calc (1 - δ) * t k * (-(1 + s k) * a) = -((1 - δ) * (t k * (1 + s k)) * a) := by ring
          _ = -((1 - δ) * a) := by rw [this, mul_one]
      linarith
    have hwF : ∀ y, c k * uk k y ≤ F y + ((1 - c k) * B + η) := by
      intro y
      have h1 := hk₀ k hk y
      have h2 : c k * uk k y ≤ c k * (F y + η) := mul_le_mul_of_nonneg_left h1 (hc0 k)
      have h3 : -(1 - c k) * F y ≤ (1 - c k) * B := by
        have := mul_le_mul_of_nonneg_left (neg_le_abs (F y) |>.trans (hB y)) (sub_nonneg.mpr (hc1 k))
        linarith
      have h4 : c k * η ≤ η := by nlinarith [hc1 k]
      nlinarith
    have hsub := le_betaSolution_of_subsolution hβpos hw hδ0 hwδ hwF U x
    have h5 : c k * gR x ≤ c k * uk k x := mul_le_mul_of_nonneg_left (hukge k x) (hc0 k)
    linarith
  -- `k → ∞`, then `η → 0`
  have hlimit : ∀ η : ℝ, 0 < η →
      (1 - δ) * gR x - δ * B - η + N * Real.log δ / β ≤ U.u x := by
    intro η hη
    have hT : Tendsto (fun k => c k * gR x - (1 - c k) * B - η + N * Real.log δ / β) atTop
        (𝓝 ((1 - δ) * gR x - (1 - (1 - δ)) * B - η + N * Real.log δ / β)) := by
      refine ((((hclim.mul_const (gR x)).sub ((tendsto_const_nhds.sub hclim).mul_const B)).sub
        tendsto_const_nhds).add tendsto_const_nhds)
    have := le_of_tendsto hT (hkey η hη)
    have he : (1 : ℝ) - (1 - δ) = δ := by ring
    rw [he] at this
    exact this
  have hfinal : (1 - δ) * gR x - δ * B + N * Real.log δ / β ≤ U.u x := by
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have := hlimit (η / 2) (half_pos hη)
    linarith
  -- conclusion
  have hlogδ : Real.log δ = -Real.log β := by
    rw [hδdef, one_div, Real.log_inv]
  have hgx : gR x - (2 * B + N * Real.log β) / β ≤ U.u x := by
    have hgB : gR x ≤ B := (hgRF x).trans ((le_abs_self _).trans (hB x))
    have h1 : δ * (gR x + B) ≤ δ * (2 * B) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ0.le
    have h2 : (2 * B + N * Real.log β) / β = δ * (2 * B) + N * Real.log β / β := by
      rw [hδdef]; field_simp
    rw [hlogδ] at hfinal
    have h3 : N * -Real.log β / β = -(N * Real.log β / β) := by ring
    rw [h3] at hfinal
    rw [h2]
    nlinarith
  calc v x ≤ g x := le_max_left _ _
    _ = ((gR x : ℝ) : EReal) := hgcoe x
    _ ≤ ((U.u x + (2 * B + N * Real.log β) / β : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (by linarith)

/-- **The envelope is squeezed by the β-solutions** (Berman 2019, Proposition 2.4): if
`ddᶜF ≤ S·A` on complex lines (`S ≥ 0`), `|F| ≤ B` and `β ≥ 1`, then
`u_β - N log(1 + S)/β ≤ P_A(F) ≤ u_β + (2B + N log β)/β`. -/
theorem envelope_bounds (A : KahlerBackground N Y) {β : ℝ} (hβ : 1 ≤ β) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) {S : ℝ} (hS : 0 ≤ S)
    (hFS : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
        S * A.form.val.coeff e z ![v, Complex.I • v])
    {B : ℝ} (hB : ∀ y, |F y| ≤ B) (U : BetaSolution A β F) (x : Y) :
    ((U.u x - N * Real.log (1 + S) / β : ℝ) : EReal) ≤
        rooftopEnvelope A.form.val (fun y => (F y : EReal)) x ∧
      rooftopEnvelope A.form.val (fun y => (F y : EReal)) x ≤
        ((U.u x + (2 * B + N * Real.log β) / β : ℝ) : EReal) := by
  have hβpos : 0 < β := by linarith
  constructor
  · have hc := isThetaPshPotential_coe_sub A U.smooth U.isKahler (N * Real.log (1 + S) / β)
    have hle : (fun y => ((U.u y - N * Real.log (1 + S) / β : ℝ) : EReal)) ≤
        fun y => ((F y : ℝ) : EReal) := fun y => EReal.coe_le_coe_iff.mpr (by
      have := betaSolution_le_add hβpos hF hS hFS U y
      linarith)
    exact le_rooftopEnvelope hc (quasiEverywhere_of_forall hle) x
  · have husc : UpperSemicontinuous
        (fun y => ((U.u y + (2 * B + N * Real.log β) / β : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.comp
        ((YauUniformEstimate.continuous_of_chartSmooth U.smooth).add
          continuous_const)).upperSemicontinuous
    refine ((rooftopEnvelope_le_iff husc).mpr fun v hv hqe => ?_) x
    intro y
    exact competitor_le_betaSolution A hβ hF hB U hv hqe y

end Lower

/-! ### The envelope estimate -/

/-- `log β / β → 0` along `β_j = j + c`. -/
theorem tendsto_log_div_natCast_add (c : ℝ) :
    Tendsto (fun j : ℕ => Real.log ((j : ℝ) + c) / ((j : ℝ) + c)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun j : ℕ => (j : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
  have := h.comp h2
  refine this.congr fun j => ?_
  simp

/-- `C / β → 0` along `β_j = j + c`. -/
theorem tendsto_const_div_natCast_add (C c : ℝ) :
    Tendsto (fun j : ℕ => C / ((j : ℝ) + c)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun j : ℕ => (j : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop h2

/-- **`BermanSmoothEnvelopeStatement`** (`tok-wn:berman` for smooth obstacles): Berman's
Laplacian estimate for the envelope `P_A(F)` of a smooth obstacle, with constants depending only
on `(Y, A)`. -/
theorem bermanSmoothEnvelopeStatement : BermanSmoothEnvelopeStatement.{u} := by
  intro N Y _ _ _ _ _ A
  obtain ⟨a, Λ, β₀, ha0, hΛ, hβ₀, hlap⟩ := betaSolution_line_le A
  refine ⟨a, Λ, ha0, hΛ, fun F hF S hS hFS m hm => ?_⟩
  -- the parameters `β_j = j + max β₀ 1`
  set c₀ : ℝ := max β₀ 1 with hc₀def
  have hc₀ : 0 < c₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set β : ℕ → ℝ := fun j => (j : ℝ) + c₀ with hβdef
  have hβ1 : ∀ j, 1 ≤ β j := fun j => by
    have := le_max_right β₀ 1
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [hβdef]; linarith
  have hββ₀ : ∀ j, β₀ ≤ β j := fun j => by
    have := le_max_left β₀ 1
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [hβdef]; linarith
  have hβpos : ∀ j, 0 < β j := fun j => by linarith [hβ1 j]
  have U : ∀ j, BetaSolution A (β j) F := fun j =>
    Classical.choice (exists_betaSolution A (hβpos j) hF)
  -- a bound for `|F|`
  obtain ⟨B, hB⟩ := YauContinuityMethod.exists_abs_le hF
  -- the error terms
  set ε : ℕ → ℝ := fun j => (N * Real.log (1 + S) + 2 * B) / β j + N * (Real.log (β j) / β j)
    with hεdef
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 := tendsto_const_div_natCast_add (N * Real.log (1 + S) + 2 * B) c₀
    have h2 := (tendsto_log_div_natCast_add c₀).const_mul (N : ℝ)
    simpa [hεdef, hβdef] using h1.add h2
  have hS1 : 0 ≤ Real.log (1 + S) := Real.log_nonneg (by linarith)
  -- the envelope is real and within `ε_j` of `u_j`
  have hbd := fun j x => envelope_bounds A (hβ1 j) hF hS hFS hB (U j) x
  have hfin : ∀ x, rooftopEnvelope A.form.val (fun y => (F y : EReal)) x =
      ((envelopeReal A.form F x : ℝ) : EReal) := by
    intro x
    obtain ⟨h1, h2⟩ := hbd 0 x
    have hne_bot : rooftopEnvelope A.form.val (fun y => (F y : EReal)) x ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
    have hne_top : rooftopEnvelope A.form.val (fun y => (F y : EReal)) x ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    exact (EReal.coe_toReal hne_top hne_bot).symm
  have hclose : ∀ j x, |(U j).u x - envelopeReal A.form F x| ≤ ε j := by
    intro j x
    obtain ⟨h1, h2⟩ := hbd j x
    rw [hfin x] at h1 h2
    have h1' := EReal.coe_le_coe_iff.mp h1
    have h2' := EReal.coe_le_coe_iff.mp h2
    have hβj := hβpos j
    have hεj : ε j = N * Real.log (1 + S) / β j + (2 * B + N * Real.log (β j)) / β j := by
      simp only [hεdef]
      field_simp
      ring
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
    have p1 : 0 ≤ N * Real.log (1 + S) / β j := by positivity
    have p2 : 0 ≤ (2 * B + N * Real.log (β j)) / β j := by
      have : 0 ≤ Real.log (β j) := Real.log_nonneg (hβ1 j)
      positivity
    have e1 : N * Real.log (1 + S) / β j ≤ ε j := by rw [hεj]; linarith
    have e2 : (2 * B + N * Real.log (β j)) / β j ≤ ε j := by rw [hεj]; linarith
    rw [abs_le]
    constructor <;> linarith
  refine ⟨hfin, fun j => (U j).u, fun j => (U j).smooth, ?_, fun j => (U j).isKahler, ?_⟩
  · -- uniform convergence
    rw [Metric.tendstoUniformly_iff]
    intro r hr
    filter_upwards [(hεlim.eventually (gt_mem_nhds hr))] with j hj x
    rw [Real.dist_eq, abs_sub_comm]
    exact (hclose j x).trans_lt hj
  · -- the line bound
    intro r hr
    have hFB : ∀ x, F x - m ≤ B - m := fun x => by linarith [(le_abs_self (F x)).trans (hB x)]
    set K : ℝ := (1 + S) * Λ * Real.exp (a * (B - m)) with hKdef
    have hK0 : 0 ≤ K := by
      have : 0 ≤ 1 + S := by linarith
      positivity
    -- `e^{a N log(1+S)/β_j} → 1`
    have hδlim : Tendsto (fun j => Real.exp (a * (N * Real.log (1 + S) / β j))) atTop (𝓝 1) := by
      have h := (tendsto_const_div_natCast_add (N * Real.log (1 + S)) c₀).const_mul a
      rw [mul_zero] at h
      have h' := (Real.continuous_exp.tendsto 0).comp h
      rw [Real.exp_zero] at h'
      exact h'
    have hev : ∀ᶠ j in atTop, K * (Real.exp (a * (N * Real.log (1 + S) / β j)) - 1) < r := by
      have h := (hδlim.sub_const 1).const_mul K
      rw [sub_self, mul_zero] at h
      exact h.eventually (gt_mem_nhds hr)
    filter_upwards [hev] with j hj e z hz v
    have hmj : ∀ y, m ≤ (U j).u y := fun y => le_betaSolution_of_le (hβpos j) hm (U j) y
    have hline := hlap (β j) (hββ₀ j) F hF S hS hFS (U j) m hmj e z hz v
    have hup := betaSolution_le_add (hβpos j) hF hS hFS (U j) (e.val.symm z)
    have hA0 : 0 ≤ A.form.val.coeff e z ![v, Complex.I • v] :=
      coefficientSemipositive_of_isKahler A.isKahler hz v
    set x := e.val.symm z
    set δj := a * (N * Real.log (1 + S) / β j)
    have hexp : Real.exp (a * ((U j).u x - m)) ≤ Real.exp (a * (F x - m)) * Real.exp δj := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : a * ((U j).u x - m) ≤ a * (F x - m + N * Real.log (1 + S) / β j) :=
        mul_le_mul_of_nonneg_left (by linarith) ha0
      simp only [δj]
      linarith
    have hcoef : (1 + S) * Λ * Real.exp (a * ((U j).u x - m)) ≤
        (1 + S) * Λ * Real.exp (a * (F x - m)) + r := by
      have h1S : 0 ≤ (1 + S) * Λ := by
        have : 0 ≤ 1 + S := by linarith
        positivity
      have h1 : (1 + S) * Λ * Real.exp (a * ((U j).u x - m)) ≤
          (1 + S) * Λ * (Real.exp (a * (F x - m)) * Real.exp δj) :=
        mul_le_mul_of_nonneg_left hexp h1S
      have h2 : (1 + S) * Λ * Real.exp (a * (F x - m)) ≤ K := by
        rw [hKdef]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hFB x) ha0)) h1S
      have hδ1 : 1 ≤ Real.exp δj := by
        apply Real.one_le_exp
        have : 0 ≤ N * Real.log (1 + S) / β j := by
          have := hβpos j; positivity
        exact mul_nonneg ha0 this
      have h3 : (1 + S) * Λ * Real.exp (a * (F x - m)) * (Real.exp δj - 1) ≤
          K * (Real.exp δj - 1) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
      nlinarith
    calc (A.form + ddcClosedForm ((U j).u) ((U j).smooth)).val.coeff e z ![v, Complex.I • v]
        ≤ (1 + S) * Λ * Real.exp (a * ((U j).u x - m)) *
          A.form.val.coeff e z ![v, Complex.I • v] := hline
      _ ≤ ((1 + S) * Λ * Real.exp (a * (F x - m)) + r) *
          A.form.val.coeff e z ![v, Complex.I • v] := mul_le_mul_of_nonneg_right hcoef hA0

end SGPT.Okounkov.TranscendentalWNReg

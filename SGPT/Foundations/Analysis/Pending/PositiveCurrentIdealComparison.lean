import SGPT.Foundations.Analysis.Pending.IdealWeightPowers
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `lem:ideal-comparison`, first inclusion: `𝔅 · 𝔅̄_m^p ⊆ 𝓘(M u)`

Source: Copy-4, `lem:ideal-comparison`, the paragraph "For the first one, let `f` be a local section
of `𝔅` ..." (`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1688-1700`),
with `lem:trace-approximants`(iii) for the bound on sections of `𝔅̄_m^p`.  Piece of the
positive-current programme (`TN.2.3.PCI`) assigned by TN23-ENVELOPES: the
route-independent first inclusion, on an arbitrary complex manifold `Z` (Copy-4: `Z = V`).

Dictionary (Copy-4 → Lean): `u` the trace of `V_θ` (or route F's limit potential), `h = h_C`,
`φ = φ_m` of type `(m⁻¹, 𝔅̄_m)`, `𝔣 = 𝔅 = 𝓘(ℓ φ_K) ⊆ 𝓘(ℓ h_C)`, `p = (C-1)ℓ/m`, `M = Cℓ`.

* `mul_idealPow_le_multiplierIdeal` — TN23's target: if `𝔣 ⊆ 𝓘(ℓ h)`, `φ` has analytic
  singularities of type `(m⁻¹, 𝔟)`, `mp = ℓ(C-1)`, `C ≥ 1`, `u` is quasi-psh and
  `h + (C-1)φ ≤ C u` everywhere, then `𝔣 · 𝔟^p ⊆ 𝓘(Cℓ u)`.
* `mul_idealPow_le_multiplierIdeal_of_quasiEverywhere` — the same with the chain only
  quasi-everywhere, which is how Copy-4 (`lem:positive-rooftop`) states it;
  `mul_idealPow_le_multiplierIdeal_of_ae` — almost everywhere in every preferred chart (both of the
  others are corollaries of this one).

`u` quasi-psh is needed for the statement to be true: membership in `𝓘(Cℓ u)` requires
a.e.-measurability of `|g|² e^{-Cℓ u}`, and for a non-measurable `u ≥ 0` (`C = ℓ = m = 1`, `p = 0`,
`φ = h = 0`) the germ `1 ∈ 𝓘(0) · 𝒪` is not in `𝓘(u)`.  Nothing is needed of `h` or `φ` beyond
the hypotheses above (`h` may take the value `⊤`).

## Proof (Copy-4's)

`p • φ` has type `(m⁻¹, 𝔟^p)` (`IdealWeightPowers.hasAnalyticSingularitiesOfType_pow`), so a germ
`b ∈ 𝔟^p` is a holomorphic combination of local generators `G_J` and
`|b|² ≤ K Σ|G_J|² ≤ K' e^{mp φ} = K' e^{ℓ(C-1)φ}` near the point
(`exists_eventually_ofReal_normSq_le_of_mem_idealPow`).  The chain gives
`e^{ℓ(C-1)φ} e^{-Cℓ u} ≤ e^{-ℓ h}` (`exp_mul_multiplierWeight_le`, all `⊥`/`⊤` cases), hence
`|f b|² e^{-Cℓu} ≤ K' |f|² e^{-ℓh}` (`multiplierDensity_mul_le_of_bound`) and `f b ∈ 𝓘(Cℓu)` for
`f ∈ 𝓘(ℓh)`.  A germ of `𝔣 · 𝔟^p` is a holomorphic combination of such products, and `𝓘(Cℓu)` is
closed under those (`MultiplierIdealProductComparison.mem_multiplierIdeal_of_isInSpanAt`, which is
where quasi-plurisubharmonicity of `u` enters, through measurability).

The tree's `MultiplierIdealProductComparison.multiplierIdeal_mul_le` proves the same inclusion for
`𝔣 = 𝓘(ℓ h_C)` from chart-level hypotheses (`h_C`, `φ_m` quasi-psh, the bound on `𝔟` assumed);
here the bound is derived from the analytic type of `φ` and no regularity of `h`, `φ` is assumed.

Sorry-free.  No existing statement is changed.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentIdealComparison

noncomputable section

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  IdealWeightPowers IdealWeightComparison MultiplierIdealProductComparison

/-! ### Pointwise estimates -/

/-- **`Σ|gᵢ|² ≤ e^{mC₀} e^{m a}`** where `a = m⁻¹ log Σ|gᵢ|² + R`, `|R| ≤ C₀`: the lower bound of a
weight with analytic singularities of type `(m⁻¹, ⟨gᵢ⟩)` by its generators, read the other way. -/
theorem ofReal_generatorNormSq_le {X : Type*} {N m : ℕ} (hm : 0 < m) {G : Fin N → X → ℂ}
    {y : X} {a : EReal} {R C₀ : ℝ} (hRC : |R| ≤ C₀)
    (ha : a = ((((m : ℚ)⁻¹ : ℚ) : ℝ) : EReal) * generatorLog G y + (R : EReal)) :
    ENNReal.ofReal (generatorNormSq G y) ≤
      ENNReal.ofReal (Real.exp (m * C₀)) * EReal.exp (((m : ℝ) : EReal) * a) := by
  set S := generatorNormSq G y with hS
  rcases (show 0 ≤ S from Finset.sum_nonneg fun i _ => sq_nonneg _).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : generatorLog G y = (Real.log S : EReal) := by
    refine generatorLog_of_nonzero ?_
    by_contra hcon
    push Not at hcon
    exact hpos.ne' (by simp [hS, generatorNormSq, hcon])
  have hcR : (((m : ℚ)⁻¹ : ℚ) : ℝ) = (m : ℝ)⁻¹ := by push_cast; ring
  have ha' : ((m : ℝ) : EReal) * a = ((Real.log S + m * R : ℝ) : EReal) := by
    rw [ha, hlog, hcR, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul]
    congr 1
    field_simp
  rw [ha', EReal.exp_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.exp_add, Real.exp_log hpos]
  have hR : 0 ≤ m * C₀ + m * R := by
    have := neg_abs_le R
    nlinarith
  have h1 : 1 ≤ Real.exp (m * C₀ + m * R) := Real.one_le_exp hR
  calc S = S * 1 := (mul_one S).symm
    _ ≤ S * Real.exp (m * C₀ + m * R) := mul_le_mul_of_nonneg_left h1 hpos.le
    _ = Real.exp (m * C₀) * (S * Real.exp (m * R)) := by rw [Real.exp_add]; ring

/-- `x - y ≤ -a` from `a + x ≤ y` in `EReal`, for a real `x`; every combination of `⊥`, `⊤` in
`a`, `y` is covered. -/
theorem ereal_coe_add_neg_le_neg {a y : EReal} {x : ℝ} (h : a + (x : EReal) ≤ y) :
    (x : EReal) + -y ≤ -a := by
  induction y using EReal.rec with
  | bot =>
    have hbot : a + (x : EReal) = ⊥ := le_bot_iff.mp h
    rcases EReal.add_eq_bot_iff.mp hbot with ha | hx
    · simp [ha]
    · exact absurd hx (EReal.coe_ne_bot x)
  | top => simp
  | coe y' =>
    induction a using EReal.rec with
    | bot => simp
    | top => simp at h
    | coe a' =>
      have h' : a' + x ≤ y' := by exact_mod_cast h
      have h'' : x + -y' ≤ -a' := by linarith
      exact_mod_cast h''

/-- **The weight inequality of `lem:ideal-comparison`**: from `h + (C-1) φ ≤ C u` at a point,
`e^{ℓ(C-1)φ} e^{-Cℓ u} ≤ e^{-ℓ h}`.  Only `φ ≠ ⊤` is needed; where `ℓ(C-1)φ = ⊥` the left side
is `0`. -/
theorem exp_mul_multiplierWeight_le {A Φ U : EReal} {C ℓ : ℕ} (hΦ : Φ ≠ ⊤)
    (hle : A + ((((C - 1 : ℕ) : ℝ)) : EReal) * Φ ≤ ((C : ℝ) : EReal) * U) :
    EReal.exp ((((ℓ * (C - 1) : ℕ) : ℝ) : EReal) * Φ) * multiplierWeight ((C * ℓ : ℕ) : ℝ) U
      ≤ multiplierWeight (ℓ : ℝ) A := by
  set X : EReal := (((ℓ * (C - 1) : ℕ) : ℝ) : EReal) * Φ with hX
  by_cases hXbot : X = ⊥
  · rw [hXbot, EReal.exp_bot, zero_mul]; exact bot_le
  have hXtop : X ≠ ⊤ := ereal_coe_mul_ne_top (Nat.cast_nonneg _) hΦ
  obtain ⟨x, hx⟩ : ∃ x : ℝ, X = x := ⟨X.toReal, (EReal.coe_toReal hXtop hXbot).symm⟩
  have hℓ0 : (0 : EReal) ≤ ((ℓ : ℝ) : EReal) := EReal.coe_nonneg.mpr (Nat.cast_nonneg _)
  have hchain : ((ℓ : ℝ) : EReal) * A + X ≤ (((C * ℓ : ℕ) : ℝ) : EReal) * U := by
    have h1 := mul_le_mul_of_nonneg_left hle hℓ0
    rw [EReal.left_distrib_of_nonneg_of_ne_top hℓ0 (EReal.coe_ne_top _), ← mul_assoc,
      ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul] at h1
    have e1 : (ℓ : ℝ) * ((C - 1 : ℕ) : ℝ) = ((ℓ * (C - 1) : ℕ) : ℝ) := by push_cast; ring
    have e2 : (ℓ : ℝ) * (C : ℝ) = ((C * ℓ : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h1
    exact h1
  unfold multiplierWeight
  rw [← EReal.exp_add]
  refine EReal.exp_monotone ?_
  rw [hx] at hchain ⊢
  exact ereal_coe_add_neg_le_neg hchain

/-- **The pointwise estimate of `lem:ideal-comparison`**:
`|f b|² e^{-Cℓ u} ≤ K |f|² e^{-ℓ h}` at a point where `h + (C-1)φ ≤ C u`, `φ ≠ ⊤` and
`|b|² ≤ K e^{ℓ(C-1)φ}`. -/
theorem multiplierDensity_mul_le_of_bound {X : Type*} {u h φ : X → EReal} {C ℓ : ℕ}
    {f b : X → ℂ} {y : X} {K : ℝ} (hφ : φ y ≠ ⊤)
    (hle : h y + ((((C - 1 : ℕ) : ℝ)) : EReal) * φ y ≤ ((C : ℝ) : EReal) * u y)
    (hb : ENNReal.ofReal (‖b y‖ ^ 2) ≤
      ENNReal.ofReal K * EReal.exp ((((ℓ * (C - 1) : ℕ) : ℝ) : EReal) * φ y)) :
    multiplierDensity u ((C * ℓ : ℕ) : ℝ) (fun z => f z * b z) y
      ≤ ENNReal.ofReal K * multiplierDensity h ℓ f y := by
  have hw := exp_mul_multiplierWeight_le (ℓ := ℓ) hφ hle
  unfold multiplierDensity
  rw [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  calc ENNReal.ofReal (‖f y‖ ^ 2) * ENNReal.ofReal (‖b y‖ ^ 2) *
        multiplierWeight ((C * ℓ : ℕ) : ℝ) (u y)
      ≤ ENNReal.ofReal (‖f y‖ ^ 2) *
          (ENNReal.ofReal K * EReal.exp ((((ℓ * (C - 1) : ℕ) : ℝ) : EReal) * φ y)) *
          multiplierWeight ((C * ℓ : ℕ) : ℝ) (u y) := by gcongr
    _ = ENNReal.ofReal K * (ENNReal.ofReal (‖f y‖ ^ 2) *
          (EReal.exp ((((ℓ * (C - 1) : ℕ) : ℝ) : EReal) * φ y) *
            multiplierWeight ((C * ℓ : ℕ) : ℝ) (u y))) := by ring
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight (ℓ : ℝ) (h y)) := by
          gcongr

/-! ### Germs of `𝔅̄_m^p` are bounded by `e^{mpφ}` -/

section Manifold

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- A weight with analytic singularities of type `(m⁻¹, 𝔟)` never takes the value `⊤`. -/
theorem ne_top_of_hasAnalyticSingularitiesOfType {φ : Z → EReal} {c : ℚ} {𝔟 : GermIdeal k Z}
    (hφ : HasAnalyticSingularitiesOfType (n := k) φ c 𝔟) (y : Z) : φ y ≠ ⊤ := by
  obtain ⟨U, -, hyU, N, G, -, -, R, C₀, -, hpres⟩ := hφ.2.2 y
  rw [hpres y hyU]
  exact EReal.add_ne_top (ereal_coe_mul_ne_top (by exact_mod_cast hφ.1.le)
    (generatorLog_ne_top G y)) (EReal.coe_ne_top _)

/-- **`lem:trace-approximants`(iii) for a weight with analytic singularities**: if `φ` has type
`(m⁻¹, 𝔟)`, every germ `b` of `𝔟^p` is holomorphic and satisfies `|b|² ≤ K e^{mpφ}` near the
point. -/
theorem exists_eventually_ofReal_normSq_le_of_mem_idealPow {φ : Z → EReal} {m p : ℕ}
    (hm : 0 < m) {𝔟 : GermIdeal k Z}
    (hφ : HasAnalyticSingularitiesOfType (n := k) φ ((m : ℚ)⁻¹) 𝔟) {x : Z} {b : Z → ℂ}
    (hb : (idealPow 𝔟 p).mem x b) :
    HolomorphicAt k b x ∧ ∃ K : ℝ, ∀ᶠ y in 𝓝 x,
      ENNReal.ofReal (‖b y‖ ^ 2) ≤
        ENNReal.ofReal K * EReal.exp ((((m * p : ℕ) : ℝ) : EReal) * φ y) := by
  obtain ⟨-, -, hloc⟩ := hasAnalyticSingularitiesOfType_pow hφ p
  obtain ⟨U, hU, hxU, N, G, -, hmem, R, C₀, hR, hpres⟩ := hloc x
  obtain ⟨hbhol, Kn, s, c, hs, hc, heq⟩ := (hmem x hxU b).mp hb
  refine ⟨hbhol, ?_⟩
  set D : ℝ := ∑ i, (‖c i x‖ + 1) ^ 2 with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcb : ∀ᶠ y in 𝓝 x, ∀ i, ‖c i y‖ ≤ ‖c i x‖ + 1 := by
    refine eventually_all.mpr fun i => ?_
    have hcont : ContinuousAt (fun y => ‖c i y‖) x :=
      ((hc i).self_of_nhds.continuousAt).norm
    filter_upwards [hcont.eventually (Iio_mem_nhds (lt_add_one ‖c i x‖))] with y hy
    exact le_of_lt hy
  refine ⟨D * Kn * Real.exp (m * C₀), ?_⟩
  filter_upwards [hU.mem_nhds hxU, heq, hcb] with y hyU hyeq hyc
  have hsy : ∀ i, ∃ j, s i y = G j y := fun i => by
    obtain ⟨j, hj⟩ := hs i
    exact ⟨j, by rw [hj]⟩
  have h1 : ‖b y‖ ^ 2 ≤ ((∑ i, ‖c i y‖ ^ 2) * (Kn : ℝ)) * generatorNormSq G y :=
    norm_sq_le_of_eq_sum hsy hyeq
  have h2 : (∑ i, ‖c i y‖ ^ 2) ≤ D :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hyc i) 2
  have hS0 : 0 ≤ generatorNormSq G y := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : ‖b y‖ ^ 2 ≤ (D * Kn) * generatorNormSq G y :=
    h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)) hS0)
  have h4 := ofReal_generatorNormSq_le hm (hR y hyU) (hpres y hyU)
  have hmp : ((m : ℝ) : EReal) * (p • φ y) = (((m * p : ℕ) : ℝ) : EReal) * φ y := by
    rw [EReal.nsmul_eq_mul, ← mul_assoc, ← EReal.coe_natCast, ← EReal.coe_mul]
    push_cast; ring_nf
  rw [hmp] at h4
  have hDK : 0 ≤ D * Kn := mul_nonneg hD0 (Nat.cast_nonneg _)
  calc ENNReal.ofReal (‖b y‖ ^ 2) ≤ ENNReal.ofReal ((D * Kn) * generatorNormSq G y) :=
        ENNReal.ofReal_le_ofReal h3
    _ = ENNReal.ofReal (D * Kn) * ENNReal.ofReal (generatorNormSq G y) :=
        ENNReal.ofReal_mul hDK
    _ ≤ ENNReal.ofReal (D * Kn) * (ENNReal.ofReal (Real.exp (m * C₀)) *
          EReal.exp ((((m * p : ℕ) : ℝ) : EReal) * φ y)) := by gcongr
    _ = ENNReal.ofReal (D * Kn * Real.exp (m * C₀)) *
          EReal.exp ((((m * p : ℕ) : ℝ) : EReal) * φ y) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hDK]

/-! ### The inclusion -/

/-- **The generator step of `lem:ideal-comparison`**: a germ `f` of `𝓘(ℓ h)` times a germ `b` of
`𝔟^p` (`φ` of type `(m⁻¹, 𝔟)`, `mp = ℓ(C-1)`) is a germ of `𝓘(Cℓ u)`, provided
`h + (C-1)φ ≤ C u` almost everywhere in the preferred chart at the point. -/
theorem mem_multiplierIdeal_mul_of_mem_idealPow {u h φ : Z → EReal} {C ℓ m p : ℕ}
    (hC : 1 ≤ C) (hℓ : 0 < ℓ) (hm : 0 < m) (hmp : m * p = ℓ * (C - 1))
    (hu : ManifoldQuasiPlurisubharmonic (n := k) u) {𝔟 : GermIdeal k Z}
    (hφ : HasAnalyticSingularitiesOfType (n := k) φ ((m : ℚ)⁻¹) 𝔟) {x : Z}
    (hchain : ∀ᵐ z ∂(volume : Measure (ComplexModel k)),
      z ∈ (complexChartAt (n := k) x).val.target →
        h ((complexChartAt (n := k) x).val.symm z)
            + ((((C - 1 : ℕ) : ℝ)) : EReal) * φ ((complexChartAt (n := k) x).val.symm z)
          ≤ ((C : ℝ) : EReal) * u ((complexChartAt (n := k) x).val.symm z))
    {f b : Z → ℂ} (hf : (multiplierIdeal (n := k) (ℓ : ℝ) h).mem x f)
    (hb : (idealPow 𝔟 p).mem x b) :
    (multiplierIdeal (n := k) ((C * ℓ : ℕ) : ℝ) u).mem x (fun y => f y * b y) := by
  set e := (complexChartAt (n := k) x).val with he
  obtain ⟨hbhol, K, hK⟩ := exists_eventually_ofReal_normSq_le_of_mem_idealPow hm hφ hb
  rw [hmp] at hK
  obtain ⟨hfhol, -, U₀, hU₀, hxU₀, hfdiff, -, hfint⟩ := hf
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp (hK.and hbhol)
  have hz : e x ∈ e.target := e.map_source (mem_complexChartAt_source x)
  have hVopen : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hV
  have hzV : e x ∈ e.target ∩ e.symm ⁻¹' V := by
    refine ⟨hz, ?_⟩
    simpa [e.left_inv (mem_complexChartAt_source x)] using hxV
  set W := U₀ ∩ (e.target ∩ e.symm ⁻¹' V) with hWdef
  have hW : IsOpen W := hU₀.inter hVopen
  have hzW : e x ∈ W := ⟨hxU₀, hzV⟩
  have hWU₀ : W ⊆ U₀ := inter_subset_left
  have hWt : W ⊆ e.target := fun _ hy => hy.2.1
  have hpos : (0 : ℝ) < ((C * ℓ : ℕ) : ℝ) := by
    have : 0 < C * ℓ := Nat.mul_pos (by omega) hℓ
    exact_mod_cast this
  have hbdiff : DifferentiableOn ℂ (fun z => b (e.symm z)) (e.target ∩ e.symm ⁻¹' V) :=
    differentiableOn_comp_chartSymm x fun y hy => ((hVsub hy).2).mdifferentiableWithinAt
  have hdiff : DifferentiableOn ℂ (fun z => f (e.symm z) * b (e.symm z)) W :=
    (hfdiff.mono hWU₀).mul (hbdiff.mono inter_subset_right)
  refine ⟨hfhol.mul hbhol, hpos, W, hW, hzW, hdiff, ?_, ?_⟩
  · exact aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn hW
      ((hu (complexChartAt (n := k) x)).mono hWt) hpos.ne' hdiff.continuousOn
  · have hpoint : ∀ᵐ z ∂(volume : Measure (ComplexModel k)), z ∈ W →
        multiplierDensity (chartFunction u (complexChartAt (n := k) x)) ((C * ℓ : ℕ) : ℝ)
            (fun z => f (e.symm z) * b (e.symm z)) z
          ≤ ENNReal.ofReal K *
              multiplierDensity (chartFunction h (complexChartAt (n := k) x)) (ℓ : ℝ)
                (fun z => f (e.symm z)) z := by
      filter_upwards [hchain] with z hz' hzW'
      have hyV : e.symm z ∈ V := hzW'.2.2
      exact multiplierDensity_mul_le_of_bound (u := u) (h := h) (f := f) (b := b)
        (y := e.symm z) (ne_top_of_hasAnalyticSingularitiesOfType hφ _) (hz' (hWt hzW'))
        (hVsub hyV).1
    calc (∫⁻ z in W, multiplierDensity (chartFunction u (complexChartAt (n := k) x))
            ((C * ℓ : ℕ) : ℝ) (fun z => f (e.symm z) * b (e.symm z)) z)
        ≤ ∫⁻ z in W, ENNReal.ofReal K *
            multiplierDensity (chartFunction h (complexChartAt (n := k) x)) (ℓ : ℝ)
              (fun z => f (e.symm z)) z :=
          setLIntegral_mono_ae' hW.measurableSet hpoint
      _ = ENNReal.ofReal K * ∫⁻ z in W,
            multiplierDensity (chartFunction h (complexChartAt (n := k) x)) (ℓ : ℝ)
              (fun z => f (e.symm z)) z := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal K * ∫⁻ z in U₀,
            multiplierDensity (chartFunction h (complexChartAt (n := k) x)) (ℓ : ℝ)
              (fun z => f (e.symm z)) z := by
          gcongr
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfint

/-- **Copy-4 `lem:ideal-comparison`, first inclusion, chart form**: `𝔣 · 𝔟^p ⊆ 𝓘(Cℓ u)` when
`𝔣 ⊆ 𝓘(ℓ h)`, `φ` has type `(m⁻¹, 𝔟)`, `mp = ℓ(C-1)`, `u` is quasi-psh and `h + (C-1)φ ≤ C u`
holds almost everywhere in every preferred chart. -/
theorem mul_idealPow_le_multiplierIdeal_of_ae {u h φ : Z → EReal} {C ℓ m p : ℕ}
    (hC : 1 ≤ C) (hℓ : 0 < ℓ) (hm : 0 < m) (hmp : m * p = ℓ * (C - 1))
    (hu : ManifoldQuasiPlurisubharmonic (n := k) u)
    (hchain : ∀ x : Z, ∀ᵐ z ∂(volume : Measure (ComplexModel k)),
      z ∈ (complexChartAt (n := k) x).val.target →
        h ((complexChartAt (n := k) x).val.symm z)
            + ((((C - 1 : ℕ) : ℝ)) : EReal) * φ ((complexChartAt (n := k) x).val.symm z)
          ≤ ((C : ℝ) : EReal) * u ((complexChartAt (n := k) x).val.symm z))
    {𝔟 𝔣 : GermIdeal k Z}
    (hφ : HasAnalyticSingularitiesOfType (n := k) φ ((m : ℚ)⁻¹) 𝔟)
    (h𝔣 : 𝔣.Le (multiplierIdeal (n := k) (ℓ : ℝ) h)) :
    (𝔣.mul (idealPow 𝔟 p)).Le (multiplierIdeal (n := k) ((C * ℓ : ℕ) : ℝ) u) := by
  intro x g hg
  obtain ⟨hgHol, N, s, a, hs, ha, heq⟩ := hg
  have hpos : (0 : ℝ) < ((C * ℓ : ℕ) : ℝ) := by
    have : 0 < C * ℓ := Nat.mul_pos (by omega) hℓ
    exact_mod_cast this
  refine mem_multiplierIdeal_of_isInSpanAt hu hpos ⟨hgHol, N, s, a, fun i => ?_, ha, heq⟩
  obtain ⟨f, b, hf, hb, hsi⟩ := hs i
  rw [hsi]
  exact mem_multiplierIdeal_mul_of_mem_idealPow hC hℓ hm hmp hu hφ (hchain x) (h𝔣 x f hf) hb

/-- **Copy-4 `lem:ideal-comparison`, first inclusion** (TN23's target, I-0773 C-0003, with the
regularity `hu` of `u` that membership in `𝓘(Cℓ u)` needs): with `h + (C-1)φ ≤ C u`
everywhere. -/
theorem mul_idealPow_le_multiplierIdeal {u h φ : Z → EReal} {C ℓ m p : ℕ}
    (hC : 1 ≤ C) (hℓ : 0 < ℓ) (hm : 0 < m) (hmp : m * p = ℓ * (C - 1))
    (hu : ManifoldQuasiPlurisubharmonic (n := k) u)
    (hle : ∀ z, h z + ((((C - 1 : ℕ) : ℝ)) : EReal) * φ z ≤ ((C : ℝ) : EReal) * u z)
    {𝔟 𝔣 : GermIdeal k Z}
    (hφ : HasAnalyticSingularitiesOfType (n := k) φ ((m : ℚ)⁻¹) 𝔟)
    (h𝔣 : 𝔣.Le (multiplierIdeal (n := k) (ℓ : ℝ) h)) :
    (𝔣.mul (idealPow 𝔟 p)).Le (multiplierIdeal (n := k) ((C * ℓ : ℕ) : ℝ) u) :=
  mul_idealPow_le_multiplierIdeal_of_ae hC hℓ hm hmp hu
    (fun _ => Eventually.of_forall fun _ _ => hle _) hφ h𝔣

/-- **Copy-4 `lem:ideal-comparison`, first inclusion, in the manuscript's form**: with
`h + (C-1)φ ≤ C u` only quasi-everywhere (off a locally pluripolar set), as
`lem:positive-rooftop` delivers it. -/
theorem mul_idealPow_le_multiplierIdeal_of_quasiEverywhere {u h φ : Z → EReal} {C ℓ m p : ℕ}
    (hC : 1 ≤ C) (hℓ : 0 < ℓ) (hm : 0 < m) (hmp : m * p = ℓ * (C - 1))
    (hu : ManifoldQuasiPlurisubharmonic (n := k) u)
    (hle : QuasiEverywhere (n := k) fun z =>
      h z + ((((C - 1 : ℕ) : ℝ)) : EReal) * φ z ≤ ((C : ℝ) : EReal) * u z)
    {𝔟 𝔣 : GermIdeal k Z}
    (hφ : HasAnalyticSingularitiesOfType (n := k) φ ((m : ℚ)⁻¹) 𝔟)
    (h𝔣 : 𝔣.Le (multiplierIdeal (n := k) (ℓ : ℝ) h)) :
    (𝔣.mul (idealPow 𝔟 p)).Le (multiplierIdeal (n := k) ((C * ℓ : ℕ) : ℝ) u) := by
  refine mul_idealPow_le_multiplierIdeal_of_ae hC hℓ hm hmp hu (fun x => ?_) hφ h𝔣
  have hae := hle.ae_in_chart (complexChartAt (n := k) x) volume
  rw [ae_restrict_iff' (complexChartAt (n := k) x).val.open_target.measurableSet] at hae
  exact hae

end Manifold

end

end SGPT.Foundations.Analysis.Pending.PositiveCurrentIdealComparison

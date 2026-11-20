import SGPT.Bergman.Quant2SharpContactUpper
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound

/-!
# Decay of Bergman measures off the envelopes `V_{θ+εω}` (no positivity)

Blueprint `claude-k-big`, nodes `claude-k-big:decay` and `claude-k-big:cover`. Support for source
`thm:DXmain1` (Step 3, the compact Kähler case) and `cor:volbigL`.

Let `X` be a connected compact complex manifold with a Kähler background `ω`, `(L,h)`, `(T,h_T)`
Hermitian holomorphic line bundles with smooth metrics, `θ = c₁(L,h)`, and let `β^k` be the partial
Bergman measures of `def:Bergman:L778` with weight `v = 0` for an ARBITRARY `φ` (no positivity of
`L`). For `ε > 0` let `W_ε = V_{θ+εω}` be the supremum of the non-positive `(θ+εω)`-psh functions
(`thetaPshSupremum`, `≡ -∞` if there is none) and `G_{ε,δ} = {W_ε < -δ}`.

* `density_le_of_lt`: there are `C > 0`, `A > 0` with `B^k(x) ≤ C kⁿ e^{-kδ}` whenever
  `A ≤ kε` and `W_ε(x) < -δ` (Lelong–Poincaré for `k⁻¹ log|s|²`, the Bergman bound `B^k ≤ Ckⁿ`, and
  `k⁻¹ c₁(T) ≤ εω`);
* `measure_gap_le`, `tendsto_measure_gap`: `β^k(G_{ε,δ}) ≤ n! C e^{-kδ} ∫ωⁿ → 0` for `δ > 0`;
* `isOpen_gap`: `G_{ε,δ}` is open (`W_ε` is upper semicontinuous);
* `exists_potential_or_mem_gap`: every point either lies in some `G_{1/(i+1), 1/(m+1)}` or carries a
  `θ`-psh function `Q ≤ 0` with `Q(x) = 0` (the decreasing limit of the model potentials
  `V_{θ+ε_iω}`, `ε_i ↓ 0`, is `θ`-psh).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Bergman.KBig

open Bundle Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.ContactConcentration
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.BernsteinMarkov
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The envelope `W_ε = V_{θ+εω}` (`θ = c₁(L,h)`): the supremum of the non-positive
`(θ+εω)`-psh functions, `≡ -∞` if there is none. -/
abbrev gapEnvelope (omega : KahlerBackground n X) (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (ε : ℝ) : X → EReal :=
  thetaPshSupremum (sourceNativeFirstChernForm L hL + ε • omega.form).val

/-- The gap set `G_{ε,δ} = {W_ε < -δ}`. -/
def gapSet (omega : KahlerBackground n X) (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (ε δ : ℝ) : Set X :=
  {x | gapEnvelope omega L hL ε x < ((-δ : ℝ) : EReal)}

/-! ### Elementary `EReal` estimates -/

theorem ereal_log_sub_le_zero {k : ℝ} (hk : 0 < k) {r M : ℝ} (hr : 0 ≤ r) (hrM : r ≤ M) :
    ((k⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal r) - ((k⁻¹ * Real.log M : ℝ) : EReal) ≤ 0 := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    simp only [ENNReal.ofReal_zero, ENNReal.log_zero]
    rw [EReal.coe_mul_bot_of_pos (inv_pos.mpr hk), EReal.bot_sub]
    exact bot_le
  · rw [ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_zero,
      EReal.coe_le_coe_iff]
    have := Real.log_le_log hpos hrM
    have hk' : 0 < k⁻¹ := inv_pos.mpr hk
    nlinarith

theorem le_of_ereal_log_sub_lt {k : ℝ} (hk : 0 < k) {r M δ : ℝ} (hr : 0 ≤ r) (hM : 0 < M)
    (h : ((k⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal r) - ((k⁻¹ * Real.log M : ℝ) : EReal) <
      ((-δ : ℝ) : EReal)) :
    r ≤ M * Real.exp (-(k * δ)) := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    positivity
  · rw [ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at h
    have hlog : Real.log r < Real.log M - k * δ := by
      have h2 : k * (k⁻¹ * Real.log r - k⁻¹ * Real.log M) < k * (-δ) := mul_lt_mul_of_pos_left h hk
      have h3 : k * (k⁻¹ * Real.log r - k⁻¹ * Real.log M) = Real.log r - Real.log M := by
        field_simp
      linarith
    have := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_log hpos, Real.exp_sub, Real.exp_log hM] at this
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact this.le

/-! ### Comparison of backgrounds -/

/-- If `-c₁(T) + Aω ≥ 0` and `A ≤ kε`, every `(θ + k⁻¹c₁(T))`-psh function is `(θ+εω)`-psh. -/
theorem isThetaPshPotential_shift (omega : KahlerBackground n X) {θ θT : ClosedRealOneOneForm n X}
    {A ε : ℝ} (hA : (-θT + A • omega.form).val.IsSemipositive) {k : ℕ} (hk : 0 < k)
    (hAk : A ≤ k * ε) {u : X → EReal}
    (hu : IsThetaPshPotential (θ + (k : ℝ)⁻¹ • θT).val u) :
    IsThetaPshPotential (θ + ε • omega.form).val u := by
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsemi : ((k : ℝ)⁻¹ • ((k * ε - A) • omega.form + (-θT + A • omega.form))).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul
      (UniformPerturbedKahlerLowerBound.isSemipositive_add
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (by linarith)) hA)
      (inv_nonneg.mpr hkp.le)
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu hsemi
  have heq : θ + (k : ℝ)⁻¹ • θT + (k : ℝ)⁻¹ • ((k * ε - A) • omega.form + (-θT + A • omega.form)) =
      θ + ε • omega.form := by
    rw [smul_add, smul_add, smul_smul, smul_neg, smul_smul]
    have h1 : (k : ℝ)⁻¹ * (k * ε - A) + (k : ℝ)⁻¹ * A = ε := by field_simp; ring
    rw [show θ + (k : ℝ)⁻¹ • θT + (((k : ℝ)⁻¹ * (k * ε - A)) • omega.form +
        (-((k : ℝ)⁻¹ • θT) + ((k : ℝ)⁻¹ * A) • omega.form)) =
        θ + (((k : ℝ)⁻¹ * (k * ε - A)) + (k : ℝ)⁻¹ * A) • omega.form by module, h1]
  rwa [heq] at h

/-! ### The envelopes are upper semicontinuous; the gap sets are open -/

theorem upperSemicontinuous_thetaPshSupremum [CompactSpace X] [Nonempty X]
    (θ : ClosedRealOneOneForm n X) : UpperSemicontinuous (thetaPshSupremum θ.val) := by
  by_cases hne : ∃ u, IsThetaPshPotential θ.val u
  · exact (FirstPass.thetaPshSupremum_isThetaPshPotential θ.val θ.2.1 θ.2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) hne).1.quasiPlurisubharmonic.upperSemicontinuous
  · have hempty : thetaPshCompetitors θ.val = ∅ := by
      ext u
      simp only [mem_empty_iff_false, iff_false]
      exact fun hu => hne ⟨u, hu.1⟩
    rw [thetaPshSupremum_of_empty hempty]
    exact upperSemicontinuous_const

theorem isOpen_gap [CompactSpace X] [Nonempty X] (omega : KahlerBackground n X)
    (L : HermitianHolomorphicLineBundle n X) (hL : IsSourceSmoothHermitianMetric L) (ε δ : ℝ) :
    IsOpen (gapSet omega L hL ε δ) :=
  (upperSemicontinuous_thetaPshSupremum _).isOpen_preimage _

/-! ### The decay estimate -/

/-- The zero weight `v = 0` is smooth in charts. -/
theorem chartSmooth_zero : ChartSmooth (n := n) (0 : C(X, ℝ)) := fun _ => contDiffOn_const

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Decay of the Bergman kernel off `V_{θ+εω}`** (blueprint `claude-k-big:decay`): there are
`C > 0` and `A` such that for every `ε`, `δ`, every `k ≥ 1` with `A ≤ kε`, every `φ` and every point
`x` with `V_{θ+εω}(x) < -δ`, the partial Bergman kernel with weight `0` satisfies
`B^k_{0,φ}(x) ≤ C kⁿ e^{-kδ}`. -/
theorem exists_density_le_of_lt (omega : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) :
    ∃ C A : ℝ, 0 < C ∧ ∀ (ε δ : ℝ) (k : ℕ), 0 < k → A ≤ k * ε → ∀ (φ : X → EReal)
      (x : (wholeWeightedSubset (n := n) (0 : C(X, ℝ))).carrier),
      x.val ∈ gapSet omega L hL ε δ →
      sourcePartialBergmanDensity L T (wholeWeightedSubset (0 : C(X, ℝ)))
          ((kahlerVolume omega).comap
            (Subtype.val : (wholeWeightedSubset (n := n) (0 : C(X, ℝ))).carrier → X)) k φ x ≤
        ENNReal.ofReal (C * (k : ℝ) ^ n * Real.exp (-(k * δ))) := by
  obtain ⟨C, hC, hb⟩ := exists_global_weighted_polynomial_section_bound L T hL hT 0
    chartSmooth_zero (kahlerVolume omega)
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
  obtain ⟨A, -, hA⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omega (-sourceNativeFirstChernForm T hT)
  refine ⟨C, A, hC, fun ε δ k hk hAk φ x hx => ?_⟩
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  unfold sourcePartialBergmanDensity
  refine iSup₂_le fun s hs => ?_
  set f : twistedSections L T k := (literalTwistedMultiplierSectionEquiv L T k φ s).val with hfdef
  change weightedSectionDensity (twistedPower L T k).Fiber k (univRealWeight 0) f x ≤ _
  rw [weightedSectionDensity_univ L T 0 k f x]
  have hdens (y : X) : realWeightedSectionDensity L T 0 k f y = ‖f y‖ ^ 2 := by
    simp [realWeightedSectionDensity]
  rw [hdens]
  apply ENNReal.ofReal_le_ofReal
  have hI := integral_realWeightedSectionDensity_le_one_of_admissible L T 0 (kahlerVolume omega) k
    f hs
  set M : ℝ := C * (k : ℝ) ^ n with hMdef
  have hM : 0 < M := by positivity
  have hglob (y : X) : ‖f y‖ ^ 2 ≤ M := by
    have h1 := (hb k hk f y).trans (by simpa only [mul_one] using mul_le_mul' le_rfl hI)
    rw [hdens] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hM.le).mp h1
  by_cases hf : f = 0
  · have : f x.val = 0 := by rw [hf]; rfl
    rw [this, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  have hpsh := isThetaPshPotential_shift omega hA hk hAk
    (sourceNormalizedTwistedSectionLogNormSq_isThetaPsh L T hL hT k hk f hf)
  have hu := hpsh.sub_const ((k : ℝ)⁻¹ * Real.log M)
  have hu0 : (fun y => ((k : ℝ)⁻¹ : EReal) * sourceSectionLogNormSq (twistedPower L T k) f y -
      (((k : ℝ)⁻¹ * Real.log M : ℝ) : EReal)) ≤ 0 := fun y =>
    ereal_log_sub_le_zero hkpos (sq_nonneg _) (hglob y)
  have hle := le_thetaPshSupremum hu hu0 x.val
  exact le_of_ereal_log_sub_lt hkpos (sq_nonneg _) hM (hle.trans_lt hx)

/-- **The Bergman measures of the gap sets** (blueprint `claude-k-big:decay`):
`β^k(G_{ε,δ}) ≤ n! C e^{-kδ} ∫ωⁿ` whenever `A ≤ kε`, for every `φ`. -/
theorem exists_measure_gap_le (omega : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) :
    ∃ C A : ℝ, 0 < C ∧ ∀ (ε δ : ℝ) (k : ℕ) (hk : 0 < k), A ≤ k * ε → ∀ φ : X → EReal,
      (sourceBergmanFiniteMeasure omega L T hL hT 0 chartSmooth_zero k hk φ : Measure X)
          (gapSet omega L hL ε δ) ≤
        ENNReal.ofReal ((n.factorial : ℝ) * C * Real.exp (-(k * δ))) * kahlerVolume omega univ := by
  obtain ⟨C, A, hC, hdens⟩ := exists_density_le_of_lt omega L T hL hT
  refine ⟨C, A, hC, fun ε δ k hk hAk φ => ?_⟩
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hG : MeasurableSet (gapSet omega L hL ε δ) := (isOpen_gap omega L hL ε δ).measurableSet
  let W := wholeWeightedSubset (n := n) (0 : C(X, ℝ))
  let μK := (kahlerVolume omega).comap (Subtype.val : W.carrier → X)
  have hGK : MeasurableSet ((Subtype.val : W.carrier → X) ⁻¹' gapSet omega L hL ε δ) :=
    measurable_subtype_coe hG
  have hμK : μK univ = kahlerVolume omega univ := by
    have h := (MeasurableEmbedding.subtype_coe
      (MeasurableSet.univ : MeasurableSet (univ : Set X))).comap_apply (kahlerVolume omega) univ
    rw [image_univ, Subtype.range_coe] at h
    exact h
  rw [sourceBergmanFiniteMeasure_toMeasure, sourcePartialBergmanMeasure,
    Measure.map_apply measurable_subtype_coe hG, sourcePartialBergmanMeasureOnK, Measure.smul_apply,
    smul_eq_mul, withDensity_apply _ hGK]
  calc sourceBergmanNormalization (n := n) k *
        ∫⁻ y in (Subtype.val : W.carrier → X) ⁻¹' gapSet omega L hL ε δ,
          sourcePartialBergmanDensity L T W μK k φ y ∂μK
      ≤ sourceBergmanNormalization (n := n) k *
        ∫⁻ _ in (Subtype.val : W.carrier → X) ⁻¹' gapSet omega L hL ε δ,
          ENNReal.ofReal (C * (k : ℝ) ^ n * Real.exp (-(k * δ))) ∂μK := by
        exact mul_le_mul_right
          (setLIntegral_mono measurable_const fun y hy => hdens ε δ k hk hAk φ y hy) _
    _ = sourceBergmanNormalization (n := n) k *
        (ENNReal.ofReal (C * (k : ℝ) ^ n * Real.exp (-(k * δ))) *
          μK ((Subtype.val : W.carrier → X) ⁻¹' gapSet omega L hL ε δ)) := by
        rw [setLIntegral_const]
    _ ≤ sourceBergmanNormalization (n := n) k *
        (ENNReal.ofReal (C * (k : ℝ) ^ n * Real.exp (-(k * δ))) * μK univ) := by
        gcongr
        exact subset_univ _
    _ = _ := by
        rw [hμK, ← mul_assoc, sourceBergmanNormalization, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- **The Bergman measures of a gap set tend to zero** (blueprint `claude-k-big:decay`): for
`ε, δ > 0` and every `φ`, `β^k(G_{ε,δ}) → 0`. -/
theorem tendsto_measure_gap (omega : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T) (φ : X → EReal)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Tendsto (fun j : ℕ => (sourceBergmanFiniteMeasure omega L T hL hT 0 chartSmooth_zero (j + 1)
      (Nat.succ_pos j) φ : Measure X) (gapSet omega L hL ε δ)) atTop (𝓝 0) := by
  obtain ⟨C, A, hC, hbound⟩ := exists_measure_gap_le omega L T hL hT
  have hk : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hexp : Tendsto (fun j : ℕ => ENNReal.ofReal ((n.factorial : ℝ) * C *
      Real.exp (-(((j + 1 : ℕ) : ℝ) * δ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => Real.exp (-(((j + 1 : ℕ) : ℝ) * δ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hk.atTop_mul_const hδ)
    have h2 := (h1.const_mul ((n.factorial : ℝ) * C))
    rw [mul_zero] at h2
    have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp h2
    rwa [ENNReal.ofReal_zero] at h3
  have hlim := ENNReal.Tendsto.mul_const hexp (Or.inr (measure_ne_top (kahlerVolume omega) univ))
  rw [zero_mul] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [(hk.atTop_mul_const hε).eventually_ge_atTop A] with j hj
  exact hbound ε δ (j + 1) (Nat.succ_pos j) hj φ

/-! ### Covering the non-contact set -/

/-- **Covering lemma** (blueprint `claude-k-big:cover`): for every `x`, either `x` lies in some
gap set `G_{1/(i+1), 1/(m+1)}`, or there is a `θ`-psh function `Q ≤ 0` with `Q(x) = 0`
(the decreasing limit of the model potentials `V_{θ+ε_iω}`, `ε_i = 1/(i+1)`). -/
theorem exists_potential_or_mem_gap (omega : KahlerBackground n X)
    (L : HermitianHolomorphicLineBundle n X) (hL : IsSourceSmoothHermitianMetric L) (x : X) :
    (∃ i m : ℕ, x ∈ gapSet omega L hL ((i : ℝ) + 1)⁻¹ ((m : ℝ) + 1)⁻¹) ∨
      ∃ Q : X → EReal, IsThetaPshPotential (sourceNativeFirstChernForm L hL).val Q ∧ Q ≤ 0 ∧
        Q x = 0 := by
  by_cases h : ∃ i m : ℕ, x ∈ gapSet omega L hL ((i : ℝ) + 1)⁻¹ ((m : ℝ) + 1)⁻¹
  · exact Or.inl h
  right
  push Not at h
  set θ := sourceNativeFirstChernForm L hL with hθ
  set ε : ℕ → ℝ := fun i => ((i : ℝ) + 1)⁻¹ with hεdef
  set W : ℕ → X → EReal := fun i => thetaPshSupremum (θ + ε i • omega.form).val with hWdef
  have hWx : ∀ i, W i x = 0 := by
    intro i
    refine le_antisymm (thetaPshSupremum_le_zero _ x) ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    have hq : q < 0 := EReal.coe_lt_coe_iff.mp (by simpa using hq2)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (neg_pos.mpr hq)
    apply h i m
    change W i x < _
    refine hq1.trans (EReal.coe_lt_coe_iff.mpr ?_)
    rw [one_div] at hm
    linarith
  have hWpsh : ∀ i, IsThetaPshPotential (θ + ε i • omega.form).val (W i) := by
    intro i
    refine FirstPass.thetaPshSupremum_isThetaPshPotential _ (θ + ε i • omega.form).2.1
      (θ + ε i • omega.form).2.2 (LocalPotentials.closedRealOneOne_hasLocalPotentials _) ?_
    by_contra hne
    have hempty : thetaPshCompetitors (θ + ε i • omega.form).val = ∅ := by
      ext u
      simp only [mem_empty_iff_false, iff_false]
      exact fun hu => hne ⟨u, hu.1⟩
    have h0 := hWx i
    simp only [hWdef, thetaPshSupremum_of_empty hempty] at h0
    exact (EReal.bot_lt_zero.ne) h0
  have hεanti : Antitone ε := fun i j hij => by
    simp only [hεdef]
    gcongr
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [hεdef, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hWanti : ∀ y, Antitone fun j => W j y := fun y i j hij => by
    have hsemi : ((ε i - ε j) • omega.form).val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr (hεanti hij))
    have := RestrictedApproximantMass.thetaPshSupremum_le_add (θ := θ + ε j • omega.form) hsemi y
    simp only [hWdef]
    rwa [show θ + ε j • omega.form + (ε i - ε j) • omega.form = θ + ε i • omega.form by module]
      at this
  refine ⟨TraceFreeLimit.traceFreeLimit θ omega.form ε W,
    TraceFreeLimit.isThetaPshPotential_traceFreeLimit omega hεanti hεlim hWpsh hWanti,
    fun y => (TraceFreeLimit.traceFreeLimit_le θ omega.form ε W 0 y).trans
      (singularityEnvelope_le_zero _ _ y), ?_⟩
  refine le_antisymm ((TraceFreeLimit.traceFreeLimit_le θ omega.form ε W 0 x).trans
    (singularityEnvelope_le_zero _ _ x)) ?_
  simp only [TraceFreeLimit.traceFreeLimit]
  refine le_iInf fun j => ?_
  rw [← hWx j]
  exact self_le_singularityEnvelope (hWpsh j) (thetaPshSupremum_le_zero _) x

end SGPT.Bergman.KBig

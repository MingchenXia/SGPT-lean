import SGPT.IGood.DXLow2Shift
import SGPT.IGood.DXLow2Final
import SGPT.Bergman.Quant3PBMConvergence
import SGPT.Foundations.Analysis.Pending.AmbientConvexCurrent

/-!
# The upper bound of the asymptotic Riemann–Roch formula for potentials of positive mass

Blueprint `claude-dx-low2`, nodes `claude-dx-low2:upper-count` and `claude-dx-low2:upper`. Source
`thm:DXmain1` (chapter *`𝓘`-good singularities*), Step 2 of the book's proof, the inequality
`limsup ≤ vol`: for `φ ∈ PSH(X, θ)_{>0}`, `θ = c₁(L, h)`, and every twist `T`,

`limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ vol θ_φ`

(`riemannRochUpperBound_of_pos`; its type is `SGPT.Bergman.Quant3.RiemannRochUpperBound`).

## Route (no ample line bundle)

The book perturbs `L` by a very ample line bundle `A` (`L` is big, so `X` is projective) and uses
Step 1 for `L^N ⊗ A`. In the analytic setting of the Bergman chapter we replace `A` by `L` itself
with a singular metric: since `φ` has positive mass there is a Kähler current `θ + dd^c ψ₀ ≥ κ/4`
with gentle analytic singularities (`lma:kahcurrentposmass`, `thm:qequi`). Fix `N ≥ 1`, put
`Φ = (N+1)⁻¹ ψ₀ + (1 - (N+1)⁻¹) φ` (a Kähler current) and write `k = k'N + r`, `0 ≤ r < N`. Then

* `𝓘(kφ) ⊆ 𝓘(k'N φ)`;
* multiplication by a non-zero `s ∈ H⁰(X, L^{k'})` with `|s|² ≲ e^{k'ψ₀}` (`s ∈ 𝓘(k' c ψ₀) ⊆
  𝓘_∞(k'ψ₀)`, `lma:IandIinf`) maps `H⁰(L^k ⊗ T ⊗ 𝓘(k'Nφ))` injectively into
  `H⁰(L^{k+k'} ⊗ T ⊗ 𝓘(k'(N+1)Φ))`, as `k'(N+1)Φ = k'ψ₀ + k'Nφ`;
* `L^{k+k'} ⊗ T = L^{k'(N+1)} ⊗ (L^r ⊗ T)` (`finrank_full_le_shift`);

so `n!/kⁿ h⁰(L^k ⊗ T ⊗ 𝓘(kφ)) ≤ ((N+1)/N)ⁿ · n!/mⁿ h⁰(L^m ⊗ T_r ⊗ 𝓘(mΦ))`, `m = k'(N+1)`,
`T_r = L^r ⊗ T`. The upper bound for the Kähler current `Φ` (BERGMAN3's
`limsup_normalizedH0_le_iVolume_of_kahlerCurrent`, for each of the finitely many twists `T_r`)
gives `limsup ≤ ((N+1)/N)ⁿ vol θ_Φ`, and `vol θ_Φ → vol θ_φ` as `N → ∞` (`cor:lineardsconv`,
`thm:contvolu`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.DXLow2

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
  SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
  SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.PSH.GlobalL2
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The `c`-multiple of a potential of a Kähler current `θ + dd^c u ≥ κ/4`, `c = (N₂+2)/(N₂+1)`,
`θ ≤ Aκ`, `N₂ > 4A`, is again a Kähler current: `θ + dd^c (cu) ≥ δ' κ`. -/
theorem isThetaPshPotential_scaled_sub {θ : ClosedRealOneOneForm n X} {κ : KahlerBackground n X}
    {u : X → EReal} (hu : IsThetaPshPotential (θ - (1 / 4 : ℝ) • κ.form).val u) {A : ℝ}
    (hA : (-θ + A • κ.form).val.IsSemipositive) {N₂ : ℕ} (hN : 4 * A < N₂) :
    0 < ((scaleFactor N₂ : ℚ) : ℝ) / 4 - (((scaleFactor N₂ : ℚ) : ℝ) - 1) * A ∧
      IsThetaPshPotential (θ - (((scaleFactor N₂ : ℚ) : ℝ) / 4 -
        (((scaleFactor N₂ : ℚ) : ℝ) - 1) * A) • κ.form).val (scaled (scaleFactor N₂) u) := by
  set c : ℝ := ((scaleFactor N₂ : ℚ) : ℝ) with hcdef
  have hc1 : 1 < c := one_lt_scaleFactor N₂
  have hcR : c = ((N₂ : ℝ) + 2) / ((N₂ : ℝ) + 1) := scaleFactor_real N₂
  have hN0 : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have hN1 : (0 : ℝ) < N₂ + 1 := by positivity
    have : c - 1 = 1 / ((N₂ : ℝ) + 1) := by rw [hcR]; field_simp; ring
    rw [this, hcR]
    rw [show ((N₂ : ℝ) + 2) / ((N₂ : ℝ) + 1) / 4 - 1 / ((N₂ : ℝ) + 1) * A =
      ((N₂ : ℝ) + 2 - 4 * A) / (4 * ((N₂ : ℝ) + 1)) by field_simp]
    apply div_pos <;> linarith
  · have hwc : IsThetaPshPotential (c • (θ - (1 / 4 : ℝ) • κ.form)).val (scaled c u) :=
      RestrictedApproximantComparison.isThetaPshPotential_smul hu (by linarith)
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hwc ?_
    have heq : θ - (c / 4 - (c - 1) * A) • κ.form - c • (θ - (1 / 4 : ℝ) • κ.form) =
        (c - 1) • (-θ + A • κ.form) := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul hA (by linarith)

/-- **Multiplication by a bounded section**: if `0 ≠ s ∈ H⁰(X, L^{p+1})` with
`|s|² e^{-(p+1)ψ} ≤ C` and `(p+1) ψ + a φ ≤ m Φ + D`, then
`h⁰(X, L^k ⊗ T ⊗ 𝓘(aφ)) ≤ h⁰(X, L^{k+p+1} ⊗ T ⊗ 𝓘(mΦ))`. -/
theorem finrank_le_of_mul_bounded {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {p k a m : ℕ} {ψ φ Φ : X → EReal} {D C : ℝ}
    (hψ : ∀ x, ψ x ≠ ⊤) (hφq : IsGlobalQuasiPshPotential (n := n) φ)
    (hΦq : IsGlobalQuasiPshPotential (n := n) Φ)
    (hineq : ∀ x, (((p + 1 : ℕ) : ℝ) : EReal) * ψ x + ((a : ℝ) : EReal) * φ x ≤
      ((m : ℝ) : EReal) * Φ x + (D : EReal))
    {s : twistedSections L unit (p + 1)} (hs0 : s ≠ 0)
    (hC : ∀ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight ((p + 1 : ℕ) : ℝ) (ψ y) ≤
      ENNReal.ofReal C) :
    Module.finrank ℂ (fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) a φ)) ≤
      Module.finrank ℂ (fullHolomorphicIdealSections (n := n) (twistedPower L T (k + p + 1)).Fiber
        (sourceDegreeMultiplierIdeal (n := n) m Φ)) := by
  have hmaps : ∀ t ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) a φ),
      mulSectionLinear s k t ∈ fullHolomorphicIdealSections (n := n)
        (twistedPower L T (k + p + 1)).Fiber (sourceDegreeMultiplierIdeal (n := n) m Φ) := by
    intro t ht
    rw [fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) _ _ hφq _ hμ] at ht
    exact (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) _ _ hΦq _ hμ).mpr
      (lintegral_mulSection_lt_top' hψ (fun x => hφq.1.ne_top x) hineq hC ht)
  let F := (mulSectionLinear (T := T) s k).restrict hmaps
  have hF : Function.Injective F := by
    intro t₁ t₂ h
    exact Subtype.ext (mulSectionLinear_injective hs0 k (congrArg Subtype.val h))
  let := fullTwistedMultiplierSections_finiteDimensional L T (k + p + 1) Φ
  have : FiniteDimensional ℂ (fullHolomorphicIdealSections (n := n)
      (twistedPower L T (k + p + 1)).Fiber (sourceDegreeMultiplierIdeal (n := n) m Φ)) := by
    let := twistedSections_finiteDimensional L T (k + p + 1)
    infer_instance
  exact LinearMap.finrank_le_finrank_of_injective hF

/-- The elementary inequality `n!/kⁿ h ≤ ((N+1)/N)ⁿ · n!/mⁿ h'` for `h ≤ h'`, `mN ≤ (N+1)k`. -/
theorem ofReal_le_ratio_mul {m k h H N : ℕ} (hm : 0 < m) (hk : 0 < k) (hN : 0 < N)
    (hmk : m * N ≤ (N + 1) * k) (hhH : h ≤ H) :
    ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n * h) ≤
      ENNReal.ofReal ((((N : ℝ) + 1) / N) ^ n) *
        ENNReal.ofReal ((n.factorial : ℝ) / (m : ℝ) ^ n * H) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmk' : (m : ℝ) * N ≤ ((N : ℝ) + 1) * k := by exact_mod_cast hmk
  have hhH' : (h : ℝ) ≤ H := by exact_mod_cast hhH
  have hratio : 1 / (k : ℝ) ≤ ((N : ℝ) + 1) / (N * m) := by
    rw [div_le_div_iff₀ hk' (by positivity)]
    linarith
  have hpow : (1 / (k : ℝ)) ^ n ≤ (((N : ℝ) + 1) / (N * m)) ^ n :=
    pow_le_pow_left₀ (by positivity) hratio n
  have e1 : (n.factorial : ℝ) / (k : ℝ) ^ n * h = (n.factorial : ℝ) * h * (1 / (k : ℝ)) ^ n := by
    rw [div_pow, one_pow]; field_simp
  have e2 : (((N : ℝ) + 1) / N) ^ n * ((n.factorial : ℝ) / (m : ℝ) ^ n * H) =
      (n.factorial : ℝ) * H * (((N : ℝ) + 1) / (N * m)) ^ n := by
    rw [div_pow, div_pow, mul_pow]; field_simp
  rw [e1, e2]
  have hf : (0 : ℝ) ≤ n.factorial := by positivity
  calc (n.factorial : ℝ) * h * (1 / (k : ℝ)) ^ n
      ≤ (n.factorial : ℝ) * H * (1 / (k : ℝ)) ^ n := by gcongr
    _ ≤ (n.factorial : ℝ) * H * (((N : ℝ) + 1) / (N * m)) ^ n := by gcongr

/-- The potential `Φ = (N+1)⁻¹ ψ + (1 - (N+1)⁻¹) φ`. -/
abbrev upperMix (N : ℕ) (ψ φ : X → EReal) : X → EReal := convexComb ((N : ℝ) + 1)⁻¹ ψ φ

/-- `k'(N+1) Φ = k' ψ + k'N φ`. -/
theorem upperMix_mul (N k' : ℕ) (ψ φ : X → EReal) (x : X) :
    (((k' * (N + 1) : ℕ) : ℝ) : EReal) * upperMix N ψ φ x =
      (((k' : ℕ) : ℝ) : EReal) * ψ x + (((k' * N : ℕ) : ℝ) : EReal) * φ x := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [upperMix, convexComb_apply, EReal.left_distrib_of_nonneg_of_ne_top
    (by exact_mod_cast (Nat.cast_nonneg _)) (EReal.coe_ne_top _), ← mul_assoc, ← mul_assoc,
    ← EReal.coe_mul, ← EReal.coe_mul]
  congr 3
  · push_cast; field_simp
  · push_cast; field_simp; ring

theorem tendsto_div_atTop {N : ℕ} (hN : 0 < N) : Tendsto (fun k : ℕ => k / N) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun B => ⟨B * N, fun k hk => ?_⟩
  rwa [Nat.le_div_iff_mul_le hN]

/-- **The counting step of the upper bound** (blueprint `claude-dx-low2:upper-count`): for
`k = k'N + r` large,
`n!/kⁿ h⁰(L^k ⊗ T ⊗ 𝓘(kφ)) ≤ ((N+1)/N)ⁿ · n!/mⁿ h⁰(L^m ⊗ (L^r ⊗ T) ⊗ 𝓘(mΦ))`,
`m = k'(N+1)`, `Φ = (N+1)⁻¹ ψ₀ + (1 - (N+1)⁻¹) φ`. -/
theorem eventually_normalizedH0_le_upperMix
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L)
    (κ : KahlerBackground n X) {ψ₀ φ : X → EReal}
    (hψ₀ : IsThetaPshPotential (sourceNativeFirstChernForm L hL - (1 / 4 : ℝ) • κ.form).val ψ₀)
    (hgent : ∃ (c : ℚ) (𝔞 : GermIdeal n X),
      ActualOriginalSquaredDensityGentle.HasGentleAnalyticSingularitiesOfType (n := n) ψ₀ c 𝔞)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    {A : ℝ} (hA : (-sourceNativeFirstChernForm L hL + A • κ.form).val.IsSemipositive)
    {N₀ : ℕ} (hN₀ : 4 * A < N₀) {N : ℕ} (hN : 0 < N) :
    ∀ᶠ k in atTop, normalizedH0 L T φ k ≤ ENNReal.ofReal ((((N : ℝ) + 1) / N) ^ n) *
      normalizedH0 L (twistedPower L T (k % N)) (upperMix N ψ₀ φ) (k / N * (N + 1)) := by
  set θ := sourceNativeFirstChernForm L hL with hθdef
  set θ' := chernForm L hL with hθ'def
  have hrt : atlasClosedFormToNative θ' = θ := sourceNativeAtlasForm_roundTrip θ
  have toNative : ∀ {u : X → EReal}, (ofFixedModel n X).IsThetaPSH θ' u →
      IsThetaPshPotential θ.val u := fun h => by
    have := (isThetaPSH_iff_nativeThetaPotential θ' _).mp h
    rwa [hrt] at this
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume κ
  -- the scaled potential `w₀ = c' ψ₀` is a Kähler current
  set c' : ℝ := ((scaleFactor N₀ : ℚ) : ℝ) with hc'def
  have hc'1 : 1 < c' := one_lt_scaleFactor N₀
  obtain ⟨hδ', hw₀δ⟩ := isThetaPshPotential_scaled_sub hψ₀ hA hN₀
  have hw₀cur : IsKahlerCurrentPotential θ (scaled c' ψ₀) :=
    ⟨KahlerBackground.smul hδ' κ, by rw [KahlerBackground.smul_form]; exact hw₀δ⟩
  have hw₀θ : IsThetaPshPotential θ.val (scaled c' ψ₀) :=
    SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hw₀δ (by
      rw [show θ - (θ - (c' / 4 - (c' - 1) * A) • κ.form) = (c' / 4 - (c' - 1) * A) • κ.form by
        abel]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive hδ'.le)
  have hw₀q : IsGlobalQuasiPshPotential (n := n) (fun x => (c' : EReal) * ψ₀ x) :=
    hw₀θ.quasiPshPotential
  obtain ⟨b₀, hb₀⟩ := exists_ne_zero_twistedMultiplierSections hL isSourceSmoothHermitianMetric_unit
    hw₀cur
  -- `lma:IandIinf` for `ψ₀`
  obtain ⟨cg, 𝔞, hg⟩ := hgent
  have hψan : (ofFixedModel n X).HasRationalAnalyticChartType ψ₀ :=
    hg.2.1.hasManifoldAnalyticSingularityType
  obtain ⟨s₀, -, hIinf⟩ := SGPT.PSH.MultiplierIdealInf.exists_multiplierIdeal_le_inftyIdeal hψan
    (show (0 : ℝ) < c' - 1 by linarith)
  have hψtop : ∀ x, ψ₀ x ≠ ⊤ := fun x => hg.1.1.ne_top x
  -- `φ ≤ M`
  have hφq : IsGlobalQuasiPshPotential (n := n) φ := (toNative hφ).quasiPshPotential
  obtain ⟨M, -, hφM⟩ := exists_nonneg_upper_bound hφq
  -- the Kähler current `Φ`
  have ht0 : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ := by positivity
  have ht1 : ((N : ℝ) + 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith)
  have hφ0 : IsThetaPshPotential (θ - (0 : ℝ) • κ.form).val φ := by
    rw [zero_smul, sub_zero]; exact toNative hφ
  have hΦ := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul κ ht0 ht1 hψ₀ hφ0
  have hΦθ : IsThetaPshPotential θ.val (upperMix N ψ₀ φ) :=
    SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hΦ (by
      rw [show θ - (θ - (((N : ℝ) + 1)⁻¹ * (1 / 4) + (1 - ((N : ℝ) + 1)⁻¹) * 0) • κ.form) =
        (((N : ℝ) + 1)⁻¹ * (1 / 4) + (1 - ((N : ℝ) + 1)⁻¹) * 0) • κ.form by abel]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by positivity))
  have hΦq : IsGlobalQuasiPshPotential (n := n) (upperMix N ψ₀ φ) := hΦθ.quasiPshPotential
  -- the eventual conditions on `k`
  have hdiv := tendsto_div_atTop hN
  have h1 : ∀ᶠ k in atTop, b₀ + 1 ≤ k / N := hdiv.eventually_ge_atTop _
  have h2 : ∀ᶠ k in atTop, s₀ ≤ ((k / N : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hdiv).eventually_ge_atTop s₀
  filter_upwards [h1, h2] with k hk1 hk2
  obtain ⟨p, hp⟩ : ∃ p, k / N = p + 1 := ⟨k / N - 1, by omega⟩
  set r := k % N with hrdef
  have hkdecomp : N * (p + 1) + r = k := by rw [← hp]; exact Nat.div_add_mod k N
  set m := (p + 1) * (N + 1) with hmdef
  obtain ⟨p', hp'⟩ : ∃ p', m = p' + 1 := ⟨m - 1, by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.zero_div] at hp; omega
    · exact h
  -- (1) `𝓘(kφ) ⊆ 𝓘(k'N φ)`
  have hstep1 : Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) ≤
      Module.finrank ℂ (fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) ((p + 1) * N) φ)) := by
    rw [(literalTwistedMultiplierSectionEquiv L T k φ).finrank_eq]
    have hle : fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k φ) ≤
        fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
          (sourceDegreeMultiplierIdeal (n := n) ((p + 1) * N) φ) := fun t ht =>
      mem_full_of_le_degree hμ _ hφq hφM (by rw [← hkdecomp]; nlinarith) ht
    have : FiniteDimensional ℂ (fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) ((p + 1) * N) φ)) := by
      let := twistedSections_finiteDimensional L T k
      infer_instance
    exact Submodule.finrank_mono hle
  -- (2) a non-zero bounded section `s ∈ H⁰(X, L^{p+1})`
  have hsec := hb₀ (p + 1) (by omega)
  let := literalTwistedMultiplierSections_finiteDimensional L (unit (n := n) (M := X)) (p + 1)
    (scaled c' ψ₀)
  obtain ⟨s', hs'⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hsec
  set s := (literalTwistedMultiplierSectionEquiv L unit (p + 1) (scaled c' ψ₀) s').val with hsdef
  have hsmem := (literalTwistedMultiplierSectionEquiv L unit (p + 1) (scaled c' ψ₀) s').property
  have hs0 : s ≠ 0 := by
    intro h0
    apply hs'
    apply (literalTwistedMultiplierSectionEquiv L unit (p + 1) (scaled c' ψ₀)).injective
    rw [map_zero]
    exact Subtype.ext h0
  have hle : (multiplierIdeal (n := n) 1
      (fun x => ((((p + 1 : ℕ) : ℝ) * c' : ℝ) : EReal) * ψ₀ x)).Le
      (SGPT.PSH.inftyIdeal (n := n) (fun x => (((p + 1 : ℕ) : ℝ) : EReal) * ψ₀ x)) := by
    have := hIinf ((p + 1 : ℕ) : ℝ) (by rw [← hp]; exact hk2)
    rwa [add_sub_cancel] at this
  obtain ⟨C, hC⟩ := exists_bound_of_mem_of_le_inftyIdeal (twistedPower L unit (p + 1)).Fiber hw₀q
    hle s hsmem
  -- (3) multiplication by `s`
  have hineq : ∀ x, (((p + 1 : ℕ) : ℝ) : EReal) * ψ₀ x + ((((p + 1) * N : ℕ) : ℝ) : EReal) * φ x ≤
      ((m : ℝ) : EReal) * upperMix N ψ₀ φ x + ((0 : ℝ) : EReal) := by
    intro x
    rw [EReal.coe_zero, add_zero, hmdef, upperMix_mul]
  have hstep3 := finrank_le_of_mul_bounded hμ (L := L) (T := T) (k := k) hψtop hφq hΦq hineq hs0 hC
  -- (4) moving `L^r` into the twist
  have hidx : k + p + 1 = r + p' + 1 := by
    calc k + p + 1 = N * (p + 1) + r + (p + 1) := by rw [hkdecomp]; ring
      _ = (p + 1) * (N + 1) + r := by ring
      _ = r + p' + 1 := by rw [← hmdef, hp']; ring
  rw [hidx] at hstep3
  have hstep4 := finrank_full_le_shift (L := L) (T := T) hμ r p' m hΦq
  have hstep5 : Module.finrank ℂ (fullHolomorphicIdealSections (n := n)
      (twistedPower L (twistedPower L T r) (p' + 1)).Fiber
      (sourceDegreeMultiplierIdeal (n := n) m (upperMix N ψ₀ φ))) =
      Module.finrank ℂ (LiteralTwistedMultiplierSections L (twistedPower L T r) m
        (upperMix N ψ₀ φ)) := by
    rw [← hp', (literalTwistedMultiplierSectionEquiv L (twistedPower L T r) m _).finrank_eq]
  have htot := ((hstep1.trans hstep3).trans hstep4).trans hstep5.le
  -- (5) the normalization
  have hmk : m * N ≤ (N + 1) * k := by rw [← hkdecomp, hmdef]; nlinarith
  have hmpos : 0 < m := by rw [hmdef]; positivity
  rw [show k / N * (N + 1) = m by rw [hp]]
  exact ofReal_le_ratio_mul hmpos hk0 hN hmk htot

/-- **The upper bound for a fixed `N`** (blueprint `claude-dx-low2:upper`, first part):
`limsup_k n!/kⁿ h⁰(L^k ⊗ T ⊗ 𝓘(kφ)) ≤ ((N+1)/N)ⁿ (vol θ_Φ + (N+1)⁻¹)`,
`Φ = (N+1)⁻¹ ψ₀ + (1 - (N+1)⁻¹) φ`. -/
theorem limsup_normalizedH0_le_upperMix
    (omega : KahlerBackground n X) (hvol : (IntegrationCurrent.kahlerVolume omega) univ = 1)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (κ : KahlerBackground n X) {ψ₀ φ : X → EReal}
    (hψ₀ : IsThetaPshPotential (sourceNativeFirstChernForm L hL - (1 / 4 : ℝ) • κ.form).val ψ₀)
    (hgent : ∃ (c : ℚ) (𝔞 : GermIdeal n X),
      ActualOriginalSquaredDensityGentle.HasGentleAnalyticSingularitiesOfType (n := n) ψ₀ c 𝔞)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    {A : ℝ} (hA : (-sourceNativeFirstChernForm L hL + A • κ.form).val.IsSemipositive)
    {N₀ : ℕ} (hN₀ : 4 * A < N₀) {N : ℕ} (hN : 0 < N)
    (hΦ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) (upperMix N ψ₀ φ)) :
    limsup (fun k => normalizedH0 L T φ k) atTop ≤ ENNReal.ofReal ((((N : ℝ) + 1) / N) ^ n) *
      (sourceIVolume (chernForm L hL) (upperMix N ψ₀ φ) hΦ +
        ENNReal.ofReal (((N : ℝ) + 1)⁻¹)) := by
  set θ := sourceNativeFirstChernForm L hL with hθdef
  have hrt : atlasClosedFormToNative (chernForm L hL) = θ := sourceNativeAtlasForm_roundTrip θ
  -- `Φ` is a Kähler current
  have ht0 : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ := by positivity
  have ht1 : ((N : ℝ) + 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith)
  have hφn : IsThetaPshPotential θ.val φ := by
    have := (isThetaPSH_iff_nativeThetaPotential (chernForm L hL) _).mp hφ
    rwa [hrt] at this
  have hφ0 : IsThetaPshPotential (θ - (0 : ℝ) • κ.form).val φ := by
    rw [zero_smul, sub_zero]; exact hφn
  have hΦn := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul κ ht0 ht1 hψ₀ hφ0
  have hpos : 0 < ((N : ℝ) + 1)⁻¹ * (1 / 4) + (1 - ((N : ℝ) + 1)⁻¹) * 0 := by positivity
  have hΦcur : IsKahlerCurrentPotential θ (upperMix N ψ₀ φ) :=
    ⟨KahlerBackground.smul hpos κ, by rw [KahlerBackground.smul_form]; exact hΦn⟩
  -- the upper bound for the Kähler current `Φ`, for each twist `L^r ⊗ T`
  set V := sourceIVolume (chernForm L hL) (upperMix N ψ₀ φ) hΦ with hVdef
  have hVfin : V ≠ ⊤ := (@measure_lt_top _ _ _
    (SGPT.Bergman.PartialEnergyDifferentiability.sourcePotentialMeasure_finite omega
      (isThetaPSH_sourceIEnvelope hΦ)) univ).ne
  have hVV : V < V + ENNReal.ofReal (((N : ℝ) + 1)⁻¹) :=
    ENNReal.lt_add_right hVfin (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact ht0)
  have hev : ∀ r ∈ Finset.range N, ∀ᶠ m in atTop,
      normalizedH0 L (twistedPower L T r) (upperMix N ψ₀ φ) m <
        V + ENNReal.ofReal (((N : ℝ) + 1)⁻¹) := by
    intro r _
    refine eventually_lt_of_limsup_lt (lt_of_le_of_lt ?_ hVV)
    exact SGPT.Bergman.Quant3.limsup_normalizedH0_le_iVolume_of_kahlerCurrent omega hvol L
      (twistedPower L T r) hL (sourceNativeTwistedPower_smooth L T hL hT r) hΦcur hΦ
  have hall := (Filter.eventually_all_finset (Finset.range N)).mpr hev
  have hmlim : Tendsto (fun k : ℕ => k / N * (N + 1)) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun B => ⟨B * N, fun k hk => by
      have : B ≤ k / N := by rwa [Nat.le_div_iff_mul_le hN]
      nlinarith⟩
  have hall' := hmlim.eventually hall
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_normalizedH0_le_upperMix (T := T) hL κ hψ₀ hgent hφ hA hN₀ hN,
    hall'] with k hk1 hk2
  refine hk1.trans ?_
  gcongr
  exact (hk2 (k % N) (Finset.mem_range.mpr (Nat.mod_lt k hN))).le

/-- **The upper bound of `thm:DXmain1` when `θ` carries a Kähler current** (blueprint
`claude-dx-low2:upper`; source `thm:DXmain1`, Step 2 of the proof): if some `θ_ψ` is a Kähler
current (`θ = c₁(L, h)`, i.e. `L` is big), then for every `φ ∈ PSH(X, θ)` and every twist `T`,
`limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ vol θ_φ`. This is
`SGPT.Bergman.Quant3.RiemannRochUpperBound (chernForm L hL) L T φ`. -/
theorem riemannRochUpperBound_of_kahlerCurrent
    (omega : KahlerBackground n X) (hvol : (IntegrationCurrent.kahlerVolume omega) univ = 1)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {ψ : X → EReal} (hψ : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    SGPT.Bergman.Quant3.RiemannRochUpperBound (chernForm L hL) L T φ := by
  set θ := sourceNativeFirstChernForm L hL with hθdef
  set θ' := chernForm L hL with hθ'def
  have hrt : atlasClosedFormToNative θ' = θ := sourceNativeAtlasForm_roundTrip θ
  have toAtlas : ∀ {u : X → EReal}, IsThetaPshPotential θ.val u →
      (ofFixedModel n X).IsThetaPSH θ' u := fun h =>
    (isThetaPSH_iff_nativeThetaPotential θ' _).mpr (by rw [hrt]; exact h)
  refine ⟨hφ, ?_⟩
  -- a gentle Kähler current `θ + dd^c ψ₀ ≥ κ/4`
  obtain ⟨κ, hκ⟩ := hψ
  obtain ⟨U, -, hgentle, hU4⟩ := exists_gentle_kahler_qea hκ
  set ψ₀ := U 0 with hψ₀def
  have hψ₀θ : IsThetaPshPotential θ.val ψ₀ :=
    SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hU4 0) (by
      rw [show θ - (θ - (1 / 4 : ℝ) • κ.form) = (1 / 4 : ℝ) • κ.form by abel]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num))
  obtain ⟨A, -, hA⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-θ)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (4 * A)
  -- the mixtures `Φ_N`, `N = i + 1`
  have hφn : IsThetaPshPotential θ.val φ := by
    have := (isThetaPSH_iff_nativeThetaPotential θ' _).mp hφ
    rwa [hrt] at this
  have hmix : ∀ N : ℕ, (ofFixedModel n X).IsThetaPSH θ' (upperMix N ψ₀ φ) := fun N => by
    apply toAtlas
    exact EndpointMixedMassConvexCombination.isThetaPshPotential_convexComb_closed hψ₀θ hφn (by positivity)
      (inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
  have hbound : ∀ i : ℕ, limsup (fun k => normalizedH0 L T φ k) atTop ≤
      ENNReal.ofReal (((((i + 1 : ℕ) : ℝ) + 1) / ((i + 1 : ℕ) : ℝ)) ^ n) *
        (sourceIVolume θ' (upperMix (i + 1) ψ₀ φ) (hmix (i + 1)) +
          ENNReal.ofReal ((((i + 1 : ℕ) : ℝ) + 1)⁻¹)) := fun i =>
    limsup_normalizedH0_le_upperMix omega hvol hL hT κ (hU4 0) (hgentle 0) hφ hA hN₀
      (Nat.succ_pos i) (hmix (i + 1))
  -- the limit `N → ∞`
  obtain ⟨hψ', hψpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL ⟨κ, hκ⟩
  have hbig := sourcePositiveMass_isBig omega hψ' hψpos
  set u₀ : SourceThetaPotentialL1 θ' := ⟨φ, hφ⟩
  set u₁ : SourceThetaPotentialL1 θ' := ⟨ψ₀, toAtlas hψ₀θ⟩
  have ht01 : ∀ i : ℕ, ((((i + 1 : ℕ) : ℝ) + 1)⁻¹) ∈ Ioo (0 : ℝ) 1 := fun i => by
    refine ⟨by positivity, inv_lt_one_of_one_lt₀ ?_⟩
    have : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    linarith
  let t : ℕ → Ioo (0 : ℝ) 1 := fun i => ⟨_, ht01 i⟩
  have hinv : Tendsto (fun i : ℕ => ((((i + 1 : ℕ) : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp ?_
    have := tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    refine this.congr fun i => ?_
    push_cast; ring
  have ht : Tendsto (fun i => (t i).val) atTop (𝓝 0) := hinv
  have hconv := tendsto_sourceGeneralInterpolation_zero omega θ' hbig u₀ u₁ atTop t ht
  have hvol' := (tendsto_sourceIVolume_and_mass_of_sourceSingularityTopology_all_mass omega θ' hbig
    atTop _ u₀ hconv).1
  have hvolN : Tendsto (fun i : ℕ => sourceIVolume θ' (upperMix (i + 1) ψ₀ φ) (hmix (i + 1)))
      atTop (𝓝 (sourceIVolume θ' φ hφ)) := by
    refine hvol'.congr fun i => sourceIVolume_congr ?_ _ _
    rw [sourceGeneralInterpolation_val]
    funext x
    rw [upperMix, convexComb_apply, add_comm]
  have hfac : Tendsto (fun i : ℕ => ENNReal.ofReal
      (((((i + 1 : ℕ) : ℝ) + 1) / ((i + 1 : ℕ) : ℝ)) ^ n)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun i : ℕ => (1 : ℝ) / ((i + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      have := tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
      refine this.congr fun i => ?_
      push_cast; ring
    have h1 : Tendsto (fun i : ℕ => (((((i + 1 : ℕ) : ℝ) + 1) / ((i + 1 : ℕ) : ℝ)) ^ n))
        atTop (𝓝 ((1 + 0) ^ n)) := by
      refine ((tendsto_const_nhds.add h0).pow n).congr fun i => ?_
      congr 1
      have : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
      field_simp
    rw [add_zero, one_pow] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h1
    rw [ENNReal.ofReal_one] at h2
    exact h2
  have hsmall : Tendsto (fun i : ℕ => ENNReal.ofReal ((((i + 1 : ℕ) : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hinv
    rwa [ENNReal.ofReal_zero] at this
  have hsum := hvolN.add hsmall
  rw [add_zero] at hsum
  have hprod := ENNReal.Tendsto.mul hfac (Or.inl one_ne_zero) hsum (Or.inr ENNReal.one_ne_top)
  rw [one_mul] at hprod
  exact ge_of_tendsto' hprod hbound

/-- **The upper bound of `thm:DXmain1` for every `φ ∈ PSH(X, θ)_{>0}`** (Bergman framework):
`limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ vol θ_φ`. -/
theorem riemannRochUpperBound_of_pos
    (omega : KahlerBackground n X) (hvol : (IntegrationCurrent.kahlerVolume omega) univ = 1)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ) :
    SGPT.Bergman.Quant3.RiemannRochUpperBound (chernForm L hL) L T φ := by
  obtain ⟨mseq, hmc, -, -, -⟩ :=
    SGPT.Bergman.Quant3.exists_increasing_kahlerCurrent_minorants omega L hL hφ hφpos
  exact riemannRochUpperBound_of_kahlerCurrent omega hvol hL hT (hmc 0) hφ

end SGPT.IGood.DXLow2

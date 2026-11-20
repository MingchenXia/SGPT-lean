import SGPT.IGood.DXLow2Main
import SGPT.Hodge.BDivChainZero

/-!
# The lower bound of `thm:DXmain1` for every Kähler current, in every dimension

Blueprint `claude-dx-low2`, node `claude-dx-low2:main-all`. Source `thm:DXmain1` (Step 1 of the
proof, `≥`), without restriction on the dimension `n`:

* `exists_ne_zero_twistedMultiplierSections`: if `θ_φ` is a Kähler current, then
  `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≠ 0` for all large `k`, for every twist `T` (the global point
  extension, `claude-global-l2:point-extension`; this is `lma:existsecposmass` with a twist);
* in dimension `0`, `vol θ_φ = 1` and `n!/kⁿ h⁰ = h⁰ ≥ 1`, which gives the lower bound;
* `riemannRochLowerBound_of_isKahlerCurrent`: `RiemannRochLowerBound (chernForm L hL) L T φ` in
  every dimension (for `n > 0` this is `riemannRochLowerBound_of_kahlerCurrent`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.IGood.DXLow2

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
  SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.PSH.GlobalL2
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- **Non-zero multiplier sections for Kähler currents, with a twist** (`lma:existsecposmass`
for `L^k ⊗ T`): if `θ_φ` is a Kähler current (`θ = c₁(L, h)`), then
`H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≠ 0` for all `k ≥ k₀`. -/
theorem exists_ne_zero_twistedMultiplierSections
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 1 ≤ Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) := by
  obtain ⟨κ, hφκ⟩ := hcurrent
  set θ := sourceNativeFirstChernForm L hL with hθdef
  set μ : Measure X := IntegrationCurrent.kahlerVolume κ with hμdef
  have hμ : IsSmoothPositiveVolume (n := n) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume κ
  obtain ⟨k₀, C, -, hext⟩ := globalPointExtension (n := n) (X := X) ‹CompactSpace X› κ μ hμ L T
    hL hT θ (sourceNativeFirstChernForm_isOwn L hL) 1 one_pos
  have hφ1 : IsThetaPshPotential (θ - (1 : ℝ) • κ.form).val φ := by rwa [one_smul]
  have hφθ : IsThetaPshPotential θ.val φ :=
    SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hφκ (by
      have heq : θ - (θ - κ.form) = κ.form := by abel
      rw [heq]; exact κ.isSemipositive)
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨x, -, hx⟩ := hφθ.2 x₀ univ isOpen_univ (mem_univ x₀)
  refine ⟨k₀, fun k hk => ?_⟩
  set e := prefFrame (twistedPower L T k) x
  set v : (twistedPower L T k).Fiber x := e.val.symm x 1 with hv
  have hv0 : v ≠ 0 := by
    have := frameNorm_pos (twistedPower L T k).Fiber e.val (mem_prefFrame _ x)
    exact norm_pos_iff.mp this
  obtain ⟨s, hsx, hsint⟩ := hext k hk φ hφ1 x hx v
  have hfin : (∫⁻ y, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k s y ∂μ) < ⊤ := by
    refine lt_of_le_of_lt hsint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have htop : φ x ≠ ⊤ := hφθ.quasiPshPotential.1.ne_top x
    obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x = r := ⟨(φ x).toReal, (EReal.coe_toReal htop hx).symm⟩
    rw [hr, multiplierWeight_coe]
    exact ENNReal.ofReal_lt_top
  have hmem := (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) _ k
    hφθ.quasiPshPotential s hμ).mpr hfin
  set s' := (literalTwistedMultiplierSectionEquiv L T k φ).symm ⟨s, hmem⟩
  have hs' : s' ≠ 0 := by
    intro h0
    have : (⟨s, hmem⟩ : fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k φ)) = 0 := by
      rw [← (literalTwistedMultiplierSectionEquiv L T k φ).apply_symm_apply ⟨s, hmem⟩]
      change (literalTwistedMultiplierSectionEquiv L T k φ) s' = 0
      rw [h0, map_zero]
    have hs0 : s = 0 := congrArg Subtype.val this
    apply hv0
    rw [← hsx, hs0]
    rfl
  let := literalTwistedMultiplierSections_finiteDimensional L T k φ
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨s', hs'⟩

/-- **The lower bound of `thm:DXmain1` for every Kähler current, in every dimension**
(blueprint `claude-dx-low2:main-all`): if `θ_φ` is a Kähler current (`θ = c₁(L, h)`), then
`vol θ_φ ≤ liminf_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`, i.e.
`SGPT.Bergman.Quant2.RiemannRochLowerBound (chernForm L hL) L T φ`. -/
theorem riemannRochLowerBound_of_isKahlerCurrent
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    RiemannRochLowerBound (chernForm L hL) L T φ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨κ, hφκ⟩ := hcurrent
    obtain ⟨hφ, -⟩ := isThetaPSH_and_pos_of_kahlerCurrent κ L hL ⟨κ, hφκ⟩
    refine ⟨hφ, ?_⟩
    rw [SGPT.Hodge.BDivChain.sourceIVolume_eq_one_of_dim_zero]
    obtain ⟨k₀, hk₀⟩ := exists_ne_zero_twistedMultiplierSections hL hT ⟨κ, hφκ⟩
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ge_atTop k₀] with k hk
    simp only [normalizedH0, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul]
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast hk₀ k hk
  · exact riemannRochLowerBound_of_kahlerCurrent hn hL hT hcurrent

end SGPT.IGood.DXLow2

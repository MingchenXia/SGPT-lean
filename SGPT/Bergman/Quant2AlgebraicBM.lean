import SGPT.Bergman.Quant2EnergyLimit
import SGPT.Bergman.SourceGlobalWeightEnergyApproximation
import SGPT.Bergman.SourceGammaPartialEnvelope
import SGPT.Bergman.SourceSectionEnvelopeExponential
import SGPT.Bergman.SourceKahlerCurrentScalingTail
import SGPT.Bergman.SourceBaseBMComparison

/-!
# Energy quantization for weighted subsets

Source `prop:quant_I_algebraic_BM` (`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`,
lines 1090--1159) and `cor:LktoI` (lines 1166--1175).

Let `φ ∈ PSH(X,θ)`, `θ = c₁(L,h)`, have analytic singularities with `θ_φ` a Kähler current and let
`(K,v)` be a weighted subset. The book's proof compares `N^k_{v,K}` with the sup norms of the
smooth weights `v_j^±` of `lma:global_env_approx`:
`N^k_{v_j^+,X} ≤ N^k_{v,K} ≤ N^k_{v_j^-,X}` on `H⁰(X, L^k ⊗ T ⊗ I(kφ))` for `k ≥ k₀`. We prove
these comparisons unconditionally (`supNorm_le_supNorm_whole`, `exists_supNorm_upper_sandwich`).

The upper comparison is proved as in the book: for a section `s` of degree `k ≥ k₀`, the function
`k⁻¹ log |s|² - k⁻¹ log N^k_{v,K}(s)²` is `(θ + ω)`-psh, more singular than `α φ` for a fixed
`α < 1` (`prop:Bergman_approx`) and `≤ v` on `K`; so it lies below the partial envelope
`P_{θ+ω,K}[αφ](v) ≤ P_{θ+ω,X}[αφ](v_j^+) ≤ v_j^+` (`lma:global_env_approx`), which is the content of
the maximum principle `lma:max_princ` used in the book.

Assuming the lower-bound half `RiemannRochLowerBound` of `thm:DXmain1` we then prove
`eq:Lkconv` (`Lkconv`), `eq:LkdiffconvtoI` (`quant_I_algebraic_BM`) and `cor:LktoI` (`LktoI`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.Quant2

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport SGPT.Bergman.NormAxioms
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEnergyDifferentiability SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Bergman.PartialDonaldson SGPT.Bergman.QuantizationFrontier
open SGPT.Bergman.GlobalWeightApproximation SGPT.Bergman.MultiplierSectionSingularity
open SGPT.Bergman.GlobalWeightSmoothApproximation
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- The partial equilibrium energy `E^φ_{θ,K}(v)` of a weighted subset `(K,v)`. -/
abbrev energyK (omega : KahlerBackground n X) {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) : ℝ :=
  partialEquilibriumEnergy omega hφ hφpos W.isClosed_carrier W.nonPluripolar_carrier W.weight

/-! ### Elementary lemmas -/

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The class of `θ = c₁(L,h)` is big as soon as it contains a Kähler current. -/
theorem isBigClass_chernForm (L : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) {φ : X → EReal}
    (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (chernForm L hL))) := by
  have h := sourceNativeAtlasForm_roundTrip (sourceNativeFirstChernForm L hL)
  unfold chernForm
  rw [h]
  exact ⟨nativeKahlerCurrentOfPotential _ hcurrent⟩

/-- `γ u ≤ β u + (γ - β) M` for `0 < β ≤ γ` and `u ≤ M`. -/
theorem ereal_smul_le_smul_add {β γ M : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) {u : EReal}
    (hu : u ≤ (M : EReal)) :
    (γ : EReal) * u ≤ (β : EReal) * u + (((γ - β) * M : ℝ) : EReal) := by
  induction u using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos (hβ.trans_le hβγ)]; exact bot_le
  | top => exact absurd hu (by simp)
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hr : r ≤ M := EReal.coe_le_coe_iff.mp hu
    nlinarith

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- For `0 < β ≤ γ` and `u` bounded above, `γ u ⪯ β u`. -/
theorem singularityLE_smul_of_le {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) {u : X → EReal}
    {M : ℝ} (hu : ∀ x, u x ≤ (M : EReal)) :
    SGPT.PSH.SingularityLE (fun x => (γ : EReal) * u x) (fun x => (β : EReal) * u x) :=
  (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
    ⟨(γ - β) * M, fun x => ereal_smul_le_smul_add hβ hβγ (hu x)⟩

/-- A larger norm has a smaller value of the partial Donaldson functional. -/
theorem partialDonaldsonFunctional_anti (omega : KahlerBackground n X)
    (hvol : (kahlerVolume omega) univ = 1) (L T : HermitianHolomorphicLineBundle n X)
    (k : ℕ) (hk : 0 < k) (φ : X → EReal) {H₁ H₂ : ComplexNorm (idealSections L T k φ)}
    (h : ∀ s, H₁.toAddGroupNorm s ≤ H₂.toAddGroupNorm s) :
    partialDonaldsonFunctional L T omega hvol k hk φ H₂ ≤
      partialDonaldsonFunctional L T omega hvol k hk φ H₁ := by
  let vol : Measure (idealSections L T k φ) := Measure.addHaar
  let R := referenceNorm L T omega hvol k hk φ
  have hv : vol.real (normUnitBall H₂) ≤ vol.real (normUnitBall H₁) :=
    measureReal_mono (normUnitBall_antitone H₁ H₂ h) (normUnitBall_measure_ne_top vol H₁)
  have hlog := Real.log_le_log (normUnitBall_real_pos vol H₂) hv
  apply sub_nonpos.mp
  change sourceDonaldsonFunctional vol n k H₂ R - sourceDonaldsonFunctional vol n k H₁ R ≤ 0
  rw [sourceDonaldsonFunctional_difference]
  exact mul_nonpos_of_nonneg_of_nonpos (sourceDonaldsonNormalization_nonneg n k) (by linarith)

/-! ### The two comparisons of sup norms -/

omit [MeasurableSpace X] [BorelSpace X] in
/-- `N^k_{v,K} ≤ N^k_{a,X}` when `a ≤ v` on `K` (`lma:mononorm`-type comparison). -/
theorem supNorm_le_supNorm_whole (L T : HermitianHolomorphicLineBundle n X)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ) (φ : X → EReal) (a : C(X, ℝ))
    (ha : ∀ x : W.carrier, a x.val ≤ W.weight x) (s : idealSections L T k φ) :
    (supNorm L T W k φ).toAddGroupNorm s ≤
      (supNorm L T (wholeWeightedSubset (n := n) a) k φ).toAddGroupNorm s := by
  apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
  rw [supNorm_ofReal, supNorm_ofReal]
  unfold weightedSupNorm
  apply iSup₂_le
  intro x _
  have hx : weightedSectionDensity (twistedPower L T k).Fiber k W.erealWeight s.val x ≤
      weightedSectionDensity (twistedPower L T k).Fiber k
        (wholeWeightedSubset (n := n) a).erealWeight s.val ⟨x.val, mem_univ _⟩ :=
    mul_le_mul_right (multiplierWeight_antitone (Nat.cast_nonneg k)
      (EReal.coe_le_coe_iff.mpr (ha x))) _
  calc _ ≤ (weightedSectionDensity (twistedPower L T k).Fiber k
        (wholeWeightedSubset (n := n) a).erealWeight s.val ⟨x.val, mem_univ _⟩) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hx (by norm_num)
    _ ≤ _ := le_iSup₂ (f := fun (y : (wholeWeightedSubset (n := n) a).carrier)
        (_ : (wholeWeightedSubset (n := n) a).erealWeight y ≠ ⊥) =>
          (weightedSectionDensity (twistedPower L T k).Fiber k
            (wholeWeightedSubset (n := n) a).erealWeight s.val y) ^ (1 / 2 : ℝ))
        ⟨x.val, mem_univ _⟩ (EReal.coe_ne_bot _)

/-- The square of a weighted point density bounded by a sup norm. -/
theorem density_le_of_rpow_le {d S : ℝ≥0∞} (h : d ^ (1 / 2 : ℝ) ≤ S) : d ≤ S ^ (2 : ℝ) := by
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2

/-- The comparison `N^k_{v_j^+,X} ≤ N^k_{v,K}` on `H⁰(X, L^k ⊗ T ⊗ I(kφ))` for all `k ≥ k₀` and all
`j`, for the decreasing smooth sequence `v_j^+` of `lma:global_env_approx` (proof of
`prop:quant_I_algebraic_BM`). -/
theorem exists_supNorm_upper_sandwich (omega : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    (b : ℕ → X → ℝ) (hb : ∀ j, Continuous (b j)) (hbm : Antitone b)
    (hbu : ∀ j x, upperObstacle (chernForm L hL) omega W x ≤ b j x)
    (hblim : ∀ x, Tendsto (fun j => b j x) atTop (𝓝 (upperObstacle (chernForm L hL) omega W x))) :
    ∃ k₁ : ℕ, 0 < k₁ ∧ ∀ k : ℕ, k₁ ≤ k → ∀ (j : ℕ) (s : idealSections L T k φ),
      (supNorm L T (wholeWeightedSubset (n := n) ⟨b j, hb j⟩) k φ).toAddGroupNorm s ≤
        (supNorm L T W k φ).toAddGroupNorm s := by
  set Θ := sourceNativeFirstChernForm L hL with hΘ
  set θ := chernForm L hL with hθ
  have hround : atlasClosedFormToNative θ = Θ := sourceNativeAtlasForm_roundTrip Θ
  obtain ⟨hnative, _⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent omega Θ
    (nonPluripolar_univ (n := n)) hcurrent
  have hq : IsGlobalQuasiPshPotential (n := n) φ := ⟨hnative.1.quasiPlurisubharmonic, hnative.2⟩
  obtain ⟨Mφ, hMφ⟩ := hnative.exists_global_upper_bound
  obtain ⟨hφ, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent omega L hL hcurrent
  have hbig := isBigClass_chernForm L hL hcurrent
  obtain ⟨α, hαmono, hα01, hαlim, Nα, hNα, horder⟩ :=
    exists_alpha_literalGamma_normalizedLogNormSq_singularityLE omega L T hq
      (hasRationalAnalyticType_iff_chartType.mp han)
  obtain ⟨Ns, hscaled, _⟩ := exists_native_scaled_tail_distance_tendsto omega Θ hcurrent α
    (fun k => (hα01 k).2) hαlim
  -- the fixed reference `φ' = α_{Ns} φ`, θ-psh with positive mass
  let φ' : X → EReal := fun x => ((α Ns : ℝ) : EReal) * φ x
  have hφ'n : IsThetaPshPotential Θ.val φ' := by simpa only [zero_add] using hscaled 0
  have hφ' : (ofFixedModel n X).IsThetaPSH θ φ' :=
    (isThetaPSH_iff_nativeThetaPotential θ φ').mpr (by rw [hround]; exact hφ'n)
  have hφφ' : SGPT.PSH.SingularityLE φ φ' := by
    have h := singularityLE_smul_of_le (hα01 Ns).1 (hα01 Ns).2.le (u := φ) hMφ
    simpa only [EReal.coe_one, one_mul] using h
  have hφ'pos : 0 < sourcePotentialNonPluripolarMeasure θ φ' hφ' univ :=
    hφpos.trans_le (sourcePotentialNonPluripolarMass_mono omega hφ hφ' hφφ')
  have hφ'T := perturbedForm_genuine omega hφ' zero_le_one
  have hφ'Tpos := perturbedForm_positive omega hφ' hφ'pos zero_le_one
  obtain ⟨_, hinf, _⟩ := decreasing_global_original omega hbig le_rfl hφ'T hφ'Tpos W hb hbm hbu hblim
  obtain ⟨NP, hNP, hpsh⟩ := exists_sourceNormalizedSection_kahler_background L T hL hT omega one_pos
  have hroundT : atlasClosedFormToNative (perturbedForm θ omega 1) = Θ + (1 : ℝ) • omega.form := by
    rw [perturbedForm, sourceNativeAtlasForm_roundTrip, hround]
  refine ⟨max (max Nα NP) (max Ns 1), by omega, fun k hk j s => ?_⟩
  have hkα : Nα ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkP : NP ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hks : Ns ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk0 : 0 < k := lt_of_lt_of_le one_pos (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk)
  by_cases hs : s = 0
  · subst hs
    simp only [map_zero, le_refl]
  -- the sup norm `N = N^k_{v,K}(s) > 0` and `P = N²`
  set N := (supNorm L T W k φ).toAddGroupNorm s with hNdef
  have hNpos : 0 < N := map_pos_of_ne_zero _ hs
  set P : ℝ := N ^ 2 with hPdef
  have hP : 0 < P := pow_pos hNpos 2
  have hSN : weightedSupNorm (twistedPower L T k).Fiber k W.erealWeight s.val = ENNReal.ofReal N :=
    (supNorm_ofReal L T W k φ s).symm
  have hSP : (ENNReal.ofReal N) ^ (2 : ℝ) = ENNReal.ofReal P := by
    rw [hPdef, ENNReal.ofReal_pow hNpos.le, ENNReal.rpow_two]
  have hts : s.val ≠ 0 := fun h => hs (Subtype.ext h)
  -- the competitor `u = k⁻¹ log |s|² - k⁻¹ log P`
  let A : ℝ := -((k : ℝ)⁻¹ * Real.log P)
  let u : X → EReal := fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * logNormSq (s.val x) + (A : EReal)
  have hobs : ∀ x : W.carrier, u x.val ≤ W.erealWeight x := by
    intro x
    have hd : weightedSectionDensity (twistedPower L T k).Fiber k W.erealWeight s.val x ≤
        ENNReal.ofReal P := by
      rw [← hSP, ← hSN]
      apply density_le_of_rpow_le
      exact le_iSup₂ (f := fun (y : W.carrier) (_ : W.erealWeight y ≠ ⊥) =>
        (weightedSectionDensity (twistedPower L T k).Fiber k W.erealWeight s.val y) ^ (1 / 2 : ℝ))
        x (EReal.coe_ne_bot _)
    have hd' : ENNReal.ofReal (‖s.val x.val‖ ^ 2 * Real.exp (-((k : ℝ) * W.weight x))) ≤
        ENNReal.ofReal P := by
      change ENNReal.ofReal (‖s.val x.val‖ ^ 2) *
        multiplierWeight (k : ℝ) ((W.weight x : ℝ) : EReal) ≤ _ at hd
      rwa [multiplierWeight_coe, ← ENNReal.ofReal_mul (sq_nonneg _)] at hd
    exact normalizedLogNormSq_add_shift_le_of_weighted_bound (s.val x.val) (W.weight x) P hP k hk0 hd'
  have hupsh : (ofFixedModel n X).IsThetaPSH (perturbedForm θ omega 1) u := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [hroundT]
    exact (hpsh k hkP s.val hts).add_const A
  -- singularity: `u ⪯ k⁻¹ log |s|² ⪯ α_k φ ⪯ α_{Ns} φ`
  have hsing : SGPT.PSH.SingularityLE u φ' := by
    have h1 : SGPT.PSH.SingularityLE u
        (fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * logNormSq (s.val x)) := ⟨A, fun _ _ => le_rfl⟩
    have h2 := horder k hkα ((literalTwistedMultiplierSectionEquiv L T k φ).symm s)
    rw [LinearEquiv.apply_symm_apply] at h2
    have h3 : SGPT.PSH.SingularityLE (fun x => ((α k : ℝ) : EReal) * φ x) φ' :=
      singularityLE_smul_of_le (hα01 Ns).1 (hαmono.monotone hks) hMφ
    exact SGPT.PSH.singularityLE_trans h1 (SGPT.PSH.singularityLE_trans h2 h3)
  have hule := le_partialEnvelope hupsh (partialObstacle_of_forall hobs) hsing
  have hPKX : partialEnvelope (perturbedForm θ omega 1) φ' W.carrier W.erealWeight ≤
      partialEnvelope (perturbedForm θ omega 1) φ' univ (fun x => (b j x.val : EReal)) := by
    rw [← hinf]
    exact iInf_le (fun i => partialEnvelope (perturbedForm θ omega 1) φ' univ
      (fun x => (b i x.val : EReal))) j
  have hXb := globalEnvelope_le_continuous omega hφ'T hφ'Tpos (hb j)
  have hub : ∀ x, u x ≤ (b j x : EReal) := fun x => (hule x).trans ((hPKX x).trans (hXb x))
  -- conclusion
  apply (ENNReal.ofReal_le_ofReal_iff hNpos.le).mp
  rw [supNorm_ofReal]
  unfold weightedSupNorm
  apply iSup₂_le
  intro x _
  have hdx := weightedDensity_le_exp_of_normalizedLog_le (s.val x.val) (b j x.val) P hP k hk0
    (b j x.val : EReal) (hub x.val)
  rw [← EReal.coe_sub, sub_self, EReal.coe_zero, mul_zero, EReal.exp_zero, mul_one] at hdx
  have hdx' : weightedSectionDensity (twistedPower L T k).Fiber k
      (wholeWeightedSubset (n := n) ⟨b j, hb j⟩).erealWeight s.val x ≤ ENNReal.ofReal P := by
    convert hdx using 1
    change ENNReal.ofReal (‖s.val x.val‖ ^ 2) * multiplierWeight (k : ℝ) ((b j x.val : ℝ) : EReal) = _
    rw [multiplierWeight_coe, ENNReal.ofReal_mul (sq_nonneg _)]
  calc _ ≤ (ENNReal.ofReal P) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hdx' (by norm_num)
    _ = ENNReal.ofReal N := by
      rw [← hSP, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

/-! ### The limits -/

/-- Source `prop:quant_I_algebraic_BM`, `eq:Lkconv`: for a weighted subset `(K,v)` and `φ` with
analytic singularities such that `θ_φ` is a Kähler current,
`L_{k,φ}(N^k_{v,K}) → E^φ_{θ,K}(v)`, assuming the lower-bound half `RiemannRochLowerBound` of
`thm:DXmain1`. -/
theorem Lkconv
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) :
    Tendsto (fun k => supDonaldson omega hvol L T φ W k) atTop
      (𝓝 (energyK omega hφ hφpos W)) := by
  have hbig := isBigClass_chernForm L hL hcurrent
  obtain ⟨a, b, ha, hb, ham, hbm, _hbound, habu, halim, hblim⟩ :=
    exists_fixed_smooth_pair omega (chernForm L hL) hbig W
  have hac : ∀ j, Continuous (a j) := fun j => continuous_of_chartSmooth (ha j)
  have hbc : ∀ j, Continuous (b j) := fun j => continuous_of_chartSmooth (hb j)
  obtain ⟨_, _, hloK, _⟩ := lowerObstacle_data omega (chernForm L hL) W
  have haK : ∀ j (x : W.carrier), a j x.val ≤ W.weight x := fun j x =>
    (habu j x.val).1.trans (le_of_eq (hloK x))
  obtain ⟨hEa, hEb⟩ := fixed_pair_energy_limits omega hbig hφ hφpos W hac hbc ham hbm
    (fun j x => (habu j x).1) (fun j x => (habu j x).2) halim hblim
  have hEa' : Tendsto (fun j => energyX omega hφ hφpos ⟨a j, hac j⟩) atTop
      (𝓝 (energyK omega hφ hφpos W)) := hEa
  have hEb' : Tendsto (fun j => energyX omega hφ hφpos ⟨b j, hbc j⟩) atTop
      (𝓝 (energyK omega hφ hφpos W)) := hEb
  obtain ⟨k₁, hk₁, hup⟩ := exists_supNorm_upper_sandwich omega L T hL hT hcurrent han W b hbc hbm
    (fun j x => (habu j x).2) hblim
  rw [tendsto_order]
  constructor
  · intro c hc
    obtain ⟨j, hj⟩ := ((tendsto_order.1 hEa').1 c hc).exists
    have hlim := Ninfdifflim omega hvol L T hL hT hcurrent han hRR hφ hφpos ⟨a j, hac j⟩
    filter_upwards [(tendsto_order.1 hlim).1 c hj, eventually_gt_atTop 0] with k hk hk0
    refine lt_of_lt_of_le hk ?_
    simp only [supDonaldson, dif_pos hk0]
    exact partialDonaldsonFunctional_anti omega hvol L T k hk0 φ
      (supNorm_le_supNorm_whole L T W k φ ⟨a j, hac j⟩ (haK j))
  · intro c hc
    obtain ⟨j, hj⟩ := ((tendsto_order.1 hEb').2 c hc).exists
    have hlim := Ninfdifflim omega hvol L T hL hT hcurrent han hRR hφ hφpos ⟨b j, hbc j⟩
    filter_upwards [(tendsto_order.1 hlim).2 c hj, eventually_ge_atTop k₁] with k hk hkk
    have hk0 : 0 < k := lt_of_lt_of_le hk₁ hkk
    refine lt_of_le_of_lt ?_ hk
    simp only [supDonaldson, dif_pos hk0]
    exact partialDonaldsonFunctional_anti omega hvol L T k hk0 φ (hup k hkk j)

/-- Source `prop:quant_I_algebraic_BM`, `eq:LkdiffconvtoI`: for two weighted subsets `(K,v)`,
`(K',v')`, `L_{k,φ}(N^k_{v,K}) - L_{k,φ}(N^k_{v',K'}) → E^φ_{θ,K}(v) - E^φ_{θ,K'}(v')`, assuming
`RiemannRochLowerBound`. -/
theorem quant_I_algebraic_BM
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (W W' : SGPT.Bergman.WeightedSubset.WeightedSubset n X) :
    Tendsto (fun k => supDonaldson omega hvol L T φ W k - supDonaldson omega hvol L T φ W' k)
      atTop (𝓝 (energyK omega hφ hφpos W - energyK omega hφ hφpos W')) :=
  (Lkconv omega hvol L T hL hT hcurrent han hRR hφ hφpos W).sub
    (Lkconv omega hvol L T hL hT hcurrent han hRR hφ hφpos W')

/-- `L_{k,φ}(N^k_{v,μ})` for a Bernstein--Markov measure `μ` (value `0` at `k = 0`). -/
def l2Donaldson (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) : ℝ :=
  if hk : 0 < k then partialDonaldsonFunctional L T omega hvol k hk φ (l2Norm L T W μ hBM k hk φ)
  else 0

/-- Source `cor:LktoI`: for `μ ∈ BM(K,v)` and `φ` with analytic singularities such that `θ_φ` is a
Kähler current, `L_{k,φ}(N^k_{v,μ}) → E^φ_{θ,K}(v)`, assuming `RiemannRochLowerBound`. -/
theorem LktoI
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
    (hBM : IsBernsteinMarkov L T W μ) :
    Tendsto (fun k => l2Donaldson omega hvol L T φ W μ hBM k) atTop
      (𝓝 (energyK omega hφ hφpos W)) := by
  have h := (Lkconv omega hvol L T hL hT hcurrent han hRR hφ hφpos W).sub
    (tendsto_partialDonaldson_sup_sub_l2 L T hL hT omega hvol W μ hBM φ)
  rw [sub_zero] at h
  apply h.congr
  intro k
  by_cases hk : 0 < k
  · simp only [supDonaldson, l2Donaldson, dif_pos hk]
    ring
  · simp only [supDonaldson, l2Donaldson, dif_neg hk, sub_zero]

end SGPT.Bergman.Quant2

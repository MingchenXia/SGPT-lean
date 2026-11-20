import SGPT.Trace.OTExt5Step
import SGPT.Trace.OTExt4Equal

/-!
# Steps 1--4 of FPT `thm:compact-submanifold-extension` from the residue hypothesis, and `thm:OT_ext`

Blueprint `claude-ot-ext5.tex`, nodes `claude-ot-ext5:gentle`, `claude-ot-ext5:ot-ext`.  Xia,
*Foundations of pluripotential theory*, q07, proof of `thm:compact-submanifold-extension`.

* `gentleSubmanifoldExtensionAlong_of_residue`: for a closed connected submanifold `W` of dimension
  `m < n`, the named hypothesis `GentleWeightedNormalResidueHypothesis ω W` (FPT
  `lem:gentle-weighted-normal-residue`) implies `GentleSubmanifoldExtensionAlong ω W` (Steps 1--4:
  the theorem for gentle weights with `c₁(V, h₀ e^{-Φ}) ≥ N₀ ω`), with
  `N₀ = 1 + b_K/π + (q + 2) b` and `C = 1280 B² C_Y + 1`.  The proof: the gluing `G` of
  `lem:critical-gain-initial-gluing` (`criticalGainInitialGluingAlong`), the sections `s_ε` of
  `exists_section_eps` for a sequence `ε_k → 0` along which the bound `T(ε)` of Step 4 is within
  `1/(k+1)` of its upper limit `≤ 1280 B² C_Y ∫_W |f|² e^{-Φ}` (residue hypothesis for the shell
  term, `lem:critical-gain-initial-gluing`'s decay for the `∂̄G` term, absolute continuity for
  `∫_{R<ε} |G|² e^{-Φ}`), and the limit by finite-dimensional compactness of `H⁰(X, V)` and Fatou's
  lemma.
* `otExtAlong_of_residue`, `otExtStatement_of_residue`: the book's `thm:OT_ext` for all dimensions of
  `Y`, conditional only on the residue hypothesis for `0 < dim Y < dim X` (the cases `dim Y = 0` and
  `dim Y = dim X` are unconditional: `otExtAlong_of_dim_zero`, `otExtAlong_of_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt5

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
  SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2 SGPT.Trace.OTExt4

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- `e^{-Φ} ≤ e^{κ M} e^{-(1+κ)Φ}` for `Φ ≤ M`, `κ ≥ 0`. -/
theorem multiplierWeight_one_le_of_le {κ M : ℝ} (hκ : 0 ≤ κ) {a : EReal} (ha : a ≤ M) :
    multiplierWeight 1 a ≤ ENNReal.ofReal (Real.exp (κ * M)) * multiplierWeight (1 + κ) a := by
  induction a using EReal.rec with
  | bot =>
      rw [multiplierWeight_bot one_pos, multiplierWeight_bot (by linarith),
        ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
  | top => exact absurd ha (by simp)
  | coe t =>
      have ht : t ≤ M := EReal.coe_le_coe_iff.mp ha
      rw [multiplierWeight_coe, multiplierWeight_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))

/-- **A submanifold of positive codimension is `μ`-null**: `R^{-1/2}` is integrable and infinite
on `W`. -/
theorem measure_eq_zero_of_isGlobalNormalPole {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : IsSmoothPositiveVolume (n := n) μ) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) (hmn : m < n) {ωb : KahlerBackground n X}
    {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R) : μ W = 0 := by
  have hq : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hmn
  have hfin := lintegral_multiplierWeight_logPole_lt_top hμ hW.2.2 hW.1.isCompact hmn hR
    (c := 1 / 2) (by norm_num) (by linarith)
  by_contra hne
  refine hfin.ne (top_le_iff.mp ?_)
  calc (⊤ : ℝ≥0∞) = ∫⁻ _ in W, ⊤ ∂μ := by rw [setLIntegral_const, ENNReal.top_mul hne]
    _ ≤ ∫⁻ x in W, multiplierWeight (1 / 2) (logPole R x) ∂μ := by
        refine setLIntegral_mono' hW.1.measurableSet fun x hx => ?_
        rw [(hR.pole.eq_bot_iff x).mpr hx, multiplierWeight_bot (by norm_num)]
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- **Steps 1--4 of FPT `thm:compact-submanifold-extension`, conditional on the residue
hypothesis**: for `dim W = m < n`, `GentleWeightedNormalResidueHypothesis ω W` implies
`GentleSubmanifoldExtensionAlong ω W`. -/
theorem gentleSubmanifoldExtensionAlong_of_residue (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) (hmn : m < n)
    (hres : GentleWeightedNormalResidueHypothesis ωb hW) :
    GentleSubmanifoldExtensionAlong ωb hW := by
  unfold GentleWeightedNormalResidueHypothesis at hres
  unfold GentleSubmanifoldExtensionAlong
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  obtain ⟨R, hR, CY, hCY, hresR⟩ := hres hmn
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  set μW := IntegrationCurrent.kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) with hμWdef
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hμW := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
  obtain ⟨b, hb0, -, hbR⟩ := hR.levi
  obtain ⟨bK, hbK0, hRic⟩ := exists_leviForm_log_chartDensity_le ωb hμ
  obtain ⟨Bρ, hBρ0, hBρ⟩ := exists_abs_deriv_cutoffProfile_le
  obtain ⟨MR, hMR0, hMR⟩ := exists_holDerivSq_le_kahlerQuad ωb hR.smooth
  set q := n - m with hqdef
  have hq : 0 < q := Nat.sub_pos_of_lt hmn
  set N₀ : ℝ := 1 + bK / Real.pi + ((q : ℝ) + 2) * b with hN₀
  have hN₀0 : 0 < N₀ := by
    have : 0 ≤ bK / Real.pi := div_nonneg hbK0 Real.pi_pos.le
    have : 0 ≤ ((q : ℝ) + 2) * b := mul_nonneg (by positivity) hb0
    linarith
  set C₀ : ℝ := 2 * (20 * (32 * Bρ ^ 2 * CY)) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨N₀, C₀ + 1, hN₀0, by positivity, fun V hV θV hθV Φ hΦ hgen hΦW f hf => ?_⟩
  obtain ⟨c₀, 𝔞, hgen'⟩ := hgen
  have hΦt : ∀ x, Φ x ≠ ⊤ := hΦ.1.quasiPlurisubharmonic.ne_top
  have hΦm : Measurable Φ := hΦ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hwm : Measurable fun x => multiplierWeight 1 (Φ x) :=
    (multiplierWeight_antitone zero_le_one).measurable.comp hΦm
  have hΦθ : IsThetaPshPotential θV.val Φ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hΦ
      (KahlerDomination.isSemipositive_smul ωb.isSemipositive hN₀0.le)
    rwa [sub_add_cancel] at h
  obtain ⟨x₀, -⟩ := hW.2.1.nonempty
  have : Nonempty X := ⟨x₀⟩
  obtain ⟨M, hM⟩ := exists_real_upper_bound_of_upperSemicontinuous
    hΦ.1.quasiPlurisubharmonic.upperSemicontinuous hΦt
  -- the gluing (`lem:critical-gain-initial-gluing`)
  have hglue := criticalGainInitialGluingAlong ωb hW hmn hR
  unfold CriticalGainInitialGluingAlong at hglue
  obtain ⟨κ, hκ, G, Dg, hGl, hGs, hGf, hDg0, hDgW, hDg, hstr, hdec⟩ :=
    hglue V hV θV hθV Φ hΦθ hΦW f hf
  -- the residue hypothesis
  have hres' := hresR V hV θV hθV Φ hΦθ ⟨c₀, 𝔞, hgen'⟩ hΦW f hf κ hκ G hGl
  -- the norm of `f`
  set B : ℝ≥0∞ := ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (Φ y) ∂μW with hB
  have hBfin : B < ⊤ := SGPT.Trace.OTExt3.lintegral_lt_top_of_isAlongMultiplierSection V.Fiber hμW
    one_pos (hΦm.comp continuous_subtype_val.measurable) hf
  -- `∫_{R < ε} |G|² e^{-Φ} → 0`
  have hμW0 : μ W = 0 := measure_eq_zero_of_isGlobalNormalPole hμ hW hmn hR
  have hGc : Continuous fun x => ‖G x‖ := continuous_norm_of_isSmoothSectionOn V hGs
  set gG : X → ℝ≥0∞ := fun x => ENNReal.ofReal (‖G x‖ ^ 2) * multiplierWeight 1 (Φ x) with hgG
  have hgGm : Measurable gG := (ENNReal.measurable_ofReal.comp (hGc.pow 2).measurable).mul hwm
  have hGfin : ∫⁻ x, gG x ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.ofReal_ne_top (r := 4 * Real.exp (κ * M))) hstr) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    have hae : ∀ᵐ x ∂μ, x ∉ W := measure_eq_zero_iff_ae_notMem.mp hμW0
    filter_upwards [hae] with x hxW
    have hx := hR.pos_of_notMem hxW
    have hR1 : R x < 1 := (hR.lt_exp x).trans (Real.exp_lt_one_iff.mpr (by norm_num))
    have hlog : Real.log (R x) ≠ 0 := (Real.log_neg hx hR1).ne
    have hpos : 0 < R x ^ q * Real.log (R x) ^ 2 := by positivity
    have h4 := sq_mul_rpow_log_le hx hR1.le hq
    have hreal : ‖G x‖ ^ 2 ≤ 4 * ((‖G x‖ ^ 2 + Dg x) * (R x ^ q * Real.log (R x) ^ 2)⁻¹) := by
      rw [← div_eq_mul_inv, mul_div_assoc', le_div_iff₀ hpos]
      nlinarith [hDg0 x, sq_nonneg ‖G x‖]
    calc gG x ≤ ENNReal.ofReal (4 * ((‖G x‖ ^ 2 + Dg x) * (R x ^ q * Real.log (R x) ^ 2)⁻¹)) *
          (ENNReal.ofReal (Real.exp (κ * M)) * multiplierWeight (1 + κ) (Φ x)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) (multiplierWeight_one_le_of_le hκ.le (hM x))
      _ = ENNReal.ofReal (4 * Real.exp (κ * M)) * (ENNReal.ofReal ((‖G x‖ ^ 2 + Dg x) *
            (R x ^ q * Real.log (R x) ^ 2)⁻¹) * multiplierWeight (1 + κ) (Φ x)) := by
        rw [ENNReal.ofReal_mul (p := 4) (by norm_num), ENNReal.ofReal_mul (p := 4) (by norm_num)]
        ring
  have hRm : ∀ ε : ℝ, MeasurableSet {x | R x < ε} := fun ε =>
    (isOpen_lt hR.continuous continuous_const).measurableSet
  have hK : Tendsto (fun ε : ℝ => ∫⁻ x in {x | R x < ε}, gG x ∂μ) (𝓝[>] 0) (𝓝 0) := by
    set ν := μ.withDensity gG with hν
    have hνs : ∀ ε, ν {x | R x < ε} = ∫⁻ x in {x | R x < ε}, gG x ∂μ := fun ε =>
      withDensity_apply _ (hRm ε)
    have h := tendsto_measure_biInter_gt (μ := ν) (s := fun ε : ℝ => {x | R x < ε}) (a := 0)
      (fun r _ => (hRm r).nullMeasurableSet) (fun i j _ hij x hx => lt_of_lt_of_le hx hij)
      ⟨1, one_pos, by rw [hνs]; exact ne_top_of_le_ne_top hGfin (setLIntegral_le_lintegral _ _)⟩
    have hinter : (⋂ r > (0 : ℝ), {x | R x < r}) = W := by
      ext x
      simp only [mem_iInter, mem_ofPred_eq]
      constructor
      · intro h
        refine (hR.eq_zero_iff x).mp (le_antisymm ?_ (hR.nonneg x))
        by_contra hlt
        rw [not_le] at hlt
        exact lt_irrefl _ (h _ hlt)
      · intro hx r hr
        rw [(hR.eq_zero_iff x).mpr hx]; exact hr
    have hνW : ν W = 0 := by
      rw [hν, withDensity_apply _ hW.1.measurableSet, Measure.restrict_eq_zero.mpr hμW0,
        lintegral_zero_measure]
    rw [hinter, hνW] at h
    refine h.congr fun ε => ?_
    exact hνs ε
  -- the bound of Step 4 and its upper limit
  set I : ℝ → ℝ≥0∞ := fun ε => ∫⁻ x in shell ε R, ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ q)⁻¹) *
    multiplierWeight 1 (Φ x) ∂μ with hIdef
  set J : ℝ → ℝ≥0∞ := fun ε => ∫⁻ x in {x | R x < ε}, ENNReal.ofReal (Dg x * (R x ^ q)⁻¹) *
    multiplierWeight 1 (Φ x) ∂μ with hJdef
  set K : ℝ → ℝ≥0∞ := fun ε => ∫⁻ x in {x | R x < ε}, gG x ∂μ with hKdef
  set T : ℝ → ℝ≥0∞ := fun ε => 2 * (ENNReal.ofReal 20 * (ENNReal.ofReal (32 * Bρ ^ 2) * I ε +
    ENNReal.ofReal (2 / Real.pi) * J ε)) + 2 * K ε with hTdef
  set L₀ : ℝ≥0∞ := 2 * (ENNReal.ofReal 20 * (ENNReal.ofReal (32 * Bρ ^ 2) *
    (ENNReal.ofReal CY * B))) with hL₀def
  have hL₀ : L₀ ≠ ⊤ := by
    rw [hL₀def]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin.ne)))
  have hIres : limsup I (𝓝[>] 0) ≤ ENNReal.ofReal CY * B := hres'
  have hlim : limsup T (𝓝[>] 0) ≤ L₀ := by
    have h2K : Tendsto (fun ε => 2 * K ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hK (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    have hcJ : Tendsto (fun ε => ENNReal.ofReal (2 / Real.pi) * J ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hdec (Or.inr ENNReal.ofReal_ne_top)
    calc limsup T (𝓝[>] 0)
        = limsup (fun ε => 2 * (ENNReal.ofReal 20 * (ENNReal.ofReal (32 * Bρ ^ 2) * I ε +
            ENNReal.ofReal (2 / Real.pi) * J ε))) (𝓝[>] 0) :=
          ENNReal.limsup_add_of_right_tendsto_zero h2K _
      _ = 2 * (ENNReal.ofReal 20 * limsup (fun ε => ENNReal.ofReal (32 * Bρ ^ 2) * I ε +
            ENNReal.ofReal (2 / Real.pi) * J ε) (𝓝[>] 0)) := by
          rw [ENNReal.limsup_const_mul_of_ne_top (by norm_num),
            ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
      _ = 2 * (ENNReal.ofReal 20 * limsup (fun ε => ENNReal.ofReal (32 * Bρ ^ 2) * I ε)
            (𝓝[>] 0)) := by
          rw [show (fun ε => ENNReal.ofReal (32 * Bρ ^ 2) * I ε +
              ENNReal.ofReal (2 / Real.pi) * J ε) = (fun ε => ENNReal.ofReal (32 * Bρ ^ 2) * I ε) +
              (fun ε => ENNReal.ofReal (2 / Real.pi) * J ε) from rfl,
            ENNReal.limsup_add_of_right_tendsto_zero hcJ]
      _ = 2 * (ENNReal.ofReal 20 * (ENNReal.ofReal (32 * Bρ ^ 2) * limsup I (𝓝[>] 0))) := by
          rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
      _ ≤ L₀ := by rw [hL₀def]; gcongr
  -- a sequence `ε_k → 0` along which `T(ε_k) < L₀ + 1/(k+1)`
  have hev : ∀ k : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < Real.exp (-4) ∧ I ε ≠ ⊤ ∧ J ε ≠ ⊤ ∧
      T ε < L₀ + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro k
    have hδ : (0 : ℝ≥0∞) < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), T ε < L₀ + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
      eventually_lt_of_limsup_lt (hlim.trans_lt (ENNReal.lt_add_right hL₀ hδ.ne'))
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), J ε < 1 := hdec.eventually (gt_mem_nhds one_pos)
    have hCB : ENNReal.ofReal CY * B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin.ne
    have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), I ε < ENNReal.ofReal CY * B + 1 :=
      eventually_lt_of_limsup_lt (hIres.trans_lt (ENNReal.lt_add_right hCB one_ne_zero))
    have h4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have h5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < Real.exp (-4) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (Real.exp_pos _))
    filter_upwards [h1, h2, h3, h4, h5] with ε e1 e2 e3 e4 e5
    exact ⟨e4, e5, ne_top_of_lt e3, ne_top_of_lt e2, e1⟩
  choose ε hε0 hε4 hIk hJk hTk using fun k => (hev k).exists
  -- the sections of Steps 2--4
  have hsec := fun k => exists_section_eps ωb hW.2.2 hW.1 hmn hR hb0 hbR hbK0 hRic hBρ hMR0 hMR
    hV hθV hΦ hgen' hM hGs hDg0 hDgW hDg (hε0 k) (hε4 k) (hIk k) (hJk k)
  choose s hsW hsint using hsec
  have hsT : ∀ k, ∫⁻ x, ENNReal.ofReal (‖s k x‖ ^ 2) * multiplierWeight 1 (Φ x) ∂μ ≤
      L₀ + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := fun k => (hsint k).trans (hTk k).le
  have hsT1 : ∀ k, ∫⁻ x, ENNReal.ofReal (‖s k x‖ ^ 2) * multiplierWeight 1 (Φ x) ∂μ ≤
      ENNReal.ofReal (L₀.toReal + 1) := by
    intro k
    refine (hsT k).trans ?_
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hL₀,
      ENNReal.ofReal_one]
    gcongr
    exact ENNReal.inv_le_one.mpr (by exact_mod_cast Nat.succ_pos k)
  -- a uniform bound in the supremum norm
  obtain ⟨c₁, hc₁, hc₁le⟩ := exists_mul_norm_sq_le_lintegral V hμ
  set Bd : ℝ := Real.exp M * (L₀.toReal + 1) / c₁ with hBd
  have hsbd : ∀ k, ‖s k‖ ≤ Real.sqrt Bd := by
    intro k
    have h1 : ENNReal.ofReal (c₁ * ‖s k‖ ^ 2) ≤
        ENNReal.ofReal (Real.exp M) * ENNReal.ofReal (L₀.toReal + 1) := by
      refine (hc₁le (s k)).trans ?_
      refine le_trans ?_ (mul_le_mul' le_rfl (hsT1 k))
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      have hw : ENNReal.ofReal (Real.exp (-M)) ≤ multiplierWeight 1 (Φ x) := by
        have := multiplierWeight_antitone zero_le_one (hM x)
        rwa [multiplierWeight_coe, one_mul] at this
      calc ENNReal.ofReal (‖s k x‖ ^ 2)
          = ENNReal.ofReal (Real.exp M) * (ENNReal.ofReal (‖s k x‖ ^ 2) *
              ENNReal.ofReal (Real.exp (-M))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_comm, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ _ := by gcongr
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    refine Real.le_sqrt_of_sq_le ?_
    rw [hBd, le_div_iff₀ hc₁]
    linarith
  -- a convergent subsequence
  obtain ⟨sL, -, φs, hφs, hlimS⟩ :=
    (isCompact_section_closedBall V.Fiber 0 (Real.sqrt Bd)).tendsto_subseq
      (x := s) fun k => mem_closedBall_zero_iff.mpr (hsbd k)
  have hpt : ∀ x, Tendsto (fun k => s (φs k) x) atTop (𝓝 (sL x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.mp hlimS)
    exact norm_apply_le_norm V (s (φs k) - sL) x
  have hsLW : ∀ y : W, sL y = f y := fun y =>
    tendsto_nhds_unique (hpt y) (tendsto_const_nhds.congr fun k =>
      ((hsW (φs k) y.1 y.2).trans (hGf y)).symm)
  refine ⟨sL, hsLW, ?_⟩
  -- Fatou
  have hFm : ∀ k, Measurable fun x => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) *
      multiplierWeight 1 (Φ x) := fun k =>
    (ENNReal.measurable_ofReal.comp ((continuous_norm_section V _).pow 2).measurable).mul hwm
  have hliminf : ∀ x, ENNReal.ofReal (‖sL x‖ ^ 2) * multiplierWeight 1 (Φ x) ≤
      liminf (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) * multiplierWeight 1 (Φ x)) atTop := by
    intro x
    by_cases h0 : ‖sL x‖ = 0
    · rw [h0]; simp
    have hn : Tendsto (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖sL x‖ ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (((continuous_norm.tendsto _).comp (hpt x)).pow 2)
    have hprod := ENNReal.Tendsto.mul_const (b := multiplierWeight 1 (Φ x)) hn (Or.inl (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity))
    exact hprod.liminf_eq.symm.le
  have hb : Tendsto (fun k => L₀ + ((φs k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 (L₀ + 0)) :=
    tendsto_const_nhds.add ((ENNReal.tendsto_inv_nat_nhds_zero.comp
      (tendsto_add_atTop_nat 1)).comp hφs.tendsto_atTop)
  calc ∫⁻ x, ENNReal.ofReal (‖sL x‖ ^ 2) * multiplierWeight 1 (Φ x) ∂μ
      ≤ ∫⁻ x, liminf (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) *
          multiplierWeight 1 (Φ x)) atTop ∂μ := lintegral_mono hliminf
    _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal (‖s (φs k) x‖ ^ 2) *
          multiplierWeight 1 (Φ x) ∂μ) atTop := lintegral_liminf_le hFm
    _ ≤ liminf (fun k => L₀ + ((φs k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k => hsT (φs k))
    _ = L₀ := by rw [hb.liminf_eq, add_zero]
    _ ≤ ENNReal.ofReal (C₀ + 1) * B := by
        have e : L₀ = ENNReal.ofReal C₀ * B := by
          rw [hL₀def, hC₀, ENNReal.ofReal_mul (p := 2) (by norm_num),
            ENNReal.ofReal_mul (p := 20) (by norm_num),
            ENNReal.ofReal_mul (p := 32 * Bρ ^ 2) (by positivity)]
          simp only [ENNReal.ofReal_ofNat]
          ring
        rw [e]
        gcongr
        linarith

/-- **`thm:OT_ext` for `Y = W`, conditional only on the residue hypothesis**: the book's
`OTExtAlong` holds for every closed connected submanifold `W` and every `δ > 0`, provided
`GentleWeightedNormalResidueHypothesis ω W` holds when `0 < dim W < dim X` (for `dim W = 0` and
`dim W = dim X` the theorem is unconditional). -/
theorem otExtAlong_of_residue (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    {δ : ℝ} (hδ : 0 < δ) (hres : 0 < m → m < n → GentleWeightedNormalResidueHypothesis ωb hW) :
    OTExtAlong ωb L T θ hW δ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact otExtAlong_of_dim_zero ωb L T hL hT θ hθ hW hδ
  · rcases (le_of_isClosedConnectedSubmanifold hW).lt_or_eq with hmn | hmn
    · exact otExtAlong_of_gentle ωb L T hL hT θ hθ hW hδ
        (gentleSubmanifoldExtensionAlong_of_residue ωb hW hmn (hres hm hmn))
    · subst hmn
      exact otExtAlong_of_eq ωb L T hL hT θ hθ hW hδ

variable (n X) in
/-- **`thm:OT_ext` in all dimensions, conditional only on the residue hypothesis** (FPT
`lem:gentle-weighted-normal-residue` for closed connected submanifolds `Y` with
`0 < dim Y < dim X`). -/
theorem otExtStatement_of_residue
    (hres : ∀ (ωb : KahlerBackground n X) (W : Set X) (m : ℕ)
      (hW : IsClosedConnectedSubmanifold n W m), 0 < m → m < n →
        GentleWeightedNormalResidueHypothesis ωb hW) :
    OTExtStatement n X := by
  intro ωb L T hL hT θ hθ W m hW δ hδ
  exact otExtAlong_of_residue ωb L T hL hT θ hθ hW hδ (hres ωb W m hW)

end SGPT.Trace.OTExt5

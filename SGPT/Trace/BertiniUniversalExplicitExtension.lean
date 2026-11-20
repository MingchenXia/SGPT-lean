import SGPT.Trace.BertiniUniversalRegularGluing
import SGPT.Trace.BertiniUniversalFiniteResidue

/-! Actual finite-weight extension at explicit normal/Ricci threshold,
for arbitrary nonempty closed regular W; connectedness is not assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
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
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2 SGPT.Trace.OTExt4 SGPT.Trace.OTExt5
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

def regularNormalPoleThreshold (n m : ℕ) (bK b : ℝ) : ℝ :=
  1 + bK / Real.pi + (((n - m : ℕ) : ℝ) + 2) * b

def regularFiniteGentleExtensionAt (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hclosed : IsClosed W) (hkn : m ≤ n)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m) (N₀ : ℝ) : Prop :=
  let hk : m ≤ n := hkn
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hreg
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hreg
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hclosed.isCompact
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  ∃ C : ℝ, 0 < C ∧
  ∀ (V : HermitianHolomorphicLineBundle.{0, 0} n X), IsSourceSmoothHermitianMetric V →
  ∀ θV : ClosedRealOneOneForm n X, IsOwnFirstChernForm V θV →
  ∀ Φ : X → EReal, IsThetaPshPotential (θV - N₀ • ωb.form).val Φ →
    (∃ (c : ℚ) (𝔞 : GermIdeal n X), HasGentleAnalyticSingularitiesOfType (n := n) Φ c 𝔞) →
    (∀ y : W, Φ y ≠ ⊥) →
  ∀ f : (y : W) → V.Fiber y,
    IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => Φ y) f →
  ∃ s : HolomorphicSections (n := n) V.Fiber, (∀ y : W, s y = f y) ∧
    ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight 1 (Φ x)
        ∂(IntegrationCurrent.kahlerVolume ωb) ≤
      ENNReal.ofReal C * ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (Φ y)
        ∂(IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hreg ωb))

private theorem regularPole_measure_zero {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : IsSmoothPositiveVolume (n := n) μ) {W : Set X} {m : ℕ}
    (hclosed : IsClosed W) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m) (hmn : m < n) {ωb : KahlerBackground n X}
    {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R) : μ W = 0 := by
  have hq : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hmn
  have hfin := lintegral_multiplierWeight_logPole_lt_top hμ hreg hclosed.isCompact hmn hR
    (c := 1 / 2) (by norm_num) (by linarith)
  by_contra hne
  refine hfin.ne (top_le_iff.mp ?_)
  calc (⊤ : ℝ≥0∞) = ∫⁻ _ in W, ⊤ ∂μ := by rw [setLIntegral_const, ENNReal.top_mul hne]
    _ ≤ ∫⁻ x in W, multiplierWeight (1 / 2) (logPole R x) ∂μ := by
        refine setLIntegral_mono' hclosed.measurableSet fun x hx => ?_
        rw [(hR.pole.eq_bot_iff x).mpr hx, multiplierWeight_bot (by norm_num)]
    _ ≤ _ := setLIntegral_le_lintegral _ _

theorem regularFiniteGentle_extensionAt_of_prescribed_pole
    (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hclosed : IsClosed W) (hkn : m ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    (hWne : W.Nonempty) (hmn : m < n) (R : X → ℝ) (hR : IsGlobalNormalPole ωb W R)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hbR : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
      ∀ v : ComplexModel n,
        0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi + b * kahlerQuad ωb c z v)
    (bK : ℝ) (hbK0 : 0 ≤ bK)
    (hRic : ∀ (c : ComplexChart n X) (ρ : ComplexModel n → ℝ),
      IsChartDensity (IntegrationCurrent.kahlerVolume ωb) c ρ →
      ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
        leviForm (fun y => Real.log (ρ y)) z v ≤ bK * kahlerQuad ωb c z v) :
    regularFiniteGentleExtensionAt ωb hclosed hkn hreg (regularNormalPoleThreshold n m bK b) := by
  unfold regularFiniteGentleExtensionAt
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hreg
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hreg
  have : CompactSpace W := isCompact_iff_compactSpace.mp hclosed.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hres : regularFiniteWeightResidueEstimate ωb hclosed hk hreg R := by
    obtain ⟨d,rfl⟩ : ∃ d, n = m + d := ⟨n - m,(Nat.add_sub_of_le hk).symm⟩
    exact regularFiniteWeight_normalResidue_aux ωb hclosed hreg R hR
  obtain ⟨CY,hCY,hresR⟩ := hres
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  set μW := IntegrationCurrent.kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hreg ωb) with hμWdef
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hμW := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hreg ωb)
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
  refine ⟨C₀ + 1, by positivity, fun V hV θV hθV Φ hΦ hgen hΦW f hf => ?_⟩
  change IsThetaPshPotential (θV - N₀ • ωb.form).val Φ at hΦ
  obtain ⟨c₀, 𝔞, hgen'⟩ := hgen
  have hΦt : ∀ x, Φ x ≠ ⊤ := hΦ.1.quasiPlurisubharmonic.ne_top
  have hΦm : Measurable Φ := hΦ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hwm : Measurable fun x => multiplierWeight 1 (Φ x) :=
    (multiplierWeight_antitone zero_le_one).measurable.comp hΦm
  have hΦθ : IsThetaPshPotential θV.val Φ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hΦ
      (KahlerDomination.isSemipositive_smul ωb.isSemipositive hN₀0.le)
    rwa [sub_add_cancel] at h
  have : Nonempty X := ⟨hWne.choose⟩
  obtain ⟨M, hM⟩ := exists_real_upper_bound_of_upperSemicontinuous
    hΦ.1.quasiPlurisubharmonic.upperSemicontinuous hΦt
  -- the gluing (`lem:critical-gain-initial-gluing`)
  have hglue := regular_criticalGainInitialGluingAlong ωb hclosed hk hreg hWne hmn hR
  unfold regularCriticalGainInitialGluingAlong at hglue
  obtain ⟨κ, hκ, G, Dg, hGl, hGs, hGf, hDg0, hDgW, hDg, hstr, hdec⟩ :=
    hglue V hV θV hθV Φ hΦθ f hf
  -- the residue hypothesis
  have hres' := hresR V hV θV hθV Φ hΦθ ⟨c₀, 𝔞, hgen'⟩ hΦW f hf κ hκ G hGl
  -- the norm of `f`
  set B : ℝ≥0∞ := ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (Φ y) ∂μW with hB
  have hBfin : B < ⊤ := SGPT.Trace.OTExt3.lintegral_lt_top_of_isAlongMultiplierSection V.Fiber hμW
    one_pos (hΦm.comp continuous_subtype_val.measurable) hf
  -- `∫_{R < ε} |G|² e^{-Φ} → 0`
  have hμW0 : μ W = 0 := regularPole_measure_zero hμ hclosed hreg hmn hR
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
      rw [hν, withDensity_apply _ hclosed.measurableSet, Measure.restrict_eq_zero.mpr hμW0,
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
  have hsec := fun k => exists_section_eps ωb hreg hclosed hmn hR hb0 hbR hbK0 hRic hBρ hMR0 hMR
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

theorem regularFiniteGentle_extensionAt_all_members
    (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hclosed : IsClosed W) (hkn : m ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    (hmn : m < n) (R : X → ℝ) (hR : IsGlobalNormalPole ωb W R)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hbR : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
      ∀ v : ComplexModel n,
        0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi + b * kahlerQuad ωb c z v)
    (bK : ℝ) (hbK0 : 0 ≤ bK)
    (hRic : ∀ (c : ComplexChart n X) (ρ : ComplexModel n → ℝ),
      IsChartDensity (IntegrationCurrent.kahlerVolume ωb) c ρ →
      ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
        leviForm (fun y => Real.log (ρ y)) z v ≤ bK * kahlerQuad ωb c z v) :
    regularFiniteGentleExtensionAt ωb hclosed hkn hreg (regularNormalPoleThreshold n m bK b) := by
  by_cases hWne : W.Nonempty
  · exact regularFiniteGentle_extensionAt_of_prescribed_pole ωb hclosed hkn hreg hWne hmn R hR b hb0 hbR bK hbK0 hRic
  · unfold regularFiniteGentleExtensionAt
    intro hk
    let := chartedSpace hk hreg
    let := isComplexManifold_chartedSpace hk hreg
    let := isCompact_iff_compactSpace.mp hclosed.isCompact
    let : MeasurableSpace W := borel W
    let : BorelSpace W := ⟨rfl⟩
    refine ⟨1,by norm_num,?_⟩
    intro V _hV θV _hθV Φ _hΦ _hgen _hFinite f _hf
    refine ⟨0,fun y => False.elim (hWne ⟨y.val,y.property⟩),?_⟩
    change (∫⁻ x, ENNReal.ofReal (‖(0 : V.Fiber x)‖ ^ 2) * multiplierWeight 1 (Φ x)
      ∂IntegrationCurrent.kahlerVolume ωb) ≤ _
    simp only [norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),ENNReal.ofReal_zero,zero_mul,lintegral_zero]
    exact zero_le

theorem exists_regularFiniteGentle_extension_threshold (ωb : KahlerBackground n X) :
    ∃ bK : ℝ, 0 ≤ bK ∧ ∀ b : ℝ, 0 ≤ b →
      ∀ (W : Set X) (m : ℕ) (hclosed : IsClosed W) (hkn : m ≤ n)
        (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m), m < n →
      ∀ (R : X → ℝ), IsGlobalNormalPole ωb W R →
      (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
        ∀ v : ComplexModel n,
          0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi + b * kahlerQuad ωb c z v) →
      regularFiniteGentleExtensionAt ωb hclosed hkn hreg (regularNormalPoleThreshold n m bK b) := by
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  obtain ⟨bK,hbK,hRic⟩ := exists_leviForm_log_chartDensity_le ωb hμ
  refine ⟨bK,hbK,?_⟩
  intro b hb W m hclosed hkn hreg hmn R hR hbR
  exact regularFiniteGentle_extensionAt_all_members ωb hclosed hkn hreg hmn R hR b hb hbR bK hbK hRic

end SGPT.Trace.BertiniUniversal

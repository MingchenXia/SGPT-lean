import SGPT.Trace.BertiniUniversalSmoothExtension
import SGPT.Trace.BertiniGlobalRealApproximation
import SGPT.Trace.BertiniSectionMultiplication
import SGPT.Bergman.SourceMultiplierSectionGlobalMass

/-! Actual original singular multiplier extension from manufactured smooth
upper weights; one coarse loss and Ricci bound BEFORE ALL regular members. -/
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
  SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2 SGPT.Trace.OTExt4 SGPT.Trace.OTExt5
open SGPT.Trace.Bertini SGPT.Trace.BertiniGlobalRealApproximation
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

private theorem actualSmooth_upperWeight_multiplier_limit
    (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hclosed : IsClosed W) (hkn : m ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m) (N₀ : ℝ)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (u : ℕ → X → ℝ) (hu : ∀ j, ChartSmooth (n := n) (u j))
    (hanti : ∀ x, Antitone (fun j => u j x)) (hdom : ∀ j x, φ x ≤ (u j x : EReal))
    (hlim : ∀ x, Tendsto (fun j => (u j x : EReal)) atTop (𝓝 (φ x)))
    (hExt : regularSmoothExtensionAt ωb hclosed hkn hreg N₀)
    (V : HermitianHolomorphicLineBundle.{0,0} n X) (hV : IsSourceSmoothHermitianMetric V)
    (θV : ClosedRealOneOneForm n X) (hθV : IsOwnFirstChernForm V θV)
    (huj : ∀ j, IsThetaPshPotential (θV - N₀ • ωb.form).val (fun x => (u j x : EReal))) :
    let hk : m ≤ n := hkn
    letI := chartedSpace hk hreg
    letI := isComplexManifold_chartedSpace hk hreg
    ∀ f : (y : W) → V.Fiber y,
      IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => φ y.val) f →
      ∃ s : nativeMultiplierSections V φ, ∀ y : W, s.val y.val = f y := by
  intro hk
  let := chartedSpace hk hreg
  let := isComplexManifold_chartedSpace hk hreg
  let := isCompact_iff_compactSpace.mp hclosed.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  intro f hf
  obtain ⟨C,hC,hgen⟩ := hExt
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  set μW := IntegrationCurrent.kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hreg ωb) with hμWdef
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hμW := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hreg ωb)
  have hφm : Measurable φ := hφ.1.upperSemicontinuous.measurable
  have hum (j : ℕ) : Measurable (fun x => (u j x : EReal)) :=
    (huj j).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hfu (j : ℕ) : IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => (u j y.val : EReal)) f :=
    isAlongMultiplierSection_of_le V.Fiber (hum j) (fun y => hdom j y.val) hf
  set B : ℝ≥0∞ := ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (φ y.val) ∂μW with hBdef
  have hBfin : B < ⊤ := SGPT.Trace.OTExt3.lintegral_lt_top_of_isAlongMultiplierSection V.Fiber hμW
    one_pos (hφm.comp continuous_subtype_val.measurable) hf
  have hBj (j : ℕ) : (∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (u j y.val) ∂μW) ≤ B :=
    lintegral_mono fun y => by gcongr; exact multiplierWeight_antitone zero_le_one (hdom j y.val)
  choose s hsW hsint using fun j : ℕ => hgen V hV θV hθV (u j) (hu j) (huj j) f (hfu j)
  have hsB : ∀ j, (∫⁻ x, ENNReal.ofReal (‖s j x‖ ^ 2) * multiplierWeight 1 (u j x) ∂μ) ≤
      ENNReal.ofReal C * B := fun j => (hsint j).trans (by gcongr; exact hBj j)
  have hu0 : Continuous (u 0) := SGPT.Trace.TwistedL2.continuous_of_chartSmooth (hu 0)
  obtain ⟨M₀,hM₀⟩ := isCompact_univ.exists_bound_of_continuousOn hu0.continuousOn
  have huM : ∀ j x, (u j x : EReal) ≤ M₀ := by
    intro j x
    apply EReal.coe_le_coe_iff.mpr
    exact (hanti x (Nat.zero_le j)).trans ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM₀ x (mem_univ x))))
  obtain ⟨c₀,hc₀,hc₀le⟩ := exists_mul_norm_sq_le_lintegral V hμ
  set Bd : ℝ := Real.exp M₀ * (C * B.toReal) / c₀ with hBd
  have hsbd : ∀ j, ‖s j‖ ≤ Real.sqrt Bd := by
    intro j
    have h1 : ENNReal.ofReal (c₀ * ‖s j‖ ^ 2) ≤ ENNReal.ofReal (Real.exp M₀) * (ENNReal.ofReal C * B) := by
      refine (hc₀le (s j)).trans ?_
      refine le_trans ?_ (mul_le_mul' le_rfl (hsB j))
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      have hw : ENNReal.ofReal (Real.exp (-M₀)) ≤ multiplierWeight 1 (u j x) := by
        have := multiplierWeight_antitone zero_le_one (huM j x)
        rwa [multiplierWeight_coe,one_mul] at this
      calc ENNReal.ofReal (‖s j x‖ ^ 2)
          = ENNReal.ofReal (Real.exp M₀) * (ENNReal.ofReal (‖s j x‖ ^ 2) * ENNReal.ofReal (Real.exp (-M₀))) := by
            rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_comm,mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
        _ ≤ _ := by gcongr
    have hfin : ENNReal.ofReal (Real.exp M₀) * (ENNReal.ofReal C * B) = ENNReal.ofReal (Real.exp M₀ * (C * B.toReal)) := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul hC.le,ENNReal.ofReal_toReal hBfin.ne]
    rw [hfin,ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    refine Real.le_sqrt_of_sq_le ?_
    rw [hBd,le_div_iff₀ hc₀]
    linarith
  obtain ⟨sL,-,φs,hφs,hsLim⟩ := (isCompact_section_closedBall V.Fiber 0 (Real.sqrt Bd)).tendsto_subseq
    (x := s) fun j => mem_closedBall_zero_iff.mpr (hsbd j)
  have hpt : ∀ x, Tendsto (fun k => s (φs k) x) atTop (𝓝 (sL x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (tendsto_iff_norm_sub_tendsto_zero.mp hsLim)
    exact norm_apply_le_norm V (s (φs k) - sL) x
  have hsLW : ∀ y : W, sL y.val = f y := fun y =>
    tendsto_nhds_unique (hpt y.val) (tendsto_const_nhds.congr fun k => (hsW (φs k) y).symm)
  have hFm : ∀ k, Measurable fun x => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) * multiplierWeight 1 (u (φs k) x) :=
    fun k => (ENNReal.measurable_ofReal.comp ((continuous_norm_section V _).pow 2).measurable).mul
      ((multiplierWeight_antitone zero_le_one).measurable.comp (hum _))
  have hliminf : ∀ x, ENNReal.ofReal (‖sL x‖ ^ 2) * multiplierWeight 1 (φ x) ≤
      liminf (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) * multiplierWeight 1 (u (φs k) x)) atTop := by
    intro x
    by_cases h0 : ‖sL x‖ = 0
    · rw [h0]; simp
    have hn : Tendsto (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2)) atTop (𝓝 (ENNReal.ofReal (‖sL x‖ ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (((continuous_norm.tendsto _).comp (hpt x)).pow 2)
    have hv : Tendsto (fun k => (u (φs k) x : EReal)) atTop (𝓝 (φ x)) := (hlim x).comp hφs.tendsto_atTop
    have hw : Tendsto (fun k => multiplierWeight 1 (u (φs k) x)) atTop (𝓝 (multiplierWeight 1 (φ x))) :=
      ((continuous_multiplierWeight one_pos).tendsto _).comp hv
    have hprod := ENNReal.Tendsto.mul hn (Or.inl (by rw [ne_eq,ENNReal.ofReal_eq_zero,not_le]; positivity)) hw (Or.inr ENNReal.ofReal_ne_top)
    exact hprod.liminf_eq.symm.le
  have hbound : (∫⁻ x, ENNReal.ofReal (‖sL x‖ ^ 2) * multiplierWeight 1 (φ x) ∂μ) ≤ ENNReal.ofReal C * B := by
    calc
      _ ≤ ∫⁻ x, liminf (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) * multiplierWeight 1 (u (φs k) x)) atTop ∂μ := lintegral_mono hliminf
      _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal (‖s (φs k) x‖ ^ 2) * multiplierWeight 1 (u (φs k) x) ∂μ) atTop := lintegral_liminf_le hFm
      _ ≤ ENNReal.ofReal C * B := liminf_le_of_frequently_le' (Frequently.of_forall fun k => hsB _)
  have hglobal : (∫⁻ x, originalSectionDensity V.Fiber φ 1 sL x ∂μ) < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBfin)
  have hmem : sL ∈ fullHolomorphicIdealSections (n := n) V.Fiber (sourceDegreeMultiplierIdeal (n := n) 1 φ) := by
    exact (fullHolomorphicDegreeIdealSections_iff_finite_integral V.Fiber 1 hφ sL hμ).mpr (by simpa only [Nat.cast_one] using hglobal)
  exact ⟨⟨sL,hmem⟩,hsLW⟩

theorem exists_regular_original_multiplier_extension_threshold
    (ωb : KahlerBackground n X) (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := n) φ) :
    ∃ C bK : ℝ, 0 < C ∧ 0 ≤ bK ∧ ∀ b : ℝ, 0 ≤ b →
      ∀ (W : Set X) (m : ℕ) (_hclosed : IsClosed W) (hkn : m ≤ n)
        (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m), m < n →
      ∀ (R : X → ℝ), IsGlobalNormalPole ωb W R →
      (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
        ∀ v : ComplexModel n,
          0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi + b * kahlerQuad ωb c z v) →
      ∀ (V : HermitianHolomorphicLineBundle.{0,0} n X), IsSourceSmoothHermitianMetric V →
      ∀ (θV : ClosedRealOneOneForm n X), IsOwnFirstChernForm V θV →
      (θV - (regularNormalPoleThreshold n m bK b + C) • ωb.form).val.IsSemipositive →
      let hk : m ≤ n := hkn
      letI := chartedSpace hk hreg
      letI := isComplexManifold_chartedSpace hk hreg
      ∀ f : (y : W) → V.Fiber y,
        IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => φ y.val) f →
        ∃ s : nativeMultiplierSections V φ, ∀ y : W, s.val y.val = f y := by
  obtain ⟨C,u,hC,hu,hanti,hdom,hlim,hpsh⟩ := exists_original_global_qpsh_real_approximation ωb φ hφ
  obtain ⟨bK,hbK,hExt⟩ := exists_regularSmooth_extension_threshold ωb
  refine ⟨C,bK,hC,hbK,?_⟩
  intro b hb W m hclosed hkn hreg hmn R hR hbR V hV θV hθV hmargin
  let N₀ := regularNormalPoleThreshold n m bK b
  have hU : ∀ j, IsThetaPshPotential (θV - N₀ • ωb.form).val (fun x => (u j x : EReal)) := by
    intro j
    apply SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hpsh j)
    have heq : (θV - N₀ • ωb.form) - C • ωb.form = θV - (N₀ + C) • ωb.form := by module
    rw [heq]
    exact hmargin
  exact actualSmooth_upperWeight_multiplier_limit ωb hclosed hkn hreg N₀ φ hφ u hu hanti hdom hlim
    (hExt b hb W m hclosed hkn hreg hmn R hR hbR) V hV θV hθV hU

end SGPT.Trace.BertiniUniversal

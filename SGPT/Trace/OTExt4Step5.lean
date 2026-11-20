import SGPT.Trace.OTExt4Glue
import SGPT.Trace.OTExt3Corollary
import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.IGood.DXLowTrace
import SGPT.Foundations.Analysis.Pending.ActualAllDimensionGentleQea

/-!
# Step 5 of FPT `thm:compact-submanifold-extension`: from gentle weights to arbitrary weights

Blueprint `claude-ot-ext4.tex`, nodes `claude-ot-ext4:gentle`, `claude-ot-ext4:step5`.  Xia,
*Foundations of pluripotential theory*, q07, proof of `thm:compact-submanifold-extension`,
Step 5.

* `GentleSubmanifoldExtensionAlong ω W` (statement): the conclusion of Steps 1--4, i.e. FPT
  `thm:compact-submanifold-extension` for weights `Φ` with gentle analytic singularities (TN's
  `HasGentleAnalyticSingularitiesOfType`, the class produced by the gentle quasi-equisingular
  approximation) and `c₁(V, h₀ e^{-Φ}) ≥ N₀ ω`.
* `compactSubmanifoldExtensionAlong_of_gentle`: Step 5.  With `N = N₀ + 1`, the gentle
  quasi-equisingular approximation `Φ_j ↓ φ` (`exists_all_dimension_gentle_qea`, applied to
  `φ ∈ PSH(X, c₁(V, h₀) - N ω)`) has `c₁(V, h₀ e^{-Φ_j}) ≥ N₀ ω` for large `j`; `f` lies in
  `𝓘(Φ_j|_W)` with a smaller norm; the gentle case gives `s_j`; they are bounded in `L²(h₀)`
  (`Φ_j ≤ Φ_{j₀} ≤ M`), hence in the supremum norm of the finite-dimensional `H⁰(X, V)`
  (`exists_mul_norm_sq_le_lintegral`); a subsequence converges uniformly to `s` with `s|_W = f`,
  and Fatou's lemma gives the bound with the same constant.
* `otExtAlong_of_gentle`: hence the book's `thm:OT_ext` (`OTExtAlong`) for `W` follows from
  `GentleSubmanifoldExtensionAlong ω W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt4

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
  SGPT.Bergman.QuantizationDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-! ### `L²` and supremum norms on `H⁰(X, V)` -/

section Norms

variable (V : HermitianHolomorphicLineBundle.{0, 0} n X)

theorem continuous_norm_section (s : HolomorphicSections (n := n) V.Fiber) :
    Continuous fun x => ‖s x‖ :=
  ContinuousFiberNorm.continuous.comp s.contMDiff.continuous

theorem norm_apply_le_norm (s : HolomorphicSections (n := n) V.Fiber) (x : X) : ‖s x‖ ≤ ‖s‖ := by
  rw [norm_section_eq_sectionSize]; exact norm_apply_le_sectionSize V.Fiber s x

/-- **Equivalence of the `L²` and supremum norms on `H⁰(X, V)`** (finite dimension): there is
`c > 0` with `c ‖s‖²_∞ ≤ ∫ |s|² dμ`. -/
theorem exists_mul_norm_sq_le_lintegral {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : IsSmoothPositiveVolume (n := n) μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : HolomorphicSections (n := n) V.Fiber,
      ENNReal.ofReal (c * ‖s‖ ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ 2) ∂μ := by
  have : μ.IsOpenPosMeasure := SGPT.IGood.DXLow.isOpenPosMeasure_of_isSmoothPositiveVolume hμ
  set Fn : HolomorphicSections (n := n) V.Fiber → ℝ := fun s => ∫ x, ‖s x‖ ^ 2 ∂μ with hFn
  have hint : ∀ s : HolomorphicSections (n := n) V.Fiber, Integrable (fun x => ‖s x‖ ^ 2) μ :=
    fun s => ((continuous_norm_section V s).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlint : ∀ s : HolomorphicSections (n := n) V.Fiber,
      ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ 2) ∂μ = ENNReal.ofReal (Fn s) := fun s =>
    (ofReal_integral_eq_lintegral_ofReal (hint s) (Eventually.of_forall fun x => by positivity)).symm
  -- `Fn` is Lipschitz on the unit sphere
  have hlip : ∀ s ∈ sphere (0 : HolomorphicSections (n := n) V.Fiber) 1,
      ∀ t ∈ sphere (0 : HolomorphicSections (n := n) V.Fiber) 1,
        dist (Fn s) (Fn t) ≤ (2 * μ.real univ) * dist s t := by
    intro s hs t ht
    rw [mem_sphere_zero_iff_norm] at hs ht
    rw [Real.dist_eq, hFn, ← integral_sub (hint s) (hint t)]
    have hpt : ∀ x, ‖‖s x‖ ^ 2 - ‖t x‖ ^ 2‖ ≤ 2 * dist s t := by
      intro x
      have h1 : ‖s x‖ ≤ 1 := hs ▸ norm_apply_le_norm V s x
      have h2 : ‖t x‖ ≤ 1 := ht ▸ norm_apply_le_norm V t x
      have h3 : |‖s x‖ - ‖t x‖| ≤ dist s t := by
        rw [dist_eq_norm]
        refine (abs_norm_sub_norm_le _ _).trans ?_
        have := norm_apply_le_norm V (s - t) x
        simpa using this
      rw [Real.norm_eq_abs, show ‖s x‖ ^ 2 - ‖t x‖ ^ 2 = (‖s x‖ - ‖t x‖) * (‖s x‖ + ‖t x‖) by ring,
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖s x‖ + ‖t x‖)]
      nlinarith [abs_nonneg (‖s x‖ - ‖t x‖), norm_nonneg (s x), norm_nonneg (t x)]
    calc ‖∫ x, ‖s x‖ ^ 2 - ‖t x‖ ^ 2 ∂μ‖ ≤ 2 * dist s t * μ.real univ :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall hpt)
      _ = 2 * μ.real univ * dist s t := by ring
  have hcont : ContinuousOn Fn (sphere (0 : HolomorphicSections (n := n) V.Fiber) 1) :=
    (LipschitzOnWith.of_dist_le' hlip).continuousOn
  have hcpt : IsCompact (sphere (0 : HolomorphicSections (n := n) V.Fiber) 1) :=
    (isCompact_section_closedBall V.Fiber 0 1).of_isClosed_subset isClosed_sphere
      sphere_subset_closedBall
  -- `Fn > 0` on the sphere
  have hpos : ∀ s : HolomorphicSections (n := n) V.Fiber, s ≠ 0 → 0 < Fn s := by
    intro s hs
    refine lt_of_le_of_ne (integral_nonneg fun x => by positivity) fun h => hs ?_
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) (hint s)).mp h.symm
    have heq : (fun x => ‖s x‖ ^ 2) = fun _ => (0 : ℝ) :=
      Continuous.ae_eq_iff_eq μ ((continuous_norm_section V s).pow 2) continuous_const |>.mp hae
    ext x
    have h2 : ‖s x‖ ^ 2 = 0 := congrFun heq x
    have : ‖s x‖ = 0 := by nlinarith [norm_nonneg (s x)]
    simpa using this
  rcases (sphere (0 : HolomorphicSections (n := n) V.Fiber) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun s => ?_⟩
    have hs0 : ‖s‖ = 0 := by
      by_contra h
      have hpos' : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
      have : (‖s‖⁻¹ : ℂ) • s ∈ sphere (0 : HolomorphicSections (n := n) V.Fiber) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hpos', inv_mul_cancel₀ hpos'.ne']
      rw [he] at this; exact this
    rw [hs0]; simp
  obtain ⟨s₀, hs₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  have hs₀0 : s₀ ≠ 0 := fun h => by
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at hs₀; exact zero_ne_one hs₀
  refine ⟨Fn s₀, hpos s₀ hs₀0, fun s => ?_⟩
  rw [hlint]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hs : s = 0
  · rw [hs, norm_zero]; simp [hFn]
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  set u : HolomorphicSections (n := n) V.Fiber := (‖s‖⁻¹ : ℂ) • s with hu
  have hu1 : u ∈ sphere (0 : HolomorphicSections (n := n) V.Fiber) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hspos, inv_mul_cancel₀ hspos.ne']
  have hFu : Fn s = ‖s‖ ^ 2 * Fn u := by
    rw [hFn, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖s x‖ ^ 2 = ‖s‖ ^ 2 * ‖((‖s‖⁻¹ : ℂ) • s) x‖ ^ 2
    rw [show (((‖s‖⁻¹ : ℂ) • s : HolomorphicSections (n := n) V.Fiber) x) = (‖s‖⁻¹ : ℂ) • s x from rfl,
      norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos, mul_pow,
      ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hspos.ne', one_pow, one_mul]
  rw [hFu]
  have : Fn s₀ ≤ Fn u := hmin hu1
  nlinarith [sq_nonneg ‖s‖]

end Norms

/-! ### The gentle case and Step 5 -/

/-- **Steps 1--4 of FPT `thm:compact-submanifold-extension`** (statement): the theorem for weights
`Φ` with gentle analytic singularities and `c₁(V, h₀ e^{-Φ}) ≥ N₀ ω`, with constants `N₀, C`
depending only on `X, ω, W`. -/
def GentleSubmanifoldExtensionAlong (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) : Prop :=
  let hk : m ≤ n := le_of_isClosedConnectedSubmanifold hW
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  ∃ N₀ C : ℝ, 0 < N₀ ∧ 0 < C ∧
  ∀ (V : HermitianHolomorphicLineBundle.{0, 0} n X), IsSourceSmoothHermitianMetric V →
  ∀ θV : ClosedRealOneOneForm n X, IsOwnFirstChernForm V θV →
  ∀ Φ : X → EReal, IsThetaPshPotential (θV - N₀ • ωb.form).val Φ →
    (∃ (c : ℚ) (𝔞 : GermIdeal n X), HasGentleAnalyticSingularitiesOfType (n := n) Φ c 𝔞) →
    (∃ y ∈ W, Φ y ≠ ⊥) →
  ∀ f : (y : W) → V.Fiber y,
    IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => Φ y) f →
  ∃ s : HolomorphicSections (n := n) V.Fiber, (∀ y : W, s y = f y) ∧
    ∫⁻ x, ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight 1 (Φ x)
        ∂(IntegrationCurrent.kahlerVolume ωb) ≤
      ENNReal.ofReal C * ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (Φ y)
        ∂(IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb))

/-- Sections in `𝓘(u)` along `W` lie in `𝓘(U'|_W)` for a larger measurable weight `U' ≥ u`. -/
theorem isAlongMultiplierSection_of_le {m : ℕ} {W : Set X} [ChartedSpace (ComplexModel m) W]
    [IsComplexManifold m W] (V : X → Type) [∀ x, NormedAddCommGroup (V x)]
    [∀ x, NormedSpace ℂ (V x)] [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V]
    [VectorBundle ℂ ℂ V] {u : W → EReal} {U' : X → EReal} (hU' : Measurable U')
    (hle : ∀ y : W, u y ≤ U' y) {s : (y : W) → V y}
    (hs : IsAlongMultiplierSection V (m := m) 1 u s) :
    IsAlongMultiplierSection V (m := m) 1 (fun y : W => U' y) s := by
  intro y
  obtain ⟨hhol, hc, U, hU, hyU, hfU, -, hfin⟩ := hs y
  set e := complexChartAt (n := m) y
  have hUT : IsOpen (U ∩ e.val.target) := hU.inter e.val.open_target
  refine ⟨hhol, hc, U ∩ e.val.target, hUT,
    ⟨hyU, e.val.map_source (mem_complexChartAt_source y)⟩, hfU.mono inter_subset_left, ?_, ?_⟩
  · refine AEMeasurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      exact ((continuous_norm.comp_continuousOn (hfU.continuousOn.mono inter_subset_left)).pow 2
        |>.aemeasurable hUT.measurableSet)
    · refine (multiplierWeight_antitone zero_le_one).measurable.comp_aemeasurable ?_
      have hm : Measurable fun w : X => ((1 : ℝ) : EReal) * U' w :=
        (measurable_const_mul _).comp hU'
      exact hm.comp_aemeasurable ((continuous_subtype_val.comp_continuousOn
        (e.val.continuousOn_symm.mono inter_subset_right)).aemeasurable hUT.measurableSet)
  · refine lt_of_le_of_lt ((lintegral_mono fun z => ?_).trans
      (lintegral_mono_set inter_subset_left)) hfin
    simp only [multiplierDensity, chartFunction]
    gcongr
    exact multiplierWeight_antitone zero_le_one
      (mul_le_mul_of_nonneg_left (hle _) (by norm_num))

/-- **Step 5 of FPT `thm:compact-submanifold-extension`**: the gentle case implies the general
case (`N = N₀ + 1`, same `C`). -/
theorem compactSubmanifoldExtensionAlong_of_gentle (ωb : KahlerBackground n X) {W : Set X}
    {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (hG : GentleSubmanifoldExtensionAlong ωb hW) : CompactSubmanifoldExtensionAlong ωb hW := by
  unfold GentleSubmanifoldExtensionAlong at hG
  unfold CompactSubmanifoldExtensionAlong
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  obtain ⟨N₀, C, hN₀, hC, hgen⟩ := hG
  refine ⟨N₀ + 1, C, by linarith, hC, fun V hV θV hθV φ hφ hφW f hf => ?_⟩
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  set μW := IntegrationCurrent.kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) with hμWdef
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hμW := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
  obtain ⟨x₀, hx₀⟩ := hW.2.1.nonempty
  have : Nonempty X := ⟨x₀⟩
  have hφm : Measurable φ := hφ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  -- the gentle quasi-equisingular approximation
  obtain ⟨ε, v, hqea, hgentle⟩ := ActualAllDimensionGentleQea.exists_all_dimension_gentle_qea ωb
    (θV - (N₀ + 1) • ωb.form) hφ
  obtain ⟨-, ⟨hε0, hεanti, hεlim⟩, hvpsh, -, ⟨hvanti, hvlim⟩, -⟩ := hqea
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ∀ j, j₀ ≤ j → ε j ≤ 1 :=
    (eventually_atTop.mp (hεlim.eventually (gt_mem_nhds one_pos))).imp fun j₀ h j hj => (h j hj).le
  have hφv : ∀ j x, φ x ≤ v j x := fun j x => (hvanti x).le_of_tendsto (hvlim x) j
  have hvN : ∀ j, j₀ ≤ j → IsThetaPshPotential (θV - N₀ • ωb.form).val (v j) := by
    intro j hj
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hvpsh j) ?_
    have hsemi : ((1 - ε j) • ωb.form).val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul ωb.isSemipositive (by linarith [hj₀ j hj])
    have heq : (θV - N₀ • ωb.form) - (θV - (N₀ + 1) • ωb.form + ε j • ωb.form) =
        (1 - ε j) • ωb.form := by module
    rw [heq]; exact hsemi
  have hvm : ∀ j, Measurable (v j) := fun j =>
    (hvpsh j).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hfv : ∀ j, IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => v j y) f := fun j =>
    isAlongMultiplierSection_of_le V.Fiber (hvm j) (fun y => hφv j y) hf
  have hvW : ∀ j, ∃ y ∈ W, v j y ≠ ⊥ := fun j => by
    obtain ⟨y, hy, hyb⟩ := hφW
    exact ⟨y, hy, fun h => hyb (le_bot_iff.mp (h ▸ hφv j y))⟩
  -- the norm of `f`
  set B : ℝ≥0∞ := ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (φ y) ∂μW with hBdef
  have hBfin : B < ⊤ := SGPT.Trace.OTExt3.lintegral_lt_top_of_isAlongMultiplierSection V.Fiber hμW
    one_pos (hφm.comp continuous_subtype_val.measurable) hf
  have hBj : ∀ j, ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (v j y) ∂μW ≤ B :=
    fun j => lintegral_mono fun y => by
      gcongr; exact multiplierWeight_antitone zero_le_one (hφv j y)
  -- the gentle case for `v (j₀ + j)`
  choose s hsW hsint using fun j : ℕ => hgen V hV θV hθV (v (j₀ + j)) (hvN _ (by omega))
    ⟨_, _, hgentle (j₀ + j)⟩ (hvW _) f (hfv _)
  have hsB : ∀ j, ∫⁻ x, ENNReal.ofReal (‖s j x‖ ^ 2) * multiplierWeight 1 (v (j₀ + j) x) ∂μ ≤
      ENNReal.ofReal C * B := fun j => (hsint j).trans (by gcongr; exact hBj _)
  -- a uniform bound in the supremum norm
  obtain ⟨M₀, hM₀⟩ := exists_real_upper_bound_of_upperSemicontinuous
    (hvpsh j₀).1.quasiPlurisubharmonic.upperSemicontinuous (hvpsh j₀).1.quasiPlurisubharmonic.ne_top
  have hvM : ∀ j x, v (j₀ + j) x ≤ M₀ := fun j x =>
    (hvanti x (Nat.le_add_right j₀ j)).trans (hM₀ x)
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_mul_norm_sq_le_lintegral V hμ
  set Bd : ℝ := Real.exp M₀ * (C * B.toReal) / c₀ with hBd
  have hsbd : ∀ j, ‖s j‖ ≤ Real.sqrt Bd := by
    intro j
    have h1 : ENNReal.ofReal (c₀ * ‖s j‖ ^ 2) ≤ ENNReal.ofReal (Real.exp M₀) * (ENNReal.ofReal C * B) := by
      refine (hc₀le (s j)).trans ?_
      refine le_trans ?_ (mul_le_mul' le_rfl (hsB j))
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      have hw : ENNReal.ofReal (Real.exp (-M₀)) ≤ multiplierWeight 1 (v (j₀ + j) x) := by
        have := multiplierWeight_antitone zero_le_one (hvM j x)
        rwa [multiplierWeight_coe, one_mul] at this
      calc ENNReal.ofReal (‖s j x‖ ^ 2)
          = ENNReal.ofReal (Real.exp M₀) * (ENNReal.ofReal (‖s j x‖ ^ 2) *
              ENNReal.ofReal (Real.exp (-M₀))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_comm, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        _ ≤ _ := by gcongr
    have hfin : ENNReal.ofReal (Real.exp M₀) * (ENNReal.ofReal C * B) =
        ENNReal.ofReal (Real.exp M₀ * (C * B.toReal)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC.le,
        ENNReal.ofReal_toReal hBfin.ne]
    rw [hfin, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    refine Real.le_sqrt_of_sq_le ?_
    rw [hBd, le_div_iff₀ hc₀]
    linarith
  -- a convergent subsequence
  obtain ⟨sL, -, φs, hφs, hlim⟩ := (isCompact_section_closedBall V.Fiber 0 (Real.sqrt Bd)).tendsto_subseq
    (x := s) fun j => mem_closedBall_zero_iff.mpr (hsbd j)
  have hpt : ∀ x, Tendsto (fun k => s (φs k) x) atTop (𝓝 (sL x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
    exact norm_apply_le_norm V (s (φs k) - sL) x
  have hsLW : ∀ y : W, sL y = f y := fun y =>
    tendsto_nhds_unique (hpt y) (tendsto_const_nhds.congr fun k => (hsW (φs k) y).symm)
  refine ⟨sL, hsLW, ?_⟩
  -- Fatou
  have hFm : ∀ k, Measurable fun x => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) *
      multiplierWeight 1 (v (j₀ + φs k) x) := fun k =>
    (ENNReal.measurable_ofReal.comp ((continuous_norm_section V _).pow 2).measurable).mul
      ((multiplierWeight_antitone zero_le_one).measurable.comp (hvm _))
  have hliminf : ∀ x, ENNReal.ofReal (‖sL x‖ ^ 2) * multiplierWeight 1 (φ x) ≤
      liminf (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) *
        multiplierWeight 1 (v (j₀ + φs k) x)) atTop := by
    intro x
    by_cases h0 : ‖sL x‖ = 0
    · rw [h0]; simp
    have hn : Tendsto (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖sL x‖ ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (((continuous_norm.tendsto _).comp (hpt x)).pow 2)
    have hv : Tendsto (fun k => v (j₀ + φs k) x) atTop (𝓝 (φ x)) :=
      (hvlim x).comp (tendsto_atTop_mono (fun k => Nat.le_add_left (φs k) j₀) hφs.tendsto_atTop)
    have hw : Tendsto (fun k => multiplierWeight 1 (v (j₀ + φs k) x)) atTop
        (𝓝 (multiplierWeight 1 (φ x))) :=
      ((continuous_multiplierWeight one_pos).tendsto _).comp hv
    have hprod := ENNReal.Tendsto.mul hn (Or.inl (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)) hw (Or.inr ENNReal.ofReal_ne_top)
    exact hprod.liminf_eq.symm.le
  calc ∫⁻ x, ENNReal.ofReal (‖sL x‖ ^ 2) * multiplierWeight 1 (φ x) ∂μ
      ≤ ∫⁻ x, liminf (fun k => ENNReal.ofReal (‖s (φs k) x‖ ^ 2) *
          multiplierWeight 1 (v (j₀ + φs k) x)) atTop ∂μ := lintegral_mono hliminf
    _ ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal (‖s (φs k) x‖ ^ 2) *
          multiplierWeight 1 (v (j₀ + φs k) x) ∂μ) atTop := lintegral_liminf_le hFm
    _ ≤ ENNReal.ofReal C * B := liminf_le_of_frequently_le' (Frequently.of_forall fun k => hsB _)

/-- **`thm:OT_ext` from the gentle case**: `GentleSubmanifoldExtensionAlong ω W` (Steps 1--4 of FPT
`thm:compact-submanifold-extension`) implies the book's `OTExtAlong` for `W` and every `δ > 0`. -/
theorem otExtAlong_of_gentle (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    {δ : ℝ} (hδ : 0 < δ) (hG : GentleSubmanifoldExtensionAlong ωb hW) :
    OTExtAlong ωb L T θ hW δ :=
  SGPT.Trace.OTExt3.otExtAlong_of_compactSubmanifoldExtension ωb L T hL hT θ hθ hW hδ
    (compactSubmanifoldExtensionAlong_of_gentle ωb hW hG)

end SGPT.Trace.OTExt4

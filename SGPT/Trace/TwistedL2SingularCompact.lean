import SGPT.Trace.TwistedL2SingularCutoff
import SGPT.Trace.TwistedL2SingularRemoval

/-!
# The twisted `L²` estimate on compact Kähler manifolds with singular weights

Blueprint node `claude-twisted-l2:compact` in `claude-twisted-l2.tex`; Xia,
*Foundations of pluripotential theory* (FPT), q07,
`lem:twisted-kahler-line-estimate` on `X \ {ψ = -∞}` with `lem:analytic-complement-cutoffs` and
`lem:l2-holomorphic-analytic-removal`, as in Steps 1--4 of the proof of
`thm:compact-submanifold-extension`.

## Main results

* `continuous_norm_of_isSmoothSectionOn`: a smooth section has a continuous pointwise norm.
* `ofReal_mul_exp_neg_toReal`: `(t e^{-ψ})₊ = t₊ · e^{-ψ}` for finite `ψ` (`multiplierWeight`).
* `compactTwistedL2CorrectionStatement_of_main` (`claude-twisted-l2:compact`):
  **`TwistedL2CorrectionStatement n X → CompactTwistedL2CorrectionStatement n X`**.  The main
  estimate is applied on `U = X \ A` with the Kähler modification and `HasCompleteCutoffs` of
  `analyticComplementCutoffStatement` and `D_σ = 2 max(D_ω, 0)`; the solution is `L²` near `A`
  and extends across `A` by `l2RemovableSingularityStatement`; `A` is `μ`-null.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Auxiliary facts -/

/-- A chart-smooth function is continuous. -/
theorem continuous_of_chartSmooth' {h : X → ℝ} (hh : ChartSmooth (n := n) h) : Continuous h := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  set c := complexChartAt (n := n) x
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  have hz : c.val x ∈ c.val.target := c.val.map_source hx
  have h1 : ContinuousAt (fun z => h (c.val.symm z)) (c.val x) :=
    ((hh c).continuousOn).continuousAt (c.val.open_target.mem_nhds hz)
  have h2 : ContinuousAt (fun y => h (c.val.symm (c.val y))) x :=
    h1.comp (c.val.continuousAt hx)
  refine h2.congr (eventually_of_mem (c.val.open_source.mem_nhds hx) fun y hy => ?_)
  simp only [c.val.left_inv hy]

/-- `ChartSmooth` implies `ChartSmoothOn` on every set. -/
theorem chartSmoothOn_of_chartSmooth {h : X → ℝ} (hh : ChartSmooth (n := n) h) (U : Set X) :
    SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) h U := fun c =>
  (hh c).mono inter_subset_left

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- **A smooth section has a continuous norm on the open set where it is smooth.** -/
theorem continuousOn_norm_of_isSmoothSectionOn {G : (x : X) → L.Fiber x} {U : Set X}
    (hU : IsOpen U) (hG : IsSmoothSectionOn L G U) : ContinuousOn (fun x => ‖G x‖) U := by
  intro x hxU
  refine ContinuousAt.continuousWithinAt ?_
  set c := complexChartAt (n := n) x
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  have hxe : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x
  have hz : c.val x ∈ chartFrameDomain L c e ∩ c.val.symm ⁻¹' U :=
    ⟨⟨c.val.map_source hx, by rw [mem_preimage, c.val.left_inv hx]; exact hxe⟩,
      by rw [mem_preimage, c.val.left_inv hx]; exact hxU⟩
  have hDo : IsOpen (chartFrameDomain L c e ∩ c.val.symm ⁻¹' U) := by
    have : chartFrameDomain L c e ∩ c.val.symm ⁻¹' U =
        c.val.target ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ U) := by
      ext z; simp [chartFrameDomain, and_assoc]
    rw [this]
    exact c.val.isOpen_inter_preimage_symm (e.val.open_baseSet.inter hU)
  have h1 : ContinuousAt (chartCoeff L c e G) (c.val x) :=
    (hG c e).continuousOn.continuousAt (hDo.mem_nhds hz)
  have h2 : ContinuousAt (fun y => ‖chartCoeff L c e G (c.val y)‖ * ‖e.val.symm y 1‖) x :=
    (h1.comp (c.val.continuousAt hx)).norm.mul
      ((SGPT.Bergman.CompactHolomorphicSectionsDraft.frameNorm_continuousOn L.Fiber
        e.val).continuousAt (e.val.open_baseSet.mem_nhds hxe))
  refine h2.congr (eventually_of_mem
    ((c.val.open_source.inter e.val.open_baseSet).mem_nhds ⟨hx, hxe⟩) fun y hy => ?_)
  have key : ∀ y', y' = y → (e.val ⟨y', G y'⟩).2 = (e.val ⟨y, G y⟩).2 := by
    rintro _ rfl; rfl
  simp only [chartCoeff, frameCoeff]
  rw [key _ (c.val.left_inv hy.1)]
  exact (norm_eq_coord_mul L e.val hy.2 (G y)).symm

/-- A smooth section has a continuous norm. -/
theorem continuous_norm_of_isSmoothSectionOn {G : (x : X) → L.Fiber x}
    (hG : IsSmoothSectionOn L G univ) : Continuous fun x => ‖G x‖ :=
  continuousOn_univ.mp (continuousOn_norm_of_isSmoothSectionOn L isOpen_univ hG)

/-- Smoothness of a section on a set is inherited by subsets. -/
theorem IsSmoothSectionOn.mono' {G : (x : X) → L.Fiber x} {U V : Set X}
    (hG : IsSmoothSectionOn L G U) (hVU : V ⊆ U) : IsSmoothSectionOn L G V := fun c e =>
  (hG c e).mono (inter_subset_inter_right _ (preimage_mono hVU))

/-- The zero section is holomorphic. -/
theorem isHolomorphicSectionOn_zero (U : Set X) :
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber (fun _ => 0) U :=
  ((Bundle.contMDiff_zeroSection ℂ L.Fiber (n := 1) (IB := 𝓘(ℂ, ComplexModel n))).mdifferentiable
    one_ne_zero).mdifferentiableOn

/-- `(t e^{-p})₊ = t₊ e^{-p}` for a finite `p`, with `e^{-p} = multiplierWeight 1 p`. -/
theorem ofReal_mul_exp_neg_toReal (t : ℝ) {p : EReal} (hp : p ≠ ⊥) (hp' : p ≠ ⊤) :
    ENNReal.ofReal (t * Real.exp (-p.toReal)) = ENNReal.ofReal t * multiplierWeight 1 p := by
  rw [ENNReal.ofReal_mul' (Real.exp_pos _).le]
  conv_rhs => rw [← EReal.coe_toReal hp' hp, multiplierWeight_coe, one_mul]

/-- On compact `X`, positive continuous functions are bounded above and below by positive
constants. -/
theorem exists_pos_bounds_of_compact [CompactSpace X] {a b : X → ℝ} (ha : Continuous a)
    (hb : Continuous b) (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ a x ∧ a x ≤ M ∧ m ≤ b x ∧ b x ≤ M := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1, 1, one_pos, fun x => isEmptyElim x⟩
  obtain ⟨xa, -, hxa⟩ := isCompact_univ.exists_isMinOn univ_nonempty ha.continuousOn
  obtain ⟨xb, -, hxb⟩ := isCompact_univ.exists_isMinOn univ_nonempty hb.continuousOn
  obtain ⟨ya, -, hya⟩ := isCompact_univ.exists_isMaxOn univ_nonempty ha.continuousOn
  obtain ⟨yb, -, hyb⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hb.continuousOn
  refine ⟨min (a xa) (b xb), max (a ya) (b yb), lt_min (ha0 xa) (hb0 xb), fun x =>
    ⟨(min_le_left _ _).trans (hxa (mem_univ x)), (hya (mem_univ x)).trans (le_max_left _ _),
      (min_le_right _ _).trans (hxb (mem_univ x)), (hyb (mem_univ x)).trans (le_max_right _ _)⟩⟩

/-! ### The compact case -/

variable [MeasurableSpace X] [BorelSpace X]

variable (n X) in
/-- **The twisted `L²` estimate on compact Kähler manifolds with admissible singular weights**
(`claude-twisted-l2:compact`), derived from the main estimate `TwistedL2CorrectionStatement`
: `TwistedL2CorrectionStatement n X → CompactTwistedL2CorrectionStatement n X`. -/
theorem compactTwistedL2CorrectionStatement_of_main (hmain : TwistedL2CorrectionStatement n X) :
    CompactTwistedL2CorrectionStatement n X := by
  intro hcpt omega μ hμ L hL ψ hψ a b ha hb ha0 hb0 hcurv G hG D Dω hD hDω hint
  obtain ⟨hqpsh, htop, hcl, hAn, hsm⟩ := hψ
  set A : Set X := {x | ψ x = ⊥} with hA
  set U : Set X := {x | ψ x ≠ ⊥} with hU
  have hUo : IsOpen U := hcl.isOpen_compl
  have hUA : univ \ A = U := by ext x; simp [hA, hU]
  set φ : X → ℝ := fun x => (ψ x).toReal with hφ
  obtain ⟨r, hrK, hrhalf, hrcut⟩ :=
    analyticComplementCutoffStatement n X hcpt omega ψ hqpsh htop hcl hsm
  have hac := continuous_of_chartSmooth' ha
  have hbc := continuous_of_chartSmooth' hb
  obtain ⟨m, M, hm, hmM⟩ := exists_pos_bounds_of_compact hac hbc ha0 hb0
  set Dσ : X → ℝ := fun x => 2 * max (Dω x) 0 with hDσdef
  have hDσ : ∀ (c : ComplexChart n X) (e : AtlasFrame L),
      ∀ z ∈ chartFrameDomain L c e, c.val.symm z ∈ U → ∀ v : ComplexModel n,
        ‖dbarPairing (chartCoeff L c e G) z v‖ ^ 2 * frameNormSq L e (c.val.symm z) ≤
          Dσ (c.val.symm z) * modifiedKahlerQuad omega r c z v := by
    intro c e z hz hzU v
    have h1 := hDω c e z hz hzU v
    have hk := kahlerQuad_nonneg omega c hz.1 v
    have h2 := hrhalf c z hz.1 hzU v
    have h3 : Dω (c.val.symm z) * kahlerQuad omega c z v ≤
        max (Dω (c.val.symm z)) 0 * kahlerQuad omega c z v :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hk
    have h4 : max (Dω (c.val.symm z)) 0 * kahlerQuad omega c z v ≤
        Dσ (c.val.symm z) * modifiedKahlerQuad omega r c z v := by
      simp only [hDσdef]
      nlinarith [le_max_right (Dω (c.val.symm z)) 0]
    linarith
  have hmw : ∀ x ∈ U, ∀ t : ℝ,
      ENNReal.ofReal (t * Real.exp (-φ x)) = ENNReal.ofReal t * multiplierWeight 1 (ψ x) :=
    fun x hx t => ofReal_mul_exp_neg_toReal t hx (htop x)
  have hintσ : ∫⁻ x in U, ENNReal.ofReal (Dσ x * Real.exp (-φ x)) ∂μ < ⊤ := by
    calc ∫⁻ x in U, ENNReal.ofReal (Dσ x * Real.exp (-φ x)) ∂μ
        ≤ ∫⁻ x in U, 2 * (ENNReal.ofReal (Dω x) * multiplierWeight 1 (ψ x)) ∂μ := by
          refine setLIntegral_mono' hUo.measurableSet fun x hx => ?_
          have hmax : ENNReal.ofReal (2 * max (Dω x) 0) = 2 * ENNReal.ofReal (Dω x) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
            congr 1
            rcases le_total (Dω x) 0 with h | h
            · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
            · rw [max_eq_left h]
          rw [hmw x hx, hDσdef]
          simp only
          rw [hmax, mul_assoc]
      _ ≤ ∫⁻ x, 2 * (ENNReal.ofReal (Dω x) * multiplierWeight 1 (ψ x)) ∂μ :=
          setLIntegral_le_lintegral _ _
      _ = 2 * ∫⁻ x, ENNReal.ofReal (Dω x) * multiplierWeight 1 (ψ x) ∂μ :=
          lintegral_const_mul' _ _ (by norm_num)
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hint
  obtain ⟨S, hShol, hSbound⟩ := hmain omega U hUo r hrK hrcut μ hμ L hL φ a b hsm
    (chartSmoothOn_of_chartSmooth ha U) (chartSmoothOn_of_chartSmooth hb U)
    ⟨m, M, hm, fun x _ => hmM x⟩ hcurv G (IsSmoothSectionOn.mono' L hG (subset_univ U)) D Dσ hD
    hDσ hintσ
  set I := ∫⁻ x, ENNReal.ofReal (D x) * multiplierWeight 1 (ψ x) ∂μ with hIdef
  by_cases hI : I = ⊤
  · exact ⟨fun _ => 0, isHolomorphicSectionOn_zero L univ, by rw [hI]; exact le_top⟩
  have hA0 : μ A = 0 := measure_eq_zero_of_isLocallyAnalyticNull hμ hAn
  have haeU : ∀ᵐ x ∂μ, x ∈ U := measure_eq_zero_iff_ae_notMem.mp hA0
  have hDU : ∫⁻ x in U, ENNReal.ofReal (D x * Real.exp (-φ x)) ∂μ ≤ I := by
    rw [hIdef]
    refine (setLIntegral_congr_fun hUo.measurableSet fun x hx => hmw x hx (D x)).trans_le ?_
    exact setLIntegral_le_lintegral _ _
  -- the solution is square integrable
  have hloc : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_isSmoothPositiveVolume hμ
  have hμX : μ univ < ⊤ := isCompact_univ.measure_lt_top
  obtain ⟨CG, hCG⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_norm_of_isSmoothSectionOn L hG).continuousOn
  obtain ⟨Mψ, hMψ⟩ := exists_le_coe_of_isCompact hqpsh (isCompact_univ (X := X))
  have hφle : ∀ x ∈ U, φ x ≤ Mψ := fun x hx => by
    have h := hMψ x (mem_univ x)
    rw [← EReal.coe_toReal (htop x) hx] at h
    exact_mod_cast h
  set f : X → ℝ := fun x => ‖G x - S x‖ ^ 2 * Real.exp (-φ x) / (a x + b x) with hf
  set κ : ℝ := 2 * (2 * M * Real.exp Mψ) with hκ
  have hptS : ∀ x ∈ U, ENNReal.ofReal (‖S x‖ ^ 2) ≤
      ENNReal.ofReal (2 * CG ^ 2) + ENNReal.ofReal κ * ENNReal.ofReal (f x) := by
    intro x hx
    have hab : 0 < a x + b x := add_pos (ha0 x) (hb0 x)
    have hM0 : 0 ≤ M := (ha0 x).le.trans (hmM x).2.1
    have hf0 : 0 ≤ f x := by rw [hf]; exact div_nonneg (by positivity) hab.le
    have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
    rw [← ENNReal.ofReal_mul hκ0, ← ENNReal.ofReal_add (by positivity) (mul_nonneg hκ0 hf0)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hG' : ‖G x‖ ≤ CG := (Real.norm_eq_abs _ ▸ (le_abs_self _)).trans (hCG x (mem_univ x))
    have habM : a x + b x ≤ 2 * M := by linarith [(hmM x).2.1, (hmM x).2.2.2]
    have hexp : Real.exp (φ x) ≤ Real.exp Mψ := Real.exp_le_exp.mpr (hφle x hx)
    have hGS : ‖G x - S x‖ ^ 2 = (a x + b x) * Real.exp (φ x) * f x := by
      rw [hf]
      field_simp
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hnorm : ‖S x‖ ≤ ‖G x‖ + ‖G x - S x‖ := by
      calc ‖S x‖ = ‖G x - (G x - S x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hsq : ‖S x‖ ^ 2 ≤ 2 * ‖G x‖ ^ 2 + 2 * ‖G x - S x‖ ^ 2 := by
      nlinarith [norm_nonneg (S x), norm_nonneg (G x), norm_nonneg (G x - S x),
        sq_nonneg (‖G x‖ - ‖G x - S x‖)]
    have hGS' : ‖G x - S x‖ ^ 2 ≤ 2 * M * Real.exp Mψ * f x := by
      rw [hGS]
      have : (a x + b x) * Real.exp (φ x) ≤ 2 * M * Real.exp Mψ :=
        mul_le_mul habM hexp (Real.exp_pos _).le (by linarith)
      exact mul_le_mul_of_nonneg_right this hf0
    have hG2 : ‖G x‖ ^ 2 ≤ CG ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG' 2
    rw [hκ]
    nlinarith
  have hL2 : ∀ K : Set X, IsCompact K → K ⊆ univ →
      ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ < ⊤ := by
    intro K hK _
    have hKA : MeasurableSet (K \ A) := hK.isClosed.measurableSet.diff hcl.measurableSet
    have hKAU : K \ A ⊆ U := fun x hx => hx.2
    calc ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ
        ≤ ∫⁻ x in K \ A, ENNReal.ofReal (2 * CG ^ 2) + ENNReal.ofReal κ * ENNReal.ofReal (f x)
            ∂μ := setLIntegral_mono' hKA fun x hx => hptS x (hKAU hx)
      _ ≤ ∫⁻ x in U, ENNReal.ofReal (2 * CG ^ 2) + ENNReal.ofReal κ * ENNReal.ofReal (f x) ∂μ :=
          lintegral_mono_set hKAU
      _ = ENNReal.ofReal (2 * CG ^ 2) * μ U + ENNReal.ofReal κ * ∫⁻ x in U, ENNReal.ofReal (f x)
            ∂μ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := by
          refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((measure_mono (subset_univ U)).trans_lt hμX), ENNReal.mul_lt_top
            ENNReal.ofReal_lt_top ?_⟩
          exact (hSbound.trans hDU).trans_lt (lt_top_iff_ne_top.mpr hI)
  obtain ⟨S', hS'hol, hS'eq⟩ := l2RemovableSingularityStatement n X μ hμ L univ A isOpen_univ hcl
    hAn S (by rw [hUA]; exact hShol) hL2
  refine ⟨S', hS'hol, ?_⟩
  rw [← Measure.restrict_eq_self_of_ae_mem haeU]
  calc ∫⁻ x in U, ENNReal.ofReal (‖G x - S' x‖ ^ 2 / (a x + b x)) * multiplierWeight 1 (ψ x) ∂μ
      = ∫⁻ x in U, ENNReal.ofReal (‖G x - S x‖ ^ 2 * Real.exp (-φ x) / (a x + b x)) ∂μ := by
        refine setLIntegral_congr_fun hUo.measurableSet fun x hx => ?_
        rw [hS'eq x (by rw [hUA]; exact hx), ← hmw x hx]
        ring_nf
    _ ≤ ∫⁻ x in U, ENNReal.ofReal (D x * Real.exp (-φ x)) ∂μ := hSbound
    _ ≤ I := hDU

end SGPT.Trace.TwistedL2

import SGPT.Trace.TwistedL2Twist
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground
import SGPT.Foundations.Analysis.FirstPass.SmoothOffPole
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Kähler modifications with complete cutoffs on complements of pole sets

Blueprint node `claude-twisted-l2:complement-cutoffs` in `claude-twisted-l2.tex`;
Xia, *Foundations of
pluripotential theory* (FPT), q07, `lem:analytic-complement-cutoffs`.

## Main results

* `hasCompleteCutoffs_of_exhaustion` (`claude-twisted-l2-c:cutoffs-of-exhaustion`): if `s` is
  smooth on an open `U`, has compact sublevel sets `{x ∈ U | s x ≤ T}` and `|ds|²_σ ≤ C`, then the
  functions `χ_k = θ(s/(k+1))` (`θ = 1` on `(-∞,1]`, `θ = 0` on `[2,∞)`) are complete cut-offs for
  `σ = ω + ddᶜr` on `U` (`HasCompleteCutoffs`).
* `exists_neg_le_leviForm_of_isCompact` (`claude-twisted-l2-c:quasi-psh-levi-bound`): a quasi-psh
  `ψ` satisfies `ddᶜψ ≥ -C ω` at the points of a compact `K` near which it is smooth, with one
  constant `C` (TN's local psh corrections, Kähler domination near each point, compactness).
* `leviForm_neg_log_sub` and `sq_fderiv_log_sub_le`: the Levi form of `-log(c - g)` and the
  gradient of `log(c - g)` (the chain rule of FPT's proof).
* `analyticComplementCutoffStatement` (`claude-twisted-l2:complement-cutoffs`): **the proof of
  `AnalyticComplementCutoffStatement`**, with `r = -log(c₀ - ψ)` and `s = log(c₀ - ψ)`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-! ### The cut-off profile -/

/-- The profile `θ(t) = smoothTransition(2 - t)`: `1` on `(-∞, 1]`, `0` on `[2, ∞)`. -/
def cutoffProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem contDiff_cutoffProfile : ContDiff ℝ ∞ cutoffProfile :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id)

theorem cutoffProfile_eq_one {t : ℝ} (ht : t ≤ 1) : cutoffProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoffProfile_eq_zero {t : ℝ} (ht : 2 ≤ t) : cutoffProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoffProfile_nonneg (t : ℝ) : 0 ≤ cutoffProfile t := Real.smoothTransition.nonneg _

theorem cutoffProfile_le_one (t : ℝ) : cutoffProfile t ≤ 1 := Real.smoothTransition.le_one _

/-- The derivative of the profile vanishes off `[1, 2]`. -/
theorem deriv_cutoffProfile_eq_zero {t : ℝ} (ht : t ∉ Icc (1 : ℝ) 2) :
    deriv cutoffProfile t = 0 := by
  rcases not_and_or.mp ht with h | h
  · have hev : cutoffProfile =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds (not_le.mp h)] with y hy
      exact cutoffProfile_eq_one (le_of_lt hy)
    rw [hev.deriv_eq, deriv_const]
  · have hev : cutoffProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds (not_le.mp h)] with y hy
      exact cutoffProfile_eq_zero (le_of_lt hy)
    rw [hev.deriv_eq, deriv_const]

/-- The derivative of the profile is bounded. -/
theorem exists_abs_deriv_cutoffProfile_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv cutoffProfile t| ≤ B := by
  have hc : Continuous (deriv cutoffProfile) :=
    contDiff_cutoffProfile.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (1 : ℝ) 2
  · exact (Real.norm_eq_abs _ ▸ hB t ht).trans (le_max_left _ _)
  · rw [deriv_cutoffProfile_eq_zero ht, abs_zero]
    exact le_max_right _ _

/-! ### Complete cut-offs from an exhaustion with bounded gradient -/

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The cut-offs `χ_k = θ(s/(k+1))` on `U`, extended by `0`. -/
def exhaustionCutoff (U : Set X) (s : X → ℝ) (k : ℕ) : X → ℝ :=
  U.indicator fun x => cutoffProfile (s x / ((k : ℝ) + 1))

/-- **Complete cut-offs from an exhaustion** (`claude-twisted-l2-c:cutoffs-of-exhaustion`; the last
paragraph of the proof of FPT `lem:analytic-complement-cutoffs`).  Let `s` be smooth on the open
set `U`, with compact sublevel sets `{x ∈ U | s x ≤ T}`, and `|ds(v)|² ≤ C σ(v)` on `U` for
`σ = ω + ddᶜr`.  Then `σ` has complete cut-offs on `U`. -/
theorem hasCompleteCutoffs_of_exhaustion (omega : KahlerBackground n X) (r : X → ℝ) {U : Set X}
    (hU : IsOpen U) (s : X → ℝ) (hs : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) s U)
    (hsub : ∀ T : ℝ, IsCompact {x | x ∈ U ∧ s x ≤ T}) {C : ℝ} (hC : 0 ≤ C)
    (hgrad : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, c.val.symm z ∈ U →
      ∀ v : ComplexModel n,
        fderiv ℝ (fun y => s (c.val.symm y)) z v ^ 2 ≤ C * modifiedKahlerQuad omega r c z v) :
    HasCompleteCutoffs omega r U := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_deriv_cutoffProfile_le
  set χ := exhaustionCutoff U s with hχ
  -- the support of `χ k` lies in the compact sublevel set `K k`
  set K : ℕ → Set X := fun k => {x | x ∈ U ∧ s x ≤ 2 * ((k : ℝ) + 1)} with hK
  have hKc : ∀ k, IsCompact (K k) := fun k => hsub _
  have hKU : ∀ k, K k ⊆ U := fun k x hx => hx.1
  have hk1 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hzero : ∀ k x, x ∉ K k → χ k x = 0 := by
    intro k x hx
    simp only [hχ, exhaustionCutoff]
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
      apply cutoffProfile_eq_zero
      have : 2 * ((k : ℝ) + 1) < s x := by
        by_contra h
        exact hx ⟨hxU, not_lt.mp h⟩
      rw [le_div_iff₀ (hk1 k)]
      linarith
    · rw [indicator_of_notMem hxU]
  have hsuppK : ∀ k, Function.support (χ k) ⊆ K k := fun k x hx => by
    by_contra h
    exact hx (hzero k x h)
  have htsK : ∀ k, tsupport (χ k) ⊆ K k := fun k =>
    closure_minimal (hsuppK k) (hKc k).isClosed
  -- smoothness in a chart near a point of `U`
  have hloc : ∀ (k : ℕ) (c : ComplexChart n X), ContDiffOn ℝ ∞
      (fun y => cutoffProfile (s (c.val.symm y) / ((k : ℝ) + 1)))
      (c.val.target ∩ c.val.symm ⁻¹' U) := fun k c =>
    contDiff_cutoffProfile.comp_contDiffOn ((hs c).div_const _)
  have hopen : ∀ c : ComplexChart n X, IsOpen (c.val.target ∩ c.val.symm ⁻¹' U) := fun c =>
    c.val.isOpen_inter_preimage_symm hU
  have heqU : ∀ (k : ℕ) (c : ComplexChart n X), EqOn (fun y => χ k (c.val.symm y))
      (fun y => cutoffProfile (s (c.val.symm y) / ((k : ℝ) + 1)))
      (c.val.target ∩ c.val.symm ⁻¹' U) := fun k c y hy => by
    simp only [hχ, exhaustionCutoff, indicator_of_mem (show c.val.symm y ∈ U from hy.2)]
  refine ⟨χ, B * Real.sqrt C, fun k c => ?_, fun k => ?_, fun k => (htsK k).trans (hKU k),
    fun k x => ?_, fun x hx => ?_, fun k c z hz hzU v => ?_⟩
  · -- smoothness
    refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
    by_cases hzU : c.val.symm z ∈ U
    · refine ⟨c.val.target ∩ c.val.symm ⁻¹' U, hopen c, ⟨hz, hzU⟩, ?_⟩
      refine ((hloc k c).mono inter_subset_right).congr fun y hy => heqU k c hy.2
    · have hKcl : IsClosed (K k) := (hKc k).isClosed
      refine ⟨c.val.target ∩ c.val.symm ⁻¹' (K k)ᶜ,
        c.val.isOpen_inter_preimage_symm hKcl.isOpen_compl, ⟨hz, fun h => hzU (hKU k h)⟩, ?_⟩
      refine contDiffOn_const.congr fun y hy => hzero k _ hy.2.2
  · exact (hKc k).of_isClosed_subset (isClosed_tsupport _) (htsK k)
  · simp only [hχ, exhaustionCutoff]
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
      exact ⟨cutoffProfile_nonneg _, cutoffProfile_le_one _⟩
    · rw [indicator_of_notMem hxU]
      exact ⟨le_rfl, zero_le_one⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈s x⌉₊] with k hk
    simp only [hχ, exhaustionCutoff, indicator_of_mem hx]
    symm
    apply cutoffProfile_eq_one
    rw [div_le_one (hk1 k)]
    have h1 : s x ≤ (⌈s x⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈s x⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  · -- the gradient bound
    have hzmem : z ∈ c.val.target ∩ c.val.symm ⁻¹' U := ⟨hz, hzU⟩
    have hev : (fun y => χ k (c.val.symm y)) =ᶠ[𝓝 z]
        fun y => cutoffProfile (s (c.val.symm y) / ((k : ℝ) + 1)) :=
      eventually_of_mem ((hopen c).mem_nhds hzmem) fun y hy => heqU k c hy
    have hsd : DifferentiableAt ℝ (fun y => s (c.val.symm y) / ((k : ℝ) + 1)) z :=
      (((hs c).div_const ((k : ℝ) + 1)).contDiffAt ((hopen c).mem_nhds hzmem)).differentiableAt
        (by simp)
    have hsd' : DifferentiableAt ℝ (fun y => s (c.val.symm y)) z :=
      ((hs c).contDiffAt ((hopen c).mem_nhds hzmem)).differentiableAt (by simp)
    have hθd : DifferentiableAt ℝ cutoffProfile (s (c.val.symm z) / ((k : ℝ) + 1)) :=
      contDiff_cutoffProfile.differentiable (by simp) _
    have hdiv : HasFDerivAt (fun y => s (c.val.symm y) / ((k : ℝ) + 1))
        (((k : ℝ) + 1)⁻¹ • fderiv ℝ (fun y => s (c.val.symm y)) z) z := by
      simpa [div_eq_mul_inv] using hsd'.hasFDerivAt.mul_const ((k : ℝ) + 1)⁻¹
    rw [hev.fderiv_eq, fderiv_comp_real hθd hsd, hdiv.fderiv]
    simp only [_root_.smul_apply, smul_eq_mul]
    set d := deriv cutoffProfile (s (c.val.symm z) / ((k : ℝ) + 1))
    set D := fderiv ℝ (fun y => s (c.val.symm y)) z v
    have hd : d ^ 2 ≤ B ^ 2 := by
      have := hB (s (c.val.symm z) / ((k : ℝ) + 1))
      nlinarith [abs_nonneg d, sq_abs d]
    have hDg := hgrad c z hz hzU v
    have hsq : (B * Real.sqrt C / ((k : ℝ) + 1)) ^ 2 = B ^ 2 * C / ((k : ℝ) + 1) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hC]
    rw [hsq]
    have hk2 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    have hlhs : (d * (((k : ℝ) + 1)⁻¹ * D)) ^ 2 = d ^ 2 * D ^ 2 / ((k : ℝ) + 1) ^ 2 := by
      field_simp
    rw [hlhs, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hk2]
    calc d ^ 2 * D ^ 2 ≤ B ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      _ ≤ B ^ 2 * (C * modifiedKahlerQuad omega r c z v) :=
          mul_le_mul_of_nonneg_left hDg (sq_nonneg _)
      _ = B ^ 2 * C * modifiedKahlerQuad omega r c z v := by ring


/-! ### `ddᶜψ ≥ -C ω` on compact sets -/

/-- **Kähler domination near a point, in every chart.**  For a chart-smooth `H` and a point `x`
there are `B > 0` and an open `V ∋ x` with `ddᶜH + B ω ≥ 0` at the points of `V`, read in any
chart (the chart change carries complex lines to complex lines). -/
theorem exists_nhds_smoothDDC_domination (omega : KahlerBackground n X) {H : X → ℝ}
    (hH : ChartSmooth (n := n) H) (x : X) :
    ∃ B : ℝ, 0 < B ∧ ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target → c.val.symm z ∈ V →
        ∀ v : ComplexModel n,
          0 ≤ smoothDDC (fun y => H (c.val.symm y)) z ![v, Complex.I • v] +
            B * kahlerQuad omega c z v := by
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxs
  obtain ⟨B, hB, hev⟩ := Pending.KahlerDomination.exists_eventually_domination
    (Pending.SmoothDDCForm.ddcForm H hH) omega.form.val e hz₀ (omega.isKahler.1 e _ hz₀).2
  obtain ⟨W, hWsub, hWo, hzW⟩ := mem_nhds_iff.mp hev
  refine ⟨B, hB, e.val.source ∩ e.val ⁻¹' W, e.val.isOpen_inter_preimage hWo, ⟨hxs, hzW⟩, ?_⟩
  intro c z hz hzV v
  have hwsrc : z ∈ (chartTransition c e).source := by
    rw [chartTransition]
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨hz, hzV.1⟩
  have hθt := Pending.KahlerDomination.lineValue_compatible
    (Pending.SmoothDDCForm.ddcForm H hH) c e hwsrc v
  have hωt := Pending.KahlerDomination.lineValue_compatible omega.form.val c e hwsrc v
  have hteq : chartTransition c e z = e.val (c.val.symm z) := rfl
  rw [hteq] at hθt hωt
  simp only [Pending.SmoothDDCForm.ddcForm_coeff] at hθt
  unfold kahlerQuad
  rw [hθt, hωt]
  exact (hWsub hzV.2).2 _

/-- The Kähler quadratic form is nonnegative on chart targets. -/
theorem kahlerQuad_nonneg (omega : KahlerBackground n X) (c : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ c.val.target) (v : ComplexModel n) :
    0 ≤ kahlerQuad omega c z v :=
  omega.isSemipositive c z hz v

/-- The Kähler quadratic form is positive on nonzero vectors of chart targets. -/
theorem kahlerQuad_pos (omega : KahlerBackground n X) (c : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ c.val.target) {v : ComplexModel n} (hv : v ≠ 0) :
    0 < kahlerQuad omega c z v :=
  (omega.isKahler.1 c z hz).2 v hv

/-- **`ddᶜψ ≥ -C ω` on a compact set** (`claude-twisted-l2-c:quasi-psh-levi-bound`; FPT
`lem:quasi-psh-basic` (4) on a compact set).  For a quasi-psh `ψ` and a compact `K` there is
`C > 0` such that at every point `z` of a chart with `c⁻¹ z ∈ K` near which `ψ` is a smooth real
function `g`, `Levi(g)(v)/π ≥ -C ω(v, iv)`. -/
theorem exists_neg_le_leviForm_of_isCompact (omega : KahlerBackground n X) {ψ : X → EReal}
    (hψ : ManifoldQuasiPlurisubharmonic (n := n) ψ) {K : Set X} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      c.val.symm z ∈ K → ∀ g : ComplexModel n → ℝ, (∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ g y) →
      chartFunction ψ c =ᶠ[𝓝 z] (fun y => (g y : EReal)) →
      ∀ v : ComplexModel n, -(C * kahlerQuad omega c z v) ≤ leviForm g z v / Real.pi := by
  classical
  choose H hH S hSo hxS hp using fun x : X =>
    Pending.GlobalQuasiPshSmoothLocalization.exists_chartSmooth_local_psh_correction hψ x
  choose B hB V hVo hxV hdom using fun x : X => exists_nhds_smoothDDC_domination omega (hH x) x
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => S x ∩ V x)
    (fun x => (hSo x).inter (hVo x)) (fun y _ => mem_iUnion.mpr ⟨y, hxS y, hxV y⟩)
  have hsum : (0 : ℝ) ≤ ∑ x ∈ t, B x := Finset.sum_nonneg fun x _ => (hB x).le
  refine ⟨1 + ∑ x ∈ t, B x, by linarith, ?_⟩
  intro c z hz hzK g hg hψg v
  obtain ⟨x, hxt, hzS, hzV⟩ : ∃ x ∈ t, c.val.symm z ∈ S x ∧ c.val.symm z ∈ V x := by
    have := ht hzK
    simp only [mem_iUnion] at this
    obtain ⟨x, hxt, h⟩ := this
    exact ⟨x, hxt, h⟩
  set Hc : ComplexModel n → ℝ := fun y => H x (c.val.symm y) with hHc
  have hHcs : ContDiffOn ℝ ∞ Hc c.val.target := hH x c
  have hz2 : ContDiffAt ℝ 2 Hc z :=
    ((hHcs z hz).contDiffAt (c.val.open_target.mem_nhds hz)).of_le (by norm_cast)
  -- the open set where `ψ = g` is psh after subtracting `H x`
  have hmem : {y | ContDiffAt ℝ ∞ g y ∧ chartFunction ψ c y = (g y : EReal)} ∩
      (c.val.target ∩ c.val.symm ⁻¹' S x) ∈ 𝓝 z :=
    inter_mem (hg.and hψg) ((c.val.isOpen_inter_preimage_symm (hSo x)).mem_nhds ⟨hz, hzS⟩)
  obtain ⟨W, hWsub, hWo, hzW⟩ := mem_nhds_iff.mp hmem
  set f : ComplexModel n → ℝ := fun y => g y - Hc y with hf
  have hfW : ContDiffOn ℝ ∞ f W := fun y hy =>
    ((hWsub hy).1.1.contDiffWithinAt).sub ((hHcs.mono fun w hw => (hWsub hw).2.1) y hy)
  have hpshW : PlurisubharmonicOn (fun y => (f y : EReal)) (⟨W, hWo⟩ : TopologicalSpace.Opens _) := by
    intro y hy
    apply (hp x c y (hWsub hy).2.1 (hWsub hy).2.2).congr
    filter_upwards [hWo.mem_nhds hy] with w hw
    change ψ (c.val.symm w) - (H x (c.val.symm w) : EReal) = ((g w - Hc w : ℝ) : EReal)
    have hw' : chartFunction ψ c w = (g w : EReal) := (hWsub hw).1.2
    change ψ (c.val.symm w) = (g w : EReal) at hw'
    rw [hw', EReal.coe_sub]
  have hlevi : 0 ≤ leviForm f z v :=
    leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := ⟨W, hWo⟩) hfW hpshW hzW v
  have hg2 : ContDiffAt ℝ 2 g z := (hWsub hzW).1.1.of_le (by norm_cast)
  have hsplit : leviForm f z v = leviForm g z v - leviForm Hc z v := by
    have : f = g + (-Hc) := rfl
    have hneg : ContDiffAt ℝ 2 (-Hc) z := hz2.neg
    rw [this, leviForm_add hg2 hneg, leviForm_neg]
    ring
  have hdd := hdom x c z hz hzV v
  rw [smoothDDC_complexDiagonal_eq_leviForm hz2 v] at hdd
  have hkq := kahlerQuad_nonneg omega c hz v
  have hBle : B x ≤ 1 + ∑ y ∈ t, B y := by
    have := Finset.single_le_sum (f := B) (fun y _ => (hB y).le) hxt
    linarith
  have hpi := Real.pi_pos
  have h1 : leviForm Hc z v / Real.pi ≤ leviForm g z v / Real.pi :=
    div_le_div_of_nonneg_right (by linarith) hpi.le
  nlinarith [mul_le_mul_of_nonneg_right hBle hkq]


/-! ### The chain rule for `-log(c - g)` -/

section Euclidean

variable {m : ℕ}

theorem hasDerivAt_neg_log_sub {c₀ t : ℝ} (ht : t < c₀) :
    HasDerivAt (fun s : ℝ => -Real.log (c₀ - s)) (c₀ - t)⁻¹ t := by
  have h : HasDerivAt (fun s : ℝ => Real.log (c₀ - s)) (-1 / (c₀ - t)) t := by
    simpa using ((hasDerivAt_id t).const_sub c₀).log (sub_pos.mpr ht).ne'
  have h2 : HasDerivAt (fun s : ℝ => -Real.log (c₀ - s)) (-(-1 / (c₀ - t))) t := h.neg
  rwa [neg_div, neg_neg, one_div] at h2

theorem leviForm_neg_log_sub {g : ComplexModel m → ℝ} {z : ComplexModel m}
    (hg : ContDiffAt ℝ 2 g z) {c₀ : ℝ} (hz : g z < c₀) (v : ComplexModel m) :
    leviForm (fun y => -Real.log (c₀ - g y)) z v =
      leviForm g z v / (c₀ - g z) + holDerivSq g z v / (c₀ - g z) ^ 2 := by
  have hpos : 0 < c₀ - g z := sub_pos.mpr hz
  have hθ : ContDiffAt ℝ 2 (fun s : ℝ => -Real.log (c₀ - s)) (g z) :=
    ((contDiffAt_const.sub contDiffAt_id).log hpos.ne').neg
  rw [Pending.StokesCutoff.leviForm_comp hθ hg v]
  have hd1 : deriv (fun s : ℝ => -Real.log (c₀ - s)) (g z) = (c₀ - g z)⁻¹ :=
    (hasDerivAt_neg_log_sub hz).deriv
  have hev : deriv (fun s : ℝ => -Real.log (c₀ - s)) =ᶠ[𝓝 (g z)] fun s => (c₀ - s)⁻¹ := by
    filter_upwards [Iio_mem_nhds hz] with s hs
    exact (hasDerivAt_neg_log_sub hs).deriv
  have hd2 : deriv (deriv fun s : ℝ => -Real.log (c₀ - s)) (g z) = ((c₀ - g z) ^ 2)⁻¹ := by
    rw [hev.deriv_eq]
    have h : HasDerivAt (fun s : ℝ => (c₀ - s)⁻¹) (-(-1) / (c₀ - g z) ^ 2) (g z) :=
      ((hasDerivAt_id (g z)).const_sub c₀).inv hpos.ne'
    rw [h.deriv, neg_neg, one_div]
  rw [hd1, hd2]
  unfold holDerivSq
  field_simp

theorem fderiv_log_sub_apply {g : ComplexModel m → ℝ} {z : ComplexModel m}
    (hg : DifferentiableAt ℝ g z) {c₀ : ℝ} (hz : g z < c₀) (v : ComplexModel m) :
    fderiv ℝ (fun y => Real.log (c₀ - g y)) z v = -fderiv ℝ g z v / (c₀ - g z) := by
  have h := (hg.hasFDerivAt.const_sub c₀).log (sub_pos.mpr hz).ne'
  rw [h.fderiv]
  simp only [_root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  field_simp

/-- `|d log(c - g)(v)|² ≤ 4 |∂g(v)|²/(c - g)²`. -/
theorem sq_fderiv_log_sub_le {g : ComplexModel m → ℝ} {z : ComplexModel m}
    (hg : DifferentiableAt ℝ g z) {c₀ : ℝ} (hz : g z < c₀) (v : ComplexModel m) :
    fderiv ℝ (fun y => Real.log (c₀ - g y)) z v ^ 2 ≤ 4 * (holDerivSq g z v / (c₀ - g z) ^ 2) := by
  have hpos : 0 < c₀ - g z := sub_pos.mpr hz
  rw [fderiv_log_sub_apply hg hz, div_pow, neg_sq]
  unfold holDerivSq
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [sq_nonneg (fderiv ℝ g z (Complex.I • v))]

end Euclidean

/-! ### The proof of `AnalyticComplementCutoffStatement` -/

omit [IsComplexManifold n X] in
/-- Off the closed pole set, `ψ` is, near `z`, the smooth real function `(ψ ∘ c⁻¹).toReal`. -/
theorem eventually_chartFunction_eq_toReal {ψ : X → EReal} (htop : ∀ x, ψ x ≠ ⊤)
    (hcl : IsClosed {x | ψ x = ⊥})
    (hsm : SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n) (fun x => (ψ x).toReal)
      {x | ψ x ≠ ⊥})
    (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target)
    (hzU : ψ (c.val.symm z) ≠ ⊥) :
    (∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ (fun y => (ψ (c.val.symm y)).toReal) y) ∧
      chartFunction ψ c =ᶠ[𝓝 z] fun y => (((ψ (c.val.symm y)).toReal : ℝ) : EReal) := by
  have hUo : IsOpen {x | ψ x ≠ ⊥} := hcl.isOpen_compl
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' {x | ψ x ≠ ⊥}) :=
    c.val.isOpen_inter_preimage_symm hUo
  have hzO : z ∈ c.val.target ∩ c.val.symm ⁻¹' {x | ψ x ≠ ⊥} := ⟨hz, hzU⟩
  refine ⟨eventually_of_mem (hO.mem_nhds hzO) fun y hy => (hsm c y hy).contDiffAt
    (hO.mem_nhds hy), eventually_of_mem (hO.mem_nhds hzO) fun y hy => ?_⟩
  exact (EReal.coe_toReal (htop _) hy.2).symm

/-- A quasi-psh function is bounded above on a compact set. -/
theorem exists_le_coe_of_isCompact {ψ : X → EReal}
    (hψ : ManifoldQuasiPlurisubharmonic (n := n) ψ) {K : Set X} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ x ∈ K, ψ x ≤ (M : EReal) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun x hx => hx.elim⟩
  obtain ⟨x₀, hx₀, hmax⟩ := (hψ.upperSemicontinuous.upperSemicontinuousOn K).exists_isMaxOn hne hK
  obtain ⟨M, hM, -⟩ := EReal.exists_rat_btwn_of_lt (lt_top_iff_ne_top.mpr (hψ.ne_top x₀))
  exact ⟨M, fun x hx => (hmax hx).trans hM.le⟩

/-- **FPT's metric on the complement of the pole set, pointwise**
(`claude-twisted-l2-c:pole-metric`).  If `ddᶜψ ≥ -C ω` near `z` and `c₀ - ψ ≥ 2C` there, then
for `r = -log(c₀ - ψ)` and `g = ψ` in the chart,
`σ(v) = ω(v) + Levi(r)(v)/π ≥ ω(v)/2 + |∂g(v)|²/(π (c₀ - g)²)`. -/
theorem half_add_le_modifiedKahlerQuad (omega : KahlerBackground n X) (c : ComplexChart n X)
    {z : ComplexModel n} (hz : z ∈ c.val.target) {g : ComplexModel n → ℝ}
    (hg : ContDiffAt ℝ 2 g z) {C c₀ : ℝ} (hC : 0 < C) (hgz : 2 * C ≤ c₀ - g z)
    (hlev : ∀ v, -(C * kahlerQuad omega c z v) ≤ leviForm g z v / Real.pi)
    {r : X → ℝ} (hr : (fun y => r (c.val.symm y)) = fun y => -Real.log (c₀ - g y))
    (v : ComplexModel n) :
    kahlerQuad omega c z v / 2 + holDerivSq g z v / (Real.pi * (c₀ - g z) ^ 2) ≤
      modifiedKahlerQuad omega r c z v := by
  have hpos : 0 < c₀ - g z := by linarith
  unfold modifiedKahlerQuad
  rw [hr, leviForm_neg_log_sub hg (by linarith) v]
  have hkq := kahlerQuad_nonneg omega c hz v
  have hl := hlev v
  have hpi := Real.pi_pos
  set u := c₀ - g z
  set L := leviForm g z v
  set Q := holDerivSq g z v
  set k := kahlerQuad omega c z v
  -- `L/(π u) ≥ -C k/u ≥ -k/2`
  have h1 : -(k / 2) ≤ L / Real.pi / u := by
    rw [le_div_iff₀ hpos]
    have : C * k ≤ u * (k / 2) := by nlinarith
    nlinarith
  have h2 : (L / u + Q / u ^ 2) / Real.pi = L / Real.pi / u + Q / (Real.pi * u ^ 2) := by
    field_simp
  rw [h2]
  linarith

variable (n X) in
/-- **`AnalyticComplementCutoffStatement` holds** (`claude-twisted-l2:complement-cutoffs`; FPT
`lem:analytic-complement-cutoffs`).  With `ψ ≤ M`, `ddᶜψ ≥ -C ω` off the poles and
`c₀ = M + 2C + 1`, the function `r = -log(c₀ - ψ)` gives `σ = ω + ddᶜr ≥ ω/2 + |∂ log(c₀ - ψ)|²/π`
on `X \ A`, and `s = log(c₀ - ψ)` is an exhaustion of `X \ A` with `|ds|²_σ ≤ 4π`. -/
theorem analyticComplementCutoffStatement [MeasurableSpace X] [BorelSpace X] :
    AnalyticComplementCutoffStatement n X := by
  intro hcpt omega ψ hψ htop hcl hsm
  obtain ⟨M, hM⟩ := exists_le_coe_of_isCompact hψ (isCompact_univ (X := X))
  obtain ⟨C, hC, hlev⟩ := exists_neg_le_leviForm_of_isCompact omega hψ (isCompact_univ (X := X))
  set c₀ : ℝ := M + 2 * C + 1 with hc₀
  set U : Set X := {x | ψ x ≠ ⊥} with hU
  have hUo : IsOpen U := hcl.isOpen_compl
  have hle : ∀ x ∈ U, (ψ x).toReal ≤ M := fun x hx => by
    have h := hM x (mem_univ x)
    rw [← EReal.coe_toReal (htop x) hx] at h
    exact_mod_cast h
  have hgap : ∀ x ∈ U, 2 * C + 1 ≤ c₀ - (ψ x).toReal := fun x hx => by
    have := hle x hx
    rw [hc₀]; linarith
  set r : X → ℝ := fun x => -Real.log (c₀ - (ψ x).toReal) with hr
  set s : X → ℝ := fun x => Real.log (c₀ - (ψ x).toReal) with hs
  -- the pointwise estimate in a chart
  have hcore : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      ψ (c.val.symm z) ≠ ⊥ → ∀ v : ComplexModel n,
        kahlerQuad omega c z v / 2 + holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
          (Real.pi * (c₀ - (ψ (c.val.symm z)).toReal) ^ 2) ≤ modifiedKahlerQuad omega r c z v := by
    intro c z hz hzU v
    obtain ⟨hgs, hgeq⟩ := eventually_chartFunction_eq_toReal htop hcl hsm c hz hzU
    exact half_add_le_modifiedKahlerQuad omega c hz (hgs.self_of_nhds.of_le (by norm_cast)) hC
      (by linarith [hgap _ hzU]) (hlev c z hz (mem_univ _) _ hgs hgeq) rfl v
  have hsmooth : ∀ c : ComplexChart n X, ContDiffOn ℝ ∞
      (fun y => c₀ - (ψ (c.val.symm y)).toReal) (c.val.target ∩ c.val.symm ⁻¹' U) := fun c =>
    contDiffOn_const.sub (hsm c)
  have hposU : ∀ (c : ComplexChart n X), ∀ y ∈ c.val.target ∩ c.val.symm ⁻¹' U,
      c₀ - (ψ (c.val.symm y)).toReal ≠ 0 := fun c y hy => by
    have := hgap _ hy.2
    have : 0 < C := hC
    linarith
  refine ⟨r, ⟨fun c => ((hsmooth c).log (hposU c)).neg, fun c z hz hzU v hv => ?_⟩,
    fun c z hz hzU v => ?_, ?_⟩
  · have h := hcore c z hz hzU v
    have hk := kahlerQuad_pos omega c hz hv
    have : 0 ≤ holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
        (Real.pi * (c₀ - (ψ (c.val.symm z)).toReal) ^ 2) := by
      apply div_nonneg _ (by positivity)
      unfold holDerivSq; positivity
    linarith
  · have h := hcore c z hz hzU v
    have : 0 ≤ holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
        (Real.pi * (c₀ - (ψ (c.val.symm z)).toReal) ^ 2) := by
      apply div_nonneg _ (by positivity)
      unfold holDerivSq; positivity
    linarith
  · refine hasCompleteCutoffs_of_exhaustion omega r hUo s
      (fun c => (hsmooth c).log (hposU c)) (fun T => ?_) (C := 4 * Real.pi) (by positivity)
      fun c z hz hzU v => ?_
    · have hset : {x | x ∈ U ∧ s x ≤ T} = ψ ⁻¹' Ici ((c₀ - Real.exp T : ℝ) : EReal) := by
        ext x
        simp only [Set.mem_ofPred_eq, mem_preimage, mem_Ici, hU, hs]
        constructor
        · rintro ⟨hx, hxT⟩
          have hpos : 0 < c₀ - (ψ x).toReal := by
            have := hgap x hx; have : 0 < C := hC; linarith
          rw [← EReal.coe_toReal (htop x) hx, EReal.coe_le_coe_iff]
          have := (Real.log_le_iff_le_exp hpos).mp hxT
          linarith
        · intro hx
          have hxU : ψ x ≠ ⊥ := fun h => by
            rw [h] at hx
            exact EReal.coe_ne_bot _ (le_bot_iff.mp hx)
          refine ⟨hxU, ?_⟩
          have hpos : 0 < c₀ - (ψ x).toReal := by
            have := hgap x hxU; have : 0 < C := hC; linarith
          rw [← EReal.coe_toReal (htop x) hxU, EReal.coe_le_coe_iff] at hx
          exact (Real.log_le_iff_le_exp hpos).mpr (by linarith)
      rw [hset]
      exact (hψ.upperSemicontinuous.isClosed_preimage _).isCompact
    · have h := hcore c z hz hzU v
      obtain ⟨hgs, -⟩ := eventually_chartFunction_eq_toReal htop hcl hsm c hz hzU
      have hgd : DifferentiableAt ℝ (fun y => (ψ (c.val.symm y)).toReal) z :=
        hgs.self_of_nhds.differentiableAt (by simp)
      have hlt : (ψ (c.val.symm z)).toReal < c₀ := by
        have := hgap _ hzU; have : 0 < C := hC; linarith
      have hgr := sq_fderiv_log_sub_le hgd hlt v
      have hk := kahlerQuad_nonneg omega c hz v
      have hpi := Real.pi_pos
      have heq : holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
          (c₀ - (ψ (c.val.symm z)).toReal) ^ 2 = Real.pi *
          (holDerivSq (fun y => (ψ (c.val.symm y)).toReal) z v /
            (Real.pi * (c₀ - (ψ (c.val.symm z)).toReal) ^ 2)) := by
        field_simp
      change fderiv ℝ (fun y => Real.log (c₀ - (ψ (c.val.symm y)).toReal)) z v ^ 2 ≤ _
      rw [heq] at hgr
      nlinarith

end SGPT.Trace.TwistedL2

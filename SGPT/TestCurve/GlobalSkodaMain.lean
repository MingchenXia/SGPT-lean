import SGPT.TestCurve.GlobalSkodaStep

/-!
# Skoda's global `L²` division theorem on `X`

Blueprint `claude-global-skoda.tex`, nodes `global-skoda:ideal-integral`, `global-skoda:closure`,
`global-skoda:main`, `global-skoda:phong-sturm`.

**`globalSkodaDivision_of_sectionsAlgebraic`** proves the statement `GlobalSkodaDivision H a`
(Skoda [Sko72b]; Demailly, *Analytic methods in algebraic geometry*, Theorem 12.8 with 12.12) on
an integral smooth projective `X`, for every metrized line bundle `(L, h)`, assuming GAGA for the
sections of `L^k`, `k ≫ 0` (`SchemeSectionsAlgebraic`, the statement already used by
`phongSturmRemark_of_sectionsAlgebraic_of_globalSkodaDivision`): if `c₁(L, h)` is Kähler and
`w₁, …, w_r ∈ H⁰(X, L^d)`, `d > 0`, there is `c₀` such that for `M ≥ n + 1` and `k ≥ c₀ + Md`
every `σ ∈ H⁰(X, L^{d+k})` in `𝓘((M+1) log |w|²)` is `∑ wⱼ tⱼ` with `tⱼ ∈ H⁰(X, L^k)` in
`𝓘(M log |w|²)`.

## Proof

* On the compact `X`, `σ ∈ 𝓘((M+1) log |w|²)` iff `I(σ) = ∫ |σ|² |w|^{-2(M+1)} dμ < ∞`
  (`skodaNorm_lt_top_of_isIdealSection`, `isIdealSection_of_skodaNorm_lt_top`), for the smooth
  positive volume `μ = c₁(L, h)ⁿ`.
* One division step (`exists_step`): `I(σ - ∑ wⱼ tⱼ) ≤ (2/λ) K I(σ)` with `∫ |tⱼ|²|w|^{-2M} < ∞`,
  `λ = (k - Md) c`, `K` independent of `M, k, σ`. For `k - Md ≥ c₀` this is `≤ I(σ)/4`.
* **Closure** (`mem_of_forall_step`): the sections `∑ wⱼ tⱼ` with `∫ |tⱼ|²|w|^{-2M} < ∞` form a
  subspace `W` of the finite-dimensional `H⁰(X, L^{d+k})`; iterating the step,
  `I(σ - τ_N) ≤ 4^{-N} I(σ)` with `τ_N ∈ W`, so `τ_N → σ` in the `L²(μ)` norm (the weight
  `|w|^{-2(M+1)}` is bounded below), and `W` is closed: `σ ∈ W`.

As corollaries, `rmk:PhongSturm` follows from GAGA for `H⁰(X, L^k)` alone
(`phongSturmRemark_of_sectionsAlgebraic`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.TestCurve.GlobalSkoda

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Metric SGPT.Okounkov
  SGPT.LineBundle
open SGPT.TestCurve.TestConfig SGPT.TestCurve.SkodaInc SGPT.TestCurve.SkodaRWN MeasureTheory Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.NAPotential.GAGAMult SGPT.Bergman.TensorDictionaryDraft SGPT.PSH.GlobalL2
open SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open scoped Topology ENNReal ContDiff Manifold

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance globalSkodaMainTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance globalSkodaMainCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance globalSkodaMainMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance globalSkodaMainBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

local instance globalSkodaMainManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

section Manifold

variable [IsSeparated f] [QuasiCompact f]

/-! ### Multiplier ideals and weighted `L²` norms on the compact `X` -/

/-- A finite cover by open sets of finite mass gives finite mass. -/
theorem lintegral_lt_top_of_local [CompactSpace (SchemeComplexPoint f)]
    {μ : Measure (SchemeComplexPoint f)} {F : SchemeComplexPoint f → ℝ≥0∞}
    (hloc : ∀ x, ∃ W : Set (SchemeComplexPoint f), IsOpen W ∧ x ∈ W ∧ ∫⁻ y in W, F y ∂μ < ⊤) :
    ∫⁻ y, F y ∂μ < ⊤ := by
  classical
  choose W hW hxW hfin using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  have hU : (⋃ x ∈ t, W x) = univ := eq_univ_of_forall fun y => ht (mem_univ y)
  calc ∫⁻ y, F y ∂μ = ∫⁻ y in ⋃ x ∈ t, W x, F y ∂μ := by rw [hU, Measure.restrict_univ]
    _ ≤ ∑ x ∈ t, ∫⁻ y in W x, F y ∂μ := lintegral_biUnion_finset_le _ _ _
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ => hfin x

/-- **Sections in a multiplier ideal have finite weighted `L²` norm**: on the compact `X`,
`σ ∈ H⁰(X, L^m ⊗ 𝓘(c log |w|²))` gives `∫_X |σ|²_{h^m} |w|^{-2c} dμ < ∞`. -/
theorem skodaNorm_lt_top_of_isIdealSection [CompactSpace (SchemeComplexPoint f)]
    {μ : Measure (SchemeComplexPoint f)} (hμ : IsSmoothPositiveVolume (n := n) μ) {d r : ℕ}
    (w : Fin r → SectionSpace f L d) {c : ℝ} (hc : 0 < c) {m : ℕ} (σ : SectionSpace f L m)
    (hσ : IsIdealSection f n E (multiplierIdeal (n := n) c (familyLog H a d w)) m σ) :
    skodaNorm H a μ d w c m σ < ⊤ := by
  refine lintegral_lt_top_of_local fun p => ?_
  set e := complexChartAt (n := n) p with he
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  obtain ⟨-, -, V, hVo, hpV, -, -, hVint⟩ := hσ (a.opens i) (a.frame i) p hi
  set Dm : Set (ComplexModel n) :=
    e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' (a.opens i)) with hDm
  have hDo : IsOpen Dm :=
    e.val.isOpen_inter_preimage_symm ((a.opens i).isOpen.preimage
      (schemeComplexPointImage_continuous f))
  have hpD : e.val p ∈ Dm := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ a.opens i
    rw [e.val.left_inv hpe]; exact hi
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hDo.inter hVo) _ ⟨hpD, hpV⟩
  set ρ := ε / 2 with hρdef
  have hρ : 0 < ρ := half_pos hε
  have hcb : closedBall (e.val p) ρ ⊆ Dm ∩ V := fun z hz =>
    hεsub (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hε))
  obtain ⟨dn, hdns, hdnpos, hmap⟩ := hμ e
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall (e.val p) ρ).exists_bound_of_continuousOn
    (hdns.continuousOn.mono fun z hz => (hcb hz).1.1)
  have hNc : ContinuousOn (fun z => H.frameNormSq (a.frame i) (e.val.symm z)) Dm :=
    (H.smooth (a.frame i) e).continuousOn
  obtain ⟨B₂, hB₂⟩ := (isCompact_closedBall (e.val p) ρ).exists_bound_of_continuousOn
    ((hNc.pow m).mono fun z hz => (hcb hz).1)
  refine ⟨e.val.source ∩ e.val ⁻¹' ball (e.val p) ρ,
    e.val.isOpen_inter_preimage isOpen_ball, ⟨hpe, mem_ball_self hρ⟩, ?_⟩
  set F : SchemeComplexPoint f → ℝ≥0∞ := fun x => ENNReal.ofReal (H.sectionNormSq a m σ x) *
    multiplierWeight c (familyLog H a d w x) with hFdef
  have hFm : Measurable F := measurable_skodaDensity H a d w hc.le m σ
  set g := sectionFrameCoefficient f n E (a.frame i) m σ with hg
  have hpt : ∀ z ∈ closedBall (e.val p) ρ, ENNReal.ofReal (dn z) * F (e.val.symm z) ≤
      ENNReal.ofReal (|B₁| * |B₂|) * multiplierDensity (chartFunction (familyLog H a d w) e) c
        (fun z => g (e.val.symm z)) z := by
    intro z hz
    have hzD := (hcb hz).1
    have h1 := hB₁ z hz
    have h2 := hB₂ z hz
    rw [Real.norm_eq_abs] at h1 h2
    have hN := H.sectionNormSq_frame a (a.frame i) m σ (e.val.symm z) hzD.2
    simp only [hFdef, multiplierDensity, chartFunction]
    rw [hN, Complex.normSq_eq_norm_sq, ← mul_assoc, ← ENNReal.ofReal_mul (hdnpos z hzD.1).le,
      ← mul_assoc (ENNReal.ofReal (|B₁| * |B₂|)) (ENNReal.ofReal _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    have hd0 : 0 ≤ dn z := (hdnpos z hzD.1).le
    have hN0 : 0 ≤ H.frameNormSq (a.frame i) (e.val.symm z) ^ m :=
      pow_nonneg (H.positive _ _ hzD.2).le m
    calc dn z * (‖g (e.val.symm z)‖ ^ 2 * H.frameNormSq (a.frame i) (e.val.symm z) ^ m)
        = (dn z * H.frameNormSq (a.frame i) (e.val.symm z) ^ m) * ‖g (e.val.symm z)‖ ^ 2 := by
          ring
      _ ≤ (|B₁| * |B₂|) * ‖g (e.val.symm z)‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul ((le_abs_self _).trans
            (h1.trans (le_abs_self _))) ((le_abs_self _).trans (h2.trans (le_abs_self _))) hN0
            (abs_nonneg _)) (sq_nonneg _)
  calc ∫⁻ y in e.val.source ∩ e.val ⁻¹' ball (e.val p) ρ, F y ∂μ
      ≤ ∫⁻ y in e.val.source ∩ e.val ⁻¹' closedBall (e.val p) ρ, F y ∂μ :=
        lintegral_mono_set (inter_subset_inter_right _ (preimage_mono ball_subset_closedBall))
    _ = ∫⁻ z in closedBall (e.val p) ρ, ENNReal.ofReal (dn z) * F (e.val.symm z) :=
        setLIntegral_source_inter_preimage e hdns.continuousOn hmap (isCompact_closedBall _ _)
          (fun z hz => (hcb hz).1.1) hFm
    _ ≤ ∫⁻ z in closedBall (e.val p) ρ, ENNReal.ofReal (|B₁| * |B₂|) *
          multiplierDensity (chartFunction (familyLog H a d w) e) c
            (fun z => g (e.val.symm z)) z :=
        setLIntegral_mono' isClosed_closedBall.measurableSet hpt
    _ = ENNReal.ofReal (|B₁| * |B₂|) * ∫⁻ z in closedBall (e.val p) ρ,
          multiplierDensity (chartFunction (familyLog H a d w) e) c
            (fun z => g (e.val.symm z)) z := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (|B₁| * |B₂|) * ∫⁻ z in V,
          multiplierDensity (chartFunction (familyLog H a d w) e) c
            (fun z => g (e.val.symm z)) z :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set fun z hz => (hcb hz).2) zero_le
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVint

/-- **Finite weighted `L²` norm gives membership in the multiplier ideal**: for a Borel weight `ψ`,
`c > 0` and a smooth positive volume, `∫_X |σ|²_{h^m} e^{-cψ} dμ < ∞` gives
`σ ∈ H⁰(X, L^m ⊗ 𝓘(cψ))`. -/
theorem isIdealSection_of_lintegral_lt_top {μ : Measure (SchemeComplexPoint f)}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {ψ : SchemeComplexPoint f → EReal}
    (hψ : Measurable ψ) {c : ℝ} (hc : 0 < c) {m : ℕ} (σ : SectionSpace f L m)
    (hfin : ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a m σ y) * multiplierWeight c (ψ y) ∂μ < ⊤) :
    IsIdealSection f n E (multiplierIdeal (n := n) c ψ) m σ := by
  intro U α p hp
  set e := complexChartAt (n := n) p with he
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  set G : ComplexModel n → ℂ := fun z => sectionFrameCoefficient f n E α m σ (e.val.symm z)
    with hG
  set w : ComplexModel n → ℝ := fun z => H.frameNormSq α (e.val.symm z) with hw
  set Dm : Set (ComplexModel n) :=
    e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) with hDm
  have hDopen : IsOpen Dm :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ Dm := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  obtain ⟨r₀, hr₀, hr₀D⟩ := Metric.isOpen_iff.mp hDopen _ hz0D
  set r := r₀ / 2 with hr
  have hrpos : 0 < r := half_pos hr₀
  have hcb : closedBall (e.val p) r ⊆ Dm := fun z hz =>
    hr₀D (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hr₀))
  obtain ⟨ρ, hρsmooth, hρpos, hmap⟩ := hμ e
  have hwcont : ContinuousOn w Dm := (H.smooth α e).continuousOn
  have hwpos : ∀ z ∈ Dm, 0 < w z := fun z hz => H.positive α _ hz.2
  obtain ⟨zw, hzw, hwmin⟩ := (isCompact_closedBall (e.val p) r).exists_isMinOn
    (nonempty_closedBall.mpr hrpos.le) (hwcont.mono hcb)
  obtain ⟨zρ, hzρ, hρmin⟩ := (isCompact_closedBall (e.val p) r).exists_isMinOn
    (nonempty_closedBall.mpr hrpos.le)
    (hρsmooth.continuousOn.mono fun z hz => (hcb hz).1)
  set κ : ℝ := ρ zρ * w zw ^ m with hκ
  have hκpos : 0 < κ := mul_pos (hρpos _ (hcb hzρ).1) (pow_pos (hwpos _ (hcb hzw)) m)
  set fM : SchemeComplexPoint f → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (H.sectionNormSq a m σ y) * multiplierWeight c (ψ y) with hfM
  have hWmeas : Measurable fun y => multiplierWeight c (ψ y) :=
    (multiplierWeight_antitone hc.le).measurable.comp hψ
  have hfMmeas : Measurable fM :=
    (ENNReal.continuous_ofReal.comp (continuous_sectionNormSq H a m σ)).measurable.mul hWmeas
  set dens := multiplierDensity (chartFunction ψ e) c G with hdens
  have hbound : ∀ z ∈ closedBall (e.val p) r,
      dens z ≤ ENNReal.ofReal κ⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) := by
    intro z hz
    have hzD := hcb hz
    have hN : H.sectionNormSq a m σ (e.val.symm z) = ‖G z‖ ^ 2 * w z ^ m := by
      rw [H.sectionNormSq_frame a α m σ _ hzD.2, Complex.normSq_eq_norm_sq]
      rfl
    have hρw : κ ≤ ρ z * w z ^ m :=
      mul_le_mul (hρmin hz) (pow_le_pow_left₀ (hwpos _ (hcb hzw)).le (hwmin hz) m)
        (pow_pos (hwpos _ (hcb hzw)) m).le (hρpos _ hzD.1).le
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (ρ z * w z ^ m) := by
      rw [← ENNReal.ofReal_mul (inv_pos.mpr hκpos).le, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div, le_div_iff₀ hκpos, one_mul]
      exact hρw
    have heq : ENNReal.ofReal κ⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) =
        (ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (ρ z * w z ^ m)) * dens z := by
      simp only [hfM, hdens, multiplierDensity, chartFunction]
      rw [hN, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (hρpos _ hzD.1).le]
      ring
    rw [heq]
    calc dens z = 1 * dens z := (one_mul _).symm
      _ ≤ _ := mul_le_mul' hone le_rfl
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, hc, ball (e.val p) r,
    isOpen_ball, mem_ball_self hrpos, ?_, ?_, ?_⟩
  · intro z hz
    have hzD : z ∈ Dm := hcb (ball_subset_closedBall hz)
    exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
      (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).self_of_nhds
      ).differentiableWithinAt
  · have hGc : ContinuousOn G (ball (e.val p) r) := by
      intro z hz
      have hzD : z ∈ Dm := hcb (ball_subset_closedBall hz)
      exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hzD.1
        (schemeOpenRegularFunction_holomorphicAt f n E U _ _ hzD.2).self_of_nhds
        ).continuousAt.continuousWithinAt
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖G z‖ ^ 2))
        (volume.restrict (ball (e.val p) r)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hGc)).aemeasurable
          measurableSet_ball)
    have h2 : AEMeasurable (fun z => multiplierWeight c (ψ (e.val.symm z)))
        (volume.restrict (ball (e.val p) r)) :=
      hWmeas.comp_aemeasurable ((e.val.continuousOn_symm.mono fun z hz =>
        (hcb (ball_subset_closedBall hz)).1).aemeasurable measurableSet_ball)
    exact h1.mul h2
  · calc (∫⁻ z in ball (e.val p) r, dens z)
        ≤ ∫⁻ z in closedBall (e.val p) r, dens z := lintegral_mono_set ball_subset_closedBall
      _ ≤ ∫⁻ z in closedBall (e.val p) r,
            ENNReal.ofReal κ⁻¹ * (ENNReal.ofReal (ρ z) * fM (e.val.symm z)) :=
          setLIntegral_mono' isClosed_closedBall.measurableSet hbound
      _ = ENNReal.ofReal κ⁻¹ *
            ∫⁻ z in closedBall (e.val p) r, ENNReal.ofReal (ρ z) * fM (e.val.symm z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal κ⁻¹ *
            ∫⁻ y in e.val.source ∩ e.val ⁻¹' closedBall (e.val p) r, fM y ∂μ := by
          rw [setLIntegral_source_inter_preimage e hρsmooth.continuousOn hmap
            (isCompact_closedBall _ _) (fun z hz => (hcb hz).1) hfMmeas]
      _ ≤ ENNReal.ofReal κ⁻¹ * ∫⁻ y, fM y ∂μ :=
          mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-! ### The sections of finite weighted norm -/

/-- The sections of `L^m` with `∫ |σ|² |w|^{-2c} dμ < ∞`, a subspace. -/
def finiteNormSubmodule (μ : Measure (SchemeComplexPoint f)) (d : ℕ) {r : ℕ}
    (w : Fin r → SectionSpace f L d) {c : ℝ} (hc : 0 ≤ c) (m : ℕ) :
    Submodule ℂ (SectionSpace f L m) where
  carrier := {s | skodaNorm H a μ d w c m s ≠ ⊤}
  zero_mem' := by
    change skodaNorm H a μ d w c m 0 ≠ ⊤
    simp only [skodaNorm, sectionNormSq_zero, ENNReal.ofReal_zero, zero_mul, lintegral_zero]
    exact ENNReal.zero_ne_top
  add_mem' := by
    intro s t hs ht
    change skodaNorm H a μ d w c m (s + t) ≠ ⊤
    change skodaNorm H a μ d w c m s ≠ ⊤ at hs
    change skodaNorm H a μ d w c m t ≠ ⊤ at ht
    have hpt : ∀ x, ENNReal.ofReal (H.sectionNormSq a m (s + t) x) *
        multiplierWeight c (familyLog H a d w x) ≤
        2 * (ENNReal.ofReal (H.sectionNormSq a m s x) * multiplierWeight c (familyLog H a d w x)) +
          2 * (ENNReal.ofReal (H.sectionNormSq a m t x) *
            multiplierWeight c (familyLog H a d w x)) := by
      intro x
      rw [sectionNormSq_eq_sectionGauge H a, sectionNormSq_eq_sectionGauge H a,
        sectionNormSq_eq_sectionGauge H a, map_add]
      have h1 : ‖sectionGauge H a m x s + sectionGauge H a m x t‖ ^ 2 ≤
          2 * ‖sectionGauge H a m x s‖ ^ 2 + 2 * ‖sectionGauge H a m x t‖ ^ 2 := by
        have := norm_add_le (sectionGauge H a m x s) (sectionGauge H a m x t)
        nlinarith [norm_nonneg (sectionGauge H a m x s), norm_nonneg (sectionGauge H a m x t),
          norm_nonneg (sectionGauge H a m x s + sectionGauge H a m x t),
          sq_nonneg (‖sectionGauge H a m x s‖ - ‖sectionGauge H a m x t‖)]
      calc ENNReal.ofReal (‖sectionGauge H a m x s + sectionGauge H a m x t‖ ^ 2) *
            multiplierWeight c (familyLog H a d w x)
          ≤ ENNReal.ofReal (2 * ‖sectionGauge H a m x s‖ ^ 2 + 2 * ‖sectionGauge H a m x t‖ ^ 2) *
            multiplierWeight c (familyLog H a d w x) :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h1) zero_le
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul zero_le_two,
              ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
            ring
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [lintegral_add_left ((measurable_skodaDensity H a d w hc m s).const_mul 2),
      lintegral_const_mul _ (measurable_skodaDensity H a d w hc m s),
      lintegral_const_mul _ (measurable_skodaDensity H a d w hc m t)]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hs,
      ENNReal.mul_ne_top (by norm_num) ht⟩
  smul_mem' := by
    intro z s hs
    change skodaNorm H a μ d w c m (z • s) ≠ ⊤
    change skodaNorm H a μ d w c m s ≠ ⊤ at hs
    have heq : ∀ x, ENNReal.ofReal (H.sectionNormSq a m (z • s) x) *
        multiplierWeight c (familyLog H a d w x) = ENNReal.ofReal (‖z‖ ^ 2) *
          (ENNReal.ofReal (H.sectionNormSq a m s x) * multiplierWeight c (familyLog H a d w x)) := by
      intro x
      rw [sectionNormSq_eq_sectionGauge H a, sectionNormSq_eq_sectionGauge H a, map_smul,
        smul_eq_mul, norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
    simp only [skodaNorm, heq]
    rw [lintegral_const_mul _ (measurable_skodaDensity H a d w hc m s)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs

/-! ### The closure argument -/

/-- **Closure in the finite-dimensional `H⁰(X, L^m)`**: if every section of finite weighted norm
`I` is approximated by `W` up to a quarter of its norm, every section of finite weighted norm
lies in `W`. -/
theorem mem_of_forall_step [IsIntegral X] [Nonempty (SchemeComplexPoint f)]
    [CompactSpace (SchemeComplexPoint f)] {μ : Measure (SchemeComplexPoint f)} [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] {d r : ℕ} (w : Fin r → SectionSpace f L d) {c : ℝ} (hc : 0 ≤ c) {m : ℕ}
    (W : Submodule ℂ (SectionSpace f L m))
    (hstep : ∀ s : SectionSpace f L m, skodaNorm H a μ d w c m s ≠ ⊤ →
      ∃ τ ∈ W, skodaNorm H a μ d w c m (s - τ) ≤ ENNReal.ofReal (1 / 4) * skodaNorm H a μ d w c m s)
    (σ : SectionSpace f L m) (hσ : skodaNorm H a μ d w c m σ ≠ ⊤) : σ ∈ W := by
  -- the iteration
  have hiter : ∀ N : ℕ, ∃ τ ∈ W, skodaNorm H a μ d w c m (σ - τ) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ N) * skodaNorm H a μ d w c m σ := by
    intro N
    induction N with
    | zero => exact ⟨0, W.zero_mem, by simp⟩
    | succ N ih =>
      obtain ⟨τ, hτ, hle⟩ := ih
      have hfin : skodaNorm H a μ d w c m (σ - τ) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσ) hle
      obtain ⟨τ', hτ', hle'⟩ := hstep (σ - τ) hfin
      refine ⟨τ + τ', W.add_mem hτ hτ', ?_⟩
      rw [show σ - (τ + τ') = σ - τ - τ' by abel]
      calc skodaNorm H a μ d w c m (σ - τ - τ')
          ≤ ENNReal.ofReal (1 / 4) * skodaNorm H a μ d w c m (σ - τ) := hle'
        _ ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal ((1 / 4 : ℝ) ^ N) *
            skodaNorm H a μ d w c m σ) := mul_le_mul_of_nonneg_left hle zero_le
        _ = ENNReal.ofReal ((1 / 4 : ℝ) ^ (N + 1)) * skodaNorm H a μ d w c m σ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), pow_succ,
              mul_comm (1 / 4 : ℝ)]
  choose τ hτW hτle using hiter
  -- the weight is bounded below
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_familyNormSq H a d w).continuousOn
  set B : ℝ := max B₀ 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  set β : ℝ := Real.exp (-(c * Real.log B)) with hβdef
  have hβ : 0 < β := Real.exp_pos _
  have hwlow : ∀ x, ENNReal.ofReal β ≤ multiplierWeight c (familyLog H a d w x) := by
    intro x
    have hle : familyLog H a d w x ≤ ((Real.log B : ℝ) : EReal) := by
      rw [familyLog, ← ENNReal.log_ofReal_of_pos (by linarith : (0 : ℝ) < B)]
      refine ENNReal.log_monotone (ENNReal.ofReal_le_ofReal ?_)
      have := hB₀ x (mem_univ x)
      rw [Real.norm_of_nonneg (familyNormSq_nonneg H a d w x)] at this
      exact this.trans (le_max_left _ _)
    calc ENNReal.ofReal β = multiplierWeight c ((Real.log B : ℝ) : EReal) := by
          rw [multiplierWeight_coe]
      _ ≤ multiplierWeight c (familyLog H a d w x) := multiplierWeight_antitone hc hle
  -- the `L²(μ)` norm is controlled by the weighted norm
  have hL2 : ∀ s : SectionSpace f L m,
      ∫⁻ x, ENNReal.ofReal (H.sectionNormSq a m s x) ∂μ ≤
        ENNReal.ofReal β⁻¹ * skodaNorm H a μ d w c m s := by
    intro s
    rw [skodaNorm, ← lintegral_const_mul _ (measurable_skodaDensity H a d w hc m s)]
    refine lintegral_mono fun x => ?_
    calc ENNReal.ofReal (H.sectionNormSq a m s x)
        = (ENNReal.ofReal β⁻¹ * ENNReal.ofReal β) * ENNReal.ofReal (H.sectionNormSq a m s x) := by
          rw [← ENNReal.ofReal_mul (inv_pos.mpr hβ).le, inv_mul_cancel₀ hβ.ne', ENNReal.ofReal_one,
            one_mul]
      _ ≤ (ENNReal.ofReal β⁻¹ * multiplierWeight c (familyLog H a d w x)) *
            ENNReal.ofReal (H.sectionNormSq a m s x) := by gcongr; exact hwlow x
      _ = _ := by ring
  -- convergence in `L²(μ)`
  set e := L2Sections.equiv (H := H) (a := a) (μ := μ) m with he
  have hnorm : ∀ s : SectionSpace f L m, ‖e s‖ ^ 2 =
      (∫⁻ x, ENNReal.ofReal (H.sectionNormSq a m s x) ∂μ).toReal := by
    intro s
    rw [L2Sections.norm_sq_eq, integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => H.sectionNormSq_nonneg a m _ x)
      (continuous_sectionNormSq H a m _).aestronglyMeasurable]
    rfl
  have htend : Tendsto (fun N => e (τ N)) atTop (𝓝 (e σ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : ∀ N, ‖e (τ N) - e σ‖ ^ 2 ≤
        β⁻¹ * ((1 / 4 : ℝ) ^ N * (skodaNorm H a μ d w c m σ).toReal) := by
      intro N
      rw [show e (τ N) - e σ = -(e (σ - τ N)) by rw [map_sub, neg_sub], norm_neg, hnorm]
      have h1 := (hL2 (σ - τ N)).trans
        (mul_le_mul_of_nonneg_left (hτle N) zero_le)
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσ)) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_pos.mpr hβ).le,
        ENNReal.toReal_ofReal (by positivity)] at h2
    have hlim : Tendsto (fun N : ℕ => Real.sqrt (β⁻¹ * ((1 / 4 : ℝ) ^ N *
        (skodaNorm H a μ d w c m σ).toReal))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N : ℕ => β⁻¹ * ((1 / 4 : ℝ) ^ N *
          (skodaNorm H a μ d w c m σ).toReal)) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num)).mul_const (skodaNorm H a μ d w c m σ).toReal
        have := this.const_mul β⁻¹
        simpa using this
      have := (Real.continuous_sqrt.tendsto 0).comp h0
      rwa [Real.sqrt_zero] at this
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim
    exact Real.le_sqrt_of_sq_le (hsq N)
  -- `W` is closed
  have := SectionSpace.finiteDimensional f E a m
  have : FiniteDimensional ℂ (L2Sections H a μ m) := LinearEquiv.finiteDimensional e
  set W' : Submodule ℂ (L2Sections H a μ m) := W.map e.toLinearMap with hW'
  have hclosed : IsClosed (W' : Set (L2Sections H a μ m)) := Submodule.closed_of_finiteDimensional W'
  have hmem : e σ ∈ W' := hclosed.mem_of_tendsto htend
    (Eventually.of_forall fun N => Submodule.mem_map_of_mem (hτW N))
  obtain ⟨σ', hσ'W, hσ'⟩ := Submodule.mem_map.mp hmem
  have : σ' = σ := e.injective hσ'
  rwa [← this]

end Manifold

/-! ### Skoda's division theorem -/

/-- **Skoda's `L²` division theorem on `X`** (`GlobalSkodaDivision`; Skoda [Sko72b], Demailly,
*Analytic methods in algebraic geometry*, Theorems 12.8 and 12.12), for an integral smooth
projective `X` and every metrized line bundle `(L, h)`, from GAGA for the sections of `L^k`,
`k ≫ 0`: if `c₁(L, h)` is Kähler and `w₁, …, w_r ∈ H⁰(X, L^d)`, `d > 0`, there is `c₀` such that
for `M ≥ n + 1` and `k ≥ c₀ + Md` every `σ ∈ H⁰(X, L^{d+k})` in `𝓘((M + 1) log |w|²)` is
`∑ⱼ wⱼ tⱼ` with `tⱼ ∈ H⁰(X, L^k)` in `𝓘(M log |w|²)`. -/
theorem globalSkodaDivision_of_sectionsAlgebraic [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)]
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j) :
    GlobalSkodaDivision H a := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro hK d r hd w
  set μ := curvatureVolume H a hK with hμdef
  have hμ : IsSmoothPositiveVolume (n := n) μ := isSmoothPositiveVolume_curvatureVolume H a hK
  have : IsFiniteMeasure μ := isFiniteMeasure_curvatureVolume H a hK
  have : μ.IsOpenPosMeasure := isOpenPosMeasure_curvatureVolume H a hK
  obtain ⟨D⟩ := exists_coverData (curvatureKahlerBackground H a hK) hμ
    (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f n E a H)
    isSourceSmoothHermitianMetric_unit (isOwnFirstChernForm_schemeHermitianLineBundle f n E a H)
    (δ := 1) one_pos
  obtain ⟨c, hc, hcL⟩ := exists_levi_lower_bound H a D hK
  set K := stepConst H a D r with hKdef
  have hKtop : K ≠ ⊤ := stepConst_ne_top H a D r
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hgaga
  set c₀' : ℕ := ⌈(D.lam + 8 * K.toReal) / c⌉₊ with hc₀'
  refine ⟨j₀ + 1 + c₀', fun M k hnM hk σ hσ => ?_⟩
  -- the constants
  have hkR : ((j₀ + 1 + c₀' : ℕ) : ℝ) + M * d ≤ k := by exact_mod_cast hk
  have hc₀le : (D.lam + 8 * K.toReal) / c ≤ c₀' := Nat.le_ceil _
  have hlamge : D.lam + 8 * K.toReal ≤ lamOf c M k d := by
    have h1 : (c₀' : ℝ) ≤ (k : ℝ) - M * d := by push_cast at hkR; linarith
    rw [div_le_iff₀ hc] at hc₀le
    unfold lamOf
    nlinarith
  have hK0 : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  have hlam : D.lam ≤ lamOf c M k d := by linarith
  have hlam0 : 0 < lamOf c M k d := lt_of_lt_of_le D.lam_pos hlam
  have hMk : (M : ℝ) * d < k := by
    have : (0 : ℝ) < (k : ℝ) - M * d := by
      unfold lamOf at hlam0
      exact (pos_of_mul_pos_left hlam0 hc.le)
    linarith
  have hfac : ENNReal.ofReal (2 / lamOf c M k d) * K ≤ ENNReal.ofReal (1 / 4) := by
    rw [← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hlam0]
    have := D.lam_pos
    linarith
  have hgk : SchemeSectionsAlgebraic f n E a H k := hj₀ k (by omega)
  -- the subspace of the `∑ wⱼ tⱼ`
  set T := finiteNormSubmodule H a μ d w (Nat.cast_nonneg M) k with hTdef
  set Φ : (Fin r → T) →ₗ[ℂ] SectionSpace f L (d + k) :=
    ∑ j, (SectionSpace.mul f a d k (w j)).comp (T.subtype.comp (LinearMap.proj j)) with hΦdef
  have hΦ : ∀ tt : Fin r → T, Φ tt = ∑ j, SectionSpace.mul f a d k (w j) (tt j) := by
    intro tt
    simp only [hΦdef, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply]
  have hstep : ∀ s : SectionSpace f L (d + k),
      skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) s ≠ ⊤ →
      ∃ τ ∈ LinearMap.range Φ, skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) (s - τ) ≤
        ENNReal.ofReal (1 / 4) * skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) s := by
    intro s hs
    obtain ⟨t, ht, hle⟩ := exists_step H a D hcL hc hnM hMk hlam w hgk s hs
    refine ⟨Φ fun j => ⟨t j, ht j⟩, LinearMap.mem_range_self _ _, ?_⟩
    rw [hΦ]
    exact hle.trans (mul_le_mul_of_nonneg_right hfac zero_le)
  have hσfin : skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) σ ≠ ⊤ :=
    (skodaNorm_lt_top_of_isIdealSection H a hμ w (by positivity) σ hσ).ne
  have hmem := mem_of_forall_step H a w (Nat.cast_nonneg _) (LinearMap.range Φ) hstep σ hσfin
  obtain ⟨tt, htt⟩ := LinearMap.mem_range.mp hmem
  refine ⟨fun j => (tt j : SectionSpace f L k), fun j => ?_, ?_⟩
  · have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    exact isIdealSection_of_lintegral_lt_top H a hμ (continuous_familyLog H a d w).measurable hM0
      _ (lt_top_iff_ne_top.mpr (tt j).2)
  · rw [← htt, hΦ]

/-- **`rmk:PhongSturm` from GAGA for `H⁰(X, L^k)` alone**: for `L` ample on the integral smooth
projective `X`, `h = e^{-φ}` positively curved and `μ = (dd^c φ)ⁿ`, GAGA for the sections of
`L^k`, `k ≫ 0`, gives `Γ^{𝓕*}_t = Φ(t)` for every ample test configuration and all `t > 0`
(Skoda's division theorem is now proved: `globalSkodaDivision_of_sectionsAlgebraic`). -/
theorem phongSturmRemark_of_sectionsAlgebraic [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hgaga : letI := E.isSeparated; letI := E.quasiCompact;
      ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j) :
    PhongSturmRemark H a (curvatureVolume H a hK) :=
  phongSturmRemark_of_sectionsAlgebraic_of_globalSkodaDivision H P hK hgaga
    (globalSkodaDivision_of_sectionsAlgebraic H a hgaga)

end SGPT.TestCurve.GlobalSkoda

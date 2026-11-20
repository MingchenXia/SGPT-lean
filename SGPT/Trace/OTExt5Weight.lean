import SGPT.Trace.OTExt5Ricci
import SGPT.Trace.OTExt4Pole
import SGPT.Trace.TwistedL2OTExtCurvature
import SGPT.PSH.GlobalL2CoverData
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
import SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Okounkov.MultiplierCancellation

/-!
# The weight `ψ = Φ + q log R` of Steps 1--4 and its twisted curvature

Blueprint `claude-ot-ext5.tex`, nodes `claude-ot-ext5:weight`, `claude-ot-ext5:levi`,
`claude-ot-ext5:curvature`.  Xia, *Foundations of pluripotential theory*, q07, proof of
`thm:compact-submanifold-extension`, Step 1.

* `poleWeight Φ q R = Φ + q log R` (`log 0 = -∞`), the weight `ψ` of the metric
  `h₀ e^{-Φ} R^{-q}`, and the twist functions `twistA ε R = μ(log(ε + R))`,
  `twistBX ε R = (2 - log(ε + R))²` of FPT `lem:critical-twist-functions`.
* `multiplierWeight_poleWeight`: `e^{-ψ} = e^{-Φ} R^{-q}` off `W`.
* `isAdmissibleSingularWeight_poleWeight`: for `Φ ∈ PSH(X, θ)` with gentle analytic singularities and
  a normal pole `R` of `W`, `ψ` is an admissible singular weight (quasi-psh, closed pole set
  `{Φ = -∞} ∪ W` locally contained in a nowhere dense analytic set, smooth off it).  The local
  analytic nullity of pole sets of potentials with analytic singularities is
  `exists_analyticNull_chart` (identity theorem on balls).
* `leviForm_frameWeight_add_ge`: for `Φ ∈ PSH(X, θ_V - N ω)` with `θ_V = c₁(V, h₀)`, smooth near a
  point, `Levi(-log |e|²_{h₀} + Φ) ≥ π N ω` in every chart and frame.
* `twistedCurvature_poleWeight_ge`: FPT `eq:global-normal-twisted-curvature` in every chart, frame
  and chart density of the Kähler volume, for `N₀ = 1 + b_K/π + (q + 2) b`:
  `H_ε ≥ π ω + (ε/R) |∂ψ_ε|²` off the poles.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt5

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm frameWeight contDiffOn_frameWeight)
open SGPT.Trace.TwistedL2
open SGPT.Trace.OTExt2 (IsGlobalNormalPole logPole)

/-! ### Extended-real weights -/

theorem multiplierWeight_one_add {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    multiplierWeight 1 (a + b) = multiplierWeight 1 a * multiplierWeight 1 b := by
  have hpos : ∀ c : EReal, c ≠ ⊤ → multiplierWeight 1 c ≠ 0 := by
    intro c hc
    induction c using EReal.rec with
    | bot => rw [multiplierWeight_bot one_pos]; exact ENNReal.top_ne_zero
    | top => exact absurd rfl hc
    | coe r => rw [multiplierWeight_coe]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  induction a using EReal.rec with
  | bot => rw [EReal.bot_add, multiplierWeight_bot one_pos, ENNReal.top_mul (hpos b hb)]
  | top => exact absurd rfl ha
  | coe r =>
    induction b using EReal.rec with
    | bot => rw [EReal.add_bot, multiplierWeight_bot one_pos, ENNReal.mul_top (hpos _ ha)]
    | top => exact absurd rfl hb
    | coe s =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The weight `ψ = Φ + q log R` of the metric `h₀ e^{-Φ} R^{-q}`. -/
def poleWeight (Φ : X → EReal) (q : ℕ) (R : X → ℝ) (x : X) : EReal :=
  Φ x + ((q : ℝ) : EReal) * logPole R x

/-- The twist function `a_ε = μ(log(ε + R))` (FPT `lem:critical-twist-functions`). -/
def twistA (ε : ℝ) (R : X → ℝ) (x : X) : ℝ := twistMu ε (Real.log (ε + R x))

/-- The twist function `b_ε = (2 - log(ε + R))²`. -/
def twistBX (ε : ℝ) (R : X → ℝ) (x : X) : ℝ := twistB (Real.log (ε + R x))

theorem logPole_ne_top (R : X → ℝ) (x : X) : logPole R x ≠ ⊤ := by
  rw [logPole, ne_eq, ENNReal.log_eq_top_iff]; exact ENNReal.ofReal_ne_top

theorem logPole_of_pos {R : X → ℝ} {x : X} (hx : 0 < R x) :
    logPole R x = (Real.log (R x) : EReal) := by
  rw [logPole, ENNReal.log_pos_real' (by rw [ENNReal.toReal_ofReal hx.le]; exact hx),
    ENNReal.toReal_ofReal hx.le]

theorem coe_mul_logPole_ne_top (q : ℕ) (R : X → ℝ) (x : X) :
    ((q : ℝ) : EReal) * logPole R x ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · simp [hq]
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  induction h : logPole R x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hq']; exact bot_ne_top
  | top => exact absurd h (logPole_ne_top R x)
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _

theorem multiplierWeight_one_coe_mul (c : ℝ) (a : EReal) :
    multiplierWeight 1 ((c : EReal) * a) = multiplierWeight c a := by
  simp [multiplierWeight]

/-- `e^{-ψ} = e^{-Φ} R^{-q}` where `R > 0`. -/
theorem multiplierWeight_poleWeight {Φ : X → EReal} (hΦ : ∀ x, Φ x ≠ ⊤) (q : ℕ) {R : X → ℝ}
    {x : X} (hx : 0 < R x) :
    multiplierWeight 1 (poleWeight Φ q R x) =
      multiplierWeight 1 (Φ x) * ENNReal.ofReal ((R x ^ q)⁻¹) := by
  rw [poleWeight, multiplierWeight_one_add (hΦ x) (coe_mul_logPole_ne_top q R x),
    multiplierWeight_one_coe_mul,
    SGPT.Trace.OTExt4.multiplierWeight_logPole hx, Real.rpow_neg hx.le, Real.rpow_natCast]

theorem poleWeight_eq_bot_iff {Φ : X → EReal} {q : ℕ} (hq : 0 < q) {R : X → ℝ} (x : X) :
    poleWeight Φ q R x = ⊥ ↔ Φ x = ⊥ ∨ logPole R x = ⊥ := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  rw [poleWeight, EReal.add_eq_bot_iff]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h, EReal.coe_mul_bot_of_pos hq']⟩
  induction hl : logPole R x using EReal.rec with
  | bot => rfl
  | top => exact absurd hl (logPole_ne_top R x)
  | coe r => rw [hl, ← EReal.coe_mul] at h; exact absurd h (EReal.coe_ne_bot _)

/-! ### Charts -/

/-- A function holomorphic on `U` is holomorphic in every chart. -/
theorem differentiableOn_chart_comp {g : X → ℂ} {U : Set X} (hU : IsOpen U)
    (hg : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U) (c : ComplexChart n X) :
    DifferentiableOn ℂ (fun z => g (c.val.symm z)) (c.val.target ∩ c.val.symm ⁻¹' U) := by
  intro z hz
  have hsy : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.val.symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) (IsManifold.subset_maximalAtlas c.property)
      hz.1).mdifferentiableAt (by simp)
  have hgx : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g (c.val.symm z) :=
    (hg _ hz.2).mdifferentiableAt (hU.mem_nhds hz.2)
  exact (mdifferentiableAt_iff_differentiableAt.mp (hgx.comp z hsy)).differentiableWithinAt

/-- **Pole sets of potentials with analytic singularities are locally analytically null**, in any
chart: near every point the pole set lies in the zero set of a function holomorphic on a ball which
does not vanish identically on any open subset of the ball. -/
theorem exists_analyticNull_chart {u : X → EReal} {c₀ : ℚ} {𝔞 : GermIdeal n X}
    (hu : HasAnalyticSingularitiesOfType (n := n) u c₀ 𝔞) (hnd : LocallyNondegenerate u)
    (c : ComplexChart n X) {x : X} (hx : x ∈ c.val.source) :
    ∃ (B : Set (ComplexModel n)) (g : ComplexModel n → ℂ), IsOpen B ∧ c.val x ∈ B ∧
      B ⊆ c.val.target ∧ DifferentiableOn ℂ g B ∧
      (∀ W' ⊆ B, IsOpen W' → W'.Nonempty → ∃ z ∈ W', g z ≠ 0) ∧
      ∀ z ∈ B, u (c.val.symm z) = ⊥ → g z = 0 := by
  obtain ⟨hc₀, -, hloc⟩ := hu
  obtain ⟨U, hUo, hxU, N, gs, hgs, -, Rr, C, -, heq⟩ := hloc x
  have hc₀' : (0 : ℝ) < (c₀ : ℝ) := by exact_mod_cast hc₀
  set O := c.val.target ∩ c.val.symm ⁻¹' U with hO
  have hOo : IsOpen O := c.val.isOpen_inter_preimage_symm hUo
  have hxO : c.val x ∈ O := ⟨c.val.map_source hx, by
    simp only [mem_preimage]; rw [c.val.left_inv hx]; exact hxU⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOo (c.val x) hxO
  -- a point of the ball off the poles
  obtain ⟨y, ⟨hys, hyB⟩, hyb⟩ := hnd x (c.val.source ∩ c.val ⁻¹' ball (c.val x) r)
    (c.val.isOpen_inter_preimage isOpen_ball) ⟨hx, mem_ball_self hr⟩
  have hyU : y ∈ U := by
    have := (hball hyB).2
    simp only [mem_preimage] at this
    rwa [c.val.left_inv hys] at this
  have hgen : ∃ j, gs j y ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hyb
    rw [heq y hyU, (generatorLog_eq_bot_iff gs y).mpr hall, EReal.coe_mul_bot_of_pos hc₀',
      EReal.bot_add]
  obtain ⟨j, hj⟩ := hgen
  refine ⟨ball (c.val x) r, fun z => gs j (c.val.symm z), isOpen_ball, mem_ball_self hr,
    fun z hz => (hball hz).1, ?_, ?_, ?_⟩
  · exact (differentiableOn_chart_comp hUo (hgs j) c).mono hball
  · intro W' hW'B hW'o hW'ne
    by_contra hzero
    push Not at hzero
    have hall := eqOn_zero_of_isOpen_convex isOpen_ball (convex_ball _ _)
      ((differentiableOn_chart_comp hUo (hgs j) c).mono hball) hW'o hW'B hW'ne
      (fun z hz => hzero z hz)
    apply hj
    have := hall hyB
    simpa [c.val.left_inv hys] using this
  · intro z hz hzb
    have hzU : c.val.symm z ∈ U := (hball hz).2
    rw [heq _ hzU] at hzb
    have hgl : generatorLog gs (c.val.symm z) = ⊥ := by
      by_contra hne
      induction hgz : generatorLog gs (c.val.symm z) using EReal.rec with
      | bot => exact hne hgz
      | top => exact generatorLog_ne_top gs _ hgz
      | coe t =>
        rw [hgz, ← EReal.coe_mul, ← EReal.coe_add] at hzb
        exact EReal.coe_ne_bot _ hzb
    exact (generatorLog_eq_bot_iff gs _).mp hgl j

/-! ### Gentle weights are smooth off their poles -/

/-- `e^{Φ/c}` for the exponent `c` of a gentle weight. -/
def gentleExp (Φ : X → EReal) (c₀ : ℚ) (x : X) : ℝ :=
  (EReal.exp ((((c₀ : ℝ)⁻¹ : ℝ) : EReal) * Φ x)).toReal

theorem gentleExp_of_coe {Φ : X → EReal} {c₀ : ℚ} {x : X} {t : ℝ} (ht : Φ x = t) :
    gentleExp Φ c₀ x = Real.exp ((c₀ : ℝ)⁻¹ * t) := by
  rw [gentleExp, ht, ← EReal.coe_mul, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem gentleExp_of_bot {Φ : X → EReal} {c₀ : ℚ} (hc₀ : 0 < c₀) {x : X} (hx : Φ x = ⊥) :
    gentleExp Φ c₀ x = 0 := by
  have : (0 : ℝ) < ((c₀ : ℝ))⁻¹ := inv_pos.mpr (by exact_mod_cast hc₀)
  rw [gentleExp, hx, EReal.coe_mul_bot_of_pos this, EReal.exp_bot, ENNReal.toReal_zero]

theorem gentleExp_pos_iff {Φ : X → EReal} {c₀ : ℚ} (hc₀ : 0 < c₀) (hΦt : ∀ x, Φ x ≠ ⊤) (x : X) :
    0 < gentleExp Φ c₀ x ↔ Φ x ≠ ⊥ := by
  constructor
  · intro h hb; rw [gentleExp_of_bot hc₀ hb] at h; exact lt_irrefl _ h
  · intro h
    rw [gentleExp_of_coe (EReal.coe_toReal (hΦt x) h).symm]
    exact Real.exp_pos _

theorem toReal_eq_of_gentleExp {Φ : X → EReal} {c₀ : ℚ} (hc₀ : 0 < c₀) (hΦt : ∀ x, Φ x ≠ ⊤)
    {x : X} (hx : Φ x ≠ ⊥) : (Φ x).toReal = (c₀ : ℝ) * Real.log (gentleExp Φ c₀ x) := by
  have hc : (c₀ : ℝ) ≠ 0 := by exact_mod_cast hc₀.ne'
  rw [gentleExp_of_coe (EReal.coe_toReal (hΦt x) hx).symm, Real.log_exp]
  field_simp

/-! ### Admissibility of `ψ = Φ + q log R` -/

theorem isLocallyAnalyticNull_union {A B : Set X}
    (hA : ∀ x : X, ∀ c : ComplexChart n X, x ∈ c.val.source →
      ∃ (O : Set (ComplexModel n)) (g : ComplexModel n → ℂ), IsOpen O ∧ c.val x ∈ O ∧
        O ⊆ c.val.target ∧ DifferentiableOn ℂ g O ∧
        (∀ W' ⊆ O, IsOpen W' → W'.Nonempty → ∃ z ∈ W', g z ≠ 0) ∧
        ∀ z ∈ O, c.val.symm z ∈ A → g z = 0)
    (hB : ∀ x : X, ∀ c : ComplexChart n X, x ∈ c.val.source →
      ∃ (O : Set (ComplexModel n)) (g : ComplexModel n → ℂ), IsOpen O ∧ c.val x ∈ O ∧
        O ⊆ c.val.target ∧ DifferentiableOn ℂ g O ∧
        (∀ W' ⊆ O, IsOpen W' → W'.Nonempty → ∃ z ∈ W', g z ≠ 0) ∧
        ∀ z ∈ O, c.val.symm z ∈ B → g z = 0) :
    IsLocallyAnalyticNull (n := n) (A ∪ B) := by
  intro x
  set c := complexChartAt (n := n) x
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  obtain ⟨O₁, g₁, hO₁, hx₁, hO₁t, hg₁, hnz₁, hz₁⟩ := hA x c hx
  obtain ⟨O₂, g₂, hO₂, hx₂, -, hg₂, hnz₂, hz₂⟩ := hB x c hx
  refine ⟨c, O₁ ∩ O₂, fun z => g₁ z * g₂ z, hx, hO₁.inter hO₂, ⟨hx₁, hx₂⟩,
    inter_subset_left.trans hO₁t, (hg₁.mono inter_subset_left).mul (hg₂.mono inter_subset_right),
    fun W' hW' hW'o hW'ne => ?_, fun z hz hzAB => ?_⟩
  · obtain ⟨z₁, hz₁W, hz₁ne⟩ := hnz₁ W' (hW'.trans inter_subset_left) hW'o hW'ne
    set W'' := W' ∩ {z | g₁ z ≠ 0}
    have hW''o : IsOpen W'' := by
      have hcont : ContinuousOn g₁ W' :=
        (hg₁.mono (hW'.trans inter_subset_left)).continuousOn
      exact hcont.isOpen_inter_preimage hW'o isOpen_ne
    obtain ⟨z₂, ⟨hz₂W, hz₂g₁⟩, hz₂ne⟩ := hnz₂ W'' (inter_subset_left.trans
      (hW'.trans inter_subset_right)) hW''o ⟨z₁, hz₁W, hz₁ne⟩
    exact ⟨z₂, hz₂W, mul_ne_zero hz₂g₁ hz₂ne⟩
  · rcases hzAB with h | h
    · show g₁ z * g₂ z = 0
      rw [hz₁ z hz.1 h, zero_mul]
    · show g₁ z * g₂ z = 0
      rw [hz₂ z hz.2 h, mul_zero]

/-- **`ψ = Φ + q log R` is an admissible singular weight** for `Φ ∈ PSH(X, θ)` with gentle
analytic singularities and a normal pole `R` of `W` (`q ≥ 1`). -/
theorem isAdmissibleSingularWeight_poleWeight (ωb : KahlerBackground n X) {W : Set X}
    (hWc : IsClosed W) {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R) {θ : ClosedRealOneOneForm n X}
    {Φ : X → EReal} (hΦ : IsThetaPshPotential θ.val Φ) {c₀ : ℚ} {𝔞 : GermIdeal n X}
    (hgen : HasGentleAnalyticSingularitiesOfType (n := n) Φ c₀ 𝔞) {q : ℕ} (hq : 0 < q) :
    IsAdmissibleSingularWeight (n := n) (poleWeight Φ q R) := by
  obtain ⟨CR, hCR, hRpsh⟩ := hR.pole.exists_thetaPsh
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hqpsh := Pending.RestrictedApproximantComparison.isThetaPshPotential_smul hRpsh hq0
  have hsum := SGPT.Okounkov.isThetaPshPotential_add_from_positive_sum hΦ hqpsh
  have hΦt : ∀ x, Φ x ≠ ⊤ := hΦ.1.quasiPlurisubharmonic.ne_top
  have hc₀ : 0 < c₀ := hgen.2.1.1
  have hEs : ChartSmooth (n := n) (gentleExp Φ c₀) := hgen.2.2.2.1
  have hEc : Continuous (gentleExp Φ c₀) := continuous_of_chartSmooth hEs
  have hbot : ∀ x, poleWeight Φ q R x = ⊥ ↔ x ∈ {x | gentleExp Φ c₀ x = 0} ∪ W := by
    intro x
    rw [poleWeight_eq_bot_iff hq, hR.pole.eq_bot_iff x, mem_union, mem_ofPred_eq]
    refine or_congr ⟨fun h => gentleExp_of_bot hc₀ h, fun h => ?_⟩ Iff.rfl
    by_contra hne
    exact (lt_irrefl _ (h ▸ (gentleExp_pos_iff hc₀ hΦt x).mpr hne))
  have hset : {x | poleWeight Φ q R x = ⊥} = {x | gentleExp Φ c₀ x = 0} ∪ W := by
    ext x; exact hbot x
  refine ⟨hsum.1.quasiPlurisubharmonic, hsum.1.quasiPlurisubharmonic.ne_top, ?_, ?_, ?_⟩
  · rw [hset]; exact (isClosed_eq hEc continuous_const).union hWc
  · rw [hset]
    refine isLocallyAnalyticNull_union (fun x c hx => ?_) (fun x c hx => ?_)
    · obtain ⟨O, g, h1, h2, h3, h4, h5, h6⟩ := exists_analyticNull_chart hgen.2.1 hΦ.2 c hx
      refine ⟨O, g, h1, h2, h3, h4, h5, fun z hz hzA => h6 z hz ?_⟩
      by_contra hne
      exact lt_irrefl _ (((gentleExp_pos_iff hc₀ hΦt _).mpr hne).trans_eq hzA)
    · obtain ⟨O, g, h1, h2, h3, h4, h5, h6⟩ :=
        exists_analyticNull_chart hR.pole.analyticType hRpsh.2 c hx
      exact ⟨O, g, h1, h2, h3, h4, h5, fun z hz hzW => h6 z hz ((hR.pole.eq_bot_iff _).mpr hzW)⟩
  · -- smoothness off the poles
    intro c z hz
    refine ContDiffAt.contDiffWithinAt ?_
    have hzψ : poleWeight Φ q R (c.val.symm z) ≠ ⊥ := hz.2
    rw [ne_eq, poleWeight_eq_bot_iff hq, not_or] at hzψ
    have hRz : 0 < R (c.val.symm z) :=
      hR.pos_of_notMem fun h => hzψ.2 ((hR.pole.eq_bot_iff _).mpr h)
    have hEz : 0 < gentleExp Φ c₀ (c.val.symm z) := (gentleExp_pos_iff hc₀ hΦt _).mpr hzψ.1
    have hO₁ : IsOpen (c.val.target ∩ (fun y => gentleExp Φ c₀ (c.val.symm y)) ⁻¹' Ioi 0) :=
      (hEs c).continuousOn.isOpen_inter_preimage c.val.open_target isOpen_Ioi
    have hO₂ : IsOpen (c.val.target ∩ (fun y => R (c.val.symm y)) ⁻¹' Ioi 0) :=
      (hR.smooth c).continuousOn.isOpen_inter_preimage c.val.open_target isOpen_Ioi
    have hev : (fun y => (poleWeight Φ q R (c.val.symm y)).toReal) =ᶠ[𝓝 z]
        fun y => (c₀ : ℝ) * Real.log (gentleExp Φ c₀ (c.val.symm y)) +
          (q : ℝ) * Real.log (R (c.val.symm y)) := by
      filter_upwards [(hO₁.inter hO₂).mem_nhds ⟨⟨hz.1, hEz⟩, ⟨hz.1, hRz⟩⟩] with y hy
      have hΦy : Φ (c.val.symm y) ≠ ⊥ := (gentleExp_pos_iff hc₀ hΦt _).mp hy.1.2
      have hRy : 0 < R (c.val.symm y) := hy.2.2
      rw [poleWeight, ← EReal.coe_toReal (hΦt _) hΦy, logPole_of_pos hRy, ← EReal.coe_mul,
        ← EReal.coe_add, EReal.toReal_coe, toReal_eq_of_gentleExp hc₀ hΦt hΦy]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine (contDiffAt_const.mul (ContDiffAt.log (f := fun y => gentleExp Φ c₀ (c.val.symm y))
      ?_ hEz.ne')).add (contDiffAt_const.mul (ContDiffAt.log (f := fun y => R (c.val.symm y))
      ?_ hRz.ne'))
    · exact (hEs c).contDiffAt (c.val.open_target.mem_nhds hz.1)
    · exact (hR.smooth c).contDiffAt (c.val.open_target.mem_nhds hz.1)

end SGPT.Trace.OTExt5

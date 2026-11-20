import SGPT.Trace.OTMarginLocal

/-!
# Local packages and the estimates on their overlaps

Blueprint `claude-ot3.tex`, node `claude-ot3:overlap`.

`MarginPatch` bundles the output of `exists_marginPatch` at a point `p`.  For two packages:

* `MarginPatch.lintegral_overlap_ne_top`: on a compact subset of `B_i ∩ B_j`,
  `∫ |S_i - S_j|² e^{-kψ} e^{-rΛ} dμ < ∞` (`r = codim W`).  The difference vanishes on `W`, so
  `|S_i - S_j|² ≤ C e^{Λ}`; with `t > 1`, `a/t + b(1 - 1/t) = r` and `b - 1 < r`, Young's
  inequality (`young_weights`) bounds the integrand by the gains of `S_i`, `S_j` plus
  `C e^{-(b-1)Λ}`, which is integrable (`sub`).
* `MarginPatch.lintegral_single_ne_top`: `∫_{K₀} |S_j|² e^{-kψ} dμ < ∞` on compact `K₀ ⊆ K_j`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.CompactHolomorphicSectionsDraft

/-! ### Weights -/

theorem one_le_multiplierWeight {a : ℝ} (ha : 0 ≤ a) {x : EReal} (hx : x ≤ 0) :
    1 ≤ multiplierWeight a x := by
  induction x using EReal.rec with
  | bot =>
    rcases ha.lt_or_eq with ha | rfl
    · rw [multiplierWeight_bot ha]; exact le_top
    · simp [multiplierWeight]
  | top => exact absurd hx (by simp)
  | coe s =>
    rw [multiplierWeight_coe, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by
      have : s ≤ 0 := EReal.coe_nonpos.mp hx
      nlinarith))

theorem multiplierWeight_le_mul_of_le {k t M : ℝ} (hk : 0 ≤ k) (ht : 1 ≤ t) {x : EReal}
    (hx : x ≤ (M : EReal)) :
    multiplierWeight k x ≤ ENNReal.ofReal (Real.exp (k * (t - 1) * M)) * multiplierWeight (k * t) x := by
  induction x using EReal.rec with
  | bot =>
    rcases hk.lt_or_eq with hk | rfl
    · rw [multiplierWeight_bot (mul_pos hk (by linarith)),
        ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
      exact le_top
    · simp [multiplierWeight]
  | top => exact absurd hx (by simp)
  | coe s =>
    have hs : s ≤ M := EReal.coe_le_coe_iff.mp hx
    rw [multiplierWeight_coe, multiplierWeight_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : 0 ≤ k * (t - 1) := mul_nonneg hk (by linarith)
    nlinarith

theorem ofReal_exp_le_multiplierWeight {k M : ℝ} (hk : 0 ≤ k) {x : EReal} (hx : x ≤ (M : EReal)) :
    ENNReal.ofReal (Real.exp (-(k * M))) ≤ multiplierWeight k x := by
  induction x using EReal.rec with
  | bot =>
    rcases hk.lt_or_eq with hk | rfl
    · rw [multiplierWeight_bot hk]; exact le_top
    · simp [multiplierWeight]
  | top => exact absurd hx (by simp)
  | coe s =>
    rw [multiplierWeight_coe]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
      have := EReal.coe_le_coe_iff.mp hx; nlinarith))

theorem exp_mul_multiplierWeight_le {b : ℝ} (hb : 1 ≤ b) (x : EReal) :
    EReal.exp x * multiplierWeight b x ≤ multiplierWeight (b - 1) x := by
  induction x using EReal.rec with
  | bot => rw [EReal.exp_bot, zero_mul]; exact zero_le
  | top => rw [multiplierWeight_top (by linarith), mul_zero]; exact zero_le
  | coe s =>
    rw [EReal.exp_coe, multiplierWeight_coe, multiplierWeight_coe,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact le_of_eq (by congr 2; ring)

/-! ### Sections -/

section Sections

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)]

theorem isHolomorphicSectionOn_sub {f g : (x : X) → V x} {U : Set X} (hU : IsOpen U)
    (hf : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V f U)
    (hg : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V g U) :
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V (fun x => f x - g x) U := by
  intro x hx
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  set e := trivializationAt ℂ V x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x
  have h1 := (Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e f hxe).mp
    ((hf x hx).mdifferentiableAt (hU.mem_nhds hx))
  have h2 := (Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e g hxe).mp
    ((hg x hx).mdifferentiableAt (hU.mem_nhds hx))
  rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e _ hxe]
  refine (h1.sub h2).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hxe] with y hy
  simp only [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hy, map_sub,
    Pi.sub_apply]

theorem isHolomorphicSectionOn_zero (U : Set X) :
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V (fun _ => 0) U :=
  ((Bundle.contMDiff_zeroSection ℂ V (IB := 𝓘(ℂ, ComplexModel n)) (n := ∞)).mdifferentiable
    (by simp)).mdifferentiableOn

theorem isHolomorphicSectionOn_of_holomorphicSections
    (σ : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) V) (U : Set X) :
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V σ U :=
  (σ.contMDiff.mdifferentiable (by simp)).mdifferentiableOn

theorem continuousOn_norm_of_isHolomorphicSectionOn [ContinuousFiberNorm V] {f : (x : X) → V x}
    {U : Set X} (hf : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V f U) :
    ContinuousOn (fun x => ‖f x‖) U :=
  ContinuousFiberNorm.continuous.comp_continuousOn hf.continuousOn

end Sections

/-! ### Local packages -/

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V]
  [MeasurableSpace X] [BorelSpace X]

/-- The output of `exists_marginPatch` at a point `p`. -/
structure MarginPatch (μ : Measure X) (W : Set X) (Λ ψ : X → EReal) (c a r : ℝ)
    (s : (y : W) → V y) (p : X) where
  B' : Set X
  K' : Set X
  B : Set X
  K : Set X
  S : (x : X) → V x
  isOpen_B' : IsOpen B'
  isOpen_B : IsOpen B
  isCompact_K' : IsCompact K'
  isCompact_K : IsCompact K
  mem : p ∈ B'
  B'_K' : B' ⊆ K'
  K'_B : K' ⊆ B
  B_K : B ⊆ K
  hol : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V S B
  agree : ∀ y : W, y.1 ∈ B → S y = s y
  gain : ∫⁻ x in K, ENNReal.ofReal (‖S x‖ ^ 2) * multiplierWeight c (ψ x) *
    multiplierWeight a (Λ x) ∂μ ≠ ⊤
  sub : ∀ c' : ℝ, 0 ≤ c' → c' < r → ∫⁻ x in K, multiplierWeight c' (Λ x) ∂μ ≠ ⊤
  lip : ∀ (h : (x : X) → V x) (O : Set X), IsOpen O → O ⊆ B →
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V h O →
    (∀ x ∈ O, x ∈ W → h x = 0) → ∀ K₀ : Set X, IsCompact K₀ → K₀ ⊆ O →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K₀, ENNReal.ofReal (‖h x‖ ^ 2) ≤ ENNReal.ofReal C * EReal.exp (Λ x)
  crit : ∀ (h : (x : X) → V x) (O : Set X), IsOpen O → O ⊆ B →
    SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V h O →
    ∀ y ∈ O, y ∈ W →
    ∫⁻ x in O, ENNReal.ofReal (‖h x‖ ^ 2) * multiplierWeight r (Λ x) ∂μ ≠ ⊤ → h y = 0

namespace MarginPatch

variable {V} {μ : Measure X} {W : Set X} {Λ ψ : X → EReal} {c a r : ℝ} {s : (y : W) → V y}

/-- **The single estimate**: `∫_{K₀} |S|² e^{-kψ} < ∞` on compact `K₀ ⊆ K`. -/
theorem lintegral_single_ne_top {p : X} (P : MarginPatch (n := n) V μ W Λ ψ c a r s p) {k t M : ℝ}
    (hk : 0 ≤ k) (ht : 1 ≤ t) (hc : c = k * t) (ha : 0 ≤ a) (hψM : ∀ x, ψ x ≤ (M : EReal))
    (hΛ0 : ∀ x, Λ x ≤ 0) {K₀ : Set X} (hK₀ : K₀ ⊆ P.K) :
    ∫⁻ x in K₀, ENNReal.ofReal (‖P.S x‖ ^ 2) * multiplierWeight k (ψ x) ∂μ ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top
    (r := Real.exp (k * (t - 1) * M))) P.gain) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (lintegral_mono_set hK₀).trans (lintegral_mono fun x => ?_)
  calc ENNReal.ofReal (‖P.S x‖ ^ 2) * multiplierWeight k (ψ x)
      ≤ ENNReal.ofReal (‖P.S x‖ ^ 2) * (ENNReal.ofReal (Real.exp (k * (t - 1) * M)) *
          multiplierWeight c (ψ x) * multiplierWeight a (Λ x)) := by
        refine mul_le_mul' le_rfl ?_
        rw [hc]
        refine (multiplierWeight_le_mul_of_le hk ht (hψM x)).trans ?_
        exact le_mul_of_one_le_right zero_le (one_le_multiplierWeight ha (hΛ0 x))
    _ = _ := by ring

/-- **The overlap estimate.** -/
theorem lintegral_overlap_ne_top {p q : X} (Pi : MarginPatch (n := n) V μ W Λ ψ c a r s p)
    (Pj : MarginPatch (n := n) V μ W Λ ψ c a r s q) {k t b M : ℝ} (hk : 0 ≤ k) (ht : 1 < t)
    (hc : c = k * t) (ha : 0 ≤ a) (hb : 1 ≤ b) (hbr : b - 1 < r)
    (hr : a / t + b * (1 - 1 / t) = r) (hψm : Measurable ψ) (hΛm : Measurable Λ)
    (_hψM : ∀ x, ψ x ≤ (M : EReal)) (_hΛ0 : ∀ x, Λ x ≤ 0) {K₀ : Set X} (hK₀ : IsCompact K₀)
    (hK₀B : K₀ ⊆ Pi.B ∩ Pj.B) :
    ∫⁻ x in K₀, ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2) * multiplierWeight k (ψ x) *
      multiplierWeight r (Λ x) ∂μ ≠ ⊤ := by
  have hr0 : 0 ≤ r := by linarith
  set O := Pi.B ∩ Pj.B with hO
  have hOo : IsOpen O := Pi.isOpen_B.inter Pj.isOpen_B
  have hDhol := isHolomorphicSectionOn_sub (n := n) V hOo (Pi.hol.mono inter_subset_left)
    (Pj.hol.mono inter_subset_right)
  have hDW : ∀ x ∈ O, x ∈ W → Pi.S x - Pj.S x = 0 := by
    intro x hx hxW
    rw [Pi.agree ⟨x, hxW⟩ hx.1, Pj.agree ⟨x, hxW⟩ hx.2, sub_self]
  obtain ⟨C, hC0, hC⟩ := Pj.lip _ O hOo inter_subset_right hDhol hDW K₀ hK₀ hK₀B
  have hKm : MeasurableSet K₀ := hK₀.isClosed.measurableSet
  -- measurability on `K₀`
  have hmeasS : ∀ (f : (x : X) → V x) (U : Set X),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V f U → K₀ ⊆ U →
      AEMeasurable (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) (μ.restrict K₀) := by
    intro f U hf hKU
    exact (ENNReal.continuous_ofReal.comp_continuousOn
      (((continuousOn_norm_of_isHolomorphicSectionOn (n := n) V hf).mono hKU).pow 2)).aemeasurable hKm
  have hwψ : ∀ c', 0 ≤ c' → Measurable fun x => multiplierWeight c' (ψ x) := fun c' hc' =>
    (multiplierWeight_antitone hc').measurable.comp hψm
  have hwΛ : ∀ c', 0 ≤ c' → Measurable fun x => multiplierWeight c' (Λ x) := fun c' hc' =>
    (multiplierWeight_antitone hc').measurable.comp hΛm
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg hk (by linarith)
  -- Young
  have hpt : ∀ x, ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2) * multiplierWeight k (ψ x) *
      multiplierWeight r (Λ x) ≤
      ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2) * multiplierWeight c (ψ x) * multiplierWeight a (Λ x) +
      ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2) * multiplierWeight b (Λ x) := by
    intro x
    have hy := young_weights (ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2)) (multiplierWeight k (ψ x))
      (multiplierWeight 1 (Λ x)) ht ha (by linarith) hr
    rw [← multiplierWeight_eq_rpow hr0, ← multiplierWeight_eq_rpow ha,
      ← multiplierWeight_eq_rpow (by linarith : (0 : ℝ) ≤ b)] at hy
    rwa [multiplierWeight_eq_rpow hk (ψ x), ← ENNReal.rpow_mul, ← multiplierWeight_eq_rpow
      (mul_nonneg hk (by linarith)), ← hc, ← multiplierWeight_eq_rpow hk] at hy
  have hA : AEMeasurable (fun x => ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2) * multiplierWeight c (ψ x) *
      multiplierWeight a (Λ x)) (μ.restrict K₀) :=
    ((hmeasS _ O hDhol hK₀B).mul (hwψ c hc0).aemeasurable).mul (hwΛ a ha).aemeasurable
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_left' hA]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · -- the gains of `S_i` and `S_j`
    have h2 : ∀ x, ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2) * multiplierWeight c (ψ x) *
        multiplierWeight a (Λ x) ≤
        2 * (ENNReal.ofReal (‖Pi.S x‖ ^ 2) * multiplierWeight c (ψ x) * multiplierWeight a (Λ x)) +
        2 * (ENNReal.ofReal (‖Pj.S x‖ ^ 2) * multiplierWeight c (ψ x) * multiplierWeight a (Λ x)) := by
      intro x
      have hn : ‖Pi.S x - Pj.S x‖ ^ 2 ≤ 2 * ‖Pi.S x‖ ^ 2 + 2 * ‖Pj.S x‖ ^ 2 := by
        have h1 := norm_sub_le (Pi.S x) (Pj.S x)
        have h2 : ‖Pi.S x - Pj.S x‖ ^ 2 ≤ (‖Pi.S x‖ + ‖Pj.S x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
        nlinarith [sq_nonneg (‖Pi.S x‖ - ‖Pj.S x‖)]
      calc ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2) * multiplierWeight c (ψ x) *
            multiplierWeight a (Λ x)
          ≤ ENNReal.ofReal (2 * ‖Pi.S x‖ ^ 2 + 2 * ‖Pj.S x‖ ^ 2) * multiplierWeight c (ψ x) *
            multiplierWeight a (Λ x) := by gcongr
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by norm_num)]
            simp only [ENNReal.ofReal_ofNat]
            ring
    have hAi : AEMeasurable (fun x => 2 * (ENNReal.ofReal (‖Pi.S x‖ ^ 2) * multiplierWeight c (ψ x) *
        multiplierWeight a (Λ x))) (μ.restrict K₀) :=
      (((hmeasS _ Pi.B Pi.hol (hK₀B.trans inter_subset_left)).mul (hwψ c hc0).aemeasurable).mul
        (hwΛ a ha).aemeasurable).const_mul 2
    refine ne_top_of_le_ne_top ?_ (lintegral_mono h2)
    rw [lintegral_add_left' hAi, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) ?_,
      ENNReal.mul_ne_top (by norm_num) ?_⟩
    · exact ne_top_of_le_ne_top Pi.gain (lintegral_mono_set
        ((hK₀B.trans inter_subset_left).trans Pi.B_K))
    · exact ne_top_of_le_ne_top Pj.gain (lintegral_mono_set
        ((hK₀B.trans inter_subset_right).trans Pj.B_K))
  · -- the Lipschitz bound and the subcritical integrability
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C))
      (Pj.sub (b - 1) (by linarith) hbr)) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_mono' hKm fun x hx => ?_).trans
      (lintegral_mono_set ((hK₀B.trans inter_subset_right).trans Pj.B_K))
    calc ENNReal.ofReal (‖Pi.S x - Pj.S x‖ ^ 2) * multiplierWeight b (Λ x)
        ≤ ENNReal.ofReal C * EReal.exp (Λ x) * multiplierWeight b (Λ x) :=
          mul_le_mul' (hC x hx) le_rfl
      _ = ENNReal.ofReal C * (EReal.exp (Λ x) * multiplierWeight b (Λ x)) := by ring
      _ ≤ ENNReal.ofReal C * multiplierWeight (b - 1) (Λ x) :=
          mul_le_mul' le_rfl (exp_mul_multiplierWeight_le hb (Λ x))

end MarginPatch

end SGPT.Trace.OTMargin

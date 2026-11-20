import SGPT.Okounkov.TranscendentalWNDeformationIdeal
import SGPT.Foundations.Analysis.Pending.ExceptionalMetricProof
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ProductTestForms
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# The circle-invariant metric of `𝒪(ℰ)`

Blueprint `tok-wn-def:exceptional-metric` (`claude-tok-wn-def`); WN21 §4.

Let `E` be a metric of `𝒪(Z)` (`IsFirstDivisorUnitMetric`), with weight `log |s_Z|²_h`, and
`W(x, [v₀ : v₁]) = |s_Z(x)|²_h N₁ + N₀` (`baseExceptionalWeight`), i.e.
`(|s_Z|²_h + |τ|²) / (1 + |τ|²)`.  For a deformation `μ : 𝒳 → X × ℙ¹`:

* `exists_exceptional_factorization`: near a point of `ℰ`, `W ∘ μ = |σ|² U'` with `σ` a local
  generator of the exceptional ideal `μ^* 𝓘_C` and `U'` smooth and positive: with
  `g ∘ π_X ∘ μ = a σ`, `τ ∘ μ = b σ` (`exists_centre_generators`, `(a, b)` without common zero),
  `U' = N₁ ∘ μ · (|a|² e^{h_Z} + |b|²)`;
* `exists_offExceptional_factorization`: off `ℰ`, `W ∘ μ` is smooth and positive and the
  exceptional ideal is the unit ideal;
* `exceptionalMetric`: the metered divisor with weight `log W ∘ μ` (TN's
  `ofWeightFactorization`), a metric of the exceptional divisor with support `ℰ`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Toric
open SGPT.Okounkov.TranscendentalMain

/-! ### Smoothness along holomorphic maps between manifolds of different dimensions -/

section Smooth

variable {k n : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A function smooth on an open `U ⊆ M` (in charts) pulls back to a function smooth on `g⁻¹ U`
along a holomorphic `g : Z → M` (dimensions may differ). -/
theorem contDiffOn_comp_chart_symm_of_holomorphic {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g) {U : Set M} (hU : IsOpen U)
    {h : M → ℝ} (hh : ∀ d : ComplexChart n M,
      ContDiffOn ℝ ∞ (fun z => h (d.val.symm z)) (d.val.target ∩ d.val.symm ⁻¹' U))
    (e : ComplexChart k Z) :
    ContDiffOn ℝ ∞ (fun z => h (g (e.val.symm z))) (e.val.target ∩ e.val.symm ⁻¹' (g ⁻¹' U)) := by
  intro u hu
  let d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ coordinateDomain g e d := ⟨hu.1, mem_complexChartAt_source _⟩
  have hW : IsOpen (potentialDomain g e d (d.val.target ∩ d.val.symm ⁻¹' U)) :=
    potentialDomain_isOpen hg e d (d.val.isOpen_inter_preimage_symm hU)
  have hmem : u ∈ potentialDomain g e d (d.val.target ∩ d.val.symm ⁻¹' U) := by
    refine ⟨hud, coordinateMap_mem_target hud, ?_⟩
    change d.val.symm (d.val (g (e.val.symm u))) ∈ U
    rw [d.val.left_inv hud.2]
    exact hu.2
  have hcomp := (hh d).comp_inter (coordinateMap_contDiffOn_real hg e d)
  refine ((hcomp.contDiffAt (hW.mem_nhds hmem)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(coordinateDomain_isOpen hg e d).mem_nhds hud] with w hw
  change h (g (e.val.symm w)) = h (d.val.symm (d.val (g (e.val.symm w))))
  rw [d.val.left_inv hw.2]

/-- A function holomorphic at every point of an open set is smooth there in charts, and so is the
square of its modulus. -/
theorem contDiffOn_norm_sq_comp_chart_symm {a : Z → ℂ} {O : Set Z} (hO : IsOpen O)
    (ha : ∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ℂ) a y) (e : ComplexChart k Z) :
    ContDiffOn ℝ ∞ (fun z => ‖a (e.val.symm z)‖ ^ 2) (e.val.target ∩ e.val.symm ⁻¹' O) := by
  have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' O) := e.val.isOpen_inter_preimage_symm hO
  have hd : DifferentiableOn ℂ (fun z => a (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' O) :=
    fun z hz => (FactorizedWeightForm.differentiableAt_comp_chart_symm e hz.1
      (ha _ hz.2)).differentiableWithinAt
  have hc : ContDiffOn ℝ ∞ (fun z => a (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' O) :=
    (contDiffOn_of_differentiableOn_complex hd hS).restrict_scalars ℝ
  exact hc.norm_sq ℝ

end Smooth

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### The local factor `|s_Z|²_h = |g|² e^h` -/

/-- On a presentation `E.weight = log |g|² + h`, `|s_Z|²_h = exp (E.weight) = |g|² e^h`. -/
theorem exp_weight_toReal_eq {E : MeteredEffectiveQDivisor (m + 1) F.carrier} {g : F.carrier → ℂ}
    {h : F.carrier → ℝ} {x : F.carrier}
    (hw : E.weight x = generatorLog (fun _ : Fin 1 => g) x + (h x : EReal)) :
    (EReal.exp (E.weight x)).toReal = ‖g x‖ ^ 2 * Real.exp (h x) := by
  rw [hw, EReal.exp_add, generatorLog_eq_log_sum, ENNReal.exp_log, EReal.exp_coe,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp

/-- `|s_Z|²_h` is smooth on `X`. -/
theorem chartSmooth_exp_weight {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) :
    ChartSmooth (n := m + 1) (fun x => (EReal.exp (E.weight x)).toReal) := by
  obtain ⟨D, -, -, hmet⟩ := hE
  intro e
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  obtain ⟨V, hV, hxV, g, hg, -, h, hh, hw⟩ := hmet (e.val.symm z)
  have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) := e.val.isOpen_inter_preimage_symm hV
  refine ⟨e.val.target ∩ e.val.symm ⁻¹' V, hS, ⟨hz, hxV⟩, ?_⟩
  have hga : ∀ y ∈ V, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) g y :=
    fun y hy => (hg y hy).mdifferentiableAt (hV.mem_nhds hy)
  have h1 := contDiffOn_norm_sq_comp_chart_symm hV hga e
  have h2 := (hh e).exp
  refine ((h1.mul h2).mono inter_subset_right).congr fun w hw' => ?_
  exact exp_weight_toReal_eq F (hw _ hw'.2.2)

/-- The base weight `W` is smooth on `X × ℙ¹`. -/
theorem chartSmooth_baseExceptionalWeight {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) :
    ChartSmooth (n := m + 1 + 1) (baseExceptionalWeight F E) := by
  have hr := ProductTestForms.chartSmooth_comp (contMDiff_fst (n := m + 1) (m := 1)
    (X := F.carrier) (Y := ProjectiveLine)) (chartSmooth_exp_weight F hE)
  have hN : ∀ i : Fin 2, ChartSmooth (n := 1) (projectiveWeight i) :=
    fun i e => contDiffOn_projectiveWeight i e
  have h1 := ProductTestForms.chartSmooth_comp (contMDiff_snd (n := m + 1) (m := 1)
    (X := F.carrier) (Y := ProjectiveLine)) (hN 1)
  have h0 := ProductTestForms.chartSmooth_comp (contMDiff_snd (n := m + 1) (m := 1)
    (X := F.carrier) (Y := ProjectiveLine)) (hN 0)
  intro e
  refine (((hr e).mul (h1 e)).add (h0 e)).congr fun z _ => ?_
  exact baseExceptionalWeight_eq F E _

/-- Off `Z`, `|s_Z|²_h > 0`. -/
theorem exp_weight_toReal_pos {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {x : F.carrier} (hx : x ∉ F.flag (1 : Fin (m + 2))) :
    0 < (EReal.exp (E.weight x)).toReal := by
  obtain ⟨D, -, hsupp, hmet⟩ := hE
  obtain ⟨V, hV, hxV, g, -, -, h, -, hw⟩ := hmet x
  rw [exp_weight_toReal_eq F (hw x hxV)]
  have hg : g x ≠ 0 := by
    intro hg0
    apply hx
    rw [← hsupp]
    change E.weight x = ⊥
    rw [hw x hxV, generatorLog_eq_log_sum]
    simp [hg0]
  have := Real.exp_pos (h x)
  positivity

/-- On `Z`, `|s_Z|²_h = 0`. -/
theorem exp_weight_toReal_eq_zero {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {x : F.carrier} (hx : x ∈ F.flag (1 : Fin (m + 2))) :
    (EReal.exp (E.weight x)).toReal = 0 := by
  obtain ⟨D, -, hsupp, -⟩ := hE
  have : E.weight x = ⊥ := by
    rw [← hsupp] at hx
    exact hx
  rw [this]
  simp

theorem eq_projectiveZero_of_rep_zero {p : ProjectiveLine} (h : p.rep 0 = 0) :
    p = projectiveZero := by
  rw [projectiveZero_eq_mk, ← Projectivization.mk_rep p, Projectivization.mk_eq_mk_iff']
  refine ⟨p.rep 1, ?_⟩
  funext i
  fin_cases i <;> simp [h]

theorem projectiveWeight_zero_projectiveZero : projectiveWeight 0 projectiveZero = 0 := by
  rw [projectiveZero_eq_mk, projectiveWeight_mk]
  simp

/-- `W ≥ 0`. -/
theorem baseExceptionalWeight_nonneg (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (q : F.carrier × ProjectiveLine) : 0 ≤ baseExceptionalWeight F E q := by
  rw [baseExceptionalWeight_eq]
  have := projectiveWeight_nonneg 0 q.2
  have := projectiveWeight_nonneg 1 q.2
  have : 0 ≤ (EReal.exp (E.weight q.1)).toReal := ENNReal.toReal_nonneg
  positivity

/-- `W > 0` off the centre. -/
theorem baseExceptionalWeight_pos {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {q : F.carrier × ProjectiveLine}
    (hq : q ∉ deformationCentre F) : 0 < baseExceptionalWeight F E q := by
  rw [baseExceptionalWeight_eq]
  have hr0 : 0 ≤ (EReal.exp (E.weight q.1)).toReal := ENNReal.toReal_nonneg
  have hN0 := projectiveWeight_nonneg 0 q.2
  have hN1 := projectiveWeight_nonneg 1 q.2
  by_cases h0 : projectiveWeight 0 q.2 = 0
  · have hrep0 : q.2.rep 0 = 0 := by
      unfold projectiveWeight at h0
      rcases div_eq_zero_iff.mp h0 with h | h
      · simpa using h
      · exact absurd h (normSq_add_pos _ q.2.rep_nonzero).ne'
    have hq2 : q.2 = projectiveZero := eq_projectiveZero_of_rep_zero hrep0
    have hx : q.1 ∉ F.flag (1 : Fin (m + 2)) := fun hx =>
      hq ((mem_deformationCentre_iff F).mpr ⟨hx, hq2⟩)
    have h1 : projectiveWeight 1 q.2 = 1 := by linarith [projectiveWeight_add q.2]
    rw [h0, h1, mul_one, add_zero]
    exact exp_weight_toReal_pos F hE hx
  · have hpos : 0 < projectiveWeight 0 q.2 := lt_of_le_of_ne hN0 (Ne.symm h0)
    positivity

/-- `W = 0` on the centre. -/
theorem baseExceptionalWeight_eq_zero {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {q : F.carrier × ProjectiveLine}
    (hq : q ∈ deformationCentre F) : baseExceptionalWeight F E q = 0 := by
  obtain ⟨hx, hq2⟩ := (mem_deformationCentre_iff F).mp hq
  rw [baseExceptionalWeight_eq, hq2, projectiveWeight_zero_projectiveZero,
    exp_weight_toReal_eq_zero F hE hx]
  simp

/-! ### The affine coordinate is holomorphic -/

/-- `τ` is holomorphic on `ℙ¹ \ {∞}`. -/
theorem holomorphicAt_projectiveAffine {p : ProjectiveLine}
    (hp : p ∈ (projectiveModelChart false).source) : HolomorphicAt 1 projectiveAffine p := by
  have hmem : projectiveModelChart false ∈ atlas (ComplexModel 1) ProjectiveLine :=
    (mem_projectiveNativeAtlas_iff _).mpr ⟨false, rfl⟩
  filter_upwards [(projectiveModelChart false).open_source.mem_nhds hp] with y hy
  have hc : MDifferentiableAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1)
      (projectiveModelChart false) y := mdifferentiableAt_atlas hmem hy
  have hproj : MDifferentiableAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ)
      (fun y => (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ)
        (projectiveModelChart false y)) y :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).mdifferentiableAt.comp y hc
  refine hproj.congr_of_eventuallyEq ?_
  filter_upwards [(projectiveModelChart false).open_source.mem_nhds hy] with y' hy'
  exact (projectiveModelChart_false_apply hy').symm

/-! ### The factorization of `W ∘ μ` -/

section Factorization

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- Pullbacks of germs of `𝓘_C` lie in the exceptional ideal `μ^* 𝓘_C`. -/
theorem mem_pullback_of_mem (hμ : IsNormalConeDeformation F μ) {y : 𝒳}
    {f : F.carrier × ProjectiveLine → ℂ}
    (hf : (vanishingIdeal (n := m + 1 + 1) (deformationCentre F)).mem (μ y) f) :
    (GermIdeal.pullback (m := m + 1 + 1) μ
      (vanishingIdeal (n := m + 1 + 1) (deformationCentre F))).mem y (f ∘ μ) :=
  ⟨hf.1.comp_contMDiff (Eventually.of_forall fun _ => hμ.contMDiff.contMDiffAt), 1,
    fun _ => f ∘ μ, fun _ => 1, fun _ => ⟨f, hf, rfl⟩, fun _ => holomorphicAt_const 1,
    Eventually.of_forall fun y => by simp⟩

/-- A germ in the span of the single generator `σ` is a multiple of `σ`. -/
theorem exists_eq_mul_of_isInSpanAt {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {σ f : M → ℂ} {y : M}
    (h : IsInSpanAt (n := n) (· = σ) y f) :
    ∃ a : M → ℂ, HolomorphicAt n a y ∧ f =ᶠ[𝓝 y] fun y' => a y' * σ y' := by
  obtain ⟨-, N, s, a, hs, ha, hf⟩ := h
  refine ⟨fun y' => ∑ i ∈ Finset.univ, a i y', HolomorphicAt.sum Finset.univ fun i _ => ha i, ?_⟩
  filter_upwards [hf] with y' hy'
  rw [hy', Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [hs i]

/-- **The factorization of `W ∘ μ` near `ℰ`**: `W ∘ μ = |σ|² U'` near every point of `ℰ`, with
`σ` a local generator of the exceptional ideal and `U'` smooth and positive. -/
theorem exists_exceptional_factorization (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {p : 𝒳} (hp : p ∈ exceptionalSet F μ) :
    ∃ O : Set 𝒳, IsOpen O ∧ p ∈ O ∧ ∃ (σ : 𝒳 → ℂ) (U' : 𝒳 → ℝ),
      (∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) σ y) ∧
      (∀ y ∈ O, ∀ f, (GermIdeal.pullback (m := m + 1 + 1) μ
          (vanishingIdeal (n := m + 1 + 1) (deformationCentre F))).mem y f ↔
        IsInSpanAt (n := m + 1 + 1) (· = σ) y f) ∧
      (∀ e : ComplexChart (m + 1 + 1) 𝒳,
        ContDiffOn ℝ ∞ (fun z => U' (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' O)) ∧
      (∀ y ∈ O, 0 < U' y) ∧
      ∀ y ∈ O, baseExceptionalWeight F E (μ y) = Complex.normSq (σ y) * U' y := by
  obtain ⟨D, hDid, -, hmet⟩ := hE
  have hq : μ p ∈ deformationCentre F := hp
  obtain ⟨hqZ, hq0⟩ := (mem_deformationCentre_iff F).mp hq
  obtain ⟨V, hV, hxV, g, hg, hgen, h, hh, hw⟩ := hmet (μ p).1
  rw [hDid] at hgen
  obtain ⟨OC, hOC, hqOC, hOCsub, hgenC⟩ := exists_centre_generators F hqZ hV hxV hgen
  have hqOC' : μ p ∈ OC := by
    rw [show μ p = ((μ p).1, projectiveZero) from Prod.ext rfl hq0]; exact hqOC
  obtain ⟨U1, hU1, hpU1, σ, hσd, hσne, hσgen⟩ := hμ.2.2.2.1 p
  have hgV : ∀ x ∈ V, HolomorphicAt (m + 1) g x := fun x hx =>
    (hV.eventually_mem hx).mono fun y hy => (hg y hy).mdifferentiableAt (hV.mem_nhds hy)
  have hgZ : (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem (μ p).1 g :=
    (hgen (μ p).1 hxV g).mpr ⟨hgV _ hxV, 1, fun _ => g, fun _ => 1, fun _ => rfl,
      fun _ => holomorphicAt_const 1, Eventually.of_forall fun y => by simp⟩
  have hτ0 : (μ p).2 ∈ (projectiveModelChart false).source := by
    rw [hq0]; exact projectiveZero_mem_chart_source
  -- the two functions `g ∘ π_X` and `τ ∘ π_{ℙ¹}` lie in `𝓘_C`
  have hu : (vanishingIdeal (n := m + 1 + 1) (deformationCentre F)).mem (μ p)
      (fun q' => g q'.1) := by
    refine ⟨HolomorphicAt.comp_contMDiff (f := Prod.fst) (hgV _ hxV)
      (Eventually.of_forall fun _ => contMDiff_fst.contMDiffAt), ?_⟩
    have h1 : Tendsto Prod.fst (𝓝 (μ p)) (𝓝 (μ p).1) := continuous_fst.continuousAt
    filter_upwards [h1.eventually hgZ.2] with q' hq' hq'C
    exact hq' ((mem_deformationCentre_iff F).mp hq'C).1
  have hv : (vanishingIdeal (n := m + 1 + 1) (deformationCentre F)).mem (μ p)
      (fun q' => projectiveAffine q'.2) := by
    refine ⟨HolomorphicAt.comp_contMDiff (f := Prod.snd) (holomorphicAt_projectiveAffine hτ0)
      (Eventually.of_forall fun _ => contMDiff_snd.contMDiffAt), ?_⟩
    exact Eventually.of_forall fun q' hq'C => by
      show projectiveAffine q'.2 = 0
      rw [((mem_deformationCentre_iff F).mp hq'C).2, projectiveAffine_zero]
  obtain ⟨a, ha, hua⟩ := exists_eq_mul_of_isInSpanAt ((hσgen p hpU1 _).mp
    (mem_pullback_of_mem F hμ hu))
  obtain ⟨b, hb, hvb⟩ := exists_eq_mul_of_isInSpanAt ((hσgen p hpU1 _).mp
    (mem_pullback_of_mem F hμ hv))
  -- `σ` is a combination of `g ∘ π_X ∘ μ` and `τ ∘ μ`
  have hσhol : HolomorphicAt (m + 1 + 1) σ p :=
    (hU1.eventually_mem hpU1).mono fun y hy => (hσd y hy).mdifferentiableAt (hU1.mem_nhds hy)
  obtain ⟨-, N, s, c, hs, hc, hσsum⟩ := (hσgen p hpU1 σ).mpr
    ⟨hσhol, 1, fun _ => σ, fun _ => 1, fun _ => rfl, fun _ => holomorphicAt_const 1,
      Eventually.of_forall fun y => by simp⟩
  choose a' ha' hsa' using hs
  choose c₁ c₂ hc₁ hc₂ hceq using fun i => hgenC (μ p) hqOC' (a' i) (ha' i)
  set A : 𝒳 → ℂ := fun y => ∑ i ∈ Finset.univ, c i y * c₁ i (μ y) with hA
  set B : 𝒳 → ℂ := fun y => ∑ i ∈ Finset.univ, c i y * c₂ i (μ y) with hB
  have hμc : ContinuousAt μ p := hμ.continuous.continuousAt
  have hcomb : ∀ᶠ y in 𝓝 p, σ y = A y * g (μ y).1 + B y * projectiveAffine (μ y).2 := by
    have hall : ∀ᶠ y in 𝓝 p, ∀ i, a' i (μ y) =
        c₁ i (μ y) * g (μ y).1 + c₂ i (μ y) * projectiveAffine (μ y).2 :=
      Filter.eventually_all.mpr fun i => hμc.eventually (hceq i)
    filter_upwards [hσsum, hall] with y hy hall'
    rw [hy, hA, hB]
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsa' i]
    simp only [Function.comp_apply, hall' i]
    ring
  -- hence `A a + B b = 1` at `p`
  have hAhol : HolomorphicAt (m + 1 + 1) A p := HolomorphicAt.sum Finset.univ fun i _ =>
    (hc i).mul (HolomorphicAt.comp_contMDiff (hc₁ i)
      (Eventually.of_forall fun _ => hμ.contMDiff.contMDiffAt))
  have hBhol : HolomorphicAt (m + 1 + 1) B p := HolomorphicAt.sum Finset.univ fun i _ =>
    (hc i).mul (HolomorphicAt.comp_contMDiff (hc₂ i)
      (Eventually.of_forall fun _ => hμ.contMDiff.contMDiffAt))
  set κ : 𝒳 → ℂ := fun y => A y * a y + B y * b y with hκ
  have hκc : ContinuousAt κ p :=
    ((hAhol.continuousAt.mul ha.continuousAt).add (hBhol.continuousAt.mul hb.continuousAt))
  have hκσ : ∀ᶠ y in 𝓝 p, σ y = κ y * σ y := by
    filter_upwards [hcomb, hua, hvb] with y h1 h2 h3
    simp only [Function.comp_apply] at h2 h3
    calc σ y = A y * g (μ y).1 + B y * projectiveAffine (μ y).2 := h1
      _ = A y * (a y * σ y) + B y * (b y * σ y) := by rw [h2, h3]
      _ = κ y * σ y := by rw [hκ]; ring
  have hκp : κ p = 1 := by
    by_contra hne
    have hev : ∀ᶠ y in 𝓝 p, κ y ≠ 1 ∧ σ y = κ y * σ y ∧ y ∈ U1 :=
      (hκc.eventually (isOpen_ne.mem_nhds hne)).and (hκσ.and (hU1.mem_nhds hpU1))
    obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hev
    obtain ⟨y, hyW, hy⟩ := hσne W hW (fun z hz => (hWsub hz).2.2) ⟨p, hpW⟩
    obtain ⟨h1, h2, -⟩ := hWsub hyW
    apply h1
    have h2' : (κ y - 1) * σ y = 0 := by rw [sub_mul, one_mul, ← h2, sub_self]
    rcases mul_eq_zero.mp h2' with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hy
  -- positivity of `|a|² e^h + |b|²` near `p`
  have hh_cont : ContinuousAt h (μ p).1 :=
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn hV hh hxV
  set P : 𝒳 → ℝ := fun y => ‖a y‖ ^ 2 * Real.exp (h (μ y).1) + ‖b y‖ ^ 2 with hP
  have hPc : ContinuousAt P p := by
    have hhμ : ContinuousAt (fun y => h (μ y).1) p :=
      hh_cont.comp (f := fun y => (μ y).1) ((continuous_fst.comp hμ.continuous).continuousAt)
    exact ((ha.continuousAt.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp hhμ)).add
      (hb.continuousAt.norm.pow 2)
  have hPp : 0 < P p := by
    by_cases ha0 : a p = 0
    · have hb0 : b p ≠ 0 := by
        intro hb0
        apply one_ne_zero (α := ℂ)
        rw [← hκp, hκ]
        simp [ha0, hb0]
      have h1 : 0 < ‖b p‖ ^ 2 := by positivity
      have h2 : 0 ≤ ‖a p‖ ^ 2 * Real.exp (h (μ p).1) := by positivity
      simp only [hP]
      linarith
    · have h1 : 0 < ‖a p‖ ^ 2 * Real.exp (h (μ p).1) := by positivity
      have h2 : 0 ≤ ‖b p‖ ^ 2 := by positivity
      simp only [hP]
      linarith
  -- the open set
  have hev : ∀ᶠ y in 𝓝 p, y ∈ U1 ∧ μ y ∈ OC ∧ g (μ y).1 = a y * σ y ∧
      projectiveAffine (μ y).2 = b y * σ y ∧
      MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) a y ∧
      MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) b y ∧ 0 < P y := by
    filter_upwards [hU1.mem_nhds hpU1, hμc.eventually (hOC.mem_nhds hqOC'), hua, hvb, ha, hb,
      hPc.eventually (lt_mem_nhds hPp)] with y h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp hev
  refine ⟨O, hO, hpO, σ, fun y => projectiveWeight 1 (μ y).2 * P y,
    fun y hy => (hσd y (hOsub hy).1).mdifferentiableAt (hU1.mem_nhds (hOsub hy).1),
    fun y hy => hσgen y (hOsub hy).1, ?_, ?_, ?_⟩
  · intro e
    have hN := ProductTestForms.chartSmooth_comp (contMDiff_deformationProjP1 F hμ.contMDiff)
      (fun e => contDiffOn_projectiveWeight 1 e)
    have hOV : O ⊆ (fun y => (μ y).1) ⁻¹' V := fun y hy => (hOCsub (hOsub hy).2.1).1
    have h1 := contDiffOn_norm_sq_comp_chart_symm hO (fun y hy => (hOsub hy).2.2.2.2.1) e
    have h2 := contDiffOn_norm_sq_comp_chart_symm hO (fun y hy => (hOsub hy).2.2.2.2.2.1) e
    have h3 := (contDiffOn_comp_chart_symm_of_holomorphic
      (contMDiff_deformationProjX F hμ.contMDiff) hV hh e).exp
    have hsub : e.val.target ∩ e.val.symm ⁻¹' O ⊆
        e.val.target ∩ e.val.symm ⁻¹' ((fun y => (μ y).1) ⁻¹' V) :=
      fun z hz => ⟨hz.1, hOV hz.2⟩
    exact ((hN e).mono inter_subset_left).mul ((h1.mul (h3.mono hsub)).add h2)
  · intro y hy
    obtain ⟨-, h2, -, -, -, -, h7⟩ := hOsub hy
    have hrep : (μ y).2.rep 1 ≠ 0 := mem_projectiveModelChart_false_source.mp (hOCsub h2).2
    exact mul_pos (projectiveWeight_one_pos hrep) h7
  · intro y hy
    obtain ⟨-, h2, h3, h4, -, -, -⟩ := hOsub hy
    have hrep : (μ y).2.rep 1 ≠ 0 := mem_projectiveModelChart_false_source.mp (hOCsub h2).2
    rw [baseExceptionalWeight_eq, exp_weight_toReal_eq F (hw _ (hOCsub h2).1),
      projectiveWeight_zero_eq hrep, h3, h4, Complex.normSq_eq_norm_sq]
    simp only [hP, norm_mul]
    ring

/-- **Off `ℰ`**, `W ∘ μ` is smooth and positive and the exceptional ideal is the unit ideal. -/
theorem exists_offExceptional_factorization (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {p : 𝒳} (hp : p ∉ exceptionalSet F μ) :
    ∃ O : Set 𝒳, IsOpen O ∧ p ∈ O ∧ ∃ (σ : 𝒳 → ℂ) (U' : 𝒳 → ℝ),
      (∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) σ y) ∧
      (∀ y ∈ O, ∀ f, (GermIdeal.pullback (m := m + 1 + 1) μ
          (vanishingIdeal (n := m + 1 + 1) (deformationCentre F))).mem y f ↔
        IsInSpanAt (n := m + 1 + 1) (· = σ) y f) ∧
      (∀ e : ComplexChart (m + 1 + 1) 𝒳,
        ContDiffOn ℝ ∞ (fun z => U' (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' O)) ∧
      (∀ y ∈ O, 0 < U' y) ∧
      ∀ y ∈ O, baseExceptionalWeight F E (μ y) = Complex.normSq (σ y) * U' y := by
  have hC := isClosed_deformationCentre F
  refine ⟨μ ⁻¹' (deformationCentre F)ᶜ, hC.isOpen_compl.preimage hμ.continuous, hp,
    fun _ => 1, fun y => baseExceptionalWeight F E (μ y),
    fun y _ => mdifferentiableAt_const, ?_, ?_, fun y hy => baseExceptionalWeight_pos F hE hy,
    fun y _ => by simp⟩
  · intro y hy f
    constructor
    · intro hf
      exact isInSpanAt_of_eq_mul rfl hf.1 hf.1 (Eventually.of_forall fun _ => by simp)
    · intro hf
      have hone : (vanishingIdeal (n := m + 1 + 1) (deformationCentre F)).mem (μ y)
          (fun _ => 1) := by
        refine ⟨holomorphicAt_const 1, ?_⟩
        filter_upwards [hC.isOpen_compl.mem_nhds hy] with z hz hzC
        exact absurd hzC hz
      exact isInSpanAt_of_eq_mul (s := fun _ => 1) (S := fun s => ∃ a,
        (vanishingIdeal (n := m + 1 + 1) (deformationCentre F)).mem (μ y) a ∧ s = a ∘ μ)
        ⟨fun _ => 1, hone, rfl⟩ hf.1 hf.1 (Eventually.of_forall fun _ => by simp)
  · intro e
    exact (ProductTestForms.chartSmooth_comp hμ.contMDiff
      (chartSmooth_baseExceptionalWeight F hE) e).mono inter_subset_left

/-- Local factorizations `W ∘ μ = |σ|² U'` at every point of `𝒳`. -/
theorem exists_local_factorization (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (p : 𝒳) :
    ∃ O : Set 𝒳, IsOpen O ∧ p ∈ O ∧ ∃ (σ : 𝒳 → ℂ) (U' : 𝒳 → ℝ),
      (∀ y ∈ O, MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) σ y) ∧
      (∀ y ∈ O, ∀ f, (GermIdeal.pullback (m := m + 1 + 1) μ
          (vanishingIdeal (n := m + 1 + 1) (deformationCentre F))).mem y f ↔
        IsInSpanAt (n := m + 1 + 1) (· = σ) y f) ∧
      (∀ e : ComplexChart (m + 1 + 1) 𝒳,
        ContDiffOn ℝ ∞ (fun z => U' (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' O)) ∧
      (∀ y ∈ O, 0 < U' y) ∧
      ∀ y ∈ O, baseExceptionalWeight F E (μ y) = Complex.normSq (σ y) * U' y := by
  by_cases hp : p ∈ exceptionalSet F μ
  · exact exists_exceptional_factorization F hμ hE hp
  · exact exists_offExceptional_factorization F hμ hE hp

/-- `ℰ` has empty interior. -/
theorem interior_exceptionalSet (hμ : IsNormalConeDeformation F μ) :
    interior (exceptionalSet F μ) = ∅ :=
  interior_eq_empty_of_regularAtDim (by omega) fun _ hz => regularAtDim_exceptionalSet F hμ hz

/-- **The metric of `𝒪(ℰ)`** (`tok-wn-def:exceptional-metric`, weight part): there is a metric of
the exceptional divisor of `μ`, with support `ℰ`, whose weight is `log W ∘ μ`. -/
theorem exists_exceptionalMetric_weight (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    ∃ Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳,
      DivisorMetric.IsDivisorMetric (BlowupExceptionalDivisor.exceptionalDivisor hμ) Eℰ ∧
      Eℰ.support = exceptionalSet F μ ∧
      (∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z)))) ∧
      ∀ x : 𝒳, ∃ O : Set 𝒳, IsOpen O ∧ x ∈ O ∧ ∃ U' : 𝒳 → ℝ,
        (∀ e : ComplexChart (m + 1 + 1) 𝒳,
          ContDiffOn ℝ ∞ (fun z => U' (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' O)) ∧
        (∀ y ∈ O, 0 < U' y) ∧
        ∀ (e : ComplexChart (m + 1 + 1) 𝒳) (z : ComplexModel (m + 1 + 1)),
          z ∈ e.val.target → e.val.symm z ∈ O →
            Eℰ.curvature.val.coeff e z = -smoothDDC (fun w => Real.log (U' (e.val.symm w))) z := by
  classical
  choose O hO hpO σ U' hσd hgen hsm hpos hfac using exists_local_factorization F hμ hE
  have hint := interior_exceptionalSet F hμ
  set Fct : FactorizedWeightForm.WeightFactorization (m + 1 + 1)
      (fun y => baseExceptionalWeight F E (μ y)) :=
    { domain := O
      isOpen_domain := hO
      mem_domain := hpO
      gen := σ
      smoothPart := U'
      gen_mdifferentiable := hσd
      smooth := hsm
      pos := hpos
      factor := hfac
      nowhereZero := fun W hW hne => by
        by_contra hall
        push Not at hall
        have hsub : W ⊆ exceptionalSet F μ := by
          intro y hy
          by_contra hyE
          exact (baseExceptionalWeight_pos F hE hyE).ne' (hall y hy)
        obtain ⟨y, hy⟩ := hne
        have := interior_maximal hsub hW hy
        rw [hint] at this
        exact this } with hFct
  refine ⟨ExceptionalMetricProof.ofWeightFactorization Fct 1 one_pos, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨O x, hO x, hpO x, σ x, fun y hy => (hσd x y hy).mdifferentiableWithinAt,
      fun y hy f => ?_, fun y => Real.log (U' x y),
      fun e => (hsm x e).log fun u hu => (hpos x _ hu.2).ne', fun y hy => ?_⟩
    · exact hgen x y hy f
    · show (((1 : ℚ) : ℝ) : EReal) * FactorizedWeightPsh.logWeight
        (fun y => baseExceptionalWeight F E (μ y)) y = _
      have hsplit : FactorizedWeightPsh.logWeight (fun y => baseExceptionalWeight F E (μ y)) y =
          generatorLog (fun _ : Fin 1 => σ x) y + (Real.log (U' x y) : EReal) := by
        show ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ y))) = _
        rw [hfac x y hy, generatorLog_eq_log_sum,
          ENNReal.ofReal_mul (Complex.normSq_nonneg _), ENNReal.log_mul_add,
          ENNReal.log_ofReal_of_pos (hpos x y hy)]
        simp [Complex.normSq_eq_norm_sq]
      rw [hsplit]
      simp
  · ext y
    change (((1 : ℚ) : ℝ) : EReal) * FactorizedWeightPsh.logWeight
      (fun y => baseExceptionalWeight F E (μ y)) y = ⊥ ↔ μ y ∈ deformationCentre F
    simp only [Rat.cast_one, EReal.coe_one, one_mul, FactorizedWeightPsh.logWeight]
    constructor
    · intro h
      by_contra hy
      have hpos' := baseExceptionalWeight_pos F hE hy
      rw [ENNReal.log_ofReal_of_pos hpos'] at h
      exact EReal.coe_ne_bot _ h
    · intro hy
      rw [baseExceptionalWeight_eq_zero F hE hy]
      simp
  · intro z
    show (((1 : ℚ) : ℝ) : EReal) * FactorizedWeightPsh.logWeight
      (fun y => baseExceptionalWeight F E (μ y)) z = _
    simp [FactorizedWeightPsh.logWeight]
  · intro x
    refine ⟨O x, hO x, hpO x, U' x, hsm x, hpos x, fun e z hz hzO => ?_⟩
    show ((-((1 : ℚ) : ℝ)) • Fct.closedForm).val.coeff e z = _
    rw [ClosedRealOneOneForm.coeff_smul,
      (Fct.closedForm_coeff_eventuallyEq x e hz hzO).self_of_nhds]
    simp only [Rat.cast_one, Fct]
    exact neg_one_smul ℝ (smoothDDC (fun u' => Real.log (U' x (e.val.symm u'))) z)

/-- The weight of a unit metric of `Z` is never `+∞`. -/
theorem weight_ne_top {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (x : F.carrier) : E.weight x ≠ ⊤ := by
  obtain ⟨D, -, -, hmet⟩ := hE
  obtain ⟨V, hV, hxV, g, -, -, h, -, hw⟩ := hmet x
  rw [hw x hxV, generatorLog_eq_log_sum]
  exact EReal.add_ne_top (fun h => ENNReal.ofReal_ne_top (ENNReal.log_eq_top_iff.mp h))
    (EReal.coe_ne_top _)

omit [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- On `X' ≅ X`, the weight `log W ∘ μ` restricts to the weight `log |s_Z|²_h` of `E`. -/
theorem weight_comp_centralSection {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {ι : F.carrier → 𝒳}
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) (x : F.carrier) :
    ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ (ι x)))) = E.weight x := by
  have h1 : projectiveWeight 1 projectiveZero = 1 := by
    linarith [projectiveWeight_add projectiveZero, projectiveWeight_zero_projectiveZero]
  rw [hμι, baseExceptionalWeight_eq]
  simp only [h1, mul_one, projectiveWeight_zero_projectiveZero, add_zero]
  rw [ENNReal.ofReal_toReal (fun h => weight_ne_top F hE x (EReal.exp_eq_top_iff.mp h)),
    EReal.log_exp]

/-- **The curvature of the metric of `𝒪(ℰ)` restricts to that of `E` on `X' ≅ X`.**  Off `Z`,
both are `-ddᶜ` of the same weight (the weights agree, `weight_comp_centralSection`); they agree
on `Z` by density of `X \ Z` and continuity of the coefficients. -/
theorem pullback_curvature_geometricallyEq {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hweight : ∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z))))
    (hsupp : Eℰ.support = exceptionalSet F μ) {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) :
    (ClosedRealOneOneForm.pullback hι Eℰ.curvature).val.GeometricallyEq E.curvature.val := by
  have hwι : ∀ y, Eℰ.weight (ι y) = E.weight y := fun y => by
    rw [hweight]; exact weight_comp_centralSection F hE hμι y
  obtain ⟨D, -, hEsupp, -⟩ := hE
  intro e
  -- equality off `Z`
  have hoff : EqOn ((ClosedRealOneOneForm.pullback hι Eℰ.curvature).val.coeff e)
      (E.curvature.val.coeff e) (e.val.target ∩ {z | e.val.symm z ∉ F.flag (1 : Fin (m + 2))}) := by
    rintro z ⟨hz, hzZ⟩
    set x := e.val.symm z with hx
    have hxE : x ∉ E.support := by rw [hEsupp]; exact hzZ
    have hιx : ι x ∉ Eℰ.support := by
      rw [hsupp]
      intro h
      apply hzZ
      have := (mem_deformationCentre_iff F).mp (show μ (ι x) ∈ deformationCentre F from h)
      rw [hμι] at this
      exact this.1
    set d := complexChartAt (n := m + 1 + 1) (ι x)
    have hzd : z ∈ coordinateDomain ι e d := ⟨hz, mem_complexChartAt_source _⟩
    obtain ⟨W₁, hW₁, hpot₁⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature Eℰ hιx d
        (mem_complexChartAt_source _)
    obtain ⟨W₂, hW₂, hpot₂⟩ :=
      MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E hxE e
        (e.val.map_target hz)
    have hpull := isSmoothLocalPotential_pullback hι e hpot₁
    have hzW : z ∈ potentialDomain ι e d W₁ := by
      refine ⟨hzd, ?_⟩
      show d.val (ι (e.val.symm z)) ∈ W₁
      exact hW₁
    have hzW₂ : z ∈ W₂ := by
      have : e.val (e.val.symm z) = z := e.val.right_inv hz
      rw [← this]; exact hW₂
    -- the two potentials agree near `z`
    have hρ : (fun ζ => (Eℰ.weight (d.val.symm ζ)).toReal) ∘ coordinateMap ι e d =ᶠ[𝓝 z]
        fun ζ => (E.weight (e.val.symm ζ)).toReal := by
      filter_upwards [(coordinateDomain_isOpen hι e d).mem_nhds hzd] with w hw
      show (Eℰ.weight (d.val.symm (d.val (ι (e.val.symm w))))).toReal = _
      rw [d.val.left_inv hw.2, hwι]
    have h1 := hpull.2.2.2 hzW
    have h2 := hpot₂.2.2.2 hzW₂
    rw [smoothDDC_congr hρ] at h1
    rw [h2] at h1
    -- `h1 : (-E.curv).coeff e z = (pullback (-Eℰ.curv)).coeff e z`
    have hneg₁ : (SmoothRealForm.pullback hι (-Eℰ.curvature).val).coeff e z =
        -(ClosedRealOneOneForm.pullback hι Eℰ.curvature).val.coeff e z := by
      rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hι _ e d hzd,
        SmoothRealForm.pullback_coeff hι _ e d hzd]
      ext v
      simp
    have hneg₂ : (-E.curvature).val.coeff e z = -E.curvature.val.coeff e z := by
      ext v
      simp
    rw [hneg₁, hneg₂] at h1
    exact (neg_inj.mp h1).symm
  -- density of `X \ Z`
  have hdense : e.val.target ⊆
      closure (e.val.target ∩ {z | e.val.symm z ∉ F.flag (1 : Fin (m + 2))}) := by
    intro z hz
    rw [mem_closure_iff]
    intro o ho hzo
    by_contra hempty
    have hsub : o ∩ e.val.target ⊆ e.val.symm ⁻¹' F.flag (1 : Fin (m + 2)) := by
      intro w hw
      by_contra hwZ
      exact hempty ⟨w, hw.1, hw.2, hwZ⟩
    have hopen : IsOpen (e.val.symm '' (o ∩ e.val.target)) :=
      e.val.symm.isOpen_image_of_subset_source (ho.inter e.val.open_target) inter_subset_right
    have himg : e.val.symm '' (o ∩ e.val.target) ⊆ F.flag (1 : Fin (m + 2)) := by
      rintro _ ⟨w, hw, rfl⟩
      exact hsub hw
    have := interior_maximal himg hopen ⟨z, ⟨hzo, hz⟩, rfl⟩
    rw [interior_firstFlag F] at this
    exact this
  exact hoff.of_subset_closure
    ((ClosedRealOneOneForm.pullback hι Eℰ.curvature).val.smooth e).continuousOn
    (E.curvature.val.smooth e).continuousOn inter_subset_left hdense

/-- **`tok-wn:deformation`, the metric of `𝒪(ℰ)`** (`ExceptionalMetricStatement`). -/
theorem exceptionalMetric : ExceptionalMetricStatement F := by
  intro E hE _ 𝒳 _ _ _ μ hμ
  obtain ⟨Eℰ, hmet, hsupp, hweight, -⟩ := exists_exceptionalMetric_weight F hμ hE
  exact ⟨Eℰ, hmet, hsupp, hweight, fun ι hι hμι =>
    pullback_curvature_geometricallyEq F hE hweight hsupp hι hμι⟩

end Factorization

end SGPT.Okounkov.TranscendentalWN

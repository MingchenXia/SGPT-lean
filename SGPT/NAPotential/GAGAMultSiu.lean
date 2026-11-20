import SGPT.PSH.GlobalL2PointMain
import SGPT.NAPotential.GAGAMultSkodaStep
import SGPT.NAPotential.GAGAMultSiuGerms
import SGPT.Okounkov.TranscendentalL2Weight

/-!
# Siu's uniform global generation of multiplier ideals on a compact complex manifold

Blueprint `claude-gagamult:siu-generation`.  Let `X` be a compact complex manifold of positive
dimension with a Kähler background `ω` and a smooth positive volume `μ`, `L, T` holomorphic line
bundles with smooth Hermitian metrics, `θ = c₁(L, h_L)` and `δ > 0`.  There is `k₀` such that for
every `k ≥ k₀`, every `φ ∈ PSH(X, θ - δω)` and every point `x`, the stalk `𝓘(kφ)_x` is generated,
in any local frame of `L^k ⊗ T` at `x`, by the coefficients of the global holomorphic sections
`s ∈ H⁰(X, L^k ⊗ T)` with `∫_X |s|² e^{-kφ} dμ < ∞` (`siuGlobalGeneration`).

This is the uniform global generation theorem of Siu (see Demailly, *Analytic methods in
algebraic geometry*, the section on Siu's uniform global generation), in the form used by the
book for the algebraic models of multiplier ideals (`def:NApotential:L975`, `lma:varphian`,
`lma:Siu_global_uniform_generatedness`).  The constant `k₀` depends only on `X, ω, μ, L, T, δ`.

## Proof

For a germ `g ∈ 𝓘(kφ)_x` take the local section `F = g e` (`e` the frame), a cut-off `χ` near
`x`, and the pole weight `φ' = φ + (n+2)/k · log|z - z(x)|²` (cut off), which lies in
`PSH(X, θ - (δ/2)ω)` for `k ≥ 2(n+2)B/δ` (`isThetaPshPotential_poleWeight`).  The global `L²`
correction (`globalCutoffCorrection`) gives `s ∈ H⁰(X, L^k ⊗ T)` with
`∫ |χF - s|² e^{-kφ'} < ∞`; then `∫ |s|² e^{-kφ} < ∞`, and near `x` the coefficient of `F - s`
satisfies `∫ |F - s|² |z - z(x)|^{-2(n+2)} e^{-kφ} < ∞`, so by the local Skoda step
(`exists_centred_division`) `g - s_e ∈ 𝔪_x 𝓘(kφ)_x` (`exists_section_mod_maximal`).  Nakayama's
lemma in the Noetherian local ring `𝒪_x` concludes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.Okounkov SGPT.PSH.IdealRestriction

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Holomorphic functions read in a chart -/

/-- A function holomorphic on an open set of a chart's model space, read through the chart, is
holomorphic near every point of the chart's source mapped into that set. -/
theorem holomorphicAt_comp_chart (c : ComplexChart n X) {f : ComplexModel n → ℂ}
    {V : Set (ComplexModel n)} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) {x : X}
    (hx : x ∈ c.val.source) (hxV : c.val x ∈ V) : HolomorphicAt n (fun y => f (c.val y)) x := by
  filter_upwards [c.val.isOpen_inter_preimage hV |>.mem_nhds ⟨hx, hxV⟩] with y hy
  have hsC : ContDiffAt ℂ ∞ f (c.val y) := contDiffAt_of_differentiableOn_complex hf hV hy.2
  exact (hsC.contMDiffAt.comp y (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas c.property) hy.1)).mdifferentiableAt (by simp)

/-- The centred chart coordinates `z_i - z_i(x)` are holomorphic near `x` and vanish at `x`. -/
theorem holomorphicAt_chartCoord (c : ComplexChart n X) {x : X} (hx : x ∈ c.val.source)
    (i : Fin n) : HolomorphicAt n (fun y => centredCoords (c.val x) i (c.val y)) x :=
  holomorphicAt_comp_chart c isOpen_univ (differentiable_centredCoords _ i).differentiableOn hx
    (mem_univ _)

variable [MeasurableSpace X] [BorelSpace X]

/-! ### The local weight of the cover data -/

section Weight

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)
  (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
  {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal}
  (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)

include hL hT hk hφ in
/-- The local weight of chart `a` is `|E_a|² e^{-kφ}` read in the chart. -/
theorem W_eq_frameNorm (a : Fin D.m) {z : ComplexModel n}
    (hz : z ∈ ball (ctr (n := n) (D.pt a)) (D.R a)) :
    (D.toGluingSystem hL hT hk hφ).W a z =
      ENNReal.ofReal (‖(D.frameE k a).val.symm ((D.chartA a).val.symm z) 1‖ ^ 2) *
        multiplierWeight (k : ℝ) (φ ((D.chartA a).val.symm z)) := by
  set G := D.toGluingSystem hL hT hk hφ
  have hzt : z ∈ (D.chartA a).val.target := D.ball_subset_target a hz
  have hs : (D.chartA a).val.symm z ∈ (D.chartA a).val.source := (D.chartA a).val.map_target hzt
  have hz' : (D.chartA a).val ((D.chartA a).val.symm z) ∈ ball (ctr (n := n) (D.pt a)) (D.R a) := by
    rw [(D.chartA a).val.right_inv hzt]; exact hz
  have h := G.density_eq a ((D.chartA a).val.symm z)
    ((D.frameE k a).val.symm ((D.chartA a).val.symm z) 1) hs hz'
  have hc : G.coef a ((D.chartA a).val.symm z)
      ((D.frameE k a).val.symm ((D.chartA a).val.symm z) 1) = 1 :=
    trivialization_coef_frame _ (D.mem_frameE_baseSet hs hz')
  rw [hc, norm_one, one_pow, ENNReal.ofReal_one, one_mul] at h
  have hcz : G.chart a ((D.chartA a).val.symm z) = z := (D.chartA a).val.right_inv hzt
  rw [hcz] at h
  exact h.symm


include hL hT hk hφ in
/-- **The section congruent to a germ modulo `𝔪_x 𝓘(kφ)_x`** (blueprint
`claude-gagamult:siu-mod-m`).  Given the pole weight `ψ = (n+2) log |z_a - z_a(x)|²` near `x`
(cut off, `ψ ≤ 0`) for which the global correction `hcorr` is available, every germ
`g ∈ 𝓘(kφ)_x` is congruent, modulo `𝔪_x 𝓘(kφ)_x` and after multiplication by a unit `t`, to the
coefficient in the frame `e` of a global section `s` with `∫ |s|² e^{-kφ} < ∞`. -/
theorem exists_section_mod_maximal (hn : 0 < n) {ψ : X → EReal}
    (hcorr : ∀ U : Set X, IsOpen U → ∀ F : (y : X) → (twistedPower L T k).Fiber y,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) (twistedPower L T k).Fiber F U →
      ∀ χ : X → ℝ, ChartSmooth (n := n) χ → tsupport χ ⊆ U →
      ∀ K : Set X, IsCompact K → K ⊆ U → (∀ y ∈ U \ K, ∀ᶠ y' in 𝓝 y, χ y' = χ y) →
      ∫⁻ y in K, ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (k : ℝ) (poleWeight φ ψ k y) ∂μ
        < ⊤ →
      ∃ s : twistedSections L T k, ∫⁻ y, ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y - s y‖ ^ 2) *
        multiplierWeight (k : ℝ) (poleWeight φ ψ k y) ∂μ < ⊤)
    (a : Fin D.m) {x : X} (hxa : x ∈ (D.chartA a).val.source) {ε : ℝ} (hε : 0 < ε)
    (hεR : ball ((D.chartA a).val x) ε ⊆ ball (ctr (n := n) (D.pt a)) (D.R a / 2))
    (hψ0 : ∀ y, ψ y ≤ 0)
    (hψpole : ∀ y ∈ (D.chartA a).val.source, (D.chartA a).val y ∈ ball ((D.chartA a).val x) ε →
      ψ y = ((((n : ℝ) + 2 : ℝ)) : EReal) * logNormSq ((D.chartA a).val y - (D.chartA a).val x))
    (hψlow : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ε → ∀ y, (y ∈ (D.chartA a).val.source →
        ρ ≤ ‖(D.chartA a).val y - (D.chartA a).val x‖) →
      (((((n : ℝ) + 2) * Real.log (ρ ^ 2)) : ℝ) : EReal) ≤ ψ y)
    (e : AtlasFrame (twistedPower L T k)) (hxe : x ∈ e.val.baseSet) {g : X → ℂ}
    (hg : (multiplierIdeal (n := n) (k : ℝ) φ).mem x g) :
    ∃ s : twistedSections L T k,
      ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ < ⊤ ∧
      ∃ (t : X → ℂ) (h : Fin n → X → ℂ), HolomorphicAt n t x ∧ t x ≠ 0 ∧
        (∀ i, (multiplierIdeal (n := n) (k : ℝ) φ).mem x (h i)) ∧
        ∀ᶠ y in 𝓝 x, t y * (g y - e.val.continuousLinearMapAt ℂ y (s y)) =
          ∑ i, centredCoords ((D.chartA a).val x) i ((D.chartA a).val y) * h i y := by
  classical
  have := e.property
  set G := D.toGluingSystem hL hT hk hφ with hG
  set c := D.chartA a with hc
  set p := c.val x with hp
  set E := D.frameE k a with hE
  have := E.property
  have hk0 : 0 < k := hk.1
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hφtop : ∀ y, φ y ≠ ⊤ := fun y => hφ.1.quasiPlurisubharmonic.ne_top y
  have hRa := D.R_pos a
  have hεR' : ball p ε ⊆ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    hεR.trans (ball_subset_ball (by linarith))
  have hpR : p ∈ ball (ctr (n := n) (D.pt a)) (D.R a) := hεR' (mem_ball_self hε)
  have hxE : x ∈ E.val.baseSet := D.mem_frameE_baseSet hxa hpR
  -- step 1: the multiplier integrability of `g` read in the chart `c`
  obtain ⟨hgx, hgint⟩ := hg
  have huscφ : ∀ e₁ e₂ : ComplexChart n X,
      UpperSemicontinuousOn (chartFunction φ e₁) (ChartWeightedL2.overlapDomain e₁ e₂) := by
    intro e₁ e₂
    have h := SGPT.Okounkov.TranscendentalL2.upperSemicontinuousOn_chartFunction_of_thetaPlurisubharmonicOn
      (Ω := univ) (fun e z hz _ => hφ.1 e z hz) e₁
    exact h.mono fun z hz => ⟨hz.1, mem_univ _⟩
  have hgc := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) c
    (complexChartAt (n := n) x) hxa (mem_complexChartAt_source x) (huscφ _ _) hk0'.ne' hgint
  obtain ⟨-, U₀, hU₀o, hpU₀, -, -, hU₀int⟩ := hgc
  -- step 2: the radius
  obtain ⟨Vg, hVg, hVgo, hxVg⟩ := eventually_nhds_iff.mp hgx
  set W₀ : Set (ComplexModel n) :=
    U₀ ∩ ball p ε ∩ (c.val.target ∩ c.val.symm ⁻¹' (Vg ∩ e.val.baseSet)) with hW₀
  have hW₀o : IsOpen W₀ := (hU₀o.inter isOpen_ball).inter
    (c.val.isOpen_inter_preimage_symm (hVgo.inter e.val.open_baseSet))
  have hpW₀ : p ∈ W₀ := ⟨⟨hpU₀, mem_ball_self hε⟩, c.val.map_source hxa, by
    simp only [mem_preimage, hp, c.val.left_inv hxa]; exact ⟨hxVg, hxe⟩⟩
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.mp hW₀o p hpW₀
  set r₁ : ℝ := min ρ ε / 8 with hr₁def
  have hr₁ : 0 < r₁ := by have := lt_min hρ hε; positivity
  have h8ρ : 8 * r₁ ≤ ρ := by have := min_le_left ρ ε; rw [hr₁def]; linarith
  have h8ε : 8 * r₁ ≤ ε := by have := min_le_right ρ ε; rw [hr₁def]; linarith
  have hW4 : ∀ z ∈ closedBall p (4 * r₁), z ∈ W₀ := fun z hz =>
    hρW (by rw [mem_ball]; linarith [mem_closedBall.mp hz])
  have hct : ∀ z ∈ closedBall p (4 * r₁), z ∈ c.val.target := fun z hz => (hW4 z hz).2.1
  have hcVe : ∀ z ∈ closedBall p (4 * r₁), c.val.symm z ∈ Vg ∩ e.val.baseSet :=
    fun z hz => (hW4 z hz).2.2
  have hcR : ∀ z ∈ closedBall p (4 * r₁), z ∈ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    fun z hz => hεR' (hW4 z hz).1.2
  have hcU₀ : ∀ z ∈ closedBall p (4 * r₁), z ∈ U₀ := fun z hz => (hW4 z hz).1.1
  -- step 3: the local section `F = g e`
  set Uset : Set X := c.val.source ∩ c.val ⁻¹' ball p (4 * r₁) with hUset
  have hUo : IsOpen Uset := c.val.isOpen_inter_preimage isOpen_ball
  have hUmem : ∀ y ∈ Uset, y ∈ Vg ∩ e.val.baseSet := by
    intro y hy
    have h := hcVe (c.val y) (ball_subset_closedBall hy.2)
    rwa [c.val.left_inv hy.1] at h
  set F : (y : X) → (twistedPower L T k).Fiber y := fun y => g y • e.val.symm y 1 with hFdef
  have hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) (twistedPower L T k).Fiber
      F Uset :=
    isHolomorphicSectionOn_smul_frame e.val (fun y hy => (hUmem y hy).2)
      (fun y hy => hVg y (hUmem y hy).1)
  -- step 4: the cut-off `χ`, `1` on `B(p, r₁)`, supported in `B(p, 2r₁)`
  set β : ContDiffBump p := ⟨r₁, 2 * r₁, hr₁, by linarith⟩ with hβ
  set χ : X → ℝ := ChartPartition.chartExtend c β with hχdef
  have hβt : tsupport β = closedBall p (2 * r₁) := β.tsupport_eq
  have hcb2 : closedBall p (2 * r₁) ⊆ c.val.target := fun z hz =>
    hct z (closedBall_subset_closedBall (by linarith) hz)
  have hχ : ChartSmooth (n := n) χ := ChartPartition.chartSmooth_chartExtend c β.contDiff
    β.hasCompactSupport.isCompact (by rw [hβt]; exact hcb2)
  have hχU : tsupport χ ⊆ Uset := by
    refine (ChartPartition.support_chartExtend_subset c).trans ?_
    rw [hβt]
    have hcomp : IsCompact (c.val.symm '' closedBall p (2 * r₁)) :=
      (isCompact_closedBall p _).image_of_continuousOn (c.val.continuousOn_symm.mono hcb2)
    rw [hcomp.isClosed.closure_eq]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨c.val.map_target (hcb2 hw), ?_⟩
    rw [mem_preimage, c.val.right_inv (hcb2 hw), mem_ball]
    have := mem_closedBall.mp hw; linarith
  have hχ0 : ∀ y, 0 ≤ χ y := ChartPartition.chartExtend_nonneg fun z => β.nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := ChartPartition.chartExtend_le_one fun z => β.le_one
  have hχone : ∀ y ∈ c.val.source, c.val y ∈ ball p r₁ → χ y = 1 := by
    intro y hy hyr
    rw [hχdef, ChartPartition.chartExtend_of_mem hy]
    exact β.one_of_mem_closedBall (ball_subset_closedBall hyr)
  set A₀ : Set (ComplexModel n) := closedBall p (2 * r₁) ∩ {w | r₁ ≤ dist w p} with hA₀
  set K : Set X := c.val.symm '' A₀ with hKdef
  have hA₀c : IsCompact A₀ := (isCompact_closedBall p _).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hK : IsCompact K :=
    hA₀c.image_of_continuousOn (c.val.continuousOn_symm.mono fun w hw => hcb2 hw.1)
  have hKU : K ⊆ Uset := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨c.val.map_target (hcb2 hw.1), ?_⟩
    rw [mem_preimage, c.val.right_inv (hcb2 hw.1), mem_ball]
    have := mem_closedBall.mp hw.1; linarith
  have hKann : ∀ y ∈ K, y ∈ c.val.source ∧ r₁ ≤ ‖c.val y - p‖ := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨c.val.map_target (hcb2 hw.1), ?_⟩
    rw [c.val.right_inv (hcb2 hw.1), ← dist_eq_norm]; exact hw.2
  have hconst : ∀ y ∈ Uset \ K, ∀ᶠ y' in 𝓝 y, χ y' = χ y := by
    rintro y ⟨⟨hy, -⟩, hyK⟩
    by_cases h1 : dist (c.val y) p < r₁
    · have hO : IsOpen (c.val.source ∩ c.val ⁻¹' ball p r₁) :=
        c.val.isOpen_inter_preimage isOpen_ball
      filter_upwards [hO.mem_nhds ⟨hy, h1⟩] with y' hy'
      rw [hχone y' hy'.1 hy'.2, hχone y hy h1]
    · have h3 : 2 * r₁ < dist (c.val y) p := by
        by_contra hle
        exact hyK ⟨c.val y, ⟨mem_closedBall.mpr (not_lt.mp hle), not_lt.mp h1⟩,
          c.val.left_inv hy⟩
      have hO : IsOpen (c.val.source ∩ c.val ⁻¹' {w | 2 * r₁ < dist w p}) :=
        c.val.isOpen_inter_preimage (isOpen_lt continuous_const
          (continuous_id.dist continuous_const))
      have hval : ∀ y' ∈ c.val.source ∩ c.val ⁻¹' {w | 2 * r₁ < dist w p}, χ y' = 0 := by
        intro y' hy'
        rw [hχdef, ChartPartition.chartExtend_of_mem hy'.1]
        exact β.zero_of_le_dist (le_of_lt hy'.2)
      filter_upwards [hO.mem_nhds ⟨hy, h3⟩] with y' hy'
      rw [hval y' hy', hval y ⟨hy, h3⟩]
  -- step 5: `∫_U |F|² e^{-kφ} < ∞`
  set Kc : Set X := c.val.symm '' closedBall p (4 * r₁) with hKc
  have hKcc : IsCompact Kc := (isCompact_closedBall p _).image_of_continuousOn
    (c.val.continuousOn_symm.mono fun z hz => hct z hz)
  have hKce : Kc ⊆ e.val.baseSet := by
    rintro _ ⟨z, hz, rfl⟩; exact (hcVe z hz).2
  obtain ⟨Ce, hCe⟩ := hKcc.exists_bound_of_continuousOn
    ((frameNorm_continuousOn (twistedPower L T k).Fiber e.val).mono hKce)
  have hball4R : ball p (4 * r₁) ⊆ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    fun z hz => hcR z (ball_subset_closedBall hz)
  have hFcoef : DifferentiableOn ℂ (G.locCoef a F) (ball p (4 * r₁)) := by
    refine (differentiableOn_coord_of_holomorphicSectionOn E.val c hUo hF).mono fun z hz => ?_
    have hzt : z ∈ c.val.target := hct z (ball_subset_closedBall hz)
    have hs : c.val.symm z ∈ c.val.source := c.val.map_target hzt
    refine ⟨hzt, ⟨hs, by rw [mem_preimage, c.val.right_inv hzt]; exact hz⟩, ?_⟩
    exact D.mem_frameE_baseSet hs (by rw [c.val.right_inv hzt]; exact hball4R hz)
  have hFU : ∫⁻ y in Uset, G.D F y ∂μ < ⊤ := by
    have h1 := G.lintegral_open_le a F isOpen_ball hball4R hFcoef.continuousOn
    refine lt_of_le_of_lt h1 (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr G.A_ne_top) ?_)
    calc ∫⁻ z in ball p (4 * r₁), ENNReal.ofReal (‖G.locCoef a F z‖ ^ 2) * G.W a z
        ≤ ∫⁻ z in ball p (4 * r₁), ENNReal.ofReal (Ce ^ 2) *
            multiplierDensity (chartFunction φ c) (k : ℝ) (fun z => g (c.val.symm z)) z := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          have hzt : z ∈ c.val.target := hct z (ball_subset_closedBall hz)
          have hs : c.val.symm z ∈ c.val.source := c.val.map_target hzt
          have hzR := hball4R hz
          have hd := G.density_eq a (c.val.symm z) (F (c.val.symm z)) hs
            (by show c.val (c.val.symm z) ∈ _; rw [c.val.right_inv hzt]; exact hzR)
          have hcz : G.chart a (c.val.symm z) = z := c.val.right_inv hzt
          rw [hcz] at hd
          have hW : G.W a z = ballWeight (G.Ψ a) G.lam (G.center a) z := rfl
          have hlc : G.locCoef a F z = G.coef a (c.val.symm z) (F (c.val.symm z)) := rfl
          rw [hlc, hW, ← hd]
          have hnF : ‖F (c.val.symm z)‖ ≤ ‖g (c.val.symm z)‖ * Ce := by
            show ‖g (c.val.symm z) • e.val.symm (c.val.symm z) 1‖ ≤ _
            rw [norm_smul]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have := hCe (c.val.symm z) ⟨z, ball_subset_closedBall hz, rfl⟩
            exact (le_abs_self _).trans this
          show ENNReal.ofReal (‖F (c.val.symm z)‖ ^ 2) * multiplierWeight (k : ℝ) (φ (c.val.symm z))
            ≤ ENNReal.ofReal (Ce ^ 2) * (ENNReal.ofReal (‖g (c.val.symm z)‖ ^ 2) *
              multiplierWeight (k : ℝ) (φ (c.val.symm z)))
          rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          calc ‖F (c.val.symm z)‖ ^ 2 ≤ (‖g (c.val.symm z)‖ * Ce) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) hnF 2
            _ = Ce ^ 2 * ‖g (c.val.symm z)‖ ^ 2 := by ring
      _ = ENNReal.ofReal (Ce ^ 2) * ∫⁻ z in ball p (4 * r₁),
            multiplierDensity (chartFunction φ c) (k : ℝ) (fun z => g (c.val.symm z)) z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Ce ^ 2) * ∫⁻ z in U₀,
            multiplierDensity (chartFunction φ c) (k : ℝ) (fun z => g (c.val.symm z)) z :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set fun z hz =>
            hcU₀ z (ball_subset_closedBall hz)) zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU₀int
  -- the energy of `F` over `K` for the pole weight
  set er : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(((n : ℝ) + 2) * Real.log (r₁ ^ 2)))) with her
  have hKint : ∫⁻ y in K, ENNReal.ofReal (‖F y‖ ^ 2) *
      multiplierWeight (k : ℝ) (poleWeight φ ψ k y) ∂μ < ⊤ := by
    calc ∫⁻ y in K, ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (k : ℝ) (poleWeight φ ψ k y) ∂μ
        ≤ ∫⁻ y in K, G.D F y * er ∂μ := by
          refine setLIntegral_mono' hK.isClosed.measurableSet fun y hy => ?_
          show _ ≤ ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) * er
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          exact multiplierWeight_poleWeight_le hk0 (hφtop y)
            (hψlow r₁ hr₁ (by linarith) y fun _ => (hKann y hy).2) (hψ0 y)
      _ = (∫⁻ y in K, G.D F y ∂μ) * er := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (∫⁻ y in Uset, G.D F y ∂μ) * er := mul_le_mul_of_nonneg_right (lintegral_mono_set hKU) zero_le
      _ < ⊤ := ENNReal.mul_lt_top hFU ENNReal.ofReal_lt_top
  -- step 6: the global correction
  obtain ⟨σ, hσ⟩ := hcorr Uset hUo F hF χ hχ hχU K hK hKU hconst hKint
  -- step 7: `∫ |σ|² e^{-kφ} < ∞`
  set v₀ : (y : X) → (twistedPower L T k).Fiber y := fun y => ((χ y : ℝ) : ℂ) • F y with hv₀
  have hσcoefd : ∀ i, DifferentiableOn ℂ (G.locCoef i (fun y => σ y))
      (ball (ctr (n := n) (D.pt i)) (D.R i)) := by
    intro i
    have := (D.frameE k i).property
    refine (differentiableOn_coord_of_holomorphicSectionOn (D.frameE k i).val (D.chartA i)
      isOpen_univ (F := fun y => σ y) (fun y _ => ((σ.contMDiff y).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt)).mono fun z hz => ?_
    have hzt := D.ball_subset_target i hz
    have hs : (D.chartA i).val.symm z ∈ (D.chartA i).val.source := (D.chartA i).val.map_target hzt
    exact ⟨hzt, mem_univ _, D.mem_frameE_baseSet hs
      (by rw [(D.chartA i).val.right_inv hzt]; exact hz)⟩
  have hσcoef : ∀ i, ContinuousOn (G.locCoef i (fun y => σ y)) (ball (G.center i) (G.r i)) :=
    fun i => (hσcoefd i).continuousOn.mono (ball_subset_ball (G.r_lt_R i).le)
  have hv₀c : ∀ i, ContinuousOn (G.locCoef i v₀) (ball (G.center i) (G.r i)) := by
    intro i z hz
    obtain ⟨C, -, hC⟩ := bound_dbarNormSq_χ hχ (D.pt i) (D.closedBall_subset_target i)
    have hzR : z ∈ ball (ctr (n := n) (D.pt i)) (D.R i) :=
      ball_subset_ball (G.r_lt_R i).le hz
    exact ((D.datum_spec hL hT hk hφ hUo hF hχ hχU hKU hconst i hC hzR).1).continuousAt
      |>.continuousWithinAt
  set X₁ := ∫⁻ y, G.D (fun y => v₀ y - σ y) y ∂μ with hX₁def
  have hX₁ : X₁ < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) hσ
    show ENNReal.ofReal (‖v₀ y - σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤ _
    exact mul_le_mul_of_nonneg_left (multiplierWeight_le_poleWeight hψ0 y) zero_le
  set X₂ := ∫⁻ y, G.D v₀ y ∂μ with hX₂def
  have hX₂ : X₂ < ⊤ := by
    have hχF : ∀ y, G.D v₀ y ≤ Uset.indicator (G.D F) y := by
      intro y
      by_cases hyU : y ∈ Uset
      · rw [indicator_of_mem hyU]
        show ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤
          ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 y), mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (hχ0 y) (hχ1 y))
      · rw [indicator_of_notMem hyU]
        have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hyU (hχU h))
        show ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤ 0
        simp [h0]
    refine lt_of_le_of_lt ?_ hFU
    rw [hX₂def, ← lintegral_indicator hUo.measurableSet]
    exact lintegral_mono hχF
  have hsplit : ∫⁻ y, G.D (fun y => σ y) y ∂μ ≤
      (D.m : ℝ≥0∞) * G.A * (2 * G.A * X₁ + 2 * G.A * X₂) := by
    refine (G.lintegral_le_sum_small _).trans ?_
    calc ∑ i, ∫⁻ y in G.small i, G.D (fun y => σ y) y ∂μ
        ≤ ∑ _i : Fin D.m, G.A * (2 * G.A * X₁ + 2 * G.A * X₂) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (G.lintegral_small_le i _ (hσcoef i)).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
            ball_subset_ball (G.r_lt_R i).le
          have hWm : AEMeasurable (G.W i) (volume.restrict (ball (G.center i) (G.r i))) :=
            (G.aemeasurable_W i).mono_measure (Measure.restrict_mono hrR le_rfl)
          have hm2 : AEMeasurable (fun z => 2 * (ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2) *
              G.W i z)) (volume.restrict (ball (G.center i) (G.r i))) :=
            ((ENNReal.measurable_ofReal.comp_aemeasurable
              (((hv₀c i).aestronglyMeasurable measurableSet_ball).norm.aemeasurable.pow_const
                2)).mul hWm).const_mul _
          have hdc : ContinuousOn (G.locCoef i (fun y => v₀ y - σ y))
              (ball (G.center i) (G.r i)) := by
            rw [G.locCoef_sub]; exact (hv₀c i).sub (hσcoef i)
          calc ∫⁻ z in ball (G.center i) (G.r i),
                ENNReal.ofReal (‖G.locCoef i (fun y => σ y) z‖ ^ 2) * G.W i z
              ≤ ∫⁻ z in ball (G.center i) (G.r i),
                  (2 * (ENNReal.ofReal (‖G.locCoef i (fun y => v₀ y - σ y) z‖ ^ 2) * G.W i z) +
                    2 * (ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2) * G.W i z)) := by
                refine lintegral_mono fun z => ?_
                have h1 := norm_sq_le_two_mul (G.locCoef i v₀ z) (G.locCoef i (fun y => σ y) z)
                have e1 : G.locCoef i (fun y => v₀ y - σ y) z =
                    G.locCoef i v₀ z - G.locCoef i (fun y => σ y) z := by rw [G.locCoef_sub]
                rw [← e1] at h1
                have h2 : ENNReal.ofReal (‖G.locCoef i (fun y => σ y) z‖ ^ 2) ≤
                    2 * ENNReal.ofReal (‖G.locCoef i (fun y => v₀ y - σ y) z‖ ^ 2) +
                      2 * ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2) := by
                  have h3 := ENNReal.ofReal_le_ofReal h1
                  rw [ENNReal.ofReal_add (by positivity) (by positivity),
                    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
                    ENNReal.ofReal_ofNat] at h3
                  exact h3
                calc ENNReal.ofReal (‖G.locCoef i (fun y => σ y) z‖ ^ 2) * G.W i z
                    ≤ (2 * ENNReal.ofReal (‖G.locCoef i (fun y => v₀ y - σ y) z‖ ^ 2) +
                      2 * ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2)) * G.W i z :=
                      mul_le_mul_of_nonneg_right h2 zero_le
                  _ = _ := by ring
            _ = 2 * (∫⁻ z in ball (G.center i) (G.r i),
                  ENNReal.ofReal (‖G.locCoef i (fun y => v₀ y - σ y) z‖ ^ 2) * G.W i z) +
                  2 * ∫⁻ z in ball (G.center i) (G.r i),
                    ENNReal.ofReal (‖G.locCoef i v₀ z‖ ^ 2) * G.W i z := by
                rw [lintegral_add_right' _ hm2, lintegral_const_mul' _ _ (by norm_num),
                  lintegral_const_mul' _ _ (by norm_num)]
            _ ≤ 2 * (G.A * ∫⁻ y in G.small i, G.D (fun y => v₀ y - σ y) y ∂μ) +
                  2 * (G.A * ∫⁻ y in G.small i, G.D v₀ y ∂μ) := by
                gcongr
                · exact G.lintegral_ball_r_le_small i _ hdc
                · exact G.lintegral_ball_r_le_small i _ (hv₀c i)
            _ ≤ 2 * (G.A * X₁) + 2 * (G.A * X₂) := by
                gcongr
                · exact setLIntegral_le_lintegral _ _
                · exact setLIntegral_le_lintegral _ _
            _ = 2 * G.A * X₁ + 2 * G.A * X₂ := by ring
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hσgood : ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ < ⊤ := by
    refine lt_of_le_of_lt hsplit ?_
    have hA : G.A ≠ ⊤ := G.A_ne_top
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
      (lt_top_iff_ne_top.mpr hA)) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hA)) hX₁
    · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hA)) hX₂
  -- step 8: the local Skoda step near `x`
  have hballr : ∀ z ∈ ball p r₁, z ∈ closedBall p (4 * r₁) := fun z hz =>
    closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz)
  set uc : ComplexModel n → ℂ := fun z => G.locCoef a F z - G.locCoef a (fun y => σ y) z with huc
  have hucd : DifferentiableOn ℂ uc (ball p r₁) :=
    (hFcoef.mono (ball_subset_ball (by linarith))).sub
      ((hσcoefd a).mono fun z hz => hcR z (hballr z hz))
  set Ψ : ComplexModel n → EReal := fun z => D.psiW k φ a z +
    ((D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2 : ℝ) : EReal) with hΨdef
  have hΨ : PlurisubharmonicOn Ψ (ball p (2 * r₁)) :=
    ((D.psiW_psh hL hT hk hφ a).mono fun z hz =>
      hcR z (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))).add
      (plurisubharmonicOn_mul_normSq D.lam_pos.le _ _)
  have hΨW : ∀ z, multiplierWeight 1 (Ψ z) = G.W a z := fun z => rfl
  -- the Skoda input is bounded by the corrected energy
  set fI : ComplexModel n → ℝ≥0∞ := fun z => ENNReal.ofReal (‖uc z‖ ^ 2) *
    multiplierWeight ((n : ℝ) + 2) (logNormSq (z - p)) * multiplierWeight 1 (Ψ z) with hfI
  have hballrR : ball p r₁ ⊆ ball (G.center a) (G.R a) := fun z hz => hcR z (hballr z hz)
  have hfIm : AEMeasurable ((ball p r₁).indicator fI) (volume.restrict (ball (G.center a) (G.R a))) := by
    refine (aemeasurable_indicator_iff measurableSet_ball).mpr ?_
    rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hballrR]
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖uc z‖ ^ 2)) (volume.restrict (ball p r₁)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hucd.continuousOn.aestronglyMeasurable measurableSet_ball).norm.aemeasurable.pow_const 2)
    have h2 : AEMeasurable (fun z => multiplierWeight ((n : ℝ) + 2) (logNormSq (z - p)))
        (volume.restrict (ball p r₁)) :=
      DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
        ((continuous_logNormSq.comp (continuous_id.sub continuous_const)).upperSemicontinuous
          |>.upperSemicontinuousOn _) (by positivity)
    have h3 : AEMeasurable (fun z => multiplierWeight 1 (Ψ z)) (volume.restrict (ball p r₁)) :=
      ((G.aemeasurable_W a).mono_measure (Measure.restrict_mono hballrR le_rfl)).congr
        (Eventually.of_forall fun z => (hΨW z).symm)
    exact (h1.mul h2).mul h3
  have hI : ∫⁻ z in ball p r₁, ENNReal.ofReal (‖uc z‖ ^ 2) *
      multiplierWeight ((n : ℝ) + 2) (logNormSq (z - p)) * multiplierWeight 1 (Ψ z) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top G.A_ne_top hσ.ne) ?_
    calc ∫⁻ z in ball p r₁, fI z
        = ∫⁻ z in ball (G.center a) (G.R a), (ball p r₁).indicator fI z := by
          rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
            inter_eq_left.mpr hballrR]
      _ ≤ G.A * ∫⁻ y in G.region a, (ball p r₁).indicator fI (G.chart a y) ∂μ :=
          G.lintegral_ball_le_region a _ hfIm
      _ ≤ G.A * ∫⁻ y, ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y - σ y‖ ^ 2) *
            multiplierWeight (k : ℝ) (poleWeight φ ψ k y) ∂μ := by
          refine mul_le_mul_of_nonneg_left ((setLIntegral_mono' (G.isOpen_region a).measurableSet
            fun y hy => ?_).trans (setLIntegral_le_lintegral _ _)) zero_le
          have hy1 : y ∈ c.val.source := hy.1
          have hy2 : c.val y ∈ ball (ctr (n := n) (D.pt a)) (D.R a) := hy.2
          show (ball p r₁).indicator fI (c.val y) ≤ _
          by_cases hyr : c.val y ∈ ball p r₁
          · rw [indicator_of_mem hyr]
            have hχy : χ y = 1 := hχone y hy1 hyr
            have hcoef : G.coef a y (((χ y : ℝ) : ℂ) • F y - σ y) = uc (c.val y) := by
              have hsy : c.val.symm (c.val y) = y := c.val.left_inv hy1
              show G.coef a y _ = G.coef a ((G.chart a).symm (c.val y)) (F ((G.chart a).symm (c.val y)))
                - G.coef a ((G.chart a).symm (c.val y)) (σ ((G.chart a).symm (c.val y)))
              have hsy' : (G.chart a).symm (c.val y) = y := hsy
              rw [hsy', hχy, Complex.ofReal_one, one_smul, map_sub]
            have hdens := G.density_eq a y (((χ y : ℝ) : ℂ) • F y - σ y) hy1 hy2
            rw [hcoef] at hdens
            have hWy : ballWeight (G.Ψ a) G.lam (G.center a) (G.chart a y) = G.W a (c.val y) := rfl
            rw [hWy] at hdens
            have hψy := hψpole y hy1 (ball_subset_ball (by linarith) hyr)
            by_cases hyp : c.val y = p
            · have hbot : ψ y = ⊥ := by
                rw [hψy, hyp, sub_self, logNormSq_zero, EReal.coe_mul_bot_of_pos (by positivity)]
              rw [multiplierWeight_poleWeight_bot hk0 hbot]
              by_cases hu0 : ‖((χ y : ℝ) : ℂ) • F y - σ y‖ = 0
              · have : uc (c.val y) = 0 := by
                  rw [← hcoef, norm_eq_zero.mp hu0, map_zero]
                simp [hfI, this]
              · rw [ENNReal.mul_top (by
                  rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)]
                exact le_top
            · set t := ‖c.val y - p‖ ^ 2 with ht
              have htpos : 0 < t := by
                have := norm_pos_iff.mpr (sub_ne_zero.mpr hyp); positivity
              have hψy' : ψ y = ((((n : ℝ) + 2) * Real.log t : ℝ) : EReal) := by
                rw [hψy, logNormSq_of_ne_zero (sub_ne_zero.mpr hyp), ← EReal.coe_mul]
              rw [multiplierWeight_poleWeight_coe hk0 (hφtop y) hψy', ← mul_assoc, hdens]
              have hlog : multiplierWeight ((n : ℝ) + 2) (logNormSq (c.val y - p)) =
                  ENNReal.ofReal (Real.exp (-(((n : ℝ) + 2) * Real.log t))) := by
                rw [logNormSq_of_ne_zero (sub_ne_zero.mpr hyp), multiplierWeight_coe]
              show ENNReal.ofReal (‖uc (c.val y)‖ ^ 2) *
                  multiplierWeight ((n : ℝ) + 2) (logNormSq (c.val y - p)) *
                    multiplierWeight 1 (Ψ (c.val y)) ≤ _
              rw [hlog, hΨW]
              exact le_of_eq (by ring)
          · rw [indicator_of_notMem hyr]; exact zero_le
  -- the division
  obtain ⟨U', hU'o, hpU', hU'r, h, hhd, hid, hhint⟩ :=
    exists_centred_division hn hr₁ (by linarith : r₁ < 2 * r₁) hΨ hucd hI
  -- the frame norm of `E` is bounded below near `p`
  have hcl4 : ∀ z ∈ closedBall p r₁, z ∈ closedBall p (4 * r₁) := fun z hz =>
    closedBall_subset_closedBall (by linarith) hz
  set Kr : Set X := c.val.symm '' closedBall p r₁ with hKr
  have hKrc : IsCompact Kr := (isCompact_closedBall p _).image_of_continuousOn
    (c.val.continuousOn_symm.mono fun z hz => hct z (hcl4 z hz))
  have hKrE : Kr ⊆ E.val.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    have hzt := hct z (hcl4 z hz)
    exact D.mem_frameE_baseSet (c.val.map_target hzt)
      (by rw [c.val.right_inv hzt]; exact hcR z (hcl4 z hz))
  obtain ⟨mE, hmE0, hmE⟩ : ∃ mE : ℝ, 0 < mE ∧ ∀ y ∈ Kr, mE ≤ ‖E.val.symm y 1‖ := by
    have hne : Kr.Nonempty := ⟨x, p, mem_closedBall_self hr₁.le, c.val.left_inv hxa⟩
    obtain ⟨y₀, hy₀, hmin⟩ := hKrc.exists_isMinOn hne
      ((frameNorm_continuousOn (twistedPower L T k).Fiber E.val).mono hKrE)
    exact ⟨frameNorm (twistedPower L T k).Fiber E.val y₀,
      frameNorm_pos (twistedPower L T k).Fiber E.val (hKrE hy₀), fun y hy => hmin hy⟩
  have hU'ball : ∀ z ∈ U', z ∈ ball p r₁ := fun z hz => hU'r hz
  have hU'K : ∀ z ∈ U', c.val.symm z ∈ Kr := fun z hz =>
    ⟨z, ball_subset_closedBall (hU'ball z hz), rfl⟩
  -- membership of the quotients `hᵢ ∘ z_a` in `𝓘(kφ)_x`
  have hhmem : ∀ i, (multiplierIdeal (n := n) (k : ℝ) φ).mem x (fun y => h i (c.val y)) := by
    intro i
    refine ⟨holomorphicAt_comp_chart c hU'o (hhd i) hxa hpU', ?_⟩
    refine ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      (g := fun y => h i (c.val y)) (complexChartAt (n := n) x)
      c (mem_complexChartAt_source x) hxa (huscφ _ _) hk0'.ne' ?_
    have hrt : ∀ z ∈ U', c.val (c.val.symm z) = z := fun z hz =>
      c.val.right_inv (hct z (hballr z (hU'ball z hz)))
    have hN : ∀ z ∈ U', 0 < ‖E.val.symm (c.val.symm z) 1‖ := fun z hz =>
      frameNorm_pos (twistedPower L T k).Fiber E.val (hKrE (hU'K z hz))
    have hiden : ∀ z ∈ U', multiplierDensity (chartFunction φ c) (k : ℝ)
        (fun z => h i (c.val (c.val.symm z))) z = ENNReal.ofReal (‖h i z‖ ^ 2) *
          (ENNReal.ofReal ((‖E.val.symm (c.val.symm z) 1‖ ^ 2)⁻¹) * G.W a z) := by
      intro z hz
      have hz4 : z ∈ closedBall p (4 * r₁) := hballr z (hU'ball z hz)
      have hW := W_eq_frameNorm D hL hT hk hφ a (hcR z hz4)
      rw [← hE, ← hc] at hW
      have hcancel : ENNReal.ofReal ((‖E.val.symm (c.val.symm z) 1‖ ^ 2)⁻¹) * G.W a z =
          multiplierWeight (k : ℝ) (φ (c.val.symm z)) := by
        rw [hW, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _)),
          inv_mul_cancel₀ (pow_ne_zero 2 (hN z hz).ne'), ENNReal.ofReal_one, one_mul]
      rw [hcancel]
      simp only [multiplierDensity, chartFunction, hrt z hz]
    refine ⟨hk0', U', hU'o, hpU', (hhd i).congr fun z hz => by simp only [hrt z hz], ?_, ?_⟩
    · have hc1 : ContinuousOn (fun z => ‖E.val.symm (c.val.symm z) 1‖) U' :=
        ((frameNorm_continuousOn (twistedPower L T k).Fiber E.val).comp
          (c.val.continuousOn_symm.mono fun z hz => hct z (hballr z (hU'ball z hz)))
          fun z hz => hKrE (hU'K z hz))
      have hc2 : ContinuousOn (fun z => ENNReal.ofReal ((‖E.val.symm (c.val.symm z) 1‖ ^ 2)⁻¹)) U' :=
        ENNReal.continuous_ofReal.comp_continuousOn
          ((hc1.pow 2).inv₀ fun z hz => pow_ne_zero 2 (hN z hz).ne')
      have hm1 : AEMeasurable (fun z => ENNReal.ofReal (‖h i z‖ ^ 2)) (volume.restrict U') :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          (((hhd i).continuousOn.aestronglyMeasurable hU'o.measurableSet).norm.aemeasurable.pow_const 2)
      have hm3 : AEMeasurable (G.W a) (volume.restrict U') :=
        (G.aemeasurable_W a).mono_measure (Measure.restrict_mono (fun z hz =>
          hballrR (hU'ball z hz)) le_rfl)
      refine (hm1.mul ((hc2.aemeasurable hU'o.measurableSet).mul hm3)).congr ?_
      filter_upwards [ae_restrict_mem hU'o.measurableSet] with z hz
      exact (hiden z hz).symm
    · calc ∫⁻ z in U', multiplierDensity (chartFunction φ c) (k : ℝ)
            (fun z => h i (c.val (c.val.symm z))) z
          = ∫⁻ z in U', ENNReal.ofReal (‖h i z‖ ^ 2) *
              (ENNReal.ofReal ((‖E.val.symm (c.val.symm z) 1‖ ^ 2)⁻¹) * G.W a z) :=
            setLIntegral_congr_fun hU'o.measurableSet hiden
        _ ≤ ∫⁻ z in U', ENNReal.ofReal ((mE ^ 2)⁻¹) *
              (ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight 1 (Ψ z)) := by
            refine setLIntegral_mono' hU'o.measurableSet fun z hz => ?_
            rw [hΨW]
            calc ENNReal.ofReal (‖h i z‖ ^ 2) *
                  (ENNReal.ofReal ((‖E.val.symm (c.val.symm z) 1‖ ^ 2)⁻¹) * G.W a z)
                = ENNReal.ofReal ((‖E.val.symm (c.val.symm z) 1‖ ^ 2)⁻¹) *
                    (ENNReal.ofReal (‖h i z‖ ^ 2) * G.W a z) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
                  (inv_anti₀ (by positivity) (pow_le_pow_left₀ hmE0.le (hmE _ (hU'K z hz)) 2)))
                  zero_le
        _ = ENNReal.ofReal ((mE ^ 2)⁻¹) *
              ∫⁻ z in U', ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight 1 (Ψ z) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr (hhint i))
  -- the unit `t` and the identity near `x`
  have ht : HolomorphicAt n (fun y => E.val.continuousLinearMapAt ℂ y (e.val.symm y 1)) x := by
    have hsec := isHolomorphicSectionOn_smul_frame (n := n) (V := (twistedPower L T k).Fiber)
      e.val (g := fun _ => (1 : ℂ)) subset_rfl (fun y _ => mdifferentiableAt_const)
    refine (holomorphicAt_coef_of_mdifferentiableOn E.val e.val.open_baseSet hsec hxe hxE).congr
      (Eventually.of_forall fun y => ?_)
    simp only [one_smul]
  refine ⟨σ, hσgood, fun y => E.val.continuousLinearMapAt ℂ y (e.val.symm y 1),
    fun i y => h i (c.val y), ht, transition_ne_zero e.val E.val hxe hxE, hhmem, ?_⟩
  have hO : IsOpen (c.val.source ∩ c.val ⁻¹' U') := c.val.isOpen_inter_preimage hU'o
  filter_upwards [hO.mem_nhds ⟨hxa, hpU'⟩] with y hy
  have hz := hid (c.val y) hy.2
  have hyU : y ∈ Uset := ⟨hy.1, ball_subset_ball (by linarith) (hU'ball _ hy.2)⟩
  have hye : y ∈ e.val.baseSet := (hUmem y hyU).2
  have hsy : (G.chart a).symm (c.val y) = y := c.val.left_inv hy.1
  have h1 : uc (c.val y) = E.val.continuousLinearMapAt ℂ y (F y) -
      E.val.continuousLinearMapAt ℂ y (σ y) := by
    show G.coef a ((G.chart a).symm (c.val y)) (F ((G.chart a).symm (c.val y))) -
      G.coef a ((G.chart a).symm (c.val y)) (σ ((G.chart a).symm (c.val y))) = _
    rw [hsy]; rfl
  have h2 : E.val.continuousLinearMapAt ℂ y (F y) =
      g y * E.val.continuousLinearMapAt ℂ y (e.val.symm y 1) := by
    show E.val.continuousLinearMapAt ℂ y (g y • e.val.symm y 1) = _
    rw [map_smul, smul_eq_mul]
  have h3 := coef_eq_coef_mul_transition e.val E.val hye (σ y)
  rw [h1, h2, h3] at hz
  rw [← hz]
  ring

end Weight

/-! ### Siu's uniform global generation -/

/-- **Siu's uniform global generation** (blueprint `claude-gagamult:siu-generation`).  On a compact
complex manifold `X` with a Kähler background `ω` and a smooth positive volume `μ`, for holomorphic
line bundles `L, T` with smooth metrics, `θ = c₁(L, h_L)` and `δ > 0`, there is `k₀` such that for
every `k ≥ k₀`, every `φ ∈ PSH(X, θ - δω)`, every `x ∈ X` and every atlas frame `e` of
`L^k ⊗ T` at `x`, the stalk `𝓘(kφ)_x` is generated by the `e`-coefficients of the global
holomorphic sections `s` of `L^k ⊗ T` with `∫_X |s|² e^{-kφ} dμ < ∞`. -/
def SiuGlobalGenerationStatement (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] :
    Prop :=
  CompactSpace X →
  ∀ (ωb : KahlerBackground n X) (μ : Measure X), IsSmoothPositiveVolume (n := n) μ →
  ∀ (L T : HermitianHolomorphicLineBundle.{0, 0} n X),
    IsSourceSmoothHermitianMetric L → IsSourceSmoothHermitianMetric T →
  ∀ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θ →
  ∀ δ : ℝ, 0 < δ →
  ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
  ∀ φ : X → EReal, IsThetaPshPotential (θ - δ • ωb.form).val φ →
  ∀ (x : X) (e : AtlasFrame (twistedPower L T k)), x ∈ e.val.baseSet →
  ∀ g : X → ℂ, (multiplierIdeal (n := n) (k : ℝ) φ).mem x g →
    IsInSpanAt (n := n) (fun h => ∃ s : twistedSections L T k,
      ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ < ⊤ ∧
      h = fun y => e.val.continuousLinearMapAt ℂ y (s y)) x g

/-- **Siu's uniform global generation in positive dimension.** -/
theorem siuGlobalGeneration_pos (hn : 0 < n) : SiuGlobalGenerationStatement n X := by
  intro hX ωb μ hμ L T hL hT θ hθ δ hδ
  obtain ⟨D⟩ := exists_coverData ωb hμ hL hT hθ (half_pos hδ)
  obtain ⟨k₁, hk₁⟩ := D.exists_goodPower (half_pos hδ)
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_poleB
  obtain ⟨k₂, hk₂⟩ := globalCutoffCorrection hX ωb μ hμ L T hL hT θ hθ (δ / 2) (half_pos hδ)
  set B' : ℝ := ((n : ℝ) + 2) * B with hB'
  refine ⟨max (max k₁ k₂) (⌈2 * B' / δ⌉₊ + 1), fun k hk φ hφ x e hxe g hg => ?_⟩
  have hkD : D.GoodPower k := hk₁ k (le_of_max_le_left (le_of_max_le_left hk))
  have hk2 : k₂ ≤ k := le_of_max_le_right (le_of_max_le_left hk)
  have hk0 : 0 < k := hkD.1
  have hkB : 2 * B' ≤ k * δ := by
    have h1 : ⌈2 * B' / δ⌉₊ + 1 ≤ k := le_of_max_le_right hk
    have h2 : 2 * B' / δ ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans h1)
    rw [div_le_iff₀ hδ] at h2; linarith
  have hφ2 : IsThetaPshPotential (θ - (δ / 2) • ωb.form).val φ := by
    have h := Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive hφ
      (Pending.KahlerDomination.isSemipositive_smul ωb.isSemipositive (half_pos hδ).le)
    have hform : θ - δ • ωb.form + (δ / 2) • ωb.form = θ - (δ / 2) • ωb.form := by module
    rwa [hform] at h
  have := e.property
  set S : (X → ℂ) → Prop := fun h => ∃ s : twistedSections L T k,
    ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ < ⊤ ∧
      h = fun y => e.val.continuousLinearMapAt ℂ y (s y) with hS
  suffices hI : stalkIdeal (multiplierIdeal (n := n) (k : ℝ) φ) x ≤ spanGerms S x from
    isInSpanAt_of_mk_mem_spanGerms hg.1 (hI (mk_mem_stalkIdeal hg.1 hg))
  apply le_of_le_sup_maximalIdeal_smul
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨g', hg', hmem, rfl⟩
  -- the chart and the pole
  obtain ⟨a, hxa, hxr⟩ := (D.toGluingSystem hL hT hkD hφ2).cover x
  set c := D.chartA a with hc
  have hxa' : x ∈ c.val.source := hxa
  set p := c.val x with hp
  have hxr' : p ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4) := hxr
  have hpc : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4) := ball_subset_closedBall hxr'
  have hP := D.poleRadii a hpc
  obtain ⟨mω, hmω, hBm⟩ := hBa a
  have hpsh := thetaPlurisubharmonic_poleFun ωb hP (m := mω)
    (fun w hw v => hmω w (D.closedBall_subset_of_mem hpc (by linarith [D.R_pos a]) hw) v)
    hB0.le hBm
  set ψ : X → EReal := fun y => (((n : ℝ) + 2 : ℝ) : EReal) *
    poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y with hψdef
  have hψpsh : ThetaPlurisubharmonic (B' • ωb.form).val ψ := by
    have := Pending.GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
      (c := (n : ℝ) + 2) (by positivity) hpsh
    rwa [smul_smul] at this
  have hψ0 : ∀ y, ψ y ≤ 0 := fun y => coe_mul_nonpos (by positivity) (poleFun_le hP y)
  have hinj : ∀ y ∈ c.val.source, c.val y = p → y = x := fun y hy h => c.val.injOn hy hxa' h
  have hψne : ∀ y, y ≠ x → ψ y ≠ ⊥ := by
    intro y hyx
    have hP0 : poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y ≠ ⊥ :=
      poleFun_ne_bot fun hy h => hyx (hinj y hy h)
    show (((n : ℝ) + 2 : ℝ) : EReal) * _ ≠ ⊥
    induction h : poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y using EReal.rec with
    | bot => exact absurd h hP0
    | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    | top => rw [EReal.coe_mul_top_of_pos (by positivity)]; exact top_ne_bot
  have hφ' := isThetaPshPotential_poleWeight hn ωb (θ := θ) hk0 hkB hφ hψpsh hψne
  have hRa := D.R_pos a
  have hrR := D.poleR_le a
  have hr0 := D.poleR_pos a
  have hεR : ball p (D.poleR a) ⊆ ball (ctr (n := n) (D.pt a)) (D.R a / 2) := by
    intro z hz
    rw [mem_ball] at hz hxr' ⊢
    linarith [dist_triangle z p (ctr (n := n) (D.pt a))]
  have hψpole : ∀ y ∈ c.val.source, c.val y ∈ ball p (D.poleR a) →
      ψ y = ((((n : ℝ) + 2 : ℝ)) : EReal) * logNormSq (c.val y - p) := by
    intro y hy hyε
    have hdist : dist (c.val y) p < D.poleR a := hyε
    show (((n : ℝ) + 2 : ℝ) : EReal) * poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y = _
    rw [poleFun_of_mem hy (by rw [mem_ball]; linarith), poleChart_eq_logNormSq
      (by rw [← dist_eq_norm]; linarith)]
  have hψlow : ∀ ρ : ℝ, 0 < ρ → ρ ≤ D.poleR a → ∀ y, (y ∈ c.val.source →
      ρ ≤ ‖c.val y - p‖) → (((((n : ℝ) + 2) * Real.log (ρ ^ 2)) : ℝ) : EReal) ≤ ψ y :=
    fun ρ hρ hρr y hy => coe_mul_le_coe_mul (by positivity) (log_le_poleFun hρ hρr hy)
  have hcorr := hk₂ k hk2 (poleWeight φ ψ k) hφ'
  obtain ⟨s, hs, t, h, ht, ht0, hh, hid⟩ := exists_section_mod_maximal D hL hT hkD hφ2 hn hcorr
    a hxa' hr0 hεR hψ0 hψpole hψlow e hxe hmem
  -- the germ algebra
  have hsx : HolomorphicAt n (fun y => e.val.continuousLinearMapAt ℂ y (s y)) x :=
    holomorphicAt_coef_of_contMDiff e.val s.contMDiff hxe
  have hci : ∀ i, HolomorphicAt n (fun y => centredCoords p i (c.val y)) x :=
    fun i => holomorphicAt_chartCoord c hxa' i
  have hhi : ∀ i, HolomorphicAt n (h i) x := fun i => (hh i).1
  have hsum : HolomorphicAt n (fun y => ∑ i, centredCoords p i (c.val y) * h i y) x :=
    HolomorphicAt.sum _ fun i _ => (hci i).mul (hhi i)
  have hu : IsUnit (NativeHolGerm.mk t ht) := by
    rw [NativeHolGerm.isUnit_iff_eval_ne_zero, NativeHolGerm.eval_mk]; exact ht0
  have hlhs : HolomorphicAt n (fun y => t y * (g' y - e.val.continuousLinearMapAt ℂ y (s y))) x :=
    ht.mul (hg'.add (hsx.mono fun y hy => hy.neg) |>.congr (Eventually.of_forall fun y => by
      simp [sub_eq_add_neg]))
  have hgerm : NativeHolGerm.mk t ht * (NativeHolGerm.mk g' hg' - NativeHolGerm.mk _ hsx) =
      ∑ i, NativeHolGerm.mk _ (hci i) * NativeHolGerm.mk (h i) (hhi i) := by
    rw [← mk_sum_mul _ _ hci hhi hsum]
    have hl : NativeHolGerm.mk t ht * (NativeHolGerm.mk g' hg' - NativeHolGerm.mk _ hsx) =
        NativeHolGerm.mk _ hlhs := rfl
    rw [hl]
    exact NativeHolGerm.mk_eq_mk_iff.mpr hid
  have hrepr : NativeHolGerm.mk g' hg' = NativeHolGerm.mk _ hsx +
      ↑hu.unit⁻¹ * ∑ i, NativeHolGerm.mk _ (hci i) * NativeHolGerm.mk (h i) (hhi i) := by
    rw [← hgerm, ← mul_assoc, IsUnit.val_inv_mul, one_mul, add_sub_cancel]
  rw [hrepr]
  refine Submodule.add_mem_sup (mk_mem_spanGerms hsx ⟨s, hs, rfl⟩) ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have heq : ↑hu.unit⁻¹ * (NativeHolGerm.mk _ (hci i) * NativeHolGerm.mk (h i) (hhi i)) =
      NativeHolGerm.mk _ (hci i) • (↑hu.unit⁻¹ * NativeHolGerm.mk (h i) (hhi i)) := by
    rw [smul_eq_mul]; ring
  rw [heq]
  exact Submodule.smul_mem_smul (mk_mem_maximalIdeal (hci i) (centredCoords_self p i))
    (Ideal.mul_mem_left _ _ (mk_mem_stalkIdeal (hhi i) (hh i)))

end SGPT.NAPotential.GAGAMult

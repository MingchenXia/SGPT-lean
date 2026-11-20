import SGPT.PSH.SiuGenMeasure
import SGPT.NAPotential.SiuGenStatement
import SGPT.NAPotential.GAGAMultSiu

/-!
# Siu's step on `X × Δ`: a section congruent to a germ modulo `𝔪 𝓘(mΦ)`

Blueprint `claude-siu-gen.tex`, node `claude-siu-gen:siu-step`.

Let `X` be compact with a smooth positive volume `μ`, `D` cover data (`θ_G` Kähler), `L` with a
smooth metric, `θ = c₁(L, h_L)`, `Φ ∈ PSH(X × Δ, p₁^*θ)`, `m > 0`, and `E` a line bundle on `X` for
which the `L²` correction of `p₁^*E` with the weights `e^{-(mΦ + Ψ)}`,
`Ψ ∈ PSH(X × Δ, p₁^*((n+3) B θ_G))`, is available (`HasProdCorrection`; this is the conclusion of
`prodCutoffCorrectionGen` for `E = L^m ⊗ G^K`).  Then for every point `q₀`, every frame `e` of `E` at
`q₀.1` and every germ `g ∈ 𝓘(mΦ)_{q₀}` there are a global section `S` of `p₁^*E ⊗ 𝓘(mΦ)` and germs
`hᵢ ∈ 𝓘(mΦ)_{q₀}` with `g - e(S) = ∑ᵢ (wᵢ - wᵢ(q₀)) hᵢ` near `q₀` (`w` a product chart)
(`exists_section_mod_maximal_prod`).

Proof: the weight `Ψ = poleP` has an isolated pole of order `n + 3` at `q₀`; the cut-off `χ g e`
is corrected to `S` with `∫ |χ g e - S|² e^{-(mΦ + Ψ)} < ∞`; near `q₀` this gives
`∫ |g - e(S)|² |w - w₀|^{-2(n+3)} e^{-mΦ} < ∞`, and the local Skoda division in dimension `n + 1`
(`GAGAMult.exists_centred_division`) gives the `hᵢ`.  The section `S` lies in `𝓘(mΦ)` at every
point because `∫ |S|² e^{-mΦ} < ∞` locally (`mem_multiplierIdeal_of_chartBall`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.SiuGen

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga SGPT.NAPotential.GAGAMult

/-- A chart-smooth function is continuous. -/
theorem chartSmooth_continuous {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] {h : M → ℝ}
    (hh : ChartSmooth (n := N) h) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro x
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have h1 : ContinuousAt (fun z => h (e.val.symm z)) (e.val x) :=
    ((hh e).continuousOn).continuousAt (e.val.open_target.mem_nhds (e.val.map_source hx))
  have h2 := h1.comp (e.val.continuousAt hx)
  refine h2.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.val.left_inv hy]

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- The `L²` correction of `p₁^*E` on `X × Δ` for the weights `e^{-(mΦ + Ψ)}`,
`Ψ ∈ PSH(X × Δ, p₁^*σ)` (the conclusion of `prodCutoffCorrectionGen` for a fixed `K`). -/
def HasProdCorrection (μ : Measure X) (E : HermitianHolomorphicLineBundle.{0, 0} n X) (m : ℕ)
    (Φ : X × unitDisc → EReal) (σ : ClosedRealOneOneForm n X) : Prop :=
  ∀ Ψ : X × unitDisc → EReal, ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) σ).val Ψ →
    (∀ q, Ψ q ≠ ⊤) →
    ∀ U : Set (X × unitDisc), IsOpen U →
    ∀ F : (q : X × unitDisc) → E.Fiber q.1, IsHolomorphicProdSectionOn E F U →
    ∀ χ : X × unitDisc → ℝ, ChartSmooth (n := n + 1) χ → tsupport χ ⊆ U →
    ∀ K' : Set (X × unitDisc), IsCompact K' → K' ⊆ U →
      (∀ q ∈ U \ K', ∀ᶠ q' in 𝓝 q, χ q' = χ q) →
      ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q)
        ∂(prodMeasure μ) < ⊤ →
    ∃ S : (q : X × unitDisc) → E.Fiber q.1, IsHolomorphicProdSectionOn E S univ ∧
      ∫⁻ q, ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
        multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) ∂(prodMeasure μ) < ⊤

/-- Bounds of the frame norm on a closed ball of a chart of `X × Δ`. -/
theorem exists_frameNorm_bounds {E : HermitianHolomorphicLineBundle.{0, 0} n X} (e : AtlasFrame E)
    (d : ComplexChart (n + 1) (X × unitDisc)) {c : ComplexModel (n + 1)} {r : ℝ} (hr : 0 ≤ r)
    (hcl : closedBall c r ⊆ d.val.target ∩ d.val.symm ⁻¹' (Prod.fst ⁻¹' e.val.baseSet)) :
    ∃ m₀ M₀ : ℝ, 0 < m₀ ∧ ∀ z ∈ closedBall c r,
      m₀ ≤ ‖e.val.symm (d.val.symm z).1 1‖ ∧ ‖e.val.symm (d.val.symm z).1 1‖ ≤ M₀ := by
  have := e.property
  have hKc : IsCompact (closedBall c r) := isCompact_closedBall c r
  have hne : (closedBall c r).Nonempty := ⟨c, mem_closedBall_self hr⟩
  have hfc : ContinuousOn (fun z => ‖e.val.symm (d.val.symm z).1 1‖) (closedBall c r) :=
    (frameNorm_continuousOn E.Fiber e.val).comp
      (continuous_fst.comp_continuousOn (d.val.continuousOn_symm.mono fun z hz => (hcl hz).1))
      fun z hz => (hcl hz).2
  obtain ⟨z₂, hz₂, hmin₂⟩ := hKc.exists_isMinOn hne hfc
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn hfc
  refine ⟨‖e.val.symm (d.val.symm z₂).1 1‖, M₀, frameNorm_pos E.Fiber e.val (hcl hz₂).2,
    fun z hz => ⟨hmin₂ hz, ?_⟩⟩
  have := hM₀ z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
  exact this

set_option maxHeartbeats 1000000 in
/-- **Siu's step on `X × Δ`** (`claude-siu-gen:siu-step`).  For every germ `g ∈ 𝓘(mΦ)_{q₀}` and frame
`e` of `E` at `q₀.1` there are a global section `S` of `p₁^*E ⊗ 𝓘(mΦ)` and `hᵢ ∈ 𝓘(mΦ)_{q₀}` with
`g - e(S) = ∑ᵢ (wᵢ - wᵢ(q₀)) hᵢ` near `q₀`, `w` the product chart of index `a`. -/
theorem exists_section_mod_maximal_prod {μ : Measure X} [SFinite μ]
    (hμ : IsSmoothPositiveVolume (n := n) μ)
    {L G : HermitianHolomorphicLineBundle.{0, 0} n X} (D : SiuCover μ L G)
    (hL : IsSourceSmoothHermitianMetric L) {θ θG : ClosedRealOneOneForm n X}
    (hθ : IsOwnFirstChernForm L θ) (hKah : θG.val.IsKahler) {B : ℝ} (hB0 : 0 < B)
    (hBa : ∀ a : Fin D.m, ∃ mω : ℝ,
      (∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
        mω * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v]) ∧
      2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * mω)
    {E : HermitianHolomorphicLineBundle.{0, 0} n X} {m : ℕ} (hm : 0 < m)
    {Φ : X × unitDisc → EReal}
    (hΦ : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
    (hcorr : HasProdCorrection μ E m Φ ((((n : ℝ) + 3) * B) • θG))
    (q₀ : X × unitDisc) (e : AtlasFrame E) (he : q₀.1 ∈ e.val.baseSet) {g : X × unitDisc → ℂ}
    (hg : (multiplierIdeal (n := n + 1) (m : ℝ) Φ).mem q₀ g) :
    ∃ S : (q : X × unitDisc) → E.Fiber q.1,
      IsProdSectionIn E (multiplierIdeal (n := n + 1) (m : ℝ) Φ) S ∧
      ∃ a : Fin D.m, q₀ ∈ (D.chartP a).val.source ∧ ∃ h : Fin (n + 1) → X × unitDisc → ℂ,
        (∀ i, (multiplierIdeal (n := n + 1) (m : ℝ) Φ).mem q₀ (h i)) ∧
        ∀ᶠ q in 𝓝 q₀, g q - e.val.continuousLinearMapAt ℂ q.1 (S q) =
          ∑ i, centredCoords ((D.chartP a).val q₀) i ((D.chartP a).val q) * h i q := by
  classical
  have := e.property
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hΦtop : ∀ q, Φ q ≠ ⊤ := fun q => hΦ.1.quasiPlurisubharmonic.ne_top q
  -- step 0: the chart index and the pole
  obtain ⟨a, ha⟩ : ∃ a, q₀.1 ∈ tsupport (D.χ a) := by
    have hne : ∑ a, D.χ a q₀.1 ≠ 0 := by rw [D.sum_χ q₀.1]; exact one_ne_zero
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨a, subset_tsupport _ ha⟩
  have hxa := D.tsupport_χ a ha
  set C := D.chartP a with hC
  set p := (D.chartX a).val q₀.1 with hp
  set t₀ := q₀.2.val with ht₀
  set w₀ := C.val q₀ with hw₀
  have hw₀' : w₀ = prodL n (p, t₀) := D.chartP_apply a q₀
  have hq₀C : q₀ ∈ C.val.source := by rw [D.chartP_source]; exact ⟨hxa.1, mem_univ _⟩
  have hpR4 : p ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4) := hxa.2
  have hpc : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4) := ball_subset_closedBall hpR4
  have ht₀1 : ‖t₀‖ < 1 := mem_unitDisc.mp q₀.2.property
  obtain ⟨mω, hmω, hBm⟩ := hBa a
  set Ψ : X × unitDisc → EReal := D.poleP a p t₀ with hΨdef
  have hΨpsh := D.thetaPlurisubharmonic_poleP hKah hB0 hmω hBm hpc t₀
  have hΨtop : ∀ q, Ψ q ≠ ⊤ := D.poleP_ne_top hpc ht₀1
  have hRa := D.R_pos a
  have hrP := D.siuPoleR_pos a
  have hrPle := D.siuPoleR_le a
  -- step 1: the integrability of `g` in the chart `C`
  obtain ⟨hgx, hgint⟩ := hg
  have huscΦ : ∀ e₁ e₂ : ComplexChart (n + 1) (X × unitDisc),
      UpperSemicontinuousOn (chartFunction Φ e₁) (ChartWeightedL2.overlapDomain e₁ e₂) :=
    fun e₁ e₂ => (upperSemicontinuousOn_chartFunction_target hΦ.1 e₁).mono fun z hz => hz.1
  have hgc := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) C
    (complexChartAt (n := n + 1) q₀) hq₀C (mem_complexChartAt_source q₀) (huscΦ _ _) hm'.ne' hgint
  obtain ⟨-, U₀, hU₀o, hw₀U₀, hgU₀, -, hU₀int⟩ := hgc
  -- step 2: the radius
  obtain ⟨Vg, hVg, hVgo, hq₀Vg⟩ := eventually_nhds_iff.mp hgx
  set W₀ : Set (ComplexModel (n + 1)) := U₀ ∩ ball w₀ (D.siuPoleR a) ∩
    (C.val.target ∩ C.val.symm ⁻¹' (Vg ∩ Prod.fst ⁻¹' e.val.baseSet)) with hW₀
  have hW₀o : IsOpen W₀ := (hU₀o.inter isOpen_ball).inter
    (C.val.isOpen_inter_preimage_symm (hVgo.inter (e.val.open_baseSet.preimage continuous_fst)))
  have hw₀W₀ : w₀ ∈ W₀ := ⟨⟨hw₀U₀, mem_ball_self hrP⟩, C.val.map_source hq₀C, by
    simp only [mem_preimage, hw₀, C.val.left_inv hq₀C]; exact ⟨hq₀Vg, he⟩⟩
  obtain ⟨ρ₀, hρ₀, hρ₀W⟩ := Metric.isOpen_iff.mp hW₀o w₀ hw₀W₀
  set r₁ : ℝ := min ρ₀ (D.siuPoleR a) / 8 with hr₁def
  have hr₁ : 0 < r₁ := by have := lt_min hρ₀ hrP; positivity
  have h8ρ : 8 * r₁ ≤ ρ₀ := by have := min_le_left ρ₀ (D.siuPoleR a); rw [hr₁def]; linarith
  have h8ε : 8 * r₁ ≤ D.siuPoleR a := by
    have := min_le_right ρ₀ (D.siuPoleR a); rw [hr₁def]; linarith
  have hW4 : ∀ z ∈ closedBall w₀ (4 * r₁), z ∈ W₀ := fun z hz =>
    hρ₀W (by rw [mem_ball]; linarith [mem_closedBall.mp hz])
  have hct : ∀ z ∈ closedBall w₀ (4 * r₁), z ∈ C.val.target := fun z hz => (hW4 z hz).2.1
  have hcVe : ∀ z ∈ closedBall w₀ (4 * r₁),
      C.val.symm z ∈ Vg ∧ (C.val.symm z).1 ∈ e.val.baseSet := fun z hz => (hW4 z hz).2.2
  have hcU₀ : ∀ z ∈ closedBall w₀ (4 * r₁), z ∈ U₀ := fun z hz => (hW4 z hz).1.1
  have hcP : ∀ z ∈ closedBall w₀ (4 * r₁), ‖z - w₀‖ < D.siuPoleR a := fun z hz => by
    have := (hW4 z hz).1.2; rwa [mem_ball, dist_eq_norm] at this
  have hcDomR : ∀ z ∈ closedBall w₀ (4 * r₁), z ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1 := by
    intro z hz
    have hzt := hct z hz
    rw [pChart_target] at hzt
    refine ⟨?_, hzt.2⟩
    have h1 : ‖projX n z - p‖ ≤ ‖z - w₀‖ := by
      have hsq := norm_sub_sq_prodL z w₀
      rw [show projX n w₀ = p by rw [hw₀', projX_prodL],
        show projT n w₀ = t₀ by rw [hw₀', projT_prodL]] at hsq
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
        (by nlinarith [sq_nonneg ‖projT n z - t₀‖])
    have h2 := hcP z hz
    have h3 : ‖p - ctr (n := n) (D.pt a)‖ < D.R a / 4 := by
      have := hpR4; rwa [mem_ball, dist_eq_norm] at this
    rw [mem_ball, dist_eq_norm]
    calc ‖projX n z - ctr (n := n) (D.pt a)‖
        ≤ ‖projX n z - p‖ + ‖p - ctr (n := n) (D.pt a)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < D.R a := by linarith
  -- step 3: the local section `F = g e`
  set Uset : Set (X × unitDisc) := C.val.source ∩ C.val ⁻¹' ball w₀ (4 * r₁) with hUset
  have hUo : IsOpen Uset := C.val.isOpen_inter_preimage isOpen_ball
  have hUmem : ∀ y ∈ Uset, y ∈ Vg ∧ y.1 ∈ e.val.baseSet := by
    intro y hy
    have h := hcVe (C.val y) (ball_subset_closedBall hy.2)
    rwa [C.val.left_inv hy.1] at h
  set F : (q : X × unitDisc) → E.Fiber q.1 := fun q => g q • e.val.symm q.1 1 with hFdef
  have hgHol : ∀ y ∈ Uset, HolomorphicAt (n + 1) g y := fun y hy =>
    eventually_of_mem (hVgo.mem_nhds (hUmem y hy).1) fun y' hy' => hVg y' hy'
  have hF : IsHolomorphicProdSectionOn E F Uset := by
    intro q hq e' hqe'
    have := e'.property
    refine (HolomorphicAt.mul' (hgHol q hq)
      (holomorphicAt_transition_prod e e' (hUmem q hq).2 hqe')).congr
      (Eventually.of_forall fun q' => ?_)
    change g q' * e'.val.continuousLinearMapAt ℂ q'.1 (e.val.symm q'.1 1) =
      e'.val.continuousLinearMapAt ℂ q'.1 (g q' • e.val.symm q'.1 1)
    rw [map_smul, smul_eq_mul]
  have hFcoef : ∀ y : X × unitDisc, y.1 ∈ e.val.baseSet →
      e.val.continuousLinearMapAt ℂ y.1 (F y) = g y := by
    intro y hy
    change e.val.continuousLinearMapAt ℂ y.1 (g y • e.val.symm y.1 1) = g y
    rw [map_smul, trivialization_coef_frame e.val hy, smul_eq_mul, mul_one]
  have hFnorm : ∀ y, ‖F y‖ = ‖g y‖ * ‖e.val.symm y.1 1‖ := fun y => norm_smul _ _
  -- step 4: the cut-off `χ`, `1` on `B(w₀, r₁)`, supported in `B(w₀, 2r₁)`
  set β : ContDiffBump w₀ := ⟨r₁, 2 * r₁, hr₁, by linarith⟩ with hβ
  set χ : X × unitDisc → ℝ := ChartPartition.chartExtend C β with hχdef
  have hβt : tsupport β = closedBall w₀ (2 * r₁) := β.tsupport_eq
  have hcb2 : closedBall w₀ (2 * r₁) ⊆ C.val.target := fun z hz =>
    hct z (closedBall_subset_closedBall (by linarith) hz)
  have hχ : ChartSmooth (n := n + 1) χ := ChartPartition.chartSmooth_chartExtend C β.contDiff
    β.hasCompactSupport.isCompact (by rw [hβt]; exact hcb2)
  have hχU : tsupport χ ⊆ Uset := by
    refine (ChartPartition.support_chartExtend_subset C).trans ?_
    rw [hβt]
    have hcomp : IsCompact (C.val.symm '' closedBall w₀ (2 * r₁)) :=
      (isCompact_closedBall w₀ _).image_of_continuousOn (C.val.continuousOn_symm.mono hcb2)
    rw [hcomp.isClosed.closure_eq]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨C.val.map_target (hcb2 hw), ?_⟩
    rw [mem_preimage, C.val.right_inv (hcb2 hw), mem_ball]
    have := mem_closedBall.mp hw; linarith
  have hχ0 : ∀ y, 0 ≤ χ y := ChartPartition.chartExtend_nonneg fun z => β.nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := ChartPartition.chartExtend_le_one fun z => β.le_one
  have hχone : ∀ y ∈ C.val.source, C.val y ∈ ball w₀ r₁ → χ y = 1 := by
    intro y hy hyr
    rw [hχdef, ChartPartition.chartExtend_of_mem hy]
    exact β.one_of_mem_closedBall (ball_subset_closedBall hyr)
  set A₀ : Set (ComplexModel (n + 1)) := closedBall w₀ (2 * r₁) ∩ {w | r₁ ≤ dist w w₀} with hA₀
  set K' : Set (X × unitDisc) := C.val.symm '' A₀ with hK'def
  have hA₀c : IsCompact A₀ := (isCompact_closedBall w₀ _).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hK' : IsCompact K' :=
    hA₀c.image_of_continuousOn (C.val.continuousOn_symm.mono fun w hw => hcb2 hw.1)
  have hK'U : K' ⊆ Uset := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨C.val.map_target (hcb2 hw.1), ?_⟩
    rw [mem_preimage, C.val.right_inv (hcb2 hw.1), mem_ball]
    have := mem_closedBall.mp hw.1; linarith
  have hK'ann : ∀ y ∈ K', y ∈ C.val.source ∧ r₁ ≤ ‖C.val y - w₀‖ := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨C.val.map_target (hcb2 hw.1), ?_⟩
    rw [C.val.right_inv (hcb2 hw.1), ← dist_eq_norm]; exact hw.2
  have hconst : ∀ y ∈ Uset \ K', ∀ᶠ y' in 𝓝 y, χ y' = χ y := by
    rintro y ⟨⟨hy, -⟩, hyK⟩
    by_cases h1 : dist (C.val y) w₀ < r₁
    · have hO : IsOpen (C.val.source ∩ C.val ⁻¹' ball w₀ r₁) :=
        C.val.isOpen_inter_preimage isOpen_ball
      filter_upwards [hO.mem_nhds ⟨hy, h1⟩] with y' hy'
      rw [hχone y' hy'.1 hy'.2, hχone y hy h1]
    · have h3 : 2 * r₁ < dist (C.val y) w₀ := by
        by_contra hle
        exact hyK ⟨C.val y, ⟨mem_closedBall.mpr (not_lt.mp hle), not_lt.mp h1⟩,
          C.val.left_inv hy⟩
      have hO : IsOpen (C.val.source ∩ C.val ⁻¹' {w | 2 * r₁ < dist w w₀}) :=
        C.val.isOpen_inter_preimage (isOpen_lt continuous_const
          (continuous_id.dist continuous_const))
      have hval : ∀ y' ∈ C.val.source ∩ C.val ⁻¹' {w | 2 * r₁ < dist w w₀}, χ y' = 0 := by
        intro y' hy'
        rw [hχdef, ChartPartition.chartExtend_of_mem hy'.1]
        exact β.zero_of_le_dist (le_of_lt hy'.2)
      filter_upwards [hO.mem_nhds ⟨hy, h3⟩] with y' hy'
      rw [hval y' hy', hval y ⟨hy, h3⟩]
  -- step 5: `∫_U |F|² e^{-mΦ} < ∞`
  obtain ⟨mE, ME, hmE0, hmEb⟩ := exists_frameNorm_bounds e C (by positivity : (0 : ℝ) ≤ 4 * r₁)
    (fun z hz => ⟨hct z hz, (hcVe z hz).2⟩)
  have hball4t : ball w₀ (4 * r₁) ⊆ C.val.target := fun z hz => hct z (ball_subset_closedBall hz)
  have hρc := D.dens_cont a
  have hmapa := D.dens_map a
  have hgcont : ContinuousOn (fun z => g (C.val.symm z)) (ball w₀ (4 * r₁)) :=
    (hgU₀.mono fun z hz => hcU₀ z (ball_subset_closedBall hz)).continuousOn
  have hfrcont : ContinuousOn (fun z => ‖e.val.symm (C.val.symm z).1 1‖) (ball w₀ (4 * r₁)) :=
    (frameNorm_continuousOn E.Fiber e.val).comp
      (continuous_fst.comp_continuousOn (C.val.continuousOn_symm.mono hball4t))
      fun z hz => (hcVe z (ball_subset_closedBall hz)).2
  have hwΦ : AEMeasurable (fun z => multiplierWeight (m : ℝ) (Φ (C.val.symm z)))
      (volume.restrict (ball w₀ (4 * r₁))) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      ((upperSemicontinuousOn_chartFunction_target hΦ.1 C).mono hball4t) hm'.ne'
  have hJ : ∫⁻ y in Uset, ENNReal.ofReal (‖F y‖ ^ 2) * multiplierWeight (m : ℝ) (Φ y)
      ∂(prodMeasure μ) < ⊤ := by
    have hcF : ContinuousOn (fun z => ‖F (C.val.symm z)‖ ^ 2) (ball w₀ (4 * r₁)) := by
      have : (fun z => ‖F (C.val.symm z)‖ ^ 2) =
          fun z => (‖g (C.val.symm z)‖ * ‖e.val.symm (C.val.symm z).1 1‖) ^ 2 := by
        funext z; rw [hFnorm]
      rw [this]
      exact (hgcont.norm.mul hfrcont).pow 2
    have hmeas : AEMeasurable (fun z => ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) *
        multiplierWeight (m : ℝ) (Φ (C.val.symm z))) (volume.restrict (ball w₀ (4 * r₁))) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (hcF.aestronglyMeasurable measurableSet_ball).aemeasurable).mul hwΦ
    rw [setLIntegral_pChart_eq (D.pt a, discOrigin) hρc hmapa isOpen_ball hball4t hmeas]
    have hME : 0 ≤ ME := (hmE0.le.trans (hmEb w₀ (mem_closedBall_self (by positivity))).1).trans
      (hmEb w₀ (mem_closedBall_self (by positivity))).2
    calc ∫⁻ z in ball w₀ (4 * r₁), ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) *
          multiplierWeight (m : ℝ) (Φ (C.val.symm z)) * ENNReal.ofReal (D.dens a (projX n z))
        ≤ ∫⁻ z in ball w₀ (4 * r₁), ENNReal.ofReal (ME ^ 2 * D.Aμ) *
            multiplierDensity (chartFunction Φ C) (m : ℝ) (fun z => g (C.val.symm z)) z := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          have hz4 : z ∈ closedBall w₀ (4 * r₁) := ball_subset_closedBall hz
          have hdom := hcDomR z hz4
          have hd1 : D.dens a (projX n z) ≤ D.Aμ := D.dens_le a _ hdom.1
          have hd2 : 1 ≤ D.Aμ * D.dens a (projX n z) := D.one_le a _ hdom.1
          have hd0 : 0 ≤ D.dens a (projX n z) := by
            by_contra hneg; push Not at hneg; nlinarith [D.Aμ_pos]
          have hfr := (hmEb z hz4).2
          have hfr0 : 0 ≤ ‖e.val.symm (C.val.symm z).1 1‖ := norm_nonneg _
          have h1 : ‖e.val.symm (C.val.symm z).1 1‖ ^ 2 ≤ ME ^ 2 := pow_le_pow_left₀ hfr0 hfr 2
          have h2 : ‖e.val.symm (C.val.symm z).1 1‖ ^ 2 * D.dens a (projX n z) ≤ ME ^ 2 * D.Aμ :=
            mul_le_mul h1 hd1 hd0 (sq_nonneg _)
          have hreal : ‖F (C.val.symm z)‖ ^ 2 * D.dens a (projX n z) ≤
              ME ^ 2 * D.Aμ * ‖g (C.val.symm z)‖ ^ 2 := by
            rw [hFnorm]
            calc (‖g (C.val.symm z)‖ * ‖e.val.symm (C.val.symm z).1 1‖) ^ 2 *
                  D.dens a (projX n z)
                = ‖g (C.val.symm z)‖ ^ 2 * (‖e.val.symm (C.val.symm z).1 1‖ ^ 2 *
                    D.dens a (projX n z)) := by ring
              _ ≤ ‖g (C.val.symm z)‖ ^ 2 * (ME ^ 2 * D.Aμ) :=
                  mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
              _ = ME ^ 2 * D.Aμ * ‖g (C.val.symm z)‖ ^ 2 := by ring
          have key : ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) * ENNReal.ofReal (D.dens a (projX n z))
              ≤ ENNReal.ofReal (ME ^ 2 * D.Aμ) * ENNReal.ofReal (‖g (C.val.symm z)‖ ^ 2) := by
            rw [← ENNReal.ofReal_mul (sq_nonneg _),
              ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) D.Aμ_pos.le)]
            exact ENNReal.ofReal_le_ofReal hreal
          show ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)) *
              ENNReal.ofReal (D.dens a (projX n z)) ≤ ENNReal.ofReal (ME ^ 2 * D.Aμ) *
            (ENNReal.ofReal (‖g (C.val.symm z)‖ ^ 2) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)))
          calc ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)) *
                ENNReal.ofReal (D.dens a (projX n z))
              = (ENNReal.ofReal (‖F (C.val.symm z)‖ ^ 2) * ENNReal.ofReal (D.dens a (projX n z))) *
                  multiplierWeight (m : ℝ) (Φ (C.val.symm z)) := by ring
            _ ≤ (ENNReal.ofReal (ME ^ 2 * D.Aμ) * ENNReal.ofReal (‖g (C.val.symm z)‖ ^ 2)) *
                  multiplierWeight (m : ℝ) (Φ (C.val.symm z)) := mul_le_mul_of_nonneg_right key zero_le
            _ = _ := by ring
      _ = ENNReal.ofReal (ME ^ 2 * D.Aμ) * ∫⁻ z in ball w₀ (4 * r₁),
            multiplierDensity (chartFunction Φ C) (m : ℝ) (fun z => g (C.val.symm z)) z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ME ^ 2 * D.Aμ) * ∫⁻ z in U₀,
            multiplierDensity (chartFunction Φ C) (m : ℝ) (fun z => g (C.val.symm z)) z :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set fun z hz =>
            hcU₀ z (ball_subset_closedBall hz)) zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU₀int
  -- the energy of `F` over `K'` for the pole weight
  have hKint : ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) *
      multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) ∂(prodMeasure μ) < ⊤ := by
    set c₀ : ℝ := ((n : ℝ) + 3) * Real.log ((r₁ / 2) ^ 2) with hc₀
    calc ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q)
          ∂(prodMeasure μ)
        ≤ ∫⁻ q in K', ENNReal.ofReal (Real.exp (-c₀)) *
            (ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight (m : ℝ) (Φ q)) ∂(prodMeasure μ) := by
          refine setLIntegral_mono' hK'.isClosed.measurableSet fun q hq => ?_
          have hlow : ((c₀ : ℝ) : EReal) ≤ Ψ q :=
            D.le_poleP t₀ hr₁ (by linarith) (by rw [← hw₀']; exact (hK'ann q hq).2)
          have := thetaGen_le_mw_of_le hm (hΦtop q) (hΨtop q) hlow
          calc ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q)
              ≤ ENNReal.ofReal (‖F q‖ ^ 2) *
                  (ENNReal.ofReal (Real.exp (-c₀)) * multiplierWeight (m : ℝ) (Φ q)) :=
                mul_le_mul_of_nonneg_left this zero_le
            _ = _ := by ring
      _ = ENNReal.ofReal (Real.exp (-c₀)) * ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) *
            multiplierWeight (m : ℝ) (Φ q) ∂(prodMeasure μ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (-c₀)) * ∫⁻ q in Uset, ENNReal.ofReal (‖F q‖ ^ 2) *
            multiplierWeight (m : ℝ) (Φ q) ∂(prodMeasure μ) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hK'U) zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ
  -- step 6: the global correction
  obtain ⟨S, hShol, hSint⟩ := hcorr Ψ hΨpsh hΨtop Uset hUo F hF χ hχ hχU K' hK' hK'U hconst hKint
  -- step 7: the local Skoda step near `q₀`
  set f : ComplexModel (n + 1) → ℂ := fun z => g (C.val.symm z) -
    e.val.continuousLinearMapAt ℂ (C.val.symm z).1 (S (C.val.symm z)) with hfdef
  have hr4 : ∀ z ∈ ball w₀ r₁, z ∈ closedBall w₀ (4 * r₁) := fun z hz =>
    closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz)
  have hfd : DifferentiableOn ℂ f (ball w₀ r₁) := by
    refine (hgU₀.mono fun z hz => hcU₀ z (hr4 z hz)).sub fun z hz => ?_
    exact (differentiableAt_comp_symm_of_holomorphicAt C (hct z (hr4 z hz))
      (hShol _ (mem_univ _) e (hcVe z (hr4 z hz)).2)).differentiableWithinAt
  have hpot := (LocalPotentialPullback.isSmoothLocalPotential_pullback
    (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (D.chartP a)
    (D.isSmoothLocalPotential_ρL hL hθ a)).mono (isOpen_prodDom _ _ _)
    (D.prodDom_subset_potentialDomain a)
  have h1 : PlurisubharmonicOn (fun w => (D.ρLP a w : EReal) + Φ ((D.chartP a).val.symm w))
      (prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :=
    plurisubharmonicOn_add_localPotential hΦ (D.chartP a) hpot
  set Ψloc : ComplexModel (n + 1) → EReal := fun w =>
    ((m : ℝ) : EReal) * ((D.ρLP a w : EReal) + Φ (C.val.symm w)) with hΨlocdef
  have hΨloc : PlurisubharmonicOn Ψloc (ball w₀ (2 * r₁)) :=
    (h1.const_mul hm').mono fun z hz =>
      hcDomR z (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))
  have hρLcont : ContinuousOn (fun z => D.ρLP a z) (closedBall w₀ (4 * r₁)) := by
    have hc : ContinuousOn (D.ρL a) (ball (ctr (n := n) (D.pt a)) (2 * D.R a)) :=
      (D.isSmoothLocalPotential_ρL hL hθ a).2.2.1.continuousOn
    refine (hc.comp (projX n).continuous.continuousOn fun z hz =>
      D.ball_subset_two a (hcDomR z hz).1).congr fun z hz => ?_
    show D.ρLP a z = D.ρL a (projX n z)
    rw [SiuCover.ρLP, D.coordinateMap_eq (hcDomR z hz)]
  obtain ⟨Cρ, hCρ⟩ := (isCompact_closedBall w₀ (4 * r₁)).exists_bound_of_continuousOn hρLcont
  have hρle : ∀ z ∈ closedBall w₀ (4 * r₁), |D.ρLP a z| ≤ Cρ := fun z hz => by
    have := hCρ z hz; rwa [Real.norm_eq_abs] at this
  have hmwloc : ∀ z, multiplierWeight 1 (Ψloc z) =
      ENNReal.ofReal (Real.exp (-(m * D.ρLP a z))) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)) :=
    fun z => mw_one_mul_add_coe hm' _ (hΦtop _)
  have hmwloc_le : ∀ z ∈ closedBall w₀ (4 * r₁), multiplierWeight 1 (Ψloc z) ≤
      ENNReal.ofReal (Real.exp (m * Cρ)) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)) := by
    intro z hz
    rw [hmwloc z]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) zero_le
    have h0 := hρle z hz
    have h2 : -D.ρLP a z ≤ Cρ := (neg_le_abs (D.ρLP a z)).trans h0
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left h2 hm'.le
  have hmwΦ_le : ∀ z ∈ closedBall w₀ (4 * r₁), multiplierWeight (m : ℝ) (Φ (C.val.symm z)) ≤
      ENNReal.ofReal (Real.exp (m * Cρ)) * multiplierWeight 1 (Ψloc z) := by
    intro z hz
    rw [hmwloc z, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    calc multiplierWeight (m : ℝ) (Φ (C.val.symm z))
        = ENNReal.ofReal 1 * multiplierWeight (m : ℝ) (Φ (C.val.symm z)) := by
          rw [ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          rw [Real.one_le_exp_iff]
          have h0 := hρle z hz
          have h2 : D.ρLP a z ≤ Cρ := (le_abs_self _).trans h0
          have h3 := mul_le_mul_of_nonneg_left h2 hm'.le
          linarith only [h3]
  set Aint := ∫⁻ q, ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
      multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) ∂(prodMeasure μ) with hAint
  have hballr_t : ball w₀ r₁ ⊆ C.val.target := fun z hz => hct z (hr4 z hz)
  have hI : ∫⁻ z in ball w₀ r₁, ENNReal.ofReal (‖f z‖ ^ 2) *
      multiplierWeight ((n : ℝ) + 3) (logNormSq (z - w₀)) * multiplierWeight 1 (Ψloc z) ≠ ⊤ := by
    set K₁ : ℝ≥0∞ := ENNReal.ofReal ((mE ^ 2)⁻¹) * ENNReal.ofReal (Real.exp (m * Cρ)) *
      ENNReal.ofReal D.Aμ with hK₁
    have hK₁ne : K₁ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hK₁ne hSint.ne) ?_
    calc ∫⁻ z in ball w₀ r₁, ENNReal.ofReal (‖f z‖ ^ 2) *
          multiplierWeight ((n : ℝ) + 3) (logNormSq (z - w₀)) * multiplierWeight 1 (Ψloc z)
        ≤ ∫⁻ z in ball w₀ r₁, K₁ * ((fun q => ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
            multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q)) (C.val.symm z) *
            ENNReal.ofReal (D.dens a (projX n z))) := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          have hz4 := hr4 z hz
          have hzt := hct z hz4
          set y := C.val.symm z with hy
          have hyC : y ∈ C.val.source := C.val.map_target hzt
          have hCy : C.val y = z := C.val.right_inv hzt
          have hyX : y.1 ∈ (D.chartX a).val.source := by
            have := hyC; rw [D.chartP_source] at this; exact this.1
          have hye : y.1 ∈ e.val.baseSet := (hcVe z hz4).2
          have hχy : χ y = 1 := hχone y hyC (by rw [hCy]; exact hz)
          set u := ((χ y : ℝ) : ℂ) • F y - S y with hu
          -- `|f| mE ≤ |u|`
          have hcoefu : e.val.continuousLinearMapAt ℂ y.1 u = f z := by
            rw [hu, hχy, Complex.ofReal_one, one_smul, map_sub, hFcoef y hye]
          have hnu : ‖u‖ = ‖f z‖ * ‖e.val.symm y.1 1‖ := by
            rw [norm_eq_coef_mul_norm_frame e.val hye u, hcoefu]
          have hfu : ‖f z‖ ^ 2 ≤ (mE ^ 2)⁻¹ * ‖u‖ ^ 2 := by
            rw [hnu, mul_pow]
            have hσ : mE ^ 2 ≤ ‖e.val.symm y.1 1‖ ^ 2 :=
              pow_le_pow_left₀ hmE0.le (hmEb z hz4).1 2
            calc ‖f z‖ ^ 2 = (mE ^ 2)⁻¹ * (‖f z‖ ^ 2 * mE ^ 2) := by field_simp
              _ ≤ (mE ^ 2)⁻¹ * (‖f z‖ ^ 2 * ‖e.val.symm y.1 1‖ ^ 2) := by gcongr
          have hi : ENNReal.ofReal (‖f z‖ ^ 2) ≤
              ENNReal.ofReal ((mE ^ 2)⁻¹) * ENNReal.ofReal (‖u‖ ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hfu
          have hii := hmwloc_le z hz4
          have hpole : Ψ y ≤ (((n : ℝ) + 3 : ℝ) : EReal) * logNormSq (z - w₀) := by
            have h := D.poleP_le_logNormSq (p := p) t₀ hyX
              (by rw [hCy, ← hw₀']; exact (hcP z hz4).le)
            rwa [hCy, ← hw₀'] at h
          have hiii := mw_mul_le_thetaGen hm (hΦtop y) (hΨtop y) hpole
          have hiv : 1 ≤ ENNReal.ofReal D.Aμ * ENNReal.ofReal (D.dens a (projX n z)) := by
            rw [← ENNReal.ofReal_mul D.Aμ_pos.le, ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (D.one_le a _ (hcDomR z hz4).1)
          show ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight ((n : ℝ) + 3) (logNormSq (z - w₀)) *
              multiplierWeight 1 (Ψloc z) ≤ K₁ * (ENNReal.ofReal (‖u‖ ^ 2) *
                multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ y) * ENNReal.ofReal (D.dens a (projX n z)))
          calc ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight ((n : ℝ) + 3) (logNormSq (z - w₀)) *
                multiplierWeight 1 (Ψloc z)
              ≤ (ENNReal.ofReal ((mE ^ 2)⁻¹) * ENNReal.ofReal (‖u‖ ^ 2)) *
                  multiplierWeight ((n : ℝ) + 3) (logNormSq (z - w₀)) *
                  (ENNReal.ofReal (Real.exp (m * Cρ)) * multiplierWeight (m : ℝ) (Φ y)) :=
                mul_le_mul' (mul_le_mul' hi le_rfl) hii
            _ = ENNReal.ofReal ((mE ^ 2)⁻¹) * ENNReal.ofReal (Real.exp (m * Cρ)) *
                  ENNReal.ofReal (‖u‖ ^ 2) * (multiplierWeight (m : ℝ) (Φ y) *
                  multiplierWeight ((n : ℝ) + 3) (logNormSq (z - w₀))) := by ring
            _ ≤ ENNReal.ofReal ((mE ^ 2)⁻¹) * ENNReal.ofReal (Real.exp (m * Cρ)) *
                  ENNReal.ofReal (‖u‖ ^ 2) * multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ y) :=
                mul_le_mul' le_rfl hiii
            _ ≤ ENNReal.ofReal ((mE ^ 2)⁻¹) * ENNReal.ofReal (Real.exp (m * Cρ)) *
                  ENNReal.ofReal (‖u‖ ^ 2) * multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ y) *
                  (ENNReal.ofReal D.Aμ * ENNReal.ofReal (D.dens a (projX n z))) :=
                le_mul_of_one_le_right' hiv
            _ = _ := by rw [hK₁]; ring
      _ = K₁ * ∫⁻ z in ball w₀ r₁, (fun q => ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
            multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q)) (C.val.symm z) *
            ENNReal.ofReal (D.dens a (projX n z)) := lintegral_const_mul' _ _ hK₁ne
      _ ≤ K₁ * ∫⁻ q in C.val.source ∩ C.val ⁻¹' ball w₀ r₁,
            ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
            multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) ∂(prodMeasure μ) :=
          mul_le_mul_of_nonneg_left (setLIntegral_pChart_le (D.pt a, discOrigin) hρc hmapa
            isOpen_ball hballr_t _) zero_le
      _ ≤ K₁ * Aint := mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le
  -- the division
  have e3 : (((n + 1 : ℕ) : ℝ) + 2) = (n : ℝ) + 3 := by push_cast; ring
  obtain ⟨U', hU'o, hw₀U', hU'r, h, hhd, hid, hhint⟩ :=
    exists_centred_division (n := n + 1) (Nat.succ_pos n) hr₁ (by linarith : r₁ < 2 * r₁) hΨloc hfd
      (by rw [e3]; exact hI)
  have hU'ball : ∀ z ∈ U', z ∈ closedBall w₀ (4 * r₁) := fun z hz => hr4 z (hU'r hz)
  -- step 8: the quotients `hᵢ ∘ w` lie in `𝓘(mΦ)_{q₀}`
  have hhmem : ∀ i, (multiplierIdeal (n := n + 1) (m : ℝ) Φ).mem q₀ (fun y => h i (C.val y)) := by
    intro i
    refine ⟨holomorphicAt_comp_chart' C hU'o (hhd i) hq₀C hw₀U', ?_⟩
    refine ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) (g := fun y => h i (C.val y))
      (complexChartAt (n := n + 1) q₀) C (mem_complexChartAt_source q₀) hq₀C (huscΦ _ _) hm'.ne' ?_
    have hrt : ∀ z ∈ U', C.val (C.val.symm z) = z := fun z hz =>
      C.val.right_inv (hct z (hU'ball z hz))
    refine ⟨hm', U', hU'o, hw₀U', (hhd i).congr fun z hz => by simp only [hrt z hz], ?_, ?_⟩
    · have hm1 : AEMeasurable (fun z => ENNReal.ofReal (‖h i z‖ ^ 2)) (volume.restrict U') :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          (((hhd i).continuousOn.aestronglyMeasurable hU'o.measurableSet).norm.aemeasurable.pow_const 2)
      have hm2 : AEMeasurable (fun z => multiplierWeight (m : ℝ) (chartFunction Φ C z))
          (volume.restrict U') :=
        DemaillyApproximation.aemeasurable_multiplierWeight_restrict hU'o
          ((upperSemicontinuousOn_chartFunction_target hΦ.1 C).mono fun z hz =>
            hct z (hU'ball z hz)) hm'.ne'
      refine (hm1.mul hm2).congr ?_
      filter_upwards [ae_restrict_mem hU'o.measurableSet] with z hz
      simp only [Pi.mul_apply, multiplierDensity, hrt z hz]
    · calc ∫⁻ z in U', multiplierDensity (chartFunction Φ C) (m : ℝ)
            (fun z => h i (C.val (C.val.symm z))) z
          = ∫⁻ z in U', ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight (m : ℝ) (Φ (C.val.symm z)) :=
            setLIntegral_congr_fun hU'o.measurableSet fun z hz => by
              simp only [multiplierDensity, chartFunction, hrt z hz]
        _ ≤ ∫⁻ z in U', ENNReal.ofReal (Real.exp (m * Cρ)) *
              (ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight 1 (Ψloc z)) := by
            refine setLIntegral_mono' hU'o.measurableSet fun z hz => ?_
            calc ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight (m : ℝ) (Φ (C.val.symm z))
                ≤ ENNReal.ofReal (‖h i z‖ ^ 2) *
                    (ENNReal.ofReal (Real.exp (m * Cρ)) * multiplierWeight 1 (Ψloc z)) :=
                  mul_le_mul' le_rfl (hmwΦ_le z (hU'ball z hz))
              _ = _ := by ring
        _ = ENNReal.ofReal (Real.exp (m * Cρ)) *
              ∫⁻ z in U', ENNReal.ofReal (‖h i z‖ ^ 2) * multiplierWeight 1 (Ψloc z) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr (hhint i))
  -- step 9: the identity near `q₀`
  have hident : ∀ᶠ q in 𝓝 q₀, g q - e.val.continuousLinearMapAt ℂ q.1 (S q) =
      ∑ i, centredCoords w₀ i (C.val q) * h i (C.val q) := by
    have hO : IsOpen (C.val.source ∩ C.val ⁻¹' U') := C.val.isOpen_inter_preimage hU'o
    filter_upwards [hO.mem_nhds ⟨hq₀C, hw₀U'⟩] with y hy
    have hz := hid (C.val y) hy.2
    have hfy : f (C.val y) = g y - e.val.continuousLinearMapAt ℂ y.1 (S y) := by
      have hyy : C.val.symm (C.val y) = y := C.val.left_inv hy.1
      show g (C.val.symm (C.val y)) - e.val.continuousLinearMapAt ℂ (C.val.symm (C.val y)).1
        (S (C.val.symm (C.val y))) = _
      rw [hyy]
    rw [← hfy]
    exact hz
  -- step 10: `S` is a section of `p₁^*E ⊗ 𝓘(mΦ)`
  have hb : ∫⁻ y, ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y‖ ^ 2) * multiplierWeight (m : ℝ) (Φ y)
      ∂(prodMeasure μ) < ⊤ := by
    refine lt_of_le_of_lt ?_ hJ
    rw [← lintegral_indicator hUo.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ Uset
    · rw [indicator_of_mem hy]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 y)]
      exact pow_le_pow_left₀ (mul_nonneg (hχ0 y) (norm_nonneg _))
        (mul_le_of_le_one_left (norm_nonneg _) (hχ1 y)) 2
    · rw [indicator_of_notMem hy]
      have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport fun h' => hy (hχU h')
      simp [h0]
  have hNcont : Continuous (fun y => ‖((χ y : ℝ) : ℂ) • F y‖) := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ Uset
    · have heq : (fun y => ‖((χ y : ℝ) : ℂ) • F y‖) =
          fun y => |χ y| * (‖g y‖ * ‖e.val.symm y.1 1‖) := by
        funext y'; rw [norm_smul, hFnorm, Complex.norm_real, Real.norm_eq_abs]
      rw [heq]
      have hfr : ContinuousAt (fun y' : X × unitDisc => ‖e.val.symm y'.1 1‖) y :=
        ((frameNorm_continuousOn E.Fiber e.val).continuousAt
          (e.val.open_baseSet.mem_nhds (hUmem y hy).2)).comp continuous_fst.continuousAt
      exact ((chartSmooth_continuous hχ).continuousAt.abs).mul
        ((hgHol y hy).continuousAt.norm.mul hfr)
    · have hyt : y ∉ tsupport χ := fun h' => hy (hχU h')
      have h0 : ∀ᶠ y' in 𝓝 y, χ y' = 0 := notMem_tsupport_iff_eventuallyEq.mp hyt
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [h0] with y' hy'
      simp [hy']
  have hSin : IsProdSectionIn E (multiplierIdeal (n := n + 1) (m : ℝ) Φ) S := by
    refine ⟨hShol, fun q e' hqe' => ?_⟩
    have := e'.property
    set d := complexChartAt (n := n + 1) q with hd
    have hqd : q ∈ d.val.source := mem_complexChartAt_source q
    have hO : IsOpen (d.val.target ∩ d.val.symm ⁻¹' (Prod.fst ⁻¹' e'.val.baseSet)) :=
      d.val.isOpen_inter_preimage_symm (e'.val.open_baseSet.preimage continuous_fst)
    have hqO : d.val q ∈ d.val.target ∩ d.val.symm ⁻¹' (Prod.fst ⁻¹' e'.val.baseSet) :=
      ⟨d.val.map_source hqd, by simp only [mem_preimage, d.val.left_inv hqd]; exact hqe'⟩
    obtain ⟨rq, hrq, hrqO⟩ := Metric.isOpen_iff.mp hO _ hqO
    have hcl : closedBall (d.val q) (rq / 2) ⊆
        d.val.target ∩ d.val.symm ⁻¹' (Prod.fst ⁻¹' e'.val.baseSet) :=
      (closedBall_subset_ball (by linarith)).trans hrqO
    refine mem_multiplierIdeal_of_chartBall hShol hΦ.1 hm' e' hqe' hcl (by linarith) ?_
    -- the density of `μ` in the chart at `q.1`
    obtain ⟨ρq, hρqs, hρqpos, hρqmap⟩ := hμ (complexChartAt (n := n) q.1)
    have hρqc : ContinuousOn (fun z : ComplexModel (n + 1) => ρq (projX n z)) d.val.target :=
      continuousOn_dens_pChart q hρqs.continuousOn hρqmap
    have hKq : IsCompact (closedBall (d.val q) (rq / 2)) := isCompact_closedBall _ _
    obtain ⟨z₁, hz₁, hmin₁⟩ := hKq.exists_isMinOn ⟨d.val q, mem_closedBall_self (by linarith)⟩
      (hρqc.mono fun z hz => (hcl hz).1)
    set ρmin := ρq (projX n z₁) with hρmin
    have hρmin0 : 0 < ρmin := by
      have := (hcl hz₁).1
      change z₁ ∈ (pChart (n := n) q).val.target at this
      rw [pChart_target] at this
      exact hρqpos _ this.1
    set bq : ComplexModel (n + 1) → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (‖((χ (d.val.symm z) : ℝ) : ℂ) • F (d.val.symm z)‖ ^ 2) *
        multiplierWeight (m : ℝ) (Φ (d.val.symm z)) * ENNReal.ofReal (ρq (projX n z)) with hbq
    set aq : ComplexModel (n + 1) → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (‖((χ (d.val.symm z) : ℝ) : ℂ) • F (d.val.symm z) - S (d.val.symm z)‖ ^ 2) *
        multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ (d.val.symm z)) *
        ENNReal.ofReal (ρq (projX n z)) with haq
    have hbqm : AEMeasurable bq (volume.restrict (ball (d.val q) (rq / 2))) := by
      have hball : ball (d.val q) (rq / 2) ⊆ d.val.target := fun z hz =>
        (hcl (ball_subset_closedBall hz)).1
      have h1 : ContinuousOn (fun z => ‖((χ (d.val.symm z) : ℝ) : ℂ) • F (d.val.symm z)‖ ^ 2)
          (ball (d.val q) (rq / 2)) :=
        (hNcont.comp_continuousOn (d.val.continuousOn_symm.mono hball)).pow 2
      have h2 : AEMeasurable (fun z => multiplierWeight (m : ℝ) (Φ (d.val.symm z)))
          (volume.restrict (ball (d.val q) (rq / 2))) :=
        DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
          ((upperSemicontinuousOn_chartFunction_target hΦ.1 d).mono hball) hm'.ne'
      have h3 : ContinuousOn (fun z => ENNReal.ofReal (ρq (projX n z))) (ball (d.val q) (rq / 2)) :=
        ENNReal.continuous_ofReal.comp_continuousOn (hρqc.mono hball)
      exact ((ENNReal.measurable_ofReal.comp_aemeasurable
        (h1.aestronglyMeasurable measurableSet_ball).aemeasurable).mul h2).mul
        (h3.aemeasurable measurableSet_ball)
    have hC₀ : ∀ y, Ψ y ≤ ((((n : ℝ) + 3) * Real.log 4 : ℝ) : EReal) := D.poleP_le hpc ht₀1
    set c₂ : ℝ≥0∞ := ENNReal.ofReal (2 * Real.exp (((n : ℝ) + 3) * Real.log 4)) with hc₂
    calc ∫⁻ z in ball (d.val q) (rq / 2), ENNReal.ofReal (‖S (d.val.symm z)‖ ^ 2) *
          multiplierWeight (m : ℝ) (Φ (d.val.symm z))
        ≤ ∫⁻ z in ball (d.val q) (rq / 2), ENNReal.ofReal ρmin⁻¹ * (c₂ * aq z + 2 * bq z) := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          set y := d.val.symm z with hy
          have hzt := (hcl (ball_subset_closedBall hz)).1
          have hρz : ρmin ≤ ρq (projX n z) := hmin₁ (ball_subset_closedBall hz)
          set v := ((χ y : ℝ) : ℂ) • F y with hv
          have hSle : ‖S y‖ ^ 2 ≤ 2 * ‖v - S y‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
            have h1 : ‖S y‖ ≤ ‖v - S y‖ + ‖v‖ := by
              calc ‖S y‖ = ‖v - (v - S y)‖ := by rw [sub_sub_cancel]
                _ ≤ ‖v‖ + ‖v - S y‖ := norm_sub_le _ _
                _ = ‖v - S y‖ + ‖v‖ := add_comm _ _
            have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
            nlinarith only [h2, sq_nonneg (‖v - S y‖ - ‖v‖)]
          have hwle := mw_le_thetaGen_of_le hm (hΦtop y) (hΨtop y) (hC₀ y)
          have h1 : 1 ≤ ENNReal.ofReal ρmin⁻¹ * ENNReal.ofReal (ρq (projX n z)) := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hρmin0.le), ← ENNReal.ofReal_one]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [inv_mul_eq_div, le_div_iff₀ hρmin0, one_mul]
            exact hρz
          set W := multiplierWeight (m : ℝ) (Φ y) with hW
          set WT := multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ y) with hWT
          set E₀ := ENNReal.ofReal (Real.exp (((n : ℝ) + 3) * Real.log 4)) with hE₀
          set δ := ENNReal.ofReal (ρq (projX n z)) with hδ
          have hsplit : ENNReal.ofReal (‖S y‖ ^ 2) ≤
              2 * ENNReal.ofReal (‖v - S y‖ ^ 2) + 2 * ENNReal.ofReal (‖v‖ ^ 2) := by
            have := ENNReal.ofReal_le_ofReal hSle
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_ofNat] at this
            exact this
          calc ENNReal.ofReal (‖S y‖ ^ 2) * W
              ≤ (2 * ENNReal.ofReal (‖v - S y‖ ^ 2) + 2 * ENNReal.ofReal (‖v‖ ^ 2)) * W :=
                mul_le_mul' hsplit le_rfl
            _ = 2 * (ENNReal.ofReal (‖v - S y‖ ^ 2) * W) + 2 * (ENNReal.ofReal (‖v‖ ^ 2) * W) := by
                ring
            _ ≤ 2 * (ENNReal.ofReal (‖v - S y‖ ^ 2) * (E₀ * WT)) +
                  2 * (ENNReal.ofReal (‖v‖ ^ 2) * W) :=
                add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl hwle)) le_rfl
            _ = (c₂ * (ENNReal.ofReal (‖v - S y‖ ^ 2) * WT) +
                  2 * (ENNReal.ofReal (‖v‖ ^ 2) * W)) * 1 := by
                rw [hc₂, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_one]; ring
            _ ≤ (c₂ * (ENNReal.ofReal (‖v - S y‖ ^ 2) * WT) +
                  2 * (ENNReal.ofReal (‖v‖ ^ 2) * W)) *
                  (ENNReal.ofReal ρmin⁻¹ * δ) := mul_le_mul' le_rfl h1
            _ = ENNReal.ofReal ρmin⁻¹ * (c₂ * aq z + 2 * bq z) := by
                rw [haq, hbq]; ring
      _ = ENNReal.ofReal ρmin⁻¹ * (c₂ * (∫⁻ z in ball (d.val q) (rq / 2), aq z) +
            2 * ∫⁻ z in ball (d.val q) (rq / 2), bq z) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_right' _ (hbqm.const_mul 2), lintegral_const_mul' _ _ (by rw [hc₂]; exact ENNReal.ofReal_ne_top),
            lintegral_const_mul' _ _ (by norm_num)]
      _ < ⊤ := by
          have hball : ball (d.val q) (rq / 2) ⊆ (pChart (n := n) q).val.target := fun z hz =>
            (hcl (ball_subset_closedBall hz)).1
          have ha' : ∫⁻ z in ball (d.val q) (rq / 2), aq z ≤ Aint :=
            (setLIntegral_pChart_le q hρqs.continuousOn hρqmap isOpen_ball hball
              (fun y => ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y - S y‖ ^ 2) *
                multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ y))).trans
              (setLIntegral_le_lintegral _ _)
          have hb' : ∫⁻ z in ball (d.val q) (rq / 2), bq z ≤
              ∫⁻ y, ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y‖ ^ 2) * multiplierWeight (m : ℝ) (Φ y)
                ∂(prodMeasure μ) :=
            (setLIntegral_pChart_le q hρqs.continuousOn hρqmap isOpen_ball hball
              (fun y => ENNReal.ofReal (‖((χ y : ℝ) : ℂ) • F y‖ ^ 2) *
                multiplierWeight (m : ℝ) (Φ y))).trans (setLIntegral_le_lintegral _ _)
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
          · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ha' hSint)
          · exact ENNReal.mul_lt_top (by norm_num) (lt_of_le_of_lt hb' hb)
  exact ⟨S, hSin, a, hq₀C, fun i y => h i (C.val y), hhmem, hident⟩

end SGPT.NAPotential.SiuGen

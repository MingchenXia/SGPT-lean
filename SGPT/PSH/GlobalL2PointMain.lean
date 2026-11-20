import SGPT.PSH.GlobalL2PointExtension

/-!
# `GlobalPointExtensionStatement` is proved

Blueprint `claude-global-l2:point-extension`.  `globalPointExtension : GlobalPointExtensionStatement n X`
(Xia, *Foundations of pluripotential theory*, `thm:compact-point-extension`, in the `k ≫ 0` form):
for `k ≥ k₀`, every `φ ∈ PSH(X, θ - δω)`, every `x` with `φ(x) > -∞` and every `v ∈ (L^k ⊗ T)_x`
there is `s ∈ H⁰(X, L^k ⊗ T)` with `s(x) = v` and `∫ |s|² e^{-kφ} dμ ≤ C |v|² e^{-kφ(x)}`, `C`
independent of `k, φ, x, v`.  See `SGPT/PSH/GlobalL2PointExtension.lean` for the route.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- **The uniform point extension in positive dimension.** -/
theorem globalPointExtension_pos (hn : 0 < n) : GlobalPointExtensionStatement n X := by
  intro hX ωb μ hμ L T hL hT θ hθ δ hδ
  obtain ⟨D⟩ := exists_coverData ωb hμ hL hT hθ (half_pos hδ)
  obtain ⟨k₁, hk₁⟩ := D.exists_goodPower (half_pos hδ)
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_poleB
  choose Tn hTn hTcov using D.exists_net
  obtain ⟨Mχ, hMχ0, hMχ⟩ := D.exists_cut_bound Tn hTn
  obtain ⟨Cot, hCot0, hCot⟩ := D.exists_OT_const
  set E : ℝ≥0∞ := ∑ a, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log (D.cutEps a ^ 2))))
    with hE
  have hEtop : E ≠ ⊤ := ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top
  have hPtop : D.pointConst Mχ E * ENNReal.ofReal Cot ≠ ⊤ :=
    ENNReal.mul_ne_top (D.pointConst_ne_top Mχ hEtop) ENNReal.ofReal_ne_top
  set Cfin : ℝ := (D.pointConst Mχ E * ENNReal.ofReal Cot).toReal + 1 with hCfin
  set B' : ℝ := ((n : ℝ) + 1) * B with hB'
  refine ⟨max k₁ (⌈2 * B' / δ⌉₊ + 1), Cfin, by positivity, fun k hk φ hφ x hφx v => ?_⟩
  have hkD : D.GoodPower k := hk₁ k (le_of_max_le_left hk)
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
  obtain ⟨a, hxa, hxr⟩ := (D.toGluingSystem hL hT hkD hφ2).cover x
  set c := D.chartA a with hc
  have hxa' : x ∈ c.val.source := hxa
  set p := c.val x with hp
  have hxr' : p ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4) := hxr
  have hpc : p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4) := ball_subset_closedBall hxr'
  obtain ⟨q, hqT, hpq⟩ := hTcov a p hpc
  have hq := hTn a q hqT
  set ε := D.cutEps a with hεdef
  have hε := D.cutEps_pos a
  have hεR := D.cutEps_le a
  have hRa := D.R_pos a
  have hεr : ε ≤ D.poleR a := by rw [hεdef, CoverData.cutEps]; linarith [D.poleR_pos a]
  have h4ε : 4 * ε = D.poleR a := by rw [hεdef, CoverData.cutEps]; ring
  have hpq' : dist p q < ε := hpq
  -- the pole
  have hP := D.poleRadii a hpc
  obtain ⟨mω, hmω, hBm⟩ := hBa a
  have hpsh := thetaPlurisubharmonic_poleFun ωb hP (m := mω)
    (fun w hw v => hmω w (D.closedBall_subset_of_mem hpc (by linarith) hw) v) hB0.le hBm
  have hinj : ∀ y ∈ c.val.source, c.val y = p → y = x := fun y hy h => c.val.injOn hy hxa' h
  set ψ := D.polePsi a p with hψdef
  have hψpsh : ThetaPlurisubharmonic (B' • ωb.form).val ψ := by
    have := Pending.GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
      (c := (n : ℝ) + 1) (by positivity) hpsh
    rwa [smul_smul] at this
  have hψ0 : ∀ y, ψ y ≤ 0 := fun y => coe_mul_nonpos (by positivity) (poleFun_le hP y)
  have hψne : ∀ y, y ≠ x → ψ y ≠ ⊥ := by
    intro y hyx
    have hP0 : poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y ≠ ⊥ :=
      poleFun_ne_bot fun hy h => hyx (hinj y hy h)
    show (((n : ℝ) + 1 : ℝ) : EReal) * _ ≠ ⊥
    induction h : poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y using EReal.rec with
    | bot => exact absurd h hP0
    | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    | top => rw [EReal.coe_mul_top_of_pos (by positivity)]; exact top_ne_bot
  have hφ' := isThetaPshPotential_poleWeight hn ωb (θ := θ) hk0 hkB hφ hψpsh hψne
  have hψpole : ∀ y ∈ c.val.source, c.val y ∈ ball p ε →
      ψ y = (((n : ℝ) + 1 : ℝ) : EReal) * logNormSq (c.val y - p) := by
    intro y hy hyε
    have hdist : dist (c.val y) p < ε := hyε
    show (((n : ℝ) + 1 : ℝ) : EReal) * poleFun c p (D.R a / 2) (Real.log (D.poleR a ^ 2)) y = _
    rw [poleFun_of_mem hy (by rw [mem_ball]; linarith), poleChart_eq_logNormSq
      (by rw [← dist_eq_norm]; linarith)]
  have hψlow : ∀ y, (y ∈ c.val.source → ε ≤ ‖c.val y - p‖) →
      ((((n : ℝ) + 1) * Real.log (ε ^ 2) : ℝ) : EReal) ≤ ψ y := fun y hy =>
    coe_mul_le_coe_mul (by positivity) (log_le_poleFun hε hεr hy)
  -- the cut-off
  set χ := D.cutChi a q with hχdef
  have hχ : ChartSmooth (n := n) χ := D.chartSmooth_cutChi hq
  have hχ0 : ∀ y, 0 ≤ χ y :=
    Pending.ChartPartition.chartExtend_nonneg fun z => (D.cutBump a q).nonneg
  have hχ1 : ∀ y, χ y ≤ 1 :=
    Pending.ChartPartition.chartExtend_le_one fun z => (D.cutBump a q).le_one
  have htar := D.closedBall_cut_subset_target hq
  have himg : ∀ w ∈ closedBall q (3 * ε), c.val.symm w ∈ c.val.source ∧
      c.val (c.val.symm w) = w := fun w hw =>
    ⟨c.val.map_target (htar hw), c.val.right_inv (htar hw)⟩
  have hχU : tsupport χ ⊆ c.val.source ∩ c.val ⁻¹' ball p (4 * ε) := by
    refine (Pending.ChartPartition.support_chartExtend_subset (D.chartA a)).trans ?_
    rw [D.tsupport_cutBump]
    have hcomp : IsCompact (c.val.symm '' closedBall q (3 * ε)) :=
      (isCompact_closedBall q _).image_of_continuousOn (c.val.continuousOn_symm.mono htar)
    rw [hcomp.isClosed.closure_eq]
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨(himg w hw).1, ?_⟩
    rw [mem_preimage, (himg w hw).2, mem_ball]
    have : dist w q ≤ 3 * ε := hw
    linarith [dist_triangle w q p, dist_comm p q]
  have hχone : ∀ y ∈ c.val.source, c.val y ∈ ball p ε → χ y = 1 := by
    intro y hy hyε
    rw [hχdef, CoverData.cutChi, Pending.ChartPartition.chartExtend_of_mem hy]
    refine (D.cutBump a q).one_of_mem_closedBall ?_
    have : dist (c.val y) p < ε := hyε
    show dist (c.val y) q ≤ 2 * D.cutEps a
    linarith [dist_triangle (c.val y) p q]
  set A₀ : Set (ComplexModel n) := closedBall q (3 * ε) ∩ {w | 2 * ε ≤ dist w q} with hA₀
  set K : Set X := c.val.symm '' A₀ with hKdef
  have hA₀c : IsCompact A₀ := (isCompact_closedBall q _).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hK : IsCompact K :=
    hA₀c.image_of_continuousOn (c.val.continuousOn_symm.mono fun w hw => htar hw.1)
  have hKU : K ⊆ c.val.source ∩ c.val ⁻¹' ball p (4 * ε) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨(himg w hw.1).1, ?_⟩
    rw [mem_preimage, (himg w hw.1).2, mem_ball]
    have : dist w q ≤ 3 * ε := hw.1
    linarith [dist_triangle w q p, dist_comm p q]
  have hKann : ∀ y ∈ K, ε ≤ ‖c.val y - p‖ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [(himg w hw.1).2, ← dist_eq_norm]
    have : 2 * ε ≤ dist w q := hw.2
    linarith [dist_triangle w p q]
  have hconst : ∀ y ∈ (c.val.source ∩ c.val ⁻¹' ball p (4 * ε)) \ K,
      ∀ᶠ y' in 𝓝 y, χ y' = χ y := by
    rintro y ⟨⟨hy, -⟩, hyK⟩
    by_cases h2 : dist (c.val y) q < 2 * ε
    · have hO : IsOpen (c.val.source ∩ c.val ⁻¹' ball q (2 * ε)) :=
        c.val.isOpen_inter_preimage isOpen_ball
      have hval : ∀ y' ∈ c.val.source ∩ c.val ⁻¹' ball q (2 * ε), χ y' = 1 := by
        intro y' hy'
        rw [hχdef, CoverData.cutChi, Pending.ChartPartition.chartExtend_of_mem hy'.1]
        exact (D.cutBump a q).one_of_mem_closedBall (ball_subset_closedBall hy'.2)
      filter_upwards [hO.mem_nhds ⟨hy, h2⟩] with y' hy'
      rw [hval y' hy', hval y ⟨hy, h2⟩]
    · have h3 : 3 * ε < dist (c.val y) q := by
        by_contra hle
        refine hyK ⟨c.val y, ⟨?_, ?_⟩, c.val.left_inv hy⟩
        · show dist (c.val y) q ≤ 3 * ε; linarith
        · show 2 * ε ≤ dist (c.val y) q; linarith
      have hO : IsOpen (c.val.source ∩ c.val ⁻¹' {w | 3 * ε < dist w q}) :=
        c.val.isOpen_inter_preimage (isOpen_lt continuous_const (continuous_id.dist continuous_const))
      have hval : ∀ y' ∈ c.val.source ∩ c.val ⁻¹' {w | 3 * ε < dist w q}, χ y' = 0 := by
        intro y' hy'
        rw [hχdef, CoverData.cutChi, Pending.ChartPartition.chartExtend_of_mem hy'.1]
        exact (D.cutBump a q).zero_of_le_dist (le_of_lt hy'.2)
      filter_upwards [hO.mem_nhds ⟨hy, h3⟩] with y' hy'
      rw [hval y' hy', hval y ⟨hy, h3⟩]
  -- the domain of the local extension
  have hΩR : ball p (4 * ε) ⊆ ball (ctr (n := n) (D.pt a)) (D.R a / 2) := by
    intro z hz
    have h1 : dist z p < 4 * ε := hz
    have h2 : dist p (ctr (n := n) (D.pt a)) < D.R a / 4 := hxr'
    rw [mem_ball]
    linarith [dist_triangle z p (ctr (n := n) (D.pt a))]
  -- the Ohsawa--Takegoshi extension from `p`
  set φOT : ComplexModel n → EReal := fun z => D.psiW k φ a z +
    ((D.lam * ‖z - ctr (n := n) (D.pt a)‖ ^ 2 : ℝ) : EReal) with hφOT
  have hΩR' : ball p (4 * ε) ⊆ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    hΩR.trans (ball_subset_ball (by linarith))
  have hφOT : PlurisubharmonicOn φOT (ball p (4 * ε)) :=
    ((D.psiW_psh hL hT hkD hφ2 a).mono hΩR').add
      (plurisubharmonicOn_mul_normSq D.lam_pos.le _ _)
  obtain ⟨F₀, hF₀, hF₀p, hF₀int⟩ := hCot a (ball p (4 * ε)) isOpen_ball (convex_ball _ _) hΩR'
    φOT hφOT p (mem_ball_self (by positivity))
  obtain ⟨σ, hσx, hσint⟩ := D.exists_section_through_point hL hT hkD hφ2 hφ' hn a hxa' hε hΩR
    hψ0 hψpole hψlow hχ hχ0 hχ1 hχU hχone hK hKU hKann hconst hMχ0 (hMχ a q hqT) hF₀ hF₀p
    hF₀int hφx v
  refine ⟨σ, hσx, hσint.trans ?_⟩
  have he : ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log (ε ^ 2)))) ≤ E :=
    Finset.single_le_sum (f := fun a => ENNReal.ofReal
      (Real.exp (-(((n : ℝ) + 1) * Real.log (D.cutEps a ^ 2))))) (fun _ _ => zero_le)
      (Finset.mem_univ a)
  have hpc' : D.pointConst Mχ (ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log (ε ^ 2))))) ≤
      D.pointConst Mχ E := by
    unfold CoverData.pointConst; gcongr
  calc D.pointConst Mχ (ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log (ε ^ 2))))) *
        ENNReal.ofReal Cot * (ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x))
      ≤ D.pointConst Mχ E * ENNReal.ofReal Cot *
          (ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x)) := by gcongr
    _ ≤ ENNReal.ofReal Cfin * (ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x)) := by
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        rw [← ENNReal.ofReal_toReal hPtop]
        exact ENNReal.ofReal_le_ofReal (by rw [hCfin]; linarith)

/-- **The uniform point extension in dimension zero**: `X` is discrete. -/
theorem globalPointExtension_zero {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
    [IsComplexManifold 0 X] [MeasurableSpace X] [BorelSpace X] :
    GlobalPointExtensionStatement 0 X := by
  intro hX ωb μ hμ L T hL hT θ hθ δ hδ
  obtain ⟨D⟩ := exists_coverData ωb hμ hL hT hθ hδ
  obtain ⟨k₁, hk₁⟩ := D.exists_goodPower hδ
  set C0 : ℝ≥0∞ := ∑ a, ENNReal.ofReal D.Aμ * volume (ball (ctr (n := 0) (D.pt a)) (D.R a))
    with hC0
  have hC0top : C0 ≠ ⊤ := ENNReal.sum_ne_top.mpr fun a _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  refine ⟨k₁, C0.toReal + 1, by positivity, fun k hk φ hφ x hφx v => ?_⟩
  classical
  set G := D.toGluingSystem hL hT (hk₁ k hk) hφ with hG
  set S : (y : X) → (twistedPower L T k).Fiber y := Function.update (fun _ => 0) x v with hS
  have hSloc : ∀ a, ∃ s : ComplexModel 0 → ℂ,
      DifferentiableOn ℂ s (ball (G.center a) (G.r a)) ∧
      ∀ y ∈ G.small a, S y = s (G.chart a y) • G.frame a y := by
    intro a
    refine ⟨G.locCoef a S, (differentiableOn_const (G.locCoef a S 0)).congr fun z _ => by
      rw [Subsingleton.elim z 0], fun y hy => ?_⟩
    have hyR : G.chart a y ∈ ball (G.center a) (G.R a) :=
      ball_subset_ball (G.r_lt_R a).le hy.2
    rw [GluingSystem.locCoef, (G.chart a).left_inv hy.1]
    exact G.eq_coef_smul_frame a y (S y) hy.1 hyR
  obtain ⟨σ, hσ⟩ := D.exists_section_of_local hL hT (hk₁ k hk) hφ S hSloc
  refine ⟨σ, by rw [hσ, hS, Function.update_self], ?_⟩
  set I₀ := ENNReal.ofReal (‖v‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) with hI₀
  have hpt : ∀ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ≤
      ({x} : Set X).indicator (fun _ => I₀) y := by
    intro y
    by_cases hy : y = x
    · subst hy; rw [indicator_of_mem (mem_singleton y), hσ, hS, Function.update_self]
    · rw [indicator_of_notMem (by simpa using hy), hσ, hS, Function.update_of_ne hy]
      simp
  obtain ⟨a, hxa, hxr⟩ := G.cover x
  have hxreg : x ∈ G.region a := ⟨hxa, ball_subset_ball ((G.r'_lt_r a).le.trans
    (G.r_lt_R a).le) hxr⟩
  have hμx : μ {x} ≤ C0 := by
    calc μ {x} ≤ μ (G.region a) := measure_mono (singleton_subset_iff.mpr hxreg)
      _ = ∫⁻ y in G.region a, (fun _ => (1 : ℝ≥0∞)) y ∂μ := by
          rw [setLIntegral_const, one_mul]
      _ = ∫⁻ z in ball (G.center a) (G.R a), 1 * G.dens a z := G.map_measure a _ aemeasurable_const
      _ ≤ ∫⁻ z in ball (G.center a) (G.R a), G.A :=
          setLIntegral_mono' measurableSet_ball fun z hz => by
            rw [one_mul]; exact G.dens_le a z hz
      _ = ENNReal.ofReal D.Aμ * volume (ball (ctr (n := 0) (D.pt a)) (D.R a)) := by
          rw [setLIntegral_const]; rfl
      _ ≤ C0 := Finset.single_le_sum (f := fun a => ENNReal.ofReal D.Aμ *
          volume (ball (ctr (n := 0) (D.pt a)) (D.R a))) (fun _ _ => zero_le) (Finset.mem_univ a)
  calc ∫⁻ y, ENNReal.ofReal (‖σ y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ
      ≤ ∫⁻ y, ({x} : Set X).indicator (fun _ => I₀) y ∂μ := lintegral_mono hpt
    _ = I₀ * μ {x} := lintegral_indicator_const (measurableSet_singleton x) I₀
    _ ≤ I₀ * C0 := mul_le_mul_of_nonneg_left hμx zero_le
    _ ≤ ENNReal.ofReal (C0.toReal + 1) * I₀ := by
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        calc C0 = ENNReal.ofReal C0.toReal := (ENNReal.ofReal_toReal hC0top).symm
          _ ≤ ENNReal.ofReal (C0.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)

/-- **`GlobalPointExtensionStatement` holds** (`claude-global-l2:point-extension`). -/
theorem globalPointExtension : GlobalPointExtensionStatement n X := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact globalPointExtension_zero
  · exact globalPointExtension_pos h

end SGPT.PSH.GlobalL2

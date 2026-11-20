import SGPT.Okounkov.TranscendentalL2Generation

/-!
# Proof of `ModificationL2GenerationStatement`

Plan `tok/RELGEN3` step P9 (blueprint `l2:modification-generation`, chapter `claude-tok-l2`).

`modificationL2Generation : ModificationL2GenerationStatement`. The constant is
`C = C_P + C₂ + 1`, with `C₂` the domination constant of the curvature of the relative Jacobian
divisor by `β` (`KahlerDomination.exists_isSemipositive_add_smul`) and `C_P` the pole constant of
`exists_pole_family`; both are uniform by compactness of `Z`. For `z ∉ A` the germ `f` itself
works (`generation_of_not_mem_exceptional`); for `z ∈ A` the proof is the flat route of the
blueprint: the hypersurface `k` (`exists_hypersurface`), Hörmander's estimate on its complement
(`exists_solution_on_complement`), the extension upstairs (`exists_upstairs_extension`),
membership (`mem_multiplierIdeal_of_estimate`) and the pole integral (`exists_pole_integral`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalL2

open Set Filter MeasureTheory Metric Complex
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
open SGPT.Foundations.Analysis.Pending.GlobalRelativeJacobianIdeal
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalRelGen

/-- **`L²` generation over a coordinate ball of the base of a modification** (blueprint
`l2:modification-generation`; the case of DRWNXZ Lemma 2.8's `L²` input used by `tok:relgen`). -/
theorem modificationL2Generation : ModificationL2GenerationStatement.{u} := by
  intro n X Z _ _ _ _ _ _ _ π hπ θ β D E c h hc hβ hE hh hheq
  obtain ⟨A, B, s, hAc, -, hAi, hBc, hBa, hBi, hpre, hs, hright, hleft⟩ := hπ.2.2
  obtain ⟨ER, -, hER⟩ :=
    DivisorMetric.exists_divisorMetric (actualRelativeJacobianDivisor (n := n) hπ)
  obtain ⟨C₂, hC₂, hdom⟩ :=
    KahlerDomination.exists_isSemipositive_add_smul (-ER.curvature).val β.val hβ.1
  obtain ⟨CP, hCP, hpole⟩ := exists_pole_family β hβ
  refine ⟨CP + C₂ + 1, by positivity, fun q N hN d p r ρ hcl hρ z hz f hf => ?_⟩
  set a : ℝ := ((N : ℝ) + 1) / c with ha
  set φ := relgenWeight π E d ρ h N a with hφ
  set V := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball p r) with hV
  have hVo : IsOpen V := (d.val.isOpen_inter_preimage isOpen_ball).preimage hπ.1.continuous
  have hφpsh := thetaPlurisubharmonicOn_weight hπ.1 θ β hβ E hc hh hheq d hρ N (le_refl a)
  have husc : ∀ e : ComplexChart n Z,
      UpperSemicontinuousOn (chartFunction φ e) (e.val.target ∩ e.val.symm ⁻¹' V) :=
    fun e => upperSemicontinuousOn_chartFunction_of_thetaPlurisubharmonicOn hφpsh e
  by_cases hzA : z ∉ A
  · exact generation_of_not_mem_exceptional hπ hpre hleft hVo husc rfl hz hzA hf q
  push Not at hzA
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqa : (q : ℝ) * CP + C₂ + 1 ≤ a := by nlinarith
  -- the pole chart
  obtain ⟨a₀, ε, χP, hz₀, hε, hχP, hεt, hχPb, hχP1, hχP0, hlevi⟩ := hpole z
  set e₀ := complexChartAt (n := n) a₀ with he₀
  set w₀ := e₀.val z with hw₀
  -- the hypersurface
  obtain ⟨r₁, hr₁0, hr₁, k, hk, hkne, hkzero⟩ := exists_hypersurface hπ hAc hBc hBa hBi hpre hs
    hleft θ β hβ hE hc hh hheq d hρ hz
  set x₀ := d.val (π z) with hx₀
  set V' := π ⁻¹' (d.val.source ∩ d.val ⁻¹' ball x₀ r₁) with hV'
  have hV'V : V' ⊆ V := fun t ht => ⟨ht.1, hr₁ (ball_subset_closedBall ht.2)⟩
  have hzV' : z ∈ V' := ⟨hz.1, mem_ball_self hr₁0⟩
  have hkz : k (d.val (π z)) = 0 := hkzero z hz.1 (mem_ball_self hr₁0)
    (Or.inl (by rw [← hpre] at hzA; exact hzA))
  -- `f` in the pole chart
  have hzez := mem_complexChartAt_source (n := n) z
  obtain ⟨-, Of, hOf, hw₀Of, hfdOf, hfmeasOf, hfintOf⟩ :=
    multiplierIntegrableAt_chart_of_isOpen hVo husc one_ne_zero (g := f) e₀
      (complexChartAt (n := n) z) hz hz₀ hzez hf.2
  -- the Jacobian bounds near `z`
  obtain ⟨OΓ, hOΓ, hw₀OΓ, hOΓd, cJ, CJ, hcJ, hbdΓ⟩ :=
    exists_jacobian_weight_bounds hπ hER a₀ d hz₀ hz.1
  set F₀ := coordinateMap π e₀ d with hF₀
  have hF₀w₀ : F₀ w₀ = x₀ := coordinateMap_at hz₀
  have hU₀o : IsOpen (Of ∩ (OΓ ∩ F₀ ⁻¹' ball x₀ r₁)) := by
    have hFc : ContinuousOn F₀ (coordinateDomain π e₀ d) :=
      (coordinateMap_contDiffOn hπ.1 e₀ d).continuousOn
    have : OΓ ∩ F₀ ⁻¹' ball x₀ r₁ = OΓ ∩ (coordinateDomain π e₀ d ∩ F₀ ⁻¹' ball x₀ r₁) := by
      ext w; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hOΓd h1, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    rw [this]
    exact hOf.inter (hOΓ.inter (hFc.isOpen_inter_preimage (coordinateDomain_isOpen hπ.1 e₀ d)
      isOpen_ball))
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := Metric.isOpen_iff.mp hU₀o w₀
    ⟨hw₀Of, hw₀OΓ, by rw [mem_preimage, hF₀w₀]; exact mem_ball_self hr₁0⟩
  set δ : ℝ := min (δ₀ / 4) (ε / 4) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ < ε / 2 := (min_le_right _ _).trans_lt (by linarith)
  have hδε' : δ ≤ ε := (min_le_right _ _).trans (by linarith)
  have h2δ : ball w₀ (2 * δ) ⊆ ball w₀ δ₀ :=
    ball_subset_ball (by have := min_le_left (δ₀ / 4) (ε / 4); linarith)
  have hball2 : ball w₀ (2 * δ) ⊆ Of ∩ (OΓ ∩ F₀ ⁻¹' ball x₀ r₁) := h2δ.trans hδ₀U
  have hδt : closedBall w₀ δ ⊆ e₀.val.target :=
    (closedBall_subset_closedBall hδε').trans hεt
  -- the data cut-off
  obtain ⟨χ₁, hχ₁s, -, hχ₁b, hχ₁1, hχ₁0⟩ := exists_bump (n := n) hδ
  set χD : ComplexModel n → ℝ := fun w => χ₁ (w - w₀) with hχD
  have hχDs : ContDiff ℝ ∞ χD := hχ₁s.comp (contDiff_id.sub contDiff_const)
  have hχD1 : ∀ w, ‖w - w₀‖ < δ / 2 → χD w = 1 := fun w hw => hχ₁1 _ hw
  have hχD0 : ∀ w, δ ≤ ‖w - w₀‖ → χD w = 0 := fun w hw => hχ₁0 _ hw
  have hχDb : ∀ w, 0 ≤ χD w ∧ χD w ≤ 1 := fun w => hχ₁b _
  -- the positivity of `β` on the support
  obtain ⟨m₀, hm₀, hm₀le⟩ :=
    exists_lineValue_lower_bound_of_isCompact (β := β.val) hβ.1 e₀ (isCompact_closedBall w₀ δ) hδt
  have hfd : DifferentiableOn ℂ (fun w => f (e₀.val.symm w)) (ball w₀ (2 * δ)) :=
    hfdOf.mono fun w hw => (hball2 hw).1
  have hfint : ∫⁻ w in ball w₀ (2 * δ), multiplierDensity (chartFunction φ e₀) 1
      (fun w => f (e₀.val.symm w)) w < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set fun w hw => (hball2 hw).1) hfintOf
  have hδdom : ball w₀ (2 * δ) ⊆ coordinateDomain π e₀ d ∩ F₀ ⁻¹' ball x₀ r₁ :=
    fun w hw => ⟨hOΓd (hball2 hw).2.1, (hball2 hw).2.2⟩
  have hCJ : ∀ w ∈ ball w₀ (2 * δ), complexJacobian F₀ w ≠ 0 →
      Complex.normSq (complexJacobian F₀ w) *
        Real.exp (-(ER.weight (e₀.val.symm w)).toReal) ≤ CJ :=
    fun w hw hJ => (hbdΓ w (hball2 hw).2.1 hJ).2.2
  -- Hörmander's estimate on the complement of the hypersurface
  obtain ⟨G, hG, hGfin⟩ := exists_solution_on_complement hπ hAc hBc hpre hs hright hleft θ β hβ
    hE hc hh hheq hER hdom d hcl hρ q N hCP hqa hzA e₀ hz₀ hχP hεt hχP1 hχP0 hlevi hr₁ hk hkzero
    hδ hδε hχDs hχD1 hχD0 hfd hfint hδdom hCJ hm₀ hm₀le
  -- the data and the weight
  set hZ := cutFunction e₀ χD f with hhZ
  set W : Z → ℝ := fun t => realWeight π E d ρ h N a t + poleWeight e₀ χP w₀ q t with hW
  have hGfin' : ∫⁻ x in ball x₀ r₁ ∩ {x | k x ≠ 0}, ENNReal.ofReal
      (‖hZ (s (d.val.symm x)) - G x‖ ^ 2 *
        Real.exp (-(W (s (d.val.symm x)) + (ER.weight (s (d.val.symm x))).toReal))) < ⊤ :=
    hGfin
  have hĥ : Continuous fun w => (χD w : ℂ) * f (e₀.val.symm w) :=
    (contDiff_cutData hχDs hδ hχD0 hfd).continuous
  obtain ⟨Mh, hMh⟩ := exists_norm_cutFunction_le e₀ hχD0 hĥ
  set MP : ℝ := q * max 0 (Real.log (ε ^ 2)) with hMP
  have hPle : ∀ t, poleWeight e₀ χP w₀ q t ≤ MP := by
    classical
    intro t
    simp only [poleWeight, chartLift]
    split_ifs
    · exact mul_le_mul_of_nonneg_left (cutoffPole_le hχPb hχP0 w₀ _) hq0
    · exact mul_nonneg hq0 (le_max_left _ _)
  -- upper bounds for the weight near points of `V'`
  have hWub : ∀ y ∈ V', ∃ N' ∈ 𝓝 y, ∃ M : ℝ, ∀ t ∈ N', E.weight t ≠ ⊥ → W t ≤ M := by
    intro y hy
    obtain ⟨U, hU, M, hM⟩ := exists_realWeight_upper_bound hπ.1 hE hh d isOpen_ball
      hρ.2.2.1.continuousOn N (by positivity : (0 : ℝ) ≤ a) (hV'V hy)
    refine ⟨U, hU, M + MP, fun t ht hEt => ?_⟩
    have h1 := hM t ht hEt
    have h2 := hPle t
    simp only [hW]
    linarith
  obtain ⟨F, hFd, hFG⟩ := exists_upstairs_extension hπ hAc hAi hBc hpre hs hright hleft hER hk
    hkne hkzero hG hGfin' hMh hWub
  -- regularity data
  have hφeq : ∀ t, E.weight t ≠ ⊥ → φ t = (realWeight π E d ρ h N a t : EReal) := fun t ht =>
    relgenWeight_eq_realWeight ht (weight_ne_top_of_isDivisorMetric hE t)
  have hWφ : ∀ t, W t ≤ realWeight π E d ρ h N a t + MP := fun t => by
    simp only [hW]; linarith [hPle t]
  have hZc : ∀ e : ComplexChart n Z, ContinuousOn (fun w => hZ (e.val.symm w)) e.val.target :=
    continuousOn_cutFunction e₀ hδt hχD0 hĥ
  have hWc : ∀ t ∈ V', k (d.val (π t)) ≠ 0 → ∀ e : ComplexChart n Z, t ∈ e.val.source →
      ContinuousAt (fun w => W (e.val.symm w)) (e.val t) := by
    intro t ht hkt e hte
    obtain ⟨htA, -, htE⟩ := upstairs_facts hpre hleft hkzero ht.1 ht.2 hkt
    have ht₀ : t ∈ e₀.val.source → e₀.val t ≠ w₀ := fun h1 h2 =>
      htA ((e₀.val.injOn h1 hz₀ h2) ▸ hzA)
    exact continuousAt_weight_add_pole hπ.1 θ β hβ hE hc hh hheq d hρ N e₀ hχP hεt hχP0 q
      (hV'V ht) htE ht₀ e hte
  have hfMI : ∀ w ∈ closedBall w₀ δ, MultiplierIntegrableAt (chartFunction φ e₀) 1
      (fun w => f (e₀.val.symm w)) w volume := fun w hw =>
    ⟨one_pos, Of, hOf, (hball2 (closedBall_subset_ball (by linarith) hw)).1, hfdOf, hfmeasOf,
      hfintOf⟩
  have hZL2 : ∀ y ∈ V', ∃ O : Set (ComplexModel n), IsOpen O ∧
      (complexChartAt (n := n) y).val y ∈ O ∧
      ∫⁻ w in O, multiplierDensity (chartFunction φ (complexChartAt (n := n) y)) 1
        (fun w => hZ ((complexChartAt (n := n) y).val.symm w)) w < ⊤ := fun y hy =>
    exists_cutFunction_lintegral_lt_top hVo husc e₀ hδt hχDb hχD0 hfMI (hV'V hy)
  refine ⟨d.val.source ∩ d.val ⁻¹' ball x₀ r₁, d.val.isOpen_inter_preimage isOpen_ball, hzV',
    fun x hx => ⟨hx.1, hr₁ (ball_subset_closedBall hx.2)⟩, F, hFd, fun y hy => ?_, ?_⟩
  · exact mem_multiplierIdeal_of_estimate hπ hAc hAi hBc hpre hs hright hleft hER husc hφeq hk
      hkne hkzero hV'V hGfin' hWφ hZc hWc hG hZL2 hFd hFG hy
  · -- the pole integral
    have hwt : ∀ w ∈ ball w₀ (δ / 2), w ∈ e₀.val.target := fun w hw =>
      hδt (ball_subset_closedBall (ball_subset_ball (by linarith) hw))
    have hZf : ∀ w ∈ ball w₀ (δ / 2), hZ (e₀.val.symm w) = f (e₀.val.symm w) := by
      intro w hw
      have hw' : ‖w - w₀‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm] at hw
      simp only [hhZ, cutFunction]
      rw [chartLift_symm e₀ _ (hwt w hw), hχD1 w hw', Complex.ofReal_one, one_mul]
    have hWlog : ∀ w ∈ ball w₀ (δ / 2), w ≠ w₀ → E.weight (e₀.val.symm w) ≠ ⊥ →
        W (e₀.val.symm w) = realWeight π E d ρ h N a (e₀.val.symm w) +
          q * Real.log (‖w - w₀‖ ^ 2) := by
      intro w hw _ _
      have hw' : ‖w - w₀‖ < ε / 2 := by
        rw [mem_ball, dist_eq_norm] at hw; linarith
      simp only [hW, poleWeight]
      rw [chartLift_symm e₀ _ (hwt w hw), cutoffPole_eq_log hχP1 hw']
    exact exists_pole_integral hπ hAc hAi hBc hpre hs hright hleft hER hVo husc
      (relgenWeight_ne_top hE d ρ h N a) hφeq hk hkne hkzero hV'V hGfin' hFd hFG a₀ hz₀ hzV' hkz
      (half_pos hδ) (hfd.mono (ball_subset_ball (by linarith))) hZf q hWlog

end SGPT.Okounkov.TranscendentalL2

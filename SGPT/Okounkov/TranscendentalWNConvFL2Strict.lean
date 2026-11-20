import SGPT.Okounkov.TranscendentalWNConvFL2Small

/-!
# Small fibre volumes near `X' \ ℰ`

Blueprint `claude-tok-wn-fl2`, node `tok-wn-fl2:strict-local`; source WN21 §7, estimate (eqeq)
(`references/wn21-restricted-volume`).

Let `q ∈ X₀ \ ℰ`, `x₀ = π_X(μ(q)) ∉ Z`.  In the chart `e` of `X` at `x₀` and the chart `c₀` of
`ℙ¹` at `0`, the inclusion `(y, t) ↦ (e⁻¹ y, c₀⁻¹ t)` lifts through `μ` to a holomorphic `Γ`
(`LSC.exists_strictLift`), and `s_τ(e⁻¹ y) = Γ(y, c₀ τ)` (injectivity of `μ` off the centre).
On a compact box `|y - e x₀| ≤ R`, `|t - c₀ 0| ≤ R`, the coefficients of `Θⁿ` at `Γ(y, t)` and the
derivative of `Γ` are bounded, so by `topFormMeasure_image_le`
`∫_{e⁻¹(V)} (s_τ^*Θ)ⁿ ≤ M · vol(V)` for every measurable `V` in the box, uniformly in `τ`.
Near `q` the central fibre is `ι(X)`, and `e(ι⁻¹ K)` is Lebesgue null when `ι⁻¹ K` is
pluripolar; by outer regularity it has an open neighbourhood `V` of volume `< ε / M`
(`strict_local`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN.FL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.TranscendentalWN.LSC

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **`tok-wn-fl2:strict-local`**: near a point of `X₀ \ ℰ`, every `K ⊆ X₀` with `ι⁻¹(K)`
pluripolar has open neighbourhoods with arbitrarily small fibre volumes. -/
theorem strict_local (hμ : IsNormalConeDeformation F μ) (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    {ι : F.carrier → 𝒳} (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) {K : Set 𝒳}
    (hK : K ⊆ centralFibre F μ) (hKι : ManifoldLocallyPluripolar (n := m + 1) (ι ⁻¹' K))
    {q : 𝒳} (hq : q ∈ centralFibre F μ) (hqE : q ∉ exceptionalSet F μ) :
    ∃ O : Set 𝒳, IsOpen O ∧ q ∈ O ∧ ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ U : Set 𝒳, IsOpen U ∧ K ∩ O ⊆ U ∧ FibreSmall F μ Θ U ε := by
  classical
  have hμc : Continuous μ := hμ.continuous
  set x₀ : F.carrier := (μ q).1 with hx₀def
  have hq0 : (μ q).2 = projectiveZero := (mem_centralBase_iff F).mp hq
  have hx₀ : x₀ ∉ F.flag (1 : Fin (m + 2)) := fun h =>
    hqE ((mem_deformationCentre_iff F).mpr ⟨h, hq0⟩)
  set e : ComplexChart (m + 1) F.carrier := complexChartAt x₀ with he
  set c₀ := chartAt (ComplexModel 1) projectiveZero with hc₀
  set L := splitEquiv m with hL
  set SD := strictDomain F x₀ with hSD
  obtain ⟨ℓ, hℓ, hμℓ⟩ := exists_strictLift F hμ x₀
  have hx₀e : x₀ ∈ e.val.source := mem_complexChartAt_source x₀
  have h0c : projectiveZero ∈ c₀.source := mem_chart_source _ _
  set y₀ : ComplexModel (m + 1) := e.val x₀ with hy₀
  set t₀ : ComplexModel 1 := c₀ projectiveZero with ht₀
  have hLL : ∀ p, L.symm (L p) = p := fun p => L.symm_apply_apply p
  have hw₀ : L (y₀, t₀) ∈ SD := by
    rw [mem_strictDomain, hLL]
    refine ⟨e.val.map_source hx₀e, ?_, c₀.map_source h0c⟩
    show e.val.symm (e.val x₀) ∉ _
    rw [e.val.left_inv hx₀e]
    exact hx₀
  set p₀ : LiftedOpen.{u} SD := LiftedOpen.mk SD (L (y₀, t₀)) hw₀
  set Γ : ComplexModel (m + 1 + 1) → 𝒳 := fun w => ℓ (liftMk SD p₀ w) with hΓ
  have hΓμ : ∀ w ∈ SD, μ (Γ w) = (e.val.symm (L.symm w).1, c₀.symm (L.symm w).2) := by
    intro w hw
    have h := congrFun hμℓ (liftMk SD p₀ w)
    simp only [Function.comp] at h
    rw [hΓ, h, strictInclusion, toModel_liftMk p₀ hw, chartAt_prod, prodChart_symm_apply]
    rfl
  have hΓnot : ∀ w ∈ SD, μ (Γ w) ∉ deformationCentre F := by
    intro w hw h
    rw [hΓμ w hw] at h
    exact ((mem_strictDomain F).mp hw).2.1 ((mem_deformationCentre_iff F).mp h).1
  have hΓsm : ∀ w ∈ SD,
      ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ w :=
    fun w hw => (hℓ _).comp w (contMDiffAt_liftMk p₀ hw)
  have hΓc : ContinuousOn Γ SD := fun w hw => (hΓsm w hw).continuousAt.continuousWithinAt
  have hΓq : Γ (L (y₀, t₀)) = q := by
    refine (eq_of_map_eq_of_notMem F hμ (hΓnot _ hw₀) ?_)
    rw [hΓμ _ hw₀, hLL]
    simp only [hy₀, ht₀, e.val.left_inv hx₀e, c₀.left_inv h0c]
    exact Prod.ext rfl hq0.symm
  -- the chart of `𝒳` and the good set
  set d : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt q with hd
  have hqd : q ∈ d.val.source := mem_complexChartAt_source _
  set G : Set (ComplexModel (m + 1 + 1)) := SD ∩ Γ ⁻¹' d.val.source with hG
  have hGo : IsOpen G := hΓc.isOpen_inter_preimage SD.isOpen d.val.open_source
  set G' : Set (ComplexModel (m + 1) × ComplexModel 1) := L ⁻¹' G with hG'
  have hG'o : IsOpen G' := hGo.preimage L.continuous
  have hp₀G' : (y₀, t₀) ∈ G' := ⟨hw₀, by simp only [mem_preimage]; rw [hΓq]; exact hqd⟩
  obtain ⟨R, hR, hbox⟩ := exists_closedBall_prod_subset hG'o hp₀G'
  set Kc := closedBall y₀ R ×ˢ closedBall t₀ R with hKc
  have hKcc : IsCompact Kc := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  -- the coordinate expression and its bounds
  set F₁ : ComplexModel (m + 1) × ComplexModel 1 → ComplexModel (m + 1 + 1) :=
    fun p => d.val (Γ (L p)) with hF₁
  have hF₁sm : ∀ p ∈ G', ContDiffAt ℝ ∞ F₁ p := fun p hp =>
    ((contDiffAt_chart_comp (hΓsm _ hp.1) d hp.2).restrict_scalars ℝ).comp p
      (L.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_fderiv hG'o hF₁sm hKcc hbox
  have hF₁c : ContinuousOn F₁ Kc := fun p hp => (hF₁sm p (hbox hp)).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_comp hKcc hF₁c
    (fun p hp => d.val.map_source (hbox hp).2) ((formPow Θ.val (m + 1)).smooth d).continuousOn
  set M : ℝ := max (C₁ * C₂ ^ (2 * (m + 1))) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  -- the neighbourhoods
  set Ob : Set (F.carrier × ProjectiveLine) := (e.val.source ∩ e.val ⁻¹' ball y₀ R) ×ˢ
    (c₀.source ∩ c₀ ⁻¹' ball t₀ R) with hOb
  have hObo : IsOpen Ob :=
    (e.val.isOpen_inter_preimage isOpen_ball).prod (c₀.isOpen_inter_preimage isOpen_ball)
  have hqOb : μ q ∈ Ob := by
    refine ⟨⟨hx₀e, mem_ball_self hR⟩, ?_⟩
    rw [hq0]
    exact ⟨h0c, mem_ball_self hR⟩
  refine ⟨μ ⁻¹' Ob, hObo.preimage hμc, hqOb, fun ε hε => ?_⟩
  -- the null set of bad coordinates and its small neighbourhood
  set B : Set (ComplexModel (m + 1)) := e.val.target ∩ e.val.symm ⁻¹' (ι ⁻¹' K) with hB
  have hB0 : volume B = 0 := by
    have h := (hKι e).measure_inter_eq_zero e.val.open_target volume
    exact measure_mono_null (fun y (hy : y ∈ B) =>
      (⟨hy, hy.1⟩ : y ∈ pluripolarChartSet (ι ⁻¹' K) e ∩ e.val.target)) h
  obtain ⟨V₀, hBV₀, hV₀o, hV₀⟩ := Set.exists_isOpen_lt_of_lt B (ε / ENNReal.ofReal M)
    (by rw [hB0]; exact div_ofReal_pos hε)
  set V : Set (ComplexModel (m + 1)) := V₀ ∩ ball y₀ R with hV
  have hVo : IsOpen V := hV₀o.inter isOpen_ball
  set Ub : Set (F.carrier × ProjectiveLine) := (e.val.source ∩ e.val ⁻¹' V) ×ˢ
    (c₀.source ∩ c₀ ⁻¹' ball t₀ R) with hUb
  have hUbo : IsOpen Ub :=
    (e.val.isOpen_inter_preimage hVo).prod (c₀.isOpen_inter_preimage isOpen_ball)
  refine ⟨μ ⁻¹' Ub, hUbo.preimage hμc, ?_, ?_⟩
  · -- `K ∩ O ⊆ U`
    rintro z ⟨hzK, hzO⟩
    have hz0 : (μ z).2 = projectiveZero := (mem_centralBase_iff F).mp (hK hzK)
    set x := (μ z).1 with hx
    have hxe : x ∈ e.val.source := hzO.1.1
    have hxb : e.val x ∈ ball y₀ R := hzO.1.2
    have hxG : (e.val x, t₀) ∈ G' := hbox ⟨ball_subset_closedBall hxb, mem_closedBall_self hR.le⟩
    have hxZ : x ∉ F.flag (1 : Fin (m + 2)) := by
      have := ((mem_strictDomain F).mp hxG.1).2.1
      rw [hLL] at this
      change e.val.symm (e.val x) ∉ _ at this
      rwa [e.val.left_inv hxe] at this
    have hzι : z = ι x := by
      have hnot : μ z ∉ deformationCentre F := fun h => hxZ ((mem_deformationCentre_iff F).mp h).1
      refine eq_of_map_eq_of_notMem F hμ hnot ?_
      rw [hμι]
      exact Prod.ext rfl hz0
    have hxB : e.val x ∈ B := by
      refine ⟨e.val.map_source hxe, ?_⟩
      show ι (e.val.symm (e.val x)) ∈ K
      rw [e.val.left_inv hxe, ← hzι]
      exact hzK
    refine ⟨⟨hxe, hBV₀ hxB, hxb⟩, ?_⟩
    rw [hz0]
    exact ⟨h0c, mem_ball_self hR⟩
  · -- the fibre volumes
    obtain ⟨r, hr, hrτ⟩ := exists_radius_chart R hR
    refine ⟨r, hr, fun τ hτ hτr s hs hsμ => ?_⟩
    let _ : MeasurableSpace F.carrier := borel F.carrier
    have _ : BorelSpace F.carrier := ⟨rfl⟩
    set p := affineLinePoint τ with hp
    obtain ⟨hpc, hpb⟩ := hrτ τ hτr
    set t : ComplexModel 1 := c₀ p with ht
    have hyt : ∀ y ∈ ball y₀ R, (y, t) ∈ G' := fun y hy =>
      hbox ⟨ball_subset_closedBall hy, ball_subset_closedBall hpb⟩
    have hyT : ∀ y ∈ ball y₀ R, y ∈ e.val.target := by
      intro y hy
      have := ((mem_strictDomain F).mp (hyt y hy).1).1
      rwa [hLL] at this
    have hsub : s ⁻¹' (μ ⁻¹' Ub) ⊆ e.val.symm '' V := by
      intro x hx
      have hx' : μ (s x) ∈ Ub := hx
      rw [hsμ x] at hx'
      exact ⟨e.val x, hx'.1.2, e.val.left_inv hx'.1.1⟩
    refine (measure_mono hsub).trans ?_
    refine le_trans ?_ (ofReal_mul_le_of_lt_div hM1
      ((measure_mono (inter_subset_left : V ⊆ V₀)).trans_lt hV₀))
    refine topFormMeasure_image_le F.omega hs Θ e d isOpen_ball
      (γ := e.val.symm) (g := fun y => Γ (L (y, t))) (fun y hy => ?_) (fun y hy => ?_)
      (fun y hy => ?_) (fun y hy => (hyt y hy).2) hVo.measurableSet inter_subset_right
      (e.val.symm.injOn.mono fun y hy => by
        rw [OpenPartialHomeomorph.symm_source]
        exact hyT y hy.2) (fun y hy => ?_)
    · exact contMDiffOn_chart_symm.contMDiffAt (e.val.open_target.mem_nhds (hyT y hy))
    · exact e.val.map_target (hyT y hy)
    · -- `s_τ(e⁻¹ y) = Γ(y, t)`
      have hG := (hyt y hy).1
      refine (eq_of_map_eq_of_notMem F hμ (hΓnot _ hG) ?_).symm
      rw [hΓμ _ hG, hLL, hsμ, c₀.left_inv hpc]
    · -- the bound of the integrand
      have hyK : (y, t) ∈ Kc := ⟨ball_subset_closedBall hy.2, ball_subset_closedBall hpb⟩
      have h1 : ‖(formPow Θ.val (m + 1)).coeff d (d.val (Γ (L (y, t))))‖ ≤ C₁ := hC₁ _ hyK
      have h2 : ‖fderiv ℝ (fun y => d.val (Γ (L (y, t)))) y‖ ≤ C₂ :=
        (norm_fderiv_left_le (f := F₁)
          ((hF₁sm _ (hbox hyK)).differentiableAt (by simp))).trans (hC₂ _ hyK)
      calc ‖(formPow Θ.val (m + 1)).coeff d (d.val (Γ (L (y, t))))‖ *
            ‖fderiv ℝ (fun y => d.val (Γ (L (y, t)))) y‖ ^ (2 * (m + 1))
          ≤ C₁ * C₂ ^ (2 * (m + 1)) := by gcongr
        _ ≤ M := le_max_left _ _

end SGPT.Okounkov.TranscendentalWN.FL2

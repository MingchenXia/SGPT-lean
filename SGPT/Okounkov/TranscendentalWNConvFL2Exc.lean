import SGPT.Okounkov.TranscendentalWNConvFL2Small
import SGPT.Okounkov.TranscendentalWNKeyLSCExcLocal

/-!
# Small fibre volumes near `ℰ \ X'`

Blueprint `claude-tok-wn-fl2`, node `tok-wn-fl2:exc-local`; source WN21 §7, estimate (eqeq)
(`references/wn21-restricted-volume`).

Let `q ∈ ℰ \ X'`.  The monomial chart data `ExcChart` and the fibre coordinates `SliceCoords`
of lane WN-LSC give `Γ(t, y) = ℓ_j(Λ(t, y))` with `τ(μ(Γ(t, y))) - τ(0) = t`, `Γ(0, ·)`
parametrizing `ℰ` near `q` and a left inverse `z ↦ (t(z), ν(W z))`.  For `τ ≠ 0` the fibre
`X_τ` is parametrized near `q` by `y ↦ π_X(μ(Γ(t, y)))`, with `s_τ ∘ γ_t = Γ(t, ·)`; on a compact
box the coefficients of `Θⁿ` and `∂_y Γ` are bounded, so `topFormMeasure_image_le` gives
`∫_{γ_t(V)} (s_τ^*Θ)ⁿ ≤ M · vol(V)`.  The trace of `K ⊆ X₀` near `q` lies in `ℰ = {t = 0}`, and
its coordinate set `{y : Γ(0, y) ∈ K}` is the image of the chart set of the pluripolar
`K ∩ ℰ` under the smooth map `ζ ↦ ν(W(ζ))`, hence Lebesgue null; by outer regularity it has an
open neighbourhood of volume `< ε / M` (`exc_local`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN.FL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN
open SGPT.Okounkov.TranscendentalWN.LSC

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **`tok-wn-fl2:exc-local`**: near a point of `ℰ \ X'`, every `K ⊆ X₀` with `K ∩ ℰ`
pluripolar in `ℰ` has open neighbourhoods with arbitrarily small fibre volumes. -/
theorem exc_local (hμ : IsNormalConeDeformation F μ) (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    {K : Set 𝒳} (hK : K ⊆ centralFibre F μ)
    (hKE : letI := exceptionalChartedSpace F hμ
      haveI := isComplexManifold_exceptional F hμ
      ManifoldLocallyPluripolar (n := m + 1) ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' K))
    {q : 𝒳} (hqE : q ∈ exceptionalSet F μ) (hqX : q ∉ strictCentralFibre F μ) :
    ∃ O : Set 𝒳, IsOpen O ∧ q ∈ O ∧ ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ U : Set 𝒳, IsOpen U ∧ K ∩ O ⊆ U ∧ FibreSmall F μ Θ U ε := by
  classical
  let _ := exceptionalChartedSpace F hμ
  have _ := isComplexManifold_exceptional F hμ
  have hμc : Continuous μ := hμ.continuous
  obtain ⟨C⟩ := nonempty_excChart F hμ hqE
  obtain ⟨S⟩ := SliceCoords.nonempty C hqE hqX
  set D := monomialDomain C.Ψ m C.j with hD
  have hWqD : C.W q ∈ D := C.W_mem_monomialDomain C.hqO
  set p₀ : LiftedOpen.{u} D := LiftedOpen.mk D (C.W q) hWqD with hp₀
  set Γ : ComplexModel 1 × ComplexModel (m + 1) → 𝒳 := fun p => C.ℓ (liftMk D p₀ (S.Λ p))
    with hΓ
  set c₀ := zeroChart with hc₀
  set c : ComplexModel 1 := c₀ projectiveZero with hc
  have h0c : projectiveZero ∈ c₀.source := mem_chart_source _ _
  have hq0 : (μ q).2 = projectiveZero := ((mem_deformationCentre_iff F).mp hqE).2
  have hτq : ((splitL m).symm (monomial m C.j (C.W q))).2 = 0 := by
    rw [C.tau_eq C.hqO, hq0, sub_self]
  obtain ⟨hP₀G, hΛq⟩ := S.hΛν q S.hqO' 0 hτq
  set y₀ : ComplexModel (m + 1) := S.ν (C.W q) with hy₀
  have hΓq : Γ (0, y₀) = q := by
    simp only [hΓ]
    rw [hΛq]
    exact C.ℓ_W C.hqO
  -- the domain of the fibre coordinates
  set G₀ : Set (ComplexModel 1 × ComplexModel (m + 1)) := S.G ∩ S.Λ ⁻¹' D with hG₀
  have hΛc : ContinuousOn S.Λ S.G := fun p hp => (S.hΛ p hp).continuousAt.continuousWithinAt
  have hG₀o : IsOpen G₀ := hΛc.isOpen_inter_preimage S.hG D.isOpen
  have hΓsm : ∀ p ∈ G₀, ContMDiffAt 𝓘(ℂ, ComplexModel 1 × ComplexModel (m + 1))
      𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ p := fun p hp =>
    (C.hℓ _).comp p ((contMDiffAt_liftMk p₀ hp.2).comp p (S.hΛ p hp.1).contMDiffAt)
  have hΓc : ContinuousOn Γ G₀ := fun p hp => (hΓsm p hp).continuousAt.continuousWithinAt
  have hΓW : ∀ p ∈ G₀, Γ p ∈ C.O → C.W (Γ p) = S.Λ p := fun p hp hO => C.W_ℓ hp.2 hO
  -- the fibre coordinate of `Γ(t, y)` is `t`
  have hΓτ : ∀ p ∈ G₀, (μ (Γ p)).2 ∈ c₀.source ∧ c₀ (μ (Γ p)).2 = p.1 + c := by
    intro p hp
    have hf := C.μ_ℓ_mem_flatDomain (liftMk D p₀ (S.Λ p))
    have h1 := C.hΨτ _ hf
    rw [C.μ_ℓ, C.flat_monomialChart, toModel_liftMk p₀ hp.2, S.hτΛ p hp.1] at h1
    have hsrc : (μ (Γ p)).2 ∈ c₀.source := by
      have := hf.1
      simp only [chartAt_prod, prodChart_source, mem_prod] at this
      exact this.2
    refine ⟨hsrc, ?_⟩
    rw [C.μ_ℓ] at hsrc ⊢
    rw [h1, sub_add_cancel]
  -- the base point of `Γ(t, y)` lies in the chart of `X` at `x₀`
  set eX : ComplexChart (m + 1) F.carrier := complexChartAt C.x₀ with heX
  have hΓX : ∀ p ∈ G₀, (μ (Γ p)).1 ∈ eX.val.source := by
    intro p _
    have := (C.μ_ℓ_mem_flatDomain (liftMk D p₀ (S.Λ p))).1
    simp only [chartAt_prod, prodChart_source, mem_prod] at this
    exact this.1
  -- `Γ(0, y) ∈ ℰ`
  have hΓE : ∀ y, ((0 : ComplexModel 1), y) ∈ G₀ → Γ (0, y) ∈ C.O →
      Γ (0, y) ∈ exceptionalSet F μ := by
    intro y hy hO
    rw [C.mem_exceptional_iff hO, hΓW _ hy hO]
    exact S.hΛE y hy.1
  -- the chart of `ℰ` at `q`
  set qE : exceptionalSet F μ := ⟨q, hqE⟩ with hqEdef
  set eE : ComplexChart (m + 1) (exceptionalSet F μ) := complexChartAt qE with heE
  obtain ⟨UE, hUEo, hUE⟩ := isOpen_induced_iff.mp eE.val.open_source
  -- the chart of `𝒳` and the good set
  set d : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt q with hd
  have hqd : q ∈ d.val.source := mem_complexChartAt_source _
  set G₁ : Set (ComplexModel 1 × ComplexModel (m + 1)) :=
    G₀ ∩ Γ ⁻¹' (d.val.source ∩ S.O' ∩ UE) with hG₁
  have hG₁o : IsOpen G₁ :=
    hΓc.isOpen_inter_preimage hG₀o ((d.val.open_source.inter S.hO').inter hUEo)
  have hP₀ : ((0 : ComplexModel 1), y₀) ∈ G₁ := by
    refine ⟨⟨hP₀G, show S.Λ (0, y₀) ∈ D by rw [hΛq]; exact hWqD⟩, ?_⟩
    simp only [mem_preimage, hΓq]
    refine ⟨⟨hqd, S.hqO'⟩, ?_⟩
    have : qE ∈ Subtype.val ⁻¹' UE := by rw [hUE]; exact mem_complexChartAt_source qE
    exact this
  obtain ⟨R, hR, hbox⟩ := exists_closedBall_prod_subset hG₁o hP₀
  set Kc := closedBall (0 : ComplexModel 1) R ×ˢ closedBall y₀ R with hKc
  have hKcc : IsCompact Kc := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  -- the coordinate expression and its bounds
  set F₁ : ComplexModel 1 × ComplexModel (m + 1) → ComplexModel (m + 1 + 1) :=
    fun p => d.val (Γ p) with hF₁
  have hF₁sm : ∀ p ∈ G₁, ContDiffAt ℝ ∞ F₁ p := fun p hp =>
    (contDiffAt_chart_comp' (hΓsm p hp.1) d hp.2.1.1).restrict_scalars ℝ
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_fderiv hG₁o hF₁sm hKcc hbox
  have hF₁c : ContinuousOn F₁ Kc := fun p hp => (hF₁sm p (hbox hp)).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_comp hKcc hF₁c
    (fun p hp => d.val.map_source (hbox hp).2.1.1) ((formPow Θ.val (m + 1)).smooth d).continuousOn
  set M : ℝ := max (C₁ * C₂ ^ (2 * (m + 1))) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  -- the coordinates of points of `O' ⊆ O`
  set νW : 𝒳 → ComplexModel (m + 1) := fun z => S.ν (C.W z) with hνW
  have hνWc : ContinuousOn νW S.O' := fun z hz =>
    (S.ν.continuous.continuousAt.comp (C.hW _ (S.hO'O hz)).continuousAt).continuousWithinAt
  have hcoord : ∀ z ∈ S.O', (μ z).2 ∈ c₀.source →
      (c₀ (μ z).2 - c, νW z) ∈ S.G ∧ Γ (c₀ (μ z).2 - c, νW z) = z := by
    intro z hz _
    have hτz := C.tau_eq (S.hO'O hz)
    obtain ⟨hG, hΛ⟩ := S.hΛν z hz _ hτz
    refine ⟨hG, ?_⟩
    simp only [hΓ]
    rw [hΛ]
    exact C.ℓ_W (S.hO'O hz)
  -- the neighbourhood
  set Oτ : Set 𝒳 := μ ⁻¹' (univ ×ˢ (c₀.source ∩ c₀ ⁻¹' ball c R)) with hOτ
  have hOτo : IsOpen Oτ :=
    (isOpen_univ.prod (c₀.isOpen_inter_preimage isOpen_ball)).preimage hμc
  set O : Set 𝒳 := (S.O' ∩ νW ⁻¹' ball y₀ R) ∩ Oτ with hO
  have hOo : IsOpen O := (hνWc.isOpen_inter_preimage S.hO' isOpen_ball).inter hOτo
  have hqO : q ∈ O := by
    refine ⟨⟨S.hqO', mem_ball_self hR⟩, mem_univ _, ?_⟩
    rw [hq0]
    exact ⟨h0c, mem_ball_self hR⟩
  have hOcoord : ∀ z ∈ O, (c₀ (μ z).2 - c, νW z) ∈ Kc ∧ Γ (c₀ (μ z).2 - c, νW z) = z := by
    intro z hz
    refine ⟨⟨?_, ball_subset_closedBall hz.1.2⟩, (hcoord z hz.1.1 hz.2.2.1).2⟩
    rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact (mem_ball.mp hz.2.2.2).le
  refine ⟨O, hOo, hqO, fun ε hε => ?_⟩
  /- ### The null set of bad coordinates -/
  set B : Set (ComplexModel (m + 1)) := ball y₀ R ∩ {y | Γ (0, y) ∈ K} with hB
  set τE : ComplexModel (m + 1) → ComplexModel (m + 1) := fun ζ => νW (eE.val.symm ζ).1
    with hτE
  set DE : Set (ComplexModel (m + 1)) :=
    eE.val.target ∩ (fun ζ => (eE.val.symm ζ).1) ⁻¹' S.O' with hDE
  have hτEd : DifferentiableOn ℝ τE DE := by
    intro ζ hζ
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
        eE.val.symm ζ :=
      contMDiffOn_chart_symm.contMDiffAt (eE.val.open_target.mem_nhds hζ.1)
    have h2 := (contMDiff_exceptionalInclusion F hμ _).comp ζ h1
    have h3 := (C.hW _ (S.hO'O hζ.2)).comp ζ h2
    exact ((contMDiffAt_iff_contDiffAt.mp (S.ν.contMDiff.contMDiffAt.comp ζ h3)).differentiableAt
      (by simp)).restrictScalars ℝ |>.differentiableWithinAt
  set P : Set (ComplexModel (m + 1)) :=
    pluripolarChartSet ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' K) eE ∩ DE with hP
  have hP0 : volume P = 0 := by
    have h := (hKE eE).measure_inter_eq_zero eE.val.open_target volume
    exact measure_mono_null (fun ζ (hζ : ζ ∈ P) => (⟨hζ.1, hζ.2.1⟩ :
      ζ ∈ pluripolarChartSet ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' K) eE ∩
        eE.val.target)) h
  have hBP : B ⊆ τE '' P := by
    rintro y ⟨hyb, hyK⟩
    have hyG : ((0 : ComplexModel 1), y) ∈ G₁ :=
      hbox ⟨mem_closedBall_self hR.le, ball_subset_closedBall hyb⟩
    have hzO : Γ (0, y) ∈ C.O := S.hO'O hyG.2.1.2
    set z : exceptionalSet F μ := ⟨Γ (0, y), hΓE y hyG.1 hzO⟩ with hz
    have hzs : z ∈ eE.val.source := by
      rw [← hUE]
      exact hyG.2.2
    refine ⟨eE.val z, ⟨⟨eE.val.map_source hzs, ?_⟩, eE.val.map_source hzs, ?_⟩, ?_⟩
    · show (eE.val.symm (eE.val z)).1 ∈ K
      rw [eE.val.left_inv hzs]
      exact hyK
    · show (eE.val.symm (eE.val z)).1 ∈ S.O'
      rw [eE.val.left_inv hzs]
      exact hyG.2.1.2
    · show νW (eE.val.symm (eE.val z)).1 = y
      rw [eE.val.left_inv hzs]
      show S.ν (C.W (Γ (0, y))) = y
      rw [hΓW _ hyG.1 hzO, S.hνΛ _ hyG.1.1]
  have hB0 : volume B = 0 :=
    measure_mono_null hBP (MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume (hτEd.mono inter_subset_right) hP0)
  obtain ⟨V₀, hBV₀, hV₀o, hV₀⟩ := Set.exists_isOpen_lt_of_lt B (ε / ENNReal.ofReal M)
    (by rw [hB0]; exact div_ofReal_pos hε)
  set V : Set (ComplexModel (m + 1)) := V₀ ∩ ball y₀ R with hV
  have hVo : IsOpen V := hV₀o.inter isOpen_ball
  set U : Set 𝒳 := O ∩ νW ⁻¹' V₀ with hU
  have hUo : IsOpen U := by
    have h := hνWc.isOpen_inter_preimage S.hO' hV₀o
    have : U = (S.O' ∩ νW ⁻¹' V₀) ∩ O := by
      ext z
      simp only [hU, hO, mem_inter_iff, mem_preimage]
      tauto
    rw [this]
    exact h.inter hOo
  refine ⟨U, hUo, ?_, ?_⟩
  · -- `K ∩ O ⊆ U`
    rintro z ⟨hzK, hzO⟩
    have hz0 : (μ z).2 = projectiveZero := (mem_centralBase_iff F).mp (hK hzK)
    obtain ⟨-, hΓz⟩ := hOcoord z hzO
    rw [hz0, sub_self] at hΓz
    refine ⟨hzO, hBV₀ ⟨hzO.1.2, ?_⟩⟩
    show Γ (0, νW z) ∈ K
    rw [hΓz]
    exact hzK
  · -- the fibre volumes
    obtain ⟨r, hr, hrτ⟩ := exists_radius_chart R hR
    refine ⟨r, hr, fun τ hτ hτr s hs hsμ => ?_⟩
    let _ : MeasurableSpace F.carrier := borel F.carrier
    have _ : BorelSpace F.carrier := ⟨rfl⟩
    set p := affineLinePoint τ with hp
    have hp0 : p ≠ projectiveZero := affineLinePoint_ne_projectiveZero hτ
    obtain ⟨hpc, hpb⟩ := hrτ τ hτr
    set t : ComplexModel 1 := c₀ p - c with ht
    have htK : t ∈ closedBall (0 : ComplexModel 1) R := by
      rw [mem_closedBall, dist_zero_right, ht, ← dist_eq_norm]
      exact (mem_ball.mp hpb).le
    have hyt : ∀ y ∈ ball y₀ R, (t, y) ∈ G₁ := fun y hy => hbox ⟨htK, ball_subset_closedBall hy⟩
    set γ : ComplexModel (m + 1) → F.carrier := fun y => (μ (Γ (t, y))).1 with hγ
    -- `μ(Γ(t, y))` lies over `p`
    have hΓp : ∀ y ∈ ball y₀ R, (μ (Γ (t, y))).2 = p := by
      intro y hy
      obtain ⟨hsrc, heq⟩ := hΓτ _ (hyt y hy).1
      refine c₀.injOn hsrc hpc ?_
      rw [heq, ht, sub_add_cancel]
    have hsΓ : ∀ y ∈ ball y₀ R, s (γ y) = Γ (t, y) := by
      intro y hy
      have hnot : μ (Γ (t, y)) ∉ deformationCentre F := fun h =>
        hp0 ((hΓp y hy).symm.trans ((mem_deformationCentre_iff F).mp h).2)
      refine (eq_of_map_eq_of_notMem F hμ hnot ?_).symm
      rw [hsμ]
      exact Prod.ext rfl (hΓp y hy)
    have hsub : s ⁻¹' U ⊆ γ '' V := by
      intro x hx
      have hxU : s x ∈ U := hx
      obtain ⟨hcK, hΓx⟩ := hOcoord (s x) hxU.1
      rw [hsμ x] at hΓx
      refine ⟨νW (s x), ⟨hxU.2, hxU.1.1.2⟩, ?_⟩
      show (μ (Γ (t, νW (s x)))).1 = x
      rw [ht, hΓx, hsμ x]
    refine (measure_mono hsub).trans ?_
    refine le_trans ?_ (ofReal_mul_le_of_lt_div hM1
      ((measure_mono (inter_subset_left : V ⊆ V₀)).trans_lt hV₀))
    refine topFormMeasure_image_le F.omega hs Θ eX d isOpen_ball (γ := γ)
      (g := fun y => Γ (t, y)) (fun y hy => ?_) (fun y hy => hΓX _ (hyt y hy).1)
      hsΓ (fun y hy => (hyt y hy).2.1.1) hVo.measurableSet inter_subset_right ?_
      (fun y hy => ?_)
    · have hin : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1))
          𝓘(ℂ, ComplexModel 1 × ComplexModel (m + 1)) ∞ (fun y => (t, y)) y :=
        (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
      have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
          (fun y => Γ (t, y)) y :=
        ContMDiffAt.comp (g := Γ) y (hΓsm _ (hyt y hy).1) hin
      exact ProductComplexManifold.contMDiff_fst.contMDiffAt.comp y
        ((hμ.contMDiff.contMDiffAt).comp y h1)
    · -- injectivity
      intro y hy y' hy' h
      have h1 : Γ (t, y) = Γ (t, y') := by
        rw [← hsΓ y hy.2, ← hsΓ y' hy'.2, h]
      have h2 : S.Λ (t, y) = S.Λ (t, y') := by
        rw [← hΓW _ (hyt y hy.2).1 (S.hO'O (hyt y hy.2).2.1.2),
          ← hΓW _ (hyt y' hy'.2).1 (S.hO'O (hyt y' hy'.2).2.1.2), h1]
      have h3 := congrArg S.ν h2
      rwa [S.hνΛ _ (hyt y hy.2).1.1, S.hνΛ _ (hyt y' hy'.2).1.1] at h3
    · -- the bound of the integrand
      have hyK : (t, y) ∈ Kc := ⟨htK, ball_subset_closedBall hy.2⟩
      have h1 : ‖(formPow Θ.val (m + 1)).coeff d (d.val (Γ (t, y)))‖ ≤ C₁ := hC₁ _ hyK
      have h2 : ‖fderiv ℝ (fun y => d.val (Γ (t, y))) y‖ ≤ C₂ :=
        (norm_fderiv_right_le (f := F₁)
          ((hF₁sm _ (hbox hyK)).differentiableAt (by simp))).trans (hC₂ _ hyK)
      calc ‖(formPow Θ.val (m + 1)).coeff d (d.val (Γ (t, y)))‖ *
            ‖fderiv ℝ (fun y => d.val (Γ (t, y))) y‖ ^ (2 * (m + 1))
          ≤ C₁ * C₂ ^ (2 * (m + 1)) := by gcongr
        _ ≤ M := le_max_left _ _

end SGPT.Okounkov.TranscendentalWN.FL2

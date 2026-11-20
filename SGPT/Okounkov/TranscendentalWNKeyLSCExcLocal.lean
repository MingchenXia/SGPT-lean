import SGPT.Okounkov.TranscendentalWNKeyLSCSlice

/-!
# Convergence of the fibre masses near `ℰ \ X'` (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-key`, node `tok-wn-key:fibre-limit-exceptional`, and `claude-tok-wn-lsc`,
node `tok-wn-lsc:exc-local`; source WN21 §5.

Let `q ∈ ℰ \ X'` with `φ(q) ≠ -∞`, and `Γ(t, y) = ℓ_j(Λ(t, y))` the fibre coordinates of
`SliceCoords` (`τ(μ(Γ(t, y))) - τ(0) = t`, `Γ(0, ·)` parametrizing `ℰ` near `q`).  With a local
potential `ρ` of `Θ` near `q`, `H(t, y) = φ(Γ(t, y)) + ρ(Γ(t, y))` is jointly smooth near
`(0, y_q)`.  The non-pluripolar measures are computed in these coordinates
(`globalMixedMeasure_image_eq_lintegral`):

* on `ℰ`, through the biholomorphism `y ↦ Γ(0, y)` (inverse `z ↦ ν(W z)`),
  `⟨(T|_ℰ)ⁿ⟩(Γ(0, T)) = ∫_T (dd^c H(0, ·))ⁿ`;
* on `X`, for `τ ≠ 0`, through `γ_t : y ↦ π_X(μ(Γ(t, y)))`, a biholomorphism onto an open set of `X`
  (inverse `x ↦ ν(W(s_τ x))`, `s_τ ∘ γ_t = Γ(t, ·)`),
  `⟨(T|_{X_τ})ⁿ⟩(γ_t(T)) = ∫_T (dd^c H(t, ·))ⁿ`, `t = τ - τ(0)`.

Fatou's lemma then gives `exc_local_transportGood`: every compact set in a neighbourhood `N` of
`q` in `ℰ` is good for the transport to the fibres (`TransportGood`), the transported sets being
`γ_t(T)`, which `s_τ` maps into any given neighbourhood of `K` for small `τ` (tube lemma).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN.LSC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN

/-- A holomorphic map from a normed space, read in a chart of the target. -/
theorem contDiffAt_chart_comp' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y]
    {f : E → Y} {w : E} (hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ComplexModel N) ∞ f w)
    (d : ComplexChart N Y) (hw : f w ∈ d.val.source) : ContDiffAt ℂ ∞ (fun z => d.val (f z)) w := by
  have hd : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ d.val (f w) :=
    (contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas d.property)).contMDiffAt
      (d.val.open_source.mem_nhds hw)
  exact contMDiffAt_iff_contDiffAt.mp (hd.comp w hf)

/-- The image of a measurable set of a chart target under the inverse chart, through a
biholomorphic pair, is the image of the parametrization. -/
theorem chart_symm_image_image {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] (e : ComplexChart k V) {g : ComplexModel k → V}
    {T : Set (ComplexModel k)} (hg : ∀ y ∈ T, g y ∈ e.val.source) :
    e.val.symm '' ((fun y => e.val (g y)) '' T) = g '' T := by
  rw [image_image]
  exact image_congr fun y hy => e.val.left_inv (hg y hy)

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **`tok-wn-lsc:exc-local`** (WN21 §5, `tok-wn-key:fibre-limit-exceptional`): near every
`q ∈ ℰ \ X'` with `φ(q) ≠ -∞` there is an open `N ∋ q` of `ℰ` in which every compact set is good
for the transport of `⟨(T|_ℰ)ⁿ⟩` to the fibres `X_τ`. -/
theorem exc_local_transportGood (hμ : IsNormalConeDeformation F μ)
    [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳} {φ : 𝒳 → EReal}
    (hφ : φ ∈ TranscendentalCore.gentleCurrents Θ)
    {s : ProjectiveLine → F.carrier → 𝒳}
    (hs : ∀ p, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ (s p))
    (hsμ : ∀ p, p ≠ projectiveZero → ∀ x, μ (s p x) = (x, p)) :
    letI := exceptionalChartedSpace F hμ
    haveI := isComplexManifold_exceptional F hμ
    letI : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
    haveI : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
    haveI := compactSpace_exceptional F hμ
    ∀ q : exceptionalSet F μ, q.1 ∉ strictCentralFibre F μ → φ q.1 ≠ ⊥ →
      ∃ N : Set (exceptionalSet F μ), IsOpen N ∧ q ∈ N ∧ ∀ K ⊆ N, IsCompact K →
        TransportGood (l := 𝓝[≠] projectiveZero)
          (fibreMeasure (contMDiff_exceptionalInclusion F hμ) Θ φ hφ.1.1) Subtype.val s
          (fun p => fibreMeasure (hs p) Θ φ hφ.1.1) K := by
  intro q hqX hqφ
  classical
  let _ := exceptionalChartedSpace F hμ
  have _ := isComplexManifold_exceptional F hμ
  let _ : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  have _ : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  have _ := compactSpace_exceptional F hμ
  have hφp : ThetaPlurisubharmonic Θ.val φ := hφ.1.1
  set q₁ : 𝒳 := q.1 with hq₁
  have hqE : q₁ ∈ exceptionalSet F μ := q.2
  obtain ⟨C⟩ := nonempty_excChart F hμ hqE
  obtain ⟨S⟩ := SliceCoords.nonempty C hqE hqX
  set D := monomialDomain C.Ψ m C.j with hD
  have hWqD : C.W q₁ ∈ D := C.W_mem_monomialDomain C.hqO
  set p₀ : LiftedOpen.{u} D := LiftedOpen.mk D (C.W q₁) hWqD with hp₀
  set Γ : ComplexModel 1 × ComplexModel (m + 1) → 𝒳 := fun p => C.ℓ (liftMk D p₀ (S.Λ p))
    with hΓ
  set c₀ := zeroChart with hc₀
  set c : ComplexModel 1 := c₀ projectiveZero with hc
  have h0c : projectiveZero ∈ c₀.source := mem_chart_source _ _
  -- the fibre coordinate of `q` is `0`
  have hq0 : (μ q₁).2 = projectiveZero := ((mem_deformationCentre_iff F).mp hqE).2
  have hτq : ((splitL m).symm (monomial m C.j (C.W q₁))).2 = 0 := by
    rw [C.tau_eq C.hqO, hq0, sub_self]
  obtain ⟨hP₀G, hΛq⟩ := S.hΛν q₁ S.hqO' 0 hτq
  set y₀ : ComplexModel (m + 1) := S.ν (C.W q₁) with hy₀
  have hΓq : Γ (0, y₀) = q₁ := by
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
  -- `Γ(0, y) ∈ ℰ`
  have hΓE : ∀ y, ((0 : ComplexModel 1), y) ∈ G₀ → Γ (0, y) ∈ C.O →
      Γ (0, y) ∈ exceptionalSet F μ := by
    intro y hy hO
    rw [C.mem_exceptional_iff hO, hΓW _ hy hO]
    exact S.hΛE y hy.1
  -- charts and the local potential
  set d : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt q₁ with hd
  have hqd : q₁ ∈ d.val.source := mem_complexChartAt_source _
  obtain ⟨Wd, ρ, hρ0, hρ, hpsh⟩ := hφp d (d.val q₁) (d.val.map_source hqd)
  set eX : ComplexChart (m + 1) F.carrier := complexChartAt C.x₀ with heX
  have hqX₀ : (μ q₁).1 ∈ eX.val.source := by
    have := (C.hWμ q₁ C.hqO).1.1
    simp only [chartAt_prod, prodChart_source, mem_prod] at this
    exact this.1
  set eE : ComplexChart (m + 1) (exceptionalSet F μ) := complexChartAt q with heE
  have hqeE : q ∈ eE.val.source := mem_complexChartAt_source q
  obtain ⟨UE, hUEo, hUE⟩ := isOpen_induced_iff.mp eE.val.open_source
  set Oφ : Set 𝒳 := {z | φ z ≠ ⊥} with hOφ
  have hOφo : IsOpen Oφ := isOpen_ne_bot_of_gentle hφ
  -- the good set
  set V : Set 𝒳 := S.O' ∩ (d.val.source ∩ d.val ⁻¹' Wd) ∩ Oφ ∩ UE ∩
    (fun z => (μ z).1) ⁻¹' eX.val.source with hV
  have hVo : IsOpen V :=
    ((((S.hO'.inter (d.val.isOpen_inter_preimage hρ.1)).inter hOφo).inter hUEo).inter
      (eX.val.open_source.preimage (continuous_fst.comp hμ.contMDiff.continuous)))
  set G₁ := G₀ ∩ Γ ⁻¹' V with hG₁
  have hG₁o : IsOpen G₁ := hΓc.isOpen_inter_preimage hG₀o hVo
  have hP₀ : ((0 : ComplexModel 1), y₀) ∈ G₁ := by
    refine ⟨⟨hP₀G, show S.Λ (0, y₀) ∈ D by rw [hΛq]; exact hWqD⟩, ?_⟩
    simp only [mem_preimage, hΓq, hV, mem_inter_iff]
    refine ⟨⟨⟨⟨S.hqO', hqd, hρ0⟩, hqφ⟩, ?_⟩, hqX₀⟩
    have : q ∈ Subtype.val ⁻¹' UE := by rw [hUE]; exact hqeE
    exact this
  have hG₁V : ∀ p ∈ G₁, Γ p ∈ S.O' ∧ Γ p ∈ d.val.source ∧ d.val (Γ p) ∈ Wd ∧ Γ p ∈ Oφ ∧
      Γ p ∈ UE ∧ (μ (Γ p)).1 ∈ eX.val.source := by
    intro p hp
    obtain ⟨-, ⟨⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩, h6⟩⟩ := hp
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  -- the smooth potential in fibre coordinates
  set H : ComplexModel 1 × ComplexModel (m + 1) → ℝ := fun p =>
    (φ (Γ p)).toReal + ρ (d.val (Γ p)) with hH
  have hHsm : ∀ p ∈ G₁, ContDiffAt ℝ ∞ H p := by
    intro p hp
    obtain ⟨-, hpd, hpW, hpφ, -, -⟩ := hG₁V p hp
    have hdΓ : ContDiffAt ℝ ∞ (fun z => d.val (Γ z)) p :=
      (contDiffAt_chart_comp' (hΓsm p hp.1) d hpd).restrict_scalars ℝ
    have hdt : d.val (Γ p) ∈ d.val.target ∩ d.val.symm ⁻¹' Oφ := by
      refine ⟨d.val.map_source hpd, ?_⟩
      simp only [mem_preimage, d.val.left_inv hpd]
      exact hpφ
    have h1 : ContDiffAt ℝ ∞ (fun z => (φ (d.val.symm z)).toReal) (d.val (Γ p)) :=
      (contDiffOn_toReal_of_gentle hφ d (d.val (Γ p)) hdt).contDiffAt
        ((d.val.continuousOn_symm.isOpen_inter_preimage d.val.open_target hOφo).mem_nhds hdt)
    have h2 : ContDiffAt ℝ ∞ ρ (d.val (Γ p)) :=
      (hρ.2.2.1 _ hpW).contDiffAt (hρ.1.mem_nhds hpW)
    have h3 : ContDiffAt ℝ ∞
        (fun z => (φ (d.val.symm (d.val (Γ z)))).toReal + ρ (d.val (Γ z))) p :=
      (h1.comp p hdΓ).add (h2.comp p hdΓ)
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hG₁o.mem_nhds hp] with z hz
    show _ = (φ (d.val.symm (d.val (Γ z)))).toReal + ρ (d.val (Γ z))
    rw [d.val.left_inv (hG₁V z hz).2.1]
  -- the box
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hG₁o _ hP₀
  set R : ℝ := ε₀ / 3 with hR
  have hR0 : 0 < R := by positivity
  have hbox : ∀ t : ComplexModel 1, dist t 0 < R → ∀ y, dist y y₀ < 2 * R → (t, y) ∈ G₁ := by
    intro t ht y hy
    apply hball
    rw [← ball_prod_same]
    exact ⟨mem_ball.mpr (by linarith), mem_ball.mpr (by linarith)⟩
  set A : Opens (ComplexModel (m + 1)) := ⟨ball y₀ (2 * R), isOpen_ball⟩ with hA
  set Wb : Opens (ComplexModel (m + 1)) := ⟨ball y₀ R, isOpen_ball⟩ with hWb
  have hWA : RelativelyCompactIn Wb A := by
    refine ⟨?_, ?_⟩
    · exact (isCompact_closedBall y₀ R).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  have hbox0 : ∀ y ∈ A, ((0 : ComplexModel 1), y) ∈ G₁ := fun y hy =>
    hbox 0 (by simpa using hR0) y hy
  /- ### The measure on `ℰ` in the coordinates `y ↦ Γ(0, y)` -/
  have hfA : ∀ p : LiftedOpen.{u} A, Γ (0, LiftedOpen.toModel A p) ∈ exceptionalSet F μ :=
    fun p => hΓE _ (hbox0 _ (LiftedOpen.toModel_mem A p)).1
      (S.hO'O (hG₁V _ (hbox0 _ (LiftedOpen.toModel_mem A p))).1)
  have hfAs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      (fun p : LiftedOpen.{u} A => Γ (0, LiftedOpen.toModel A p)) := by
    intro p
    have hpG := (hbox0 _ (LiftedOpen.toModel_mem A p)).1
    have hin : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel 1 × ComplexModel (m + 1)) ∞
        (fun p : LiftedOpen.{u} A => ((0 : ComplexModel 1), LiftedOpen.toModel A p)) p :=
      ((contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt).comp p
        (LiftedOpen.contMDiff_toModel A p)
    exact ContMDiffAt.comp (g := Γ) p (hΓsm _ hpG) hin
  set GA : LiftedOpen.{u} A → exceptionalSet F μ := fun p =>
    ⟨Γ (0, LiftedOpen.toModel A p), hfA p⟩ with hGA
  have hGAs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ GA :=
    SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_succ (m + 1))
      (fun _ hz => regularAtDim_exceptionalSet F hμ hz) hfAs hfA
  set pA : LiftedOpen.{u} A := LiftedOpen.mk A y₀ (mem_ball_self (by linarith)) with hpA
  set gE : ComplexModel (m + 1) → exceptionalSet F μ := fun y => GA (liftMk A pA y) with hgE
  have hgE : ∀ y ∈ A, (gE y).1 = Γ (0, y) := by
    intro y hy
    simp only [hgE, hGA, toModel_liftMk pA hy]
  have hgEs : ∀ y ∈ A, ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      gE y := fun y hy => (hGAs _).comp y (contMDiffAt_liftMk pA hy)
  have hgEsrc : ∀ y ∈ A, gE y ∈ eE.val.source := by
    intro y hy
    rw [← hUE]
    show (gE y).1 ∈ UE
    rw [hgE y hy]
    exact (hG₁V _ (hbox0 y hy)).2.2.2.2.1
  -- the inverse `z ↦ ν(W z)` on `ℰ`
  have hinvE : ∀ z : exceptionalSet F μ, z.1 ∈ S.O' →
      ((0 : ComplexModel 1), S.ν (C.W z.1)) ∈ S.G ∧ Γ (0, S.ν (C.W z.1)) = z.1 := by
    intro z hz
    have hτz : ((splitL m).symm (monomial m C.j (C.W z.1))).2 = 0 := by
      rw [C.tau_eq (S.hO'O hz), ((mem_deformationCentre_iff F).mp z.2).2, sub_self]
    obtain ⟨hG, hΛ⟩ := S.hΛν z.1 hz 0 hτz
    refine ⟨hG, ?_⟩
    simp only [hΓ]
    rw [hΛ]
    exact C.ℓ_W (S.hO'O hz)
  set σE : ComplexModel (m + 1) → ComplexModel (m + 1) := fun y => eE.val (gE y) with hσE
  set τE : ComplexModel (m + 1) → ComplexModel (m + 1) := fun ζ => S.ν (C.W (eE.val.symm ζ).1)
    with hτE
  set DE : Set (ComplexModel (m + 1)) :=
    (eE.val.target ∩ (fun ζ => (eE.val.symm ζ).1) ⁻¹' S.O') ∩ τE ⁻¹' A with hDE
  have hτEc : ContinuousOn τE (eE.val.target ∩ (fun ζ => (eE.val.symm ζ).1) ⁻¹' S.O') := by
    intro ζ hζ
    have h1 : ContinuousAt (fun ζ => (eE.val.symm ζ).1) ζ :=
      continuous_subtype_val.continuousAt.comp (eE.val.continuousAt_symm hζ.1)
    have h2 : ContinuousAt (fun z => S.ν (C.W z)) (eE.val.symm ζ).1 :=
      S.ν.continuous.continuousAt.comp (C.hW _ (S.hO'O hζ.2)).continuousAt
    exact (h2.comp_of_eq h1 rfl).continuousWithinAt
  have hDEo : IsOpen DE := by
    refine hτEc.isOpen_inter_preimage ?_ isOpen_ball
    exact (continuous_subtype_val.comp_continuousOn eE.val.continuousOn_symm).isOpen_inter_preimage
      eE.val.open_target S.hO'
  set DEo : Opens (ComplexModel (m + 1)) := ⟨DE, hDEo⟩ with hDEo'
  have hDEinv : ∀ ζ ∈ DE, Γ (0, τE ζ) = (eE.val.symm ζ).1 ∧ ((0 : ComplexModel 1), τE ζ) ∈ G₁ :=
    fun ζ hζ => ⟨(hinvE _ hζ.1.2).2, hbox0 _ hζ.2⟩
  have hpairE : IsBiholomorphicPair A DEo σE τE := by
    refine ⟨fun y hy => ?_, fun ζ hζ => ?_, fun y hy => ?_, fun ζ hζ => hζ.2, fun y hy => ?_,
      fun ζ hζ => ?_⟩
    · exact (contDiffAt_chart_comp (hgEs y hy) eE (hgEsrc y hy)).contDiffWithinAt
    · have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
          eE.val.symm ζ :=
        contMDiffOn_chart_symm.contMDiffAt (eE.val.open_target.mem_nhds hζ.1.1)
      have h2 := (contMDiff_exceptionalInclusion F hμ _).comp ζ h1
      have h3 := (C.hW _ (S.hO'O hζ.1.2)).comp ζ h2
      exact (contMDiffAt_iff_contDiffAt.mp (S.ν.contMDiff.contMDiffAt.comp ζ h3)).contDiffWithinAt
    · have hsrc := hgEsrc y hy
      refine ⟨⟨eE.val.map_source hsrc, ?_⟩, ?_⟩
      · show (eE.val.symm (eE.val (gE y))).1 ∈ S.O'
        rw [eE.val.left_inv hsrc, hgE y hy]
        exact (hG₁V _ (hbox0 y hy)).1
      · show S.ν (C.W (eE.val.symm (eE.val (gE y))).1) ∈ A
        rw [eE.val.left_inv hsrc, hgE y hy, hΓW _ (hbox0 y hy).1 (S.hO'O (hG₁V _ (hbox0 y hy)).1),
          S.hνΛ _ (hbox0 y hy).1.1]
        exact hy
    · have hsrc := hgEsrc y hy
      show S.ν (C.W (eE.val.symm (eE.val (gE y))).1) = y
      rw [eE.val.left_inv hsrc, hgE y hy, hΓW _ (hbox0 y hy).1 (S.hO'O (hG₁V _ (hbox0 y hy)).1),
        S.hνΛ _ (hbox0 y hy).1.1]
    · have hgz : gE (τE ζ) = eE.val.symm ζ := Subtype.ext (by
        rw [hgE _ hζ.2]
        exact (hDEinv ζ hζ).1)
      show eE.val (gE (τE ζ)) = ζ
      rw [hgz, eE.val.right_inv hζ.1.1]
  have hDE_pot : (DEo : Set (ComplexModel (m + 1))) ⊆
      potentialDomain (Subtype.val : exceptionalSet F μ → 𝒳) eE d Wd := by
    intro ζ hζ
    obtain ⟨h1, h2⟩ := hDEinv ζ hζ
    have hV := hG₁V _ h2
    rw [h1] at hV
    exact ⟨⟨hζ.1.1, hV.2.1⟩, hV.2.2.1⟩
  have hmeasE : ∀ T : Set (ComplexModel (m + 1)), MeasurableSet T → T ⊆ Wb →
      fibreMeasure (contMDiff_exceptionalInclusion F hμ) Θ φ hφp (gE '' T) =
        ∫⁻ y in T, ENNReal.ofReal (smoothDensity (fun y => H (0, y)) y) := by
    intro T hT hTW
    have hf : ContDiffOn ℝ ∞ (fun y => H (0, y)) A := fun y hy =>
      ((hHsm _ (hbox0 y hy)).comp y (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
    have hfeq : ∀ y ∈ A, φ (eE.val.symm (σE y)).1 +
        (ρ (d.val (eE.val.symm (σE y)).1) : EReal) = ((fun y => H (0, y)) y : EReal) := by
      intro y hy
      have hsrc := hgEsrc y hy
      simp only [hσE, eE.val.left_inv hsrc, hgE y hy, hH, EReal.coe_add]
      rw [← eq_coe_toReal_of_ne_bot hφ.1 (hG₁V _ (hbox0 y hy)).2.2.2.1]
    have h := globalMixedMeasure_image_eq_lintegral (Nat.succ_pos m)
      (contMDiff_exceptionalInclusion F hμ)
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp (contMDiff_exceptionalInclusion F hμ) hφp)
      d hρ hpsh eE hpairE hDE_pot hf hfeq hWA hT hTW
    rw [chart_symm_image_image eE (fun y hy => hgEsrc y (subset_closure.trans hWA.2 (hTW hy)))]
      at h
    exact h
  /- ### The measures on the fibres in the coordinates `γ_t` -/
  have hmeasX : ∀ p : ProjectiveLine, p ≠ projectiveZero → p ∈ c₀.source →
      dist (c₀ p - c) 0 < R → ∀ T : Set (ComplexModel (m + 1)), MeasurableSet T → T ⊆ Wb →
        fibreMeasure (hs p) Θ φ hφp ((fun y => (μ (Γ (c₀ p - c, y))).1) '' T) =
          ∫⁻ y in T, ENNReal.ofReal (smoothDensity (fun y => H (c₀ p - c, y)) y) := by
    intro p hp0 hpc hpR T hT hTW
    set t : ComplexModel 1 := c₀ p - c with ht
    have hboxt : ∀ y ∈ A, (t, y) ∈ G₁ := fun y hy => hbox t hpR y hy
    -- `μ(Γ(t, y))` lies over `p`
    have hΓp : ∀ y ∈ A, (μ (Γ (t, y))).2 = p := by
      intro y hy
      obtain ⟨hsrc, heq⟩ := hΓτ _ (hboxt y hy).1
      refine c₀.injOn hsrc hpc ?_
      rw [heq, ht, sub_add_cancel]
    have hsΓ : ∀ y ∈ A, s p (μ (Γ (t, y))).1 = Γ (t, y) := by
      intro y hy
      have hnot : μ (Γ (t, y)) ∉ deformationCentre F := by
        intro h
        exact hp0 ((hΓp y hy).symm.trans ((mem_deformationCentre_iff F).mp h).2)
      refine (eq_of_map_eq_of_notMem F hμ hnot ?_).symm
      rw [hsμ p hp0, ← hΓp y hy]
    set γ : ComplexModel (m + 1) → F.carrier := fun y => (μ (Γ (t, y))).1 with hγ
    set σX : ComplexModel (m + 1) → ComplexModel (m + 1) := fun y => eX.val (γ y) with hσX
    set τX : ComplexModel (m + 1) → ComplexModel (m + 1) :=
      fun ζ => S.ν (C.W (s p (eX.val.symm ζ))) with hτX
    set DX : Set (ComplexModel (m + 1)) :=
      (eX.val.target ∩ (fun ζ => s p (eX.val.symm ζ)) ⁻¹' S.O') ∩ τX ⁻¹' A with hDX
    have hτXc : ContinuousOn τX (eX.val.target ∩ (fun ζ => s p (eX.val.symm ζ)) ⁻¹' S.O') := by
      intro ζ hζ
      have h1 : ContinuousAt (fun ζ => s p (eX.val.symm ζ)) ζ :=
        (hs p).continuous.continuousAt.comp (eX.val.continuousAt_symm hζ.1)
      have h2 : ContinuousAt (fun z => S.ν (C.W z)) (s p (eX.val.symm ζ)) :=
        S.ν.continuous.continuousAt.comp (C.hW _ (S.hO'O hζ.2)).continuousAt
      exact (h2.comp_of_eq h1 rfl).continuousWithinAt
    have hDXo : IsOpen DX := by
      refine hτXc.isOpen_inter_preimage ?_ isOpen_ball
      exact ((hs p).continuous.comp_continuousOn eX.val.continuousOn_symm).isOpen_inter_preimage
        eX.val.open_target S.hO'
    set DXo : Opens (ComplexModel (m + 1)) := ⟨DX, hDXo⟩ with hDXo'
    -- the inverse
    have hDXinv : ∀ ζ ∈ DX, Γ (t, τX ζ) = s p (eX.val.symm ζ) := by
      intro ζ hζ
      have hz := hζ.1.2
      have hτz : ((splitL m).symm (monomial m C.j (C.W (s p (eX.val.symm ζ))))).2 = t := by
        rw [C.tau_eq (S.hO'O hz), hsμ p hp0]
      have hΛ := (S.hΛν _ hz t hτz).2
      simp only [hΓ, hτX]
      rw [hΛ]
      exact C.ℓ_W (S.hO'O hz)
    have hpairX : IsBiholomorphicPair A DXo σX τX := by
      refine ⟨fun y hy => ?_, fun ζ hζ => ?_, fun y hy => ?_, fun ζ hζ => hζ.2, fun y hy => ?_,
        fun ζ hζ => ?_⟩
      · have hin : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1))
            𝓘(ℂ, ComplexModel 1 × ComplexModel (m + 1)) ∞ (fun y => (t, y)) y :=
          (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
        have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
            (fun y => Γ (t, y)) y :=
          ContMDiffAt.comp (g := Γ) y (hΓsm _ (hboxt y hy).1) hin
        have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ γ y :=
          ProductComplexManifold.contMDiff_fst.contMDiffAt.comp y
            ((hμ.contMDiff.contMDiffAt).comp y h1)
        exact (contDiffAt_chart_comp h2 eX (hG₁V _ (hboxt y hy)).2.2.2.2.2).contDiffWithinAt
      · have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
            eX.val.symm ζ :=
          contMDiffOn_chart_symm.contMDiffAt (eX.val.open_target.mem_nhds hζ.1.1)
        have h2 := ((hs p) _).comp ζ h1
        have h3 := (C.hW _ (S.hO'O hζ.1.2)).comp ζ h2
        exact (contMDiffAt_iff_contDiffAt.mp
          (S.ν.contMDiff.contMDiffAt.comp ζ h3)).contDiffWithinAt
      · have hsrc := (hG₁V _ (hboxt y hy)).2.2.2.2.2
        refine ⟨⟨eX.val.map_source hsrc, ?_⟩, ?_⟩
        · show s p (eX.val.symm (eX.val (γ y))) ∈ S.O'
          rw [eX.val.left_inv hsrc, hsΓ y hy]
          exact (hG₁V _ (hboxt y hy)).1
        · show S.ν (C.W (s p (eX.val.symm (eX.val (γ y))))) ∈ A
          rw [eX.val.left_inv hsrc, hsΓ y hy,
            hΓW _ (hboxt y hy).1 (S.hO'O (hG₁V _ (hboxt y hy)).1), S.hνΛ _ (hboxt y hy).1.1]
          exact hy
      · have hsrc := (hG₁V _ (hboxt y hy)).2.2.2.2.2
        show S.ν (C.W (s p (eX.val.symm (eX.val (γ y))))) = y
        rw [eX.val.left_inv hsrc, hsΓ y hy,
          hΓW _ (hboxt y hy).1 (S.hO'O (hG₁V _ (hboxt y hy)).1), S.hνΛ _ (hboxt y hy).1.1]
      · show eX.val (γ (τX ζ)) = ζ
        have h1 : γ (τX ζ) = eX.val.symm ζ := by
          simp only [hγ]
          rw [hDXinv ζ hζ, hsμ p hp0]
        rw [h1, eX.val.right_inv hζ.1.1]
    have hDX_pot : (DXo : Set (ComplexModel (m + 1))) ⊆ potentialDomain (s p) eX d Wd := by
      intro ζ hζ
      have hV := hG₁V _ (hboxt _ hζ.2)
      rw [hDXinv ζ hζ] at hV
      exact ⟨⟨hζ.1.1, hV.2.1⟩, hV.2.2.1⟩
    have hf : ContDiffOn ℝ ∞ (fun y => H (t, y)) A := fun y hy =>
      ((hHsm _ (hboxt y hy)).comp y (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
    have hfeq : ∀ y ∈ A, φ (s p (eX.val.symm (σX y))) +
        (ρ (d.val (s p (eX.val.symm (σX y)))) : EReal) = ((fun y => H (t, y)) y : EReal) := by
      intro y hy
      have hsrc : γ y ∈ eX.val.source := (hG₁V _ (hboxt y hy)).2.2.2.2.2
      have h1 : s p (eX.val.symm (σX y)) = Γ (t, y) := by
        simp only [hσX]
        rw [eX.val.left_inv hsrc]
        exact hsΓ y hy
      rw [h1]
      simp only [hH, EReal.coe_add]
      rw [← eq_coe_toReal_of_ne_bot hφ.1 (hG₁V _ (hboxt y hy)).2.2.2.1]
    have h := globalMixedMeasure_image_eq_lintegral (Nat.succ_pos m) (hs p)
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp (hs p) hφp)
      d hρ hpsh eX hpairX hDX_pot hf hfeq hWA hT hTW
    rw [chart_symm_image_image eX (g := γ) (fun y hy =>
      (hG₁V _ (hboxt y (subset_closure.trans hWA.2 (hTW hy)))).2.2.2.2.2)] at h
    exact h
  /- ### The neighbourhood and the transport -/
  set hE : exceptionalSet F μ → ComplexModel (m + 1) := fun z => S.ν (C.W z.1) with hhE
  have hhEc : ContinuousOn hE (Subtype.val ⁻¹' S.O') := fun z hz =>
    ((S.ν.continuous.continuousAt.comp ((C.hW _ (S.hO'O hz)).continuousAt)).comp
      continuous_subtype_val.continuousAt).continuousWithinAt
  refine ⟨Subtype.val ⁻¹' S.O' ∩ hE ⁻¹' Wb,
    hhEc.isOpen_inter_preimage (S.hO'.preimage continuous_subtype_val) isOpen_ball,
    ⟨S.hqO', mem_ball_self hR0⟩, fun K hKN hK => ?_⟩
  set T₀ := hE '' K with hT₀
  have hT₀c : IsCompact T₀ := hK.image_of_continuousOn (hhEc.mono fun z hz => (hKN hz).1)
  have hT₀W : T₀ ⊆ Wb := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hKN hz).2
  have hT₀A : ∀ y ∈ T₀, y ∈ A := fun y hy =>
    ball_subset_ball (by linarith) (hT₀W hy)
  have hgK : gE '' T₀ = K := by
    ext z
    constructor
    · rintro ⟨_, ⟨z', hz', rfl⟩, rfl⟩
      have h1 : gE (hE z') = z' := Subtype.ext (by
        rw [hgE _ (hT₀A _ ⟨z', hz', rfl⟩)]
        exact (hinvE z' (hKN hz').1).2)
      rw [h1]
      exact hz'
    · intro hz
      refine ⟨hE z, ⟨z, hz, rfl⟩, Subtype.ext ?_⟩
      rw [hgE _ (hT₀A _ ⟨z, hz, rfl⟩)]
      exact (hinvE z (hKN hz).1).2
  have hνK : fibreMeasure (contMDiff_exceptionalInclusion F hμ) Θ φ hφp K =
      ∫⁻ y in T₀, ENNReal.ofReal (smoothDensity (fun y => H (0, y)) y) := by
    rw [← hgK]
    exact hmeasE T₀ hT₀c.measurableSet hT₀W
  intro O hO hKO ε hε
  refine ⟨fun p => (fun y => (μ (Γ (c₀ p - c, y))).1) '' T₀, ?_⟩
  have := nhdsWithin_projectiveZero_neBot
  have hct : Tendsto (fun p : ProjectiveLine => c₀ p - c) (𝓝[≠] projectiveZero) (𝓝 0) := by
    have h := ((chartAt (ComplexModel 1) projectiveZero).continuousAt h0c).tendsto
    have h' : Tendsto (fun p : ProjectiveLine => c₀ p - c) (𝓝 projectiveZero) (𝓝 (c - c)) :=
      h.sub tendsto_const_nhds
    rw [sub_self] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  -- the transported sets land in `O` (tube lemma)
  have htube : ∀ᶠ t in 𝓝 (0 : ComplexModel 1), ∀ y ∈ T₀, Γ (t, y) ∈ O := by
    refine hT₀c.eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : Γ (0, y) ∈ O := by
      obtain ⟨z, hz, rfl⟩ := hy
      rw [(hinvE z (hKN hz).1).2]
      exact hKO ⟨z, hz, rfl⟩
    have hc : ContinuousAt Γ ((0 : ComplexModel 1), y) :=
      (hΓsm _ (hbox0 y (hT₀A y hy)).1).continuousAt
    exact hc.preimage_mem_nhds (hO.mem_nhds hy0)
  have hnear : ∀ᶠ p in 𝓝[≠] projectiveZero, p ≠ projectiveZero ∧ p ∈ c₀.source ∧
      dist (c₀ p - c) 0 < R := by
    refine (eventually_mem_nhdsWithin (s := {projectiveZero}ᶜ)).and ?_
    refine Filter.Eventually.and (nhdsWithin_le_nhds
      ((chartAt (ComplexModel 1) projectiveZero).open_source.mem_nhds h0c)) ?_
    exact hct.eventually (ball_mem_nhds 0 hR0)
  have hfat := eventually_setLIntegral_density_le (Fj := fun t y => H (t, y)) hct
    (isCompact_closedBall y₀ R) (hT₀W.trans ball_subset_closedBall) hT₀c.measurableSet
    (fun y hy => by
      have : ((0 : ComplexModel 1), y) ∈ G₁ := hbox 0 (by simpa using hR0) y (by
        have := mem_closedBall.mp hy
        linarith)
      exact hHsm _ this) hε
  filter_upwards [hnear, hct.eventually htube, hfat] with p hp hpO hpfat
  obtain ⟨hp0, hpc, hpR⟩ := hp
  have hboxt : ∀ y ∈ A, (c₀ p - c, y) ∈ G₁ := fun y hy => hbox _ hpR y hy
  have hγc : ContinuousOn (fun y => (μ (Γ (c₀ p - c, y))).1) T₀ := fun y hy =>
    (continuous_fst.continuousAt.comp (hμ.contMDiff.continuous.continuousAt.comp
      ((hΓsm _ (hboxt y (hT₀A y hy)).1).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt))).continuousWithinAt
  refine ⟨(hT₀c.image_of_continuousOn hγc).measurableSet, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    -- `s_p(γ_t y) = Γ(t, y)`
    have hΓp : (μ (Γ (c₀ p - c, y))).2 = p := by
      obtain ⟨hsrc, heq⟩ := hΓτ _ (hboxt y (hT₀A y hy)).1
      refine c₀.injOn hsrc hpc ?_
      rw [heq, sub_add_cancel]
    have hnot : μ (Γ (c₀ p - c, y)) ∉ deformationCentre F := by
      intro h
      exact hp0 (hΓp.symm.trans ((mem_deformationCentre_iff F).mp h).2)
    have hs' : s p (μ (Γ (c₀ p - c, y))).1 = Γ (c₀ p - c, y) := by
      refine (eq_of_map_eq_of_notMem F hμ hnot ?_).symm
      rw [hsμ p hp0]
      exact Prod.ext rfl hΓp
    show s p (μ (Γ (c₀ p - c, y))).1 ∈ O
    rw [hs']
    exact hpO y hy
  · rw [hνK, hmeasX p hp0 hpc hpR T₀ hT₀c.measurableSet hT₀W]
    exact hpfat

end SGPT.Okounkov.TranscendentalWN.LSC

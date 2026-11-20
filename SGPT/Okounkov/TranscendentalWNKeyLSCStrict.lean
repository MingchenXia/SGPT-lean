import SGPT.Okounkov.TranscendentalWNKeyLSCLocal

/-!
# Convergence of the fibre masses away from `ℰ` (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-key`, node `tok-wn-key:fibre-limit-strict` (analytic half), and
`claude-tok-wn-lsc`, nodes `tok-wn-lsc:strict-chart`, `tok-wn-lsc:strict-local`; source WN21 §5.

Let `μ : 𝒳 → X × ℙ¹` be the deformation to the normal cone of `Z`, `ι'` the lift of
`x ↦ (x, 0)` and `s_τ` the sections of `μ` over `x ↦ (x, τ)`, `τ ≠ 0`.  Near a point `x₀ ∉ Z`,
in a chart `e` of `X` at `x₀` and the chart `c₀` of `ℙ¹` at `0`, the inclusion
`(y, t) ↦ (e⁻¹ y, c₀⁻¹ t)` avoids the centre `Z × {0}`, so it lifts through `μ` (universal
property of the blow-up) to a holomorphic `Γ` (`strictLift`) with `s_τ(e⁻¹ y) = Γ(y, c₀ τ)` and
`ι'(e⁻¹ y) = Γ(y, c₀ 0)` (injectivity of `μ` off the centre).

For a potential `φ` with gentle analytic singularities, finite at `ι'(x₀)`, the function
`F(t, y) = φ(Γ(y, t)) + ρ(d(Γ(y, t)))` (`ρ` a local potential of `Θ` in a chart `d` of `𝒳`) is
jointly smooth near `(c₀ 0, e x₀)`, the masses of `φ ∘ s_τ` and `φ ∘ ι'` on `e⁻¹(T)` are
`∫_T (dd^c F(c₀ τ, ·))ⁿ` and `∫_T (dd^c F(c₀ 0, ·))ⁿ`
(`globalMixedMeasure_image_eq_lintegral`), and Fatou's lemma gives the local lower
semicontinuity `strict_local_eventually_le`: near every `x₀ ∉ Z` with `φ(ι' x₀) ≠ -∞`, for every
measurable `S` and `ε > 0`, eventually as `τ → 0`,
`⟨(T|_{X'})ⁿ⟩(S) ≤ ⟨(T|_{X_τ})ⁿ⟩(S) + ε`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN.LSC

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN

/-! ### Lifted open sets of the model -/

section Lifted

variable {n N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The total extension of `LiftedOpen.mk` (the value `p₀` off `S` is irrelevant). -/
def liftMk (S : Opens (ComplexModel n)) (p₀ : LiftedOpen.{u} S) (w : ComplexModel n) :
    LiftedOpen.{u} S :=
  open Classical in if h : w ∈ S then LiftedOpen.mk S w h else p₀

theorem toModel_liftMk {S : Opens (ComplexModel n)} (p₀ : LiftedOpen.{u} S) {w : ComplexModel n}
    (hw : w ∈ S) : LiftedOpen.toModel S (liftMk S p₀ w) = w := by
  simp only [liftMk, hw, dite_true]
  rfl

theorem contMDiffAt_liftMk {S : Opens (ComplexModel n)} (p₀ : LiftedOpen.{u} S)
    {w : ComplexModel n} (hw : w ∈ S) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (liftMk S p₀) w := by
  apply LiftedOpen.contMDiffAt_of_toModel
  have h : (LiftedOpen.toModel S ∘ liftMk S p₀) =ᶠ[𝓝 w] id := by
    filter_upwards [S.isOpen.mem_nhds hw] with v hv
    exact toModel_liftMk p₀ hv
  exact contMDiffAt_id.congr_of_eventuallyEq h

/-- A holomorphic map from (an open set of) the model, read in a chart of the target. -/
theorem contDiffAt_chart_comp {f : ComplexModel n → Y} {w : ComplexModel n}
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ f w) (d : ComplexChart N Y)
    (hw : f w ∈ d.val.source) : ContDiffAt ℂ ∞ (fun z => d.val (f z)) w := by
  have hd : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ d.val (f w) :=
    (contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas d.property)).contMDiffAt
      (d.val.open_source.mem_nhds hw)
  exact contMDiffAt_iff_contDiffAt.mp (hd.comp w hf)

end Lifted

/-! ### The non-pluripolar measures of the restrictions -/

section FibreMeasure

variable {k N : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  {𝒳 : Type*} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]

/-- The non-pluripolar measure `⟨(j^*Θ + dd^c(φ ∘ j))ⁿ⟩` of the restriction of a `Θ`-psh `φ`
along a holomorphic `j : V → 𝒳` (no nondegeneracy needed to define it). -/
def fibreMeasure {j : V → 𝒳} (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j)
    (Θ : ClosedRealOneOneForm N 𝒳) (φ : 𝒳 → EReal) (hφ : ThetaPlurisubharmonic Θ.val φ) :
    Measure V :=
  globalMixedMeasure (fun _ : Fin k => ClosedRealOneOneForm.pullback hj Θ)
    (fun _ => fun x => φ (j x)) (fun _ => GlobalPotentialPullback.thetaPlurisubharmonic_comp hj hφ)

omit [BorelSpace V] in
theorem diagonalPotentialMeasure_eq_fibreMeasure {j : V → 𝒳}
    (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j)
    (Θ : ClosedRealOneOneForm N 𝒳) (φ : 𝒳 → EReal) (hφ : ThetaPlurisubharmonic Θ.val φ)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hj Θ).val (fun x => φ (j x))) :
    DiagonalMass.diagonalPotentialMeasure (ClosedRealOneOneForm.pullback hj Θ)
      (fun x => φ (j x)) hw = fibreMeasure hj Θ φ hφ := rfl

end FibreMeasure

/-! ### The strict chart -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The splitting `ℂ^{m+2} = ℂ^{m+1} × ℂ` of the product charts of `X × ℙ¹`. -/
abbrev splitEquiv (m : ℕ) : (ComplexModel (m + 1) × ComplexModel 1) ≃L[ℂ] ComplexModel (m + 1 + 1) :=
  prodModelEquiv (m + 1) 1

/-- The coordinates `(y, t)` of the product chart at `(x₀, 0)` with `e⁻¹ y ∉ Z`. -/
def strictDomain (x₀ : F.carrier) : Opens (ComplexModel (m + 1 + 1)) :=
  ⟨(splitEquiv m).symm ⁻¹'
      (((chartAt (ComplexModel (m + 1)) x₀).target ∩
        (chartAt (ComplexModel (m + 1)) x₀).symm ⁻¹' (F.flag (1 : Fin (m + 2)))ᶜ) ×ˢ
        (chartAt (ComplexModel 1) projectiveZero).target),
    (((chartAt (ComplexModel (m + 1)) x₀).isOpen_inter_preimage_symm
        F.firstDivisor.1.isOpen_compl).prod
      (chartAt (ComplexModel 1) projectiveZero).open_target).preimage
      (splitEquiv m).symm.continuous⟩

theorem mem_strictDomain {x₀ : F.carrier} {w : ComplexModel (m + 1 + 1)} :
    w ∈ strictDomain F x₀ ↔
      ((splitEquiv m).symm w).1 ∈ (chartAt (ComplexModel (m + 1)) x₀).target ∧
      (chartAt (ComplexModel (m + 1)) x₀).symm ((splitEquiv m).symm w).1 ∉
        F.flag (1 : Fin (m + 2)) ∧
      ((splitEquiv m).symm w).2 ∈ (chartAt (ComplexModel 1) projectiveZero).target := by
  simp only [strictDomain, Opens.mem_mk, mem_preimage, mem_prod, mem_inter_iff, mem_compl_iff]
  tauto

theorem strictDomain_subset_target (x₀ : F.carrier) :
    (strictDomain F x₀ : Set (ComplexModel (m + 1 + 1))) ⊆
      (chartAt (ComplexModel (m + 1 + 1)) (x₀, projectiveZero)).target := by
  intro w hw
  have hw := (mem_strictDomain F).mp hw
  rw [chartAt_prod, prodChart_target]
  exact ⟨hw.1, hw.2.2⟩

/-- The inclusion of the strict coordinates into `X × ℙ¹`. -/
def strictInclusion (x₀ : F.carrier) : LiftedOpen.{u} (strictDomain F x₀) →
    F.carrier × ProjectiveLine := fun p =>
  (chartAt (ComplexModel (m + 1 + 1)) (x₀, projectiveZero)).symm
    (LiftedOpen.toModel (strictDomain F x₀) p)

theorem contMDiff_strictInclusion (x₀ : F.carrier) :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      (strictInclusion F x₀) := by
  intro p
  have hp := strictDomain_subset_target F x₀ (LiftedOpen.toModel_mem _ p)
  exact (contMDiffOn_chart_symm.contMDiffAt
    ((chartAt (ComplexModel (m + 1 + 1)) (x₀, projectiveZero)).open_target.mem_nhds hp)).comp p
      (LiftedOpen.contMDiff_toModel _ p)

theorem strictInclusion_notMem (x₀ : F.carrier) (p : LiftedOpen.{u} (strictDomain F x₀)) :
    strictInclusion F x₀ p ∉ deformationCentre F := by
  have hw := (mem_strictDomain F).mp (LiftedOpen.toModel_mem _ p)
  intro h
  refine hw.2.1 ?_
  have h1 := ((mem_deformationCentre_iff F).mp h).1
  simpa [strictInclusion, chartAt_prod, prodChart_symm_apply] using h1

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- The lift `ℓ` of the strict coordinates through `μ` (universal property of the blow-up). -/
theorem exists_strictLift (hμ : IsNormalConeDeformation F μ) (x₀ : F.carrier) :
    ∃ ℓ : LiftedOpen.{u} (strictDomain F x₀) → 𝒳,
      ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ℓ ∧
        μ ∘ ℓ = strictInclusion F x₀ := by
  obtain ⟨ℓ, hℓ, -⟩ := hμ.2.2.2.2 (m + 1 + 1) (LiftedOpen.{u} (strictDomain F x₀))
    (strictInclusion F x₀) (contMDiff_strictInclusion F x₀)
    (HolomorphicIdealSheaves.isInvertible_pullback_vanishingIdeal_of_disjoint
      (isClosed_deformationCentre F) (strictInclusion_notMem F x₀))
  exact ⟨ℓ, hℓ⟩

/-! ### Generic helpers -/

theorem isBiholomorphicPair_id {n : ℕ} (A : Opens (ComplexModel n)) :
    IsBiholomorphicPair A A id id :=
  ⟨contDiffOn_id, contDiffOn_id, fun _ h => h, fun _ h => h, fun _ _ => rfl, fun _ _ => rfl⟩

theorem nhdsWithin_projectiveZero_neBot : (𝓝[≠] projectiveZero).NeBot :=
  ⟨fun h => not_isOpen_singleton_projectiveZero
    ((isOpen_singleton_iff_punctured_nhds _).mpr h)⟩

/-- A measurable subset of a chart source has a measurable coordinate image. -/
theorem measurableSet_chart_image {n : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel n) V] [MeasurableSpace V] [BorelSpace V] (e : ComplexChart n V)
    {S : Set V} (hS : MeasurableSet S) (hSe : S ⊆ e.val.source) :
    MeasurableSet (e.val '' S) := by
  rw [e.val.image_eq_target_inter_inv_preimage hSe]
  exact SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
    e.val.open_target.measurableSet e.val.continuousOn_symm hS

/-! ### The local lower semicontinuity away from `ℰ` -/

/-- **`tok-wn-lsc:strict-local`** (WN21 §5, `tok-wn-key:fibre-limit-strict`): near a point
`x₀ ∉ Z` with `φ(ι' x₀) ≠ -∞`, the non-pluripolar measure of `φ ∘ ι'` is locally dominated, up to
`ε`, by those of `φ ∘ s_τ` for `τ` near `0`: there is an open `N ∋ x₀` such that for every
measurable `S ⊆ N` and `ε > 0`, eventually as `τ → 0`, `τ ≠ 0`,
`⟨(T|_{X'})ⁿ⟩(S) ≤ ⟨(T|_{X_τ})ⁿ⟩(S) + ε`. -/
theorem strict_local_eventually_le (hμ : IsNormalConeDeformation F μ)
    [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳} {φ : 𝒳 → EReal}
    (hφ : φ ∈ TranscendentalCore.gentleCurrents Θ)
    {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero))
    {s : ProjectiveLine → F.carrier → 𝒳}
    (hs : ∀ p, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ (s p))
    (hsμ : ∀ p, p ≠ projectiveZero → ∀ x, μ (s p x) = (x, p))
    {x₀ : F.carrier} (hx₀ : x₀ ∉ F.flag (1 : Fin (m + 2))) (hφx₀ : φ (ι x₀) ≠ ⊥) :
    ∃ N : Set F.carrier, IsOpen N ∧ x₀ ∈ N ∧ ∀ S : Set F.carrier, MeasurableSet S → S ⊆ N →
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ p in 𝓝[≠] projectiveZero,
        fibreMeasure hι Θ φ hφ.1.1 S ≤ fibreMeasure (hs p) Θ φ hφ.1.1 S + ε := by
  classical
  have hφp : ThetaPlurisubharmonic Θ.val φ := hφ.1.1
  set e : ComplexChart (m + 1) F.carrier := complexChartAt x₀ with he
  set c₀ := chartAt (ComplexModel 1) projectiveZero with hc₀
  set L := splitEquiv m with hL
  set SD := strictDomain F x₀ with hSD
  obtain ⟨ℓ, hℓ, hμℓ⟩ := exists_strictLift F hμ x₀
  have hx₀e : x₀ ∈ e.val.source := mem_complexChartAt_source x₀
  have h0c : projectiveZero ∈ c₀.source := mem_chart_source _ _
  set y₀ : ComplexModel (m + 1) := e.val x₀ with hy₀
  set t₀ : ComplexModel 1 := c₀ projectiveZero with ht₀
  set w₀ : ComplexModel (m + 1 + 1) := L (y₀, t₀) with hw₀def
  have hLL : ∀ y t, L.symm (L (y, t)) = (y, t) := fun y t => L.symm_apply_apply _
  have hw₀ : w₀ ∈ SD := by
    rw [mem_strictDomain, hw₀def, hLL]
    refine ⟨e.val.map_source hx₀e, ?_, c₀.map_source h0c⟩
    show e.val.symm (e.val x₀) ∉ _
    rw [e.val.left_inv hx₀e]
    exact hx₀
  set p₀ : LiftedOpen.{u} SD := LiftedOpen.mk SD w₀ hw₀
  set Γ : ComplexModel (m + 1 + 1) → 𝒳 := fun w => ℓ (liftMk SD p₀ w) with hΓ
  have hΓμ : ∀ w ∈ SD, μ (Γ w) = (e.val.symm (L.symm w).1, c₀.symm (L.symm w).2) := by
    intro w hw
    have h := congrFun hμℓ (liftMk SD p₀ w)
    simp only [Function.comp] at h
    rw [hΓ, h, strictInclusion, toModel_liftMk p₀ hw, chartAt_prod, prodChart_symm_apply]
    rfl
  have hΓsm : ∀ w ∈ SD,
      ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ w :=
    fun w hw => (hℓ _).comp w (contMDiffAt_liftMk p₀ hw)
  have hΓc : ContinuousOn Γ SD := fun w hw => (hΓsm w hw).continuousAt.continuousWithinAt
  -- `Γ` is the section of `μ` over the base point
  have hΓsec : ∀ w ∈ SD, ∀ j : F.carrier → 𝒳,
      μ (j (e.val.symm (L.symm w).1)) = (e.val.symm (L.symm w).1, c₀.symm (L.symm w).2) →
        j (e.val.symm (L.symm w).1) = Γ w := by
    intro w hw j hj
    have hnot : μ (Γ w) ∉ deformationCentre F := by
      rw [hΓμ w hw]
      intro h
      exact ((mem_strictDomain F).mp hw).2.1 ((mem_deformationCentre_iff F).mp h).1
    exact (eq_of_map_eq_of_notMem F hμ hnot (by rw [hΓμ w hw, hj])).symm
  have hΓw₀ : Γ w₀ = ι x₀ := by
    have h := hΓsec w₀ hw₀ ι (by
      rw [hw₀def, hLL]
      simp only [hy₀, ht₀, e.val.left_inv hx₀e, c₀.left_inv h0c, hμι])
    rw [hw₀def, hLL] at h
    simp only [hy₀, e.val.left_inv hx₀e] at h
    exact h.symm
  -- the chart of `𝒳` and the local potential
  set d : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt (ι x₀) with hd
  have hιd : ι x₀ ∈ d.val.source := mem_complexChartAt_source _
  obtain ⟨Wd, ρ, hρ0, hρ, hpsh⟩ := hφp d (d.val (ι x₀)) (d.val.map_source hιd)
  set O : Set 𝒳 := {z | φ z ≠ ⊥} with hO
  have hOo : IsOpen O := isOpen_ne_bot_of_gentle hφ
  -- the good set of coordinates
  set G : Set (ComplexModel (m + 1 + 1)) :=
    SD ∩ Γ ⁻¹' ((d.val.source ∩ d.val ⁻¹' Wd) ∩ O) with hG
  have hGo : IsOpen G := hΓc.isOpen_inter_preimage SD.isOpen
    ((d.val.isOpen_inter_preimage hρ.1).inter hOo)
  have hw₀G : w₀ ∈ G := by
    refine ⟨hw₀, ?_⟩
    simp only [mem_preimage, hΓw₀]
    exact ⟨⟨hιd, hρ0⟩, hφx₀⟩
  -- the smooth potential in the joint coordinates
  set H : ComplexModel (m + 1 + 1) → ℝ := fun w => (φ (Γ w)).toReal + ρ (d.val (Γ w)) with hH
  have hHsm : ∀ w ∈ G, ContDiffAt ℝ ∞ H w := by
    intro w hw
    have hdΓ : ContDiffAt ℝ ∞ (fun z => d.val (Γ z)) w :=
      (contDiffAt_chart_comp (hΓsm w hw.1) d hw.2.1.1).restrict_scalars ℝ
    have hdt : d.val (Γ w) ∈ d.val.target ∩ d.val.symm ⁻¹' O := by
      refine ⟨d.val.map_source hw.2.1.1, ?_⟩
      simp only [mem_preimage, d.val.left_inv hw.2.1.1]
      exact hw.2.2
    have h1 : ContDiffAt ℝ ∞ (fun z => (φ (d.val.symm z)).toReal) (d.val (Γ w)) :=
      (contDiffOn_toReal_of_gentle hφ d (d.val (Γ w)) hdt).contDiffAt
        ((d.val.continuousOn_symm.isOpen_inter_preimage d.val.open_target hOo).mem_nhds hdt)
    have h2 : ContDiffAt ℝ ∞ ρ (d.val (Γ w)) :=
      (hρ.2.2.1 _ hw.2.1.2).contDiffAt (hρ.1.mem_nhds hw.2.1.2)
    have h3 : ContDiffAt ℝ ∞ (fun z => (φ (d.val.symm (d.val (Γ z)))).toReal + ρ (d.val (Γ z))) w :=
      (h1.comp w hdΓ).add (h2.comp w hdΓ)
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hGo.mem_nhds hw] with z hz
    simp only [hH, d.val.left_inv hz.2.1.1]
  -- the family `F(t, y) = H(L(y, t))`
  set Fj : ComplexModel 1 → ComplexModel (m + 1) → ℝ := fun t y => H (L (y, t)) with hFj
  have hLsw : ContDiff ℝ ∞ (fun p : ComplexModel 1 × ComplexModel (m + 1) => L (p.2, p.1)) :=
    ((L : (ComplexModel (m + 1) × ComplexModel 1) →L[ℂ] ComplexModel (m + 1 + 1)).contDiff.restrict_scalars
      ℝ).comp (contDiff_snd.prodMk contDiff_fst)
  set G' : Set (ComplexModel 1 × ComplexModel (m + 1)) :=
    (fun p : ComplexModel 1 × ComplexModel (m + 1) => L (p.2, p.1)) ⁻¹' G with hG'
  have hG'o : IsOpen G' := hGo.preimage hLsw.continuous
  have hFsm : ∀ p ∈ G', ContDiffAt ℝ ∞ (Function.uncurry Fj) p := fun p hp =>
    ContDiffAt.comp (g := H) p (hHsm _ hp) hLsw.contDiffAt
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hG'o (t₀, y₀) (by
    show L (y₀, t₀) ∈ G
    exact hw₀G)
  set R : ℝ := ε₀ / 3 with hR
  have hR0 : 0 < R := by positivity
  -- the coordinate sets
  set A : Opens (ComplexModel (m + 1)) := ⟨ball y₀ (2 * R), isOpen_ball⟩ with hA
  set W : Opens (ComplexModel (m + 1)) := ⟨ball y₀ R, isOpen_ball⟩ with hW
  have hWA : RelativelyCompactIn W A := by
    refine ⟨?_, ?_⟩
    · exact (isCompact_closedBall y₀ R).of_isClosed_subset isClosed_closure
        (closure_ball_subset_closedBall)
    · exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  have hbox : ∀ t, dist t t₀ < R → ∀ y, dist y y₀ < 2 * R → (t, y) ∈ G' := by
    intro t ht y hy
    apply hball
    rw [← ball_prod_same]
    exact ⟨mem_ball.mpr (by linarith), mem_ball.mpr (by linarith)⟩
  -- the measure on a chart piece, for a section over `c₀⁻¹ t`
  have hmeas : ∀ t, dist t t₀ < R → ∀ (j : F.carrier → 𝒳)
      (hj : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ j),
      (∀ x, μ (j x) = (x, c₀.symm t)) → ∀ T : Set (ComplexModel (m + 1)), MeasurableSet T →
        T ⊆ W → fibreMeasure hj Θ φ hφp (e.val.symm '' T) =
          ∫⁻ y in T, ENNReal.ofReal (smoothDensity (Fj t) y) := by
    intro t ht j hj hjμ T hT hTW
    have hjΓ : ∀ y ∈ A, j (e.val.symm y) = Γ (L (y, t)) := by
      intro y hy
      have hG := (hbox t ht y hy).1
      have h := hΓsec _ hG j (by rw [hLL]; exact hjμ _)
      rwa [hLL] at h
    have hD : (A : Set (ComplexModel (m + 1))) ⊆ potentialDomain j e d Wd := by
      intro y hy
      have hG := hbox t ht y hy
      have hy1 : y ∈ e.val.target := by
        have := ((mem_strictDomain F).mp hG.1).1
        rwa [hLL] at this
      have hjy := hjΓ y hy
      refine ⟨⟨hy1, ?_⟩, ?_⟩
      · show j (e.val.symm y) ∈ d.val.source
        rw [hjy]
        exact hG.2.1.1
      · show d.val (j (e.val.symm y)) ∈ Wd
        rw [hjy]
        exact hG.2.1.2
    have hf : ContDiffOn ℝ ∞ (Fj t) A := fun y hy =>
      ((hFsm (t, y) (hbox t ht y hy)).comp y (contDiffAt_const.prodMk contDiffAt_id)
        ).contDiffWithinAt
    have hfeq : ∀ y ∈ A, φ (j (e.val.symm (id y))) + (ρ (d.val (j (e.val.symm (id y)))) : EReal) =
        (Fj t y : EReal) := by
      intro y hy
      simp only [id, hjΓ y hy, hFj, hH, EReal.coe_add]
      rw [← eq_coe_toReal_of_ne_bot hφ.1 (hbox t ht y hy).2.2]
    have h := globalMixedMeasure_image_eq_lintegral (Nat.succ_pos m) hj
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hj hφp) d hρ hpsh e
      (isBiholomorphicPair_id A) hD hf hfeq hWA hT hTW
    rwa [image_id] at h
  -- the neighbourhood
  refine ⟨e.val.source ∩ e.val ⁻¹' ball y₀ R, e.val.isOpen_inter_preimage isOpen_ball,
    ⟨hx₀e, mem_ball_self hR0⟩, fun S hS hSN ε hε => ?_⟩
  have hSe : S ⊆ e.val.source := fun x hx => (hSN hx).1
  set T : Set (ComplexModel (m + 1)) := e.val '' S with hT
  have hTm : MeasurableSet T := measurableSet_chart_image e hS hSe
  have hTW : T ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hSN hx).2
  have hST : S = e.val.symm '' T := (e.val.symm_image_image_of_subset_source hSe).symm
  have hι0 := hmeas t₀ (by simpa using hR0) ι hι (fun x => by rw [hμι, ht₀, c₀.left_inv h0c]) T hTm hTW
  -- Fatou
  have := nhdsWithin_projectiveZero_neBot
  have hct : Tendsto (fun p : ProjectiveLine => c₀ p) (𝓝[≠] projectiveZero) (𝓝 t₀) :=
    ((chartAt (ComplexModel 1) projectiveZero).continuousAt h0c).tendsto.mono_left
      nhdsWithin_le_nhds
  have hK : IsCompact (closedBall y₀ R) := isCompact_closedBall y₀ R
  have hTK : T ⊆ closedBall y₀ R := hTW.trans ball_subset_closedBall
  have hfat := eventually_setLIntegral_density_le hct hK hTK hTm (fun y hy =>
    hFsm (t₀, y) (hbox t₀ (by simpa using hR0) y (by
      have := mem_closedBall.mp hy
      linarith))) hε
  have hnear : ∀ᶠ p in 𝓝[≠] projectiveZero, p ≠ projectiveZero ∧ p ∈ c₀.source ∧
      dist (c₀ p) t₀ < R := by
    refine (eventually_mem_nhdsWithin (s := {projectiveZero}ᶜ)).and ?_
    refine Filter.Eventually.and (nhdsWithin_le_nhds
      ((chartAt (ComplexModel 1) projectiveZero).open_source.mem_nhds h0c)) ?_
    exact hct.eventually (ball_mem_nhds t₀ hR0)
  filter_upwards [hfat, hnear] with p hp hpn
  have hsp := hmeas (c₀ p) hpn.2.2 (s p) (hs p)
    (fun x => by rw [hsμ p hpn.1 x, c₀.left_inv hpn.2.1]) T hTm hTW
  rw [hST, hι0, hsp]
  exact hp

end SGPT.Okounkov.TranscendentalWN.LSC

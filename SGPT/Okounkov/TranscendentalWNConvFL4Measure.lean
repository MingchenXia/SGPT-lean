import SGPT.Okounkov.TranscendentalWNConvFL4Coords
import SGPT.Okounkov.TranscendentalWNConvFL4Param
import SGPT.Okounkov.TranscendentalWNKeyLSCExcLocal

/-!
# The fibre measures and the measure on `ℰ` in fibre-disc coordinates

Blueprint `claude-tok-wn-fl4`, node `tok-wn-fl4:coords-measure`; source WN21 §7, proof of
Proposition 7.4 near `ℰ \ X'`.

Let `K : ExcCoords F μ p` (fibre-disc coordinates `Γ(τ, y)`, left inverse `ν`), `ρ` a smooth local
potential of `Θ` on `Wd` in a chart `d` of `𝒳`, and `B` an open ball of parameters `y` with
`Γ(τ, y) ∈ O ∩ d⁻¹(Wd)`.

* `fibre_testMass_eq`: for `τ ≠ 0` and a holomorphic section `s` of `μ` over `[τ : 1]`, if
  `f(y) = u(Γ(τ, y)) + ρ(d(Γ(τ, y))) + c` is bounded on `B`, then `f` is locally bounded psh on `B`
  and `∫_X ρ_t ∘ s d⟨(s^*Θ + dd^c (u ∘ s))ⁿ⟩ = ∫ χ d(dd^c f)ⁿ` for test functions `ρ_t` living
  over `ν⁻¹(B)` with `χ = ρ_t ∘ Γ(τ, ·)`.  The fibre `X_τ` is parametrized by
  `γ_τ : y ↦ π_X(μ(Γ(τ, y)))` (`s ∘ γ_τ = Γ(τ, ·)`), a biholomorphism onto an open set of the chart
  of `X` at `x₀` with inverse `x ↦ ν(s x)`.
* `exc_testMass_eq`: the same on `ℰ`, through `y ↦ Γ(0, y)` (inverse `z ↦ ν z`).

Both follow from `restrictedTestMass_eq_of_param`; the biholomorphic pairs are those of lane
WN-LSC (`LSC.exc_local_transportGood`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN.LSC

/-- Local boundedness and plurisubharmonicity only depend on the values on the domain. -/
theorem isLocallyBoundedPshOn_congr {n : ℕ} {Ω : Opens (ComplexModel n)}
    {f g : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f) (h : EqOn f g Ω) :
    IsLocallyBoundedPshOn Ω g := by
  refine ⟨plurisubharmonicOn_congr_of_isOpen Ω.isOpen hf.1 fun z hz => by
    simp only [h hz], fun z hz => ?_⟩
  obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
  exact ⟨V, hzV, hVΩ, C, fun w hw => by rw [← h (hVΩ hw)]; exact hC w hw⟩

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine} {p : 𝒳}

/-- **The fibre test masses in fibre-disc coordinates.** -/
theorem fibre_testMass_eq (hμ : IsNormalConeDeformation F μ) (K : ExcCoords F μ p)
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (d : ComplexChart (m + 1 + 1) 𝒳)
    {Wd : Set (ComplexModel (m + 1 + 1))} {ρ : ComplexModel (m + 1 + 1) → ℝ}
    (hρ : IsSmoothLocalPotential Θ.val d Wd ρ) {τ : ℂ} (hτ : τ ≠ 0) {s : F.carrier → 𝒳}
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s)
    (hsμ : ∀ x, μ (s x) = (x, affineLinePoint τ)) {u : 𝒳 → EReal}
    (hu : IsThetaPshPotential (ClosedRealOneOneForm.pullback hs Θ).val (fun x => u (s x)))
    (B : Opens (ComplexModel (m + 1)))
    (hB : ∀ y ∈ B, (τ, y) ∈ K.G ∧ K.Γ (τ, y) ∈ K.O ∧ K.Γ (τ, y) ∈ d.val.source ∧
      d.val (K.Γ (τ, y)) ∈ Wd)
    (c : ℝ) {f : ComplexModel (m + 1) → ℝ}
    (hfeq : ∀ y ∈ B, u (K.Γ (τ, y)) + ((ρ (d.val (K.Γ (τ, y))) + c : ℝ) : EReal) = (f y : EReal))
    {M : ℝ} (hM : ∀ y ∈ B, |f y| ≤ M) (ρt : 𝒳 → ℝ) (hρt0 : ∀ z, 0 ≤ ρt z)
    (hsupp : ∀ z, ρt z ≠ 0 → z ∈ K.O ∧ z ∈ d.val.source ∧ d.val z ∈ Wd ∧ K.ν z ∈ B)
    {χ : ComplexModel (m + 1) → ℝ} (hχc : Continuous χ) {L : Set (ComplexModel (m + 1))}
    (hL : IsCompact L) (hLB : L ⊆ B) (hχL : ∀ y, y ∉ L → χ y = 0)
    (hχeq : ∀ y ∈ B, ρt (K.Γ (τ, y)) = χ y) :
    ∃ hf : IsLocallyBoundedPshOn B f, restrictedTestMass hs Θ (fun x => u (s x)) hu ρt =
      ENNReal.ofReal (∫ y, χ y ∂(MongeAmpere.canonicalBedfordTaylorMeasure B f hf)) := by
  classical
  set e : ComplexChart (m + 1) F.carrier := complexChartAt K.x₀ with he
  have hbase : ∀ q ∈ K.G, (μ (K.Γ q)).1 ∈ e.val.source := K.base
  -- `s ∘ γ_τ = Γ(τ, ·)`
  have hsΓ : ∀ y ∈ B, s (μ (K.Γ (τ, y))).1 = K.Γ (τ, y) := by
    intro y hy
    have hfib := K.fibre _ (hB y hy).1
    have hnot : μ (K.Γ (τ, y)) ∉ deformationCentre F := fun h =>
      affineLinePoint_ne_projectiveZero hτ (hfib.symm.trans ((mem_deformationCentre_iff F).mp h).2)
    refine (eq_of_map_eq_of_notMem F hμ hnot ?_).symm
    rw [hsμ]
    exact Prod.ext rfl hfib
  -- points of the fibre near `p`
  have hfibO : ∀ z ∈ K.O, (μ z).2 = affineLinePoint τ → (τ, K.ν z) ∈ K.G ∧ K.Γ (τ, K.ν z) = z :=
    fun z hz h => K.Γ_ν z hz τ h
  set σX : ComplexModel (m + 1) → ComplexModel (m + 1) := fun y => e.val (μ (K.Γ (τ, y))).1
    with hσX
  set τX : ComplexModel (m + 1) → ComplexModel (m + 1) := fun ζ => K.ν (s (e.val.symm ζ))
    with hτX
  set Og : Set 𝒳 := K.O ∩ (d.val.source ∩ d.val ⁻¹' Wd) with hOg
  have hOgo : IsOpen Og := K.isOpen_O.inter (d.val.isOpen_inter_preimage hρ.1)
  set A₀ : Set (ComplexModel (m + 1)) := e.val.target ∩ (fun ζ => s (e.val.symm ζ)) ⁻¹' Og
    with hA₀
  have hA₀o : IsOpen A₀ :=
    (hs.continuous.comp_continuousOn e.val.continuousOn_symm).isOpen_inter_preimage
      e.val.open_target hOgo
  have hτXc : ContinuousOn τX A₀ := by
    intro ζ hζ
    have h1 : ContinuousAt (fun ζ => s (e.val.symm ζ)) ζ :=
      hs.continuous.continuousAt.comp (e.val.continuousAt_symm hζ.1)
    have h2 : ContinuousAt K.ν (s (e.val.symm ζ)) := (K.smooth_ν _ hζ.2.1).continuousAt
    exact (h2.comp_of_eq h1 rfl).continuousWithinAt
  set A : Opens (ComplexModel (m + 1)) := ⟨A₀ ∩ τX ⁻¹' B, hτXc.isOpen_inter_preimage hA₀o B.isOpen⟩
    with hA
  have hAinv : ∀ ζ ∈ A, K.Γ (τ, τX ζ) = s (e.val.symm ζ) ∧ (τ, τX ζ) ∈ K.G := by
    intro ζ hζ
    have h := hfibO _ hζ.1.2.1 (congrArg Prod.snd (hsμ _))
    exact ⟨h.2, h.1⟩
  have hpair : IsBiholomorphicPair B A σX τX := by
    refine ⟨fun y hy => ?_, fun ζ hζ => ?_, fun y hy => ?_, fun ζ hζ => hζ.2, fun y hy => ?_,
      fun ζ hζ => ?_⟩
    · have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
          (fun y => (μ (K.Γ (τ, y))).1) y :=
        ProductComplexManifold.contMDiff_fst.contMDiffAt.comp y
          ((hμ.contMDiff.contMDiffAt).comp y (K.smooth_slice (hB y hy).1))
      exact (contDiffAt_chart_comp h2 e (hbase _ (hB y hy).1)).contDiffWithinAt
    · have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
          e.val.symm ζ :=
        contMDiffOn_chart_symm.contMDiffAt (e.val.open_target.mem_nhds hζ.1.1)
      have h2 := (hs _).comp ζ h1
      have h3 := (K.smooth_ν _ hζ.1.2.1).comp ζ h2
      exact (contMDiffAt_iff_contDiffAt.mp h3).contDiffWithinAt
    · have hsrc := hbase _ (hB y hy).1
      have hl : s (e.val.symm (σX y)) = K.Γ (τ, y) := by
        simp only [hσX]
        rw [e.val.left_inv hsrc]
        exact hsΓ y hy
      refine ⟨⟨e.val.map_source hsrc, ?_⟩, ?_⟩
      · show s (e.val.symm (σX y)) ∈ Og
        rw [hl]
        exact ⟨(hB y hy).2.1, (hB y hy).2.2.1, (hB y hy).2.2.2⟩
      · show K.ν (s (e.val.symm (σX y))) ∈ B
        rw [hl, K.ν_Γ _ (hB y hy).1 (hB y hy).2.1]
        exact hy
    · have hsrc := hbase _ (hB y hy).1
      show K.ν (s (e.val.symm (e.val (μ (K.Γ (τ, y))).1))) = y
      rw [e.val.left_inv hsrc, hsΓ y hy, K.ν_Γ _ (hB y hy).1 (hB y hy).2.1]
    · show e.val (μ (K.Γ (τ, τX ζ))).1 = ζ
      rw [(hAinv ζ hζ).1, hsμ]
      exact e.val.right_inv hζ.1.1
  -- the local potential on `A`
  have hP : IsSmoothLocalPotential (ClosedRealOneOneForm.pullback hs Θ).val e A
      (fun ζ => ρ (d.val (s (e.val.symm ζ))) + c) :=
    isSmoothLocalPotential_pullback_of_eqOn hs Θ hρ e A.isOpen (fun ζ hζ => hζ.1.1)
      (fun ζ hζ => ⟨hζ.1.2.2.1, hζ.1.2.2.2⟩) c (fun _ _ => rfl)
  -- the corrected potential on `A`
  have hgeq : ∀ ζ ∈ A, chartFunction (fun x => u (s x)) e ζ +
      ((ρ (d.val (s (e.val.symm ζ))) + c : ℝ) : EReal) = (f (τX ζ) : EReal) := by
    intro ζ hζ
    show u (s (e.val.symm ζ)) + _ = _
    rw [← (hAinv ζ hζ).1]
    exact hfeq _ hζ.2
  have hg : IsLocallyBoundedPshOn A (fun ζ => f (τX ζ)) :=
    isLocallyBoundedPshOn_of_corrected hu.1 e A hP hgeq (fun ζ hζ => hM _ hζ.2)
  have hf : IsLocallyBoundedPshOn B f := by
    refine isLocallyBoundedPshOn_congr
      (LocalCurrentPullbackDdc.isLocallyBoundedPshOn_comp hpair hg) fun y hy => ?_
    show f (τX (σX y)) = f y
    rw [hpair.left_inv y hy]
  refine ⟨hf, restrictedTestMass_eq_of_param Θ hs hu e A B hpair hP hf (fun y hy => ?_) ρt hρt0
    (fun x hx => ?_) hχc hL hLB hχL (fun y hy => ?_)⟩
  · have hsrc := hbase _ (hB y hy).1
    have hl : s (e.val.symm (σX y)) = K.Γ (τ, y) := by
      simp only [hσX]
      rw [e.val.left_inv hsrc]
      exact hsΓ y hy
    show u (s (e.val.symm (σX y))) + ((ρ (d.val (s (e.val.symm (σX y)))) + c : ℝ) : EReal) = _
    rw [hl]
    exact hfeq y hy
  · obtain ⟨h1, h2, h3, h4⟩ := hsupp _ hx
    have hfx := hfibO _ h1 (congrArg Prod.snd (hsμ x))
    have hxe : x ∈ e.val.source := by
      have := hbase _ hfx.1
      rwa [hfx.2, hsμ] at this
    refine ⟨hxe, ⟨⟨e.val.map_source hxe, ?_⟩, ?_⟩⟩
    · show s (e.val.symm (e.val x)) ∈ Og
      rw [e.val.left_inv hxe]
      exact ⟨h1, h2, h3⟩
    · show K.ν (s (e.val.symm (e.val x))) ∈ B
      rw [e.val.left_inv hxe]
      exact h4
  · have hsrc := hbase _ (hB y hy).1
    show ρt (s (e.val.symm (e.val (μ (K.Γ (τ, y))).1))) = χ y
    rw [e.val.left_inv hsrc, hsΓ y hy]
    exact hχeq y hy

/-- **The test masses on `ℰ` in fibre-disc coordinates.** -/
theorem exc_testMass_eq (hμ : IsNormalConeDeformation F μ) (K : ExcCoords F μ p)
    (hpE : p ∈ exceptionalSet F μ)
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (d : ComplexChart (m + 1 + 1) 𝒳)
    {Wd : Set (ComplexModel (m + 1 + 1))} {ρ : ComplexModel (m + 1 + 1) → ℝ}
    (hρ : IsSmoothLocalPotential Θ.val d Wd ρ) {w : exceptionalSet F μ → EReal}
    (hw : letI := exceptionalChartedSpace F hμ
      haveI := isComplexManifold_exceptional F hμ
      IsThetaPshPotential (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val
        w)
    (B : Opens (ComplexModel (m + 1))) (hy₀B : K.y₀ ∈ B)
    (hB : ∀ y ∈ B, ((0 : ℂ), y) ∈ K.G ∧ K.Γ (0, y) ∈ K.O ∧ K.Γ (0, y) ∈ d.val.source ∧
      d.val (K.Γ (0, y)) ∈ Wd)
    (hBE : letI := exceptionalChartedSpace F hμ
      ∀ y ∈ B, ∀ z : exceptionalSet F μ, z.1 = K.Γ (0, y) →
        z ∈ (complexChartAt (n := m + 1) (⟨p, hpE⟩ : exceptionalSet F μ)).val.source)
    (c : ℝ) {f : ComplexModel (m + 1) → ℝ}
    (hfeq : ∀ y ∈ B, ∀ z : exceptionalSet F μ, z.1 = K.Γ (0, y) →
      w z + ((ρ (d.val z.1) + c : ℝ) : EReal) = (f y : EReal))
    {M : ℝ} (hM : ∀ y ∈ B, |f y| ≤ M) (ρt : 𝒳 → ℝ) (hρt0 : ∀ z, 0 ≤ ρt z)
    (hsupp : ∀ z, ρt z ≠ 0 → z ∈ K.O ∧ z ∈ d.val.source ∧ d.val z ∈ Wd ∧ K.ν z ∈ B)
    {χ : ComplexModel (m + 1) → ℝ} (hχc : Continuous χ) {L : Set (ComplexModel (m + 1))}
    (hL : IsCompact L) (hLB : L ⊆ B) (hχL : ∀ y, y ∉ L → χ y = 0)
    (hχeq : ∀ y ∈ B, ρt (K.Γ (0, y)) = χ y) :
    letI := exceptionalChartedSpace F hμ
    haveI := isComplexManifold_exceptional F hμ
    haveI := compactSpace_exceptional F hμ
    ∃ hf : IsLocallyBoundedPshOn B f,
      restrictedTestMass (contMDiff_exceptionalInclusion F hμ) Θ w hw ρt =
        ENNReal.ofReal (∫ y, χ y ∂(MongeAmpere.canonicalBedfordTaylorMeasure B f hf)) := by
  classical
  let _ := exceptionalChartedSpace F hμ
  have _ := isComplexManifold_exceptional F hμ
  have _ := compactSpace_exceptional F hμ
  set pE : exceptionalSet F μ := ⟨p, hpE⟩ with hpEdef
  set eE : ComplexChart (m + 1) (exceptionalSet F μ) := complexChartAt pE with heE
  have h0 : ∀ z : exceptionalSet F μ, (μ z.1).2 = projectiveZero := fun z =>
    ((mem_deformationCentre_iff F).mp z.2).2
  -- the lift `y ↦ Γ(0, y) ∈ ℰ`
  have hfA : ∀ q : LiftedOpen.{u} B, K.Γ (0, LiftedOpen.toModel B q) ∈ exceptionalSet F μ :=
    fun q => K.exceptional _ (hB _ (LiftedOpen.toModel_mem B q)).1
      (hB _ (LiftedOpen.toModel_mem B q)).2.1
  have hfAs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      (fun q : LiftedOpen.{u} B => K.Γ (0, LiftedOpen.toModel B q)) := fun q =>
    (K.smooth_slice (hB _ (LiftedOpen.toModel_mem B q)).1).comp q
      (LiftedOpen.contMDiff_toModel B q)
  set GA : LiftedOpen.{u} B → exceptionalSet F μ := fun q =>
    ⟨K.Γ (0, LiftedOpen.toModel B q), hfA q⟩ with hGA
  have hGAs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ GA :=
    SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_succ (m + 1))
      (fun _ hz => regularAtDim_exceptionalSet F hμ hz) hfAs hfA
  set pA : LiftedOpen.{u} B := LiftedOpen.mk B K.y₀ hy₀B with hpA
  set gE : ComplexModel (m + 1) → exceptionalSet F μ := fun y => GA (liftMk B pA y) with hgEdef
  have hgE : ∀ y ∈ B, (gE y).1 = K.Γ (0, y) := by
    intro y hy
    simp only [hgEdef, hGA, toModel_liftMk pA hy]
  have hgEs : ∀ y ∈ B, ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      gE y := fun y hy => (hGAs _).comp y (contMDiffAt_liftMk pA hy)
  have hgEsrc : ∀ y ∈ B, gE y ∈ eE.val.source := fun y hy => hBE y hy _ (hgE y hy)
  -- the inverse `z ↦ ν z`
  set σE : ComplexModel (m + 1) → ComplexModel (m + 1) := fun y => eE.val (gE y) with hσE
  set τE : ComplexModel (m + 1) → ComplexModel (m + 1) := fun ζ => K.ν (eE.val.symm ζ).1
    with hτE
  set Og : Set 𝒳 := K.O ∩ (d.val.source ∩ d.val ⁻¹' Wd) with hOg
  have hOgo : IsOpen Og := K.isOpen_O.inter (d.val.isOpen_inter_preimage hρ.1)
  set D₀ : Set (ComplexModel (m + 1)) := eE.val.target ∩ (fun ζ => (eE.val.symm ζ).1) ⁻¹' Og
    with hD₀
  have hD₀o : IsOpen D₀ :=
    (continuous_subtype_val.comp_continuousOn eE.val.continuousOn_symm).isOpen_inter_preimage
      eE.val.open_target hOgo
  have hτEc : ContinuousOn τE D₀ := by
    intro ζ hζ
    have h1 : ContinuousAt (fun ζ => (eE.val.symm ζ).1) ζ :=
      continuous_subtype_val.continuousAt.comp (eE.val.continuousAt_symm hζ.1)
    have h2 : ContinuousAt K.ν (eE.val.symm ζ).1 := (K.smooth_ν _ hζ.2.1).continuousAt
    exact (h2.comp_of_eq h1 rfl).continuousWithinAt
  set DE : Opens (ComplexModel (m + 1)) := ⟨D₀ ∩ τE ⁻¹' B, hτEc.isOpen_inter_preimage hD₀o B.isOpen⟩
    with hDE
  have hDEinv : ∀ ζ ∈ DE, K.Γ (0, τE ζ) = (eE.val.symm ζ).1 ∧ ((0 : ℂ), τE ζ) ∈ K.G := by
    intro ζ hζ
    have h := K.Γ_ν_zero hζ.1.2.1 (h0 _)
    exact ⟨h.2, h.1⟩
  have hpair : IsBiholomorphicPair B DE σE τE := by
    refine ⟨fun y hy => ?_, fun ζ hζ => ?_, fun y hy => ?_, fun ζ hζ => hζ.2, fun y hy => ?_,
      fun ζ hζ => ?_⟩
    · exact (contDiffAt_chart_comp (hgEs y hy) eE (hgEsrc y hy)).contDiffWithinAt
    · have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
          eE.val.symm ζ :=
        contMDiffOn_chart_symm.contMDiffAt (eE.val.open_target.mem_nhds hζ.1.1)
      have h2 := (contMDiff_exceptionalInclusion F hμ _).comp ζ h1
      have h3 := (K.smooth_ν _ hζ.1.2.1).comp ζ h2
      exact (contMDiffAt_iff_contDiffAt.mp h3).contDiffWithinAt
    · have hsrc := hgEsrc y hy
      refine ⟨⟨eE.val.map_source hsrc, ?_⟩, ?_⟩
      · show (eE.val.symm (eE.val (gE y))).1 ∈ Og
        rw [eE.val.left_inv hsrc, hgE y hy]
        exact ⟨(hB y hy).2.1, (hB y hy).2.2.1, (hB y hy).2.2.2⟩
      · show K.ν (eE.val.symm (eE.val (gE y))).1 ∈ B
        rw [eE.val.left_inv hsrc, hgE y hy, K.ν_Γ _ (hB y hy).1 (hB y hy).2.1]
        exact hy
    · have hsrc := hgEsrc y hy
      show K.ν (eE.val.symm (eE.val (gE y))).1 = y
      rw [eE.val.left_inv hsrc, hgE y hy, K.ν_Γ _ (hB y hy).1 (hB y hy).2.1]
    · have hgz : gE (τE ζ) = eE.val.symm ζ := Subtype.ext (by
        rw [hgE _ hζ.2]
        exact (hDEinv ζ hζ).1)
      show eE.val (gE (τE ζ)) = ζ
      rw [hgz, eE.val.right_inv hζ.1.1]
  -- the local potential on `DE`
  have hP : IsSmoothLocalPotential
      (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val eE DE
      (fun ζ => ρ (d.val (eE.val.symm ζ).1) + c) :=
    isSmoothLocalPotential_pullback_of_eqOn (contMDiff_exceptionalInclusion F hμ) Θ hρ eE
      DE.isOpen (fun ζ hζ => hζ.1.1) (fun ζ hζ => ⟨hζ.1.2.2.1, hζ.1.2.2.2⟩) c (fun _ _ => rfl)
  have hgeq : ∀ ζ ∈ DE, chartFunction w eE ζ +
      ((ρ (d.val (eE.val.symm ζ).1) + c : ℝ) : EReal) = (f (τE ζ) : EReal) := by
    intro ζ hζ
    exact hfeq _ hζ.2 _ (hDEinv ζ hζ).1.symm
  have hg : IsLocallyBoundedPshOn DE (fun ζ => f (τE ζ)) :=
    isLocallyBoundedPshOn_of_corrected hw.1 eE DE hP hgeq (fun ζ hζ => hM _ hζ.2)
  have hf : IsLocallyBoundedPshOn B f := by
    refine isLocallyBoundedPshOn_congr
      (LocalCurrentPullbackDdc.isLocallyBoundedPshOn_comp hpair hg) fun y hy => ?_
    show f (τE (σE y)) = f y
    rw [hpair.left_inv y hy]
  refine ⟨hf, restrictedTestMass_eq_of_param Θ (contMDiff_exceptionalInclusion F hμ) hw eE DE B
    hpair hP hf (fun y hy => ?_) ρt hρt0 (fun x hx => ?_) hχc hL hLB hχL (fun y hy => ?_)⟩
  · have hsrc := hgEsrc y hy
    show w (eE.val.symm (eE.val (gE y))) +
      ((ρ (d.val (eE.val.symm (eE.val (gE y))).1) + c : ℝ) : EReal) = _
    rw [eE.val.left_inv hsrc]
    exact hfeq y hy _ (hgE y hy)
  · obtain ⟨h1, h2, h3, h4⟩ := hsupp _ hx
    have hfx := K.Γ_ν_zero h1 (h0 x)
    have hxe : x ∈ eE.val.source := hBE _ h4 x hfx.2.symm
    refine ⟨hxe, ⟨⟨eE.val.map_source hxe, ?_⟩, ?_⟩⟩
    · show (eE.val.symm (eE.val x)).1 ∈ Og
      rw [eE.val.left_inv hxe]
      exact ⟨h1, h2, h3⟩
    · show K.ν (eE.val.symm (eE.val x)).1 ∈ B
      rw [eE.val.left_inv hxe]
      exact h4
  · have hsrc := hgEsrc y hy
    show ρt (eE.val.symm (eE.val (gE y))).1 = χ y
    rw [eE.val.left_inv hsrc, hgE y hy]
    exact hχeq y hy

end SGPT.Okounkov.TranscendentalWN

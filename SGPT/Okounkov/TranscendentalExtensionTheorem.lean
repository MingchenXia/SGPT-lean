import SGPT.Okounkov.TranscendentalExtension

/-!
# The extension theorem in all dimensions (conditional on the pole input)

Blueprint `tok:ct-extension` (package EXT); source: the book's `thm:CT-thm-refined'`, DRWNXZ
Theorem 6.1, FPT `thm:holder-positive-potential-extension`.

* `exists_extension_of_eq` (FPT Step 0, `Y = X`): a closed connected submanifold of dimension `n`
  of a connected manifold is the whole manifold, and `φ` itself is the extension; its
  `θ`-plurisubharmonicity on `X` is read off the local extensions of
  `TranscendentalExtensionLocal` (which reduce to `φ` when `k = n`). No pole is needed.
* `exists_extension` combines it with `exists_extension_of_normalPole` (`k < n`).
* **Conditional results** (they assume `NormalPoleStatement`, the input of package POLE,
  blueprint `tok:ext-pole`): `hasKahlerCurrentExtension_of_normalPoleStatement`,
  `kahlerCurrentExtensionStatement_of_normalPoleStatement` (the book's `thm:CT-thm-refined'`),
  `continuousKahlerCurrentExtensionStatement_of_normalPoleStatement` (DRWNXZ Theorem 6.1 in the
  form of `tok:ct-extension`). The pole input is proved in package POLE
  (`SGPT.Okounkov.TranscendentalPole.normalPoleStatement`); the unconditional versions are in
  `TranscendentalExtensionMain.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A closed connected submanifold of full dimension of a connected manifold is everything. -/
theorem eq_univ_of_isClosedConnectedSubmanifold [ConnectedSpace X] {Y : Set X}
    (hY : IsClosedConnectedSubmanifold n Y n) : Y = univ := by
  have hopen : IsOpen Y := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    let G := FlatData.ofRegularAtDim (hY.2.2 y hy)
    have hyG : y ∈ G.ambSource := FlatData.mem_ambSource_ofRegularAtDim (hY.2.2 y hy)
    filter_upwards [G.isOpen_ambSource.mem_nhds hyG] with x hx
    refine (G.mem_iff x hx.1 hx.2).mpr ?_
    intro i hi
    exact absurd i.2 (not_lt.mpr hi)
  exact IsClopen.eq_univ ⟨hY.1, hopen⟩ hY.2.1.nonempty

/-- `θ`-psh on a neighbourhood of every point is `θ`-psh. -/
theorem thetaPlurisubharmonic_of_locally {θ : SmoothRealForm n X 2} {u : X → EReal}
    (h : ∀ x, ∃ Ω : Set X, x ∈ Ω ∧ ThetaPlurisubharmonicOn θ u Ω) :
    ThetaPlurisubharmonic θ u := by
  intro e z hz
  obtain ⟨Ω, hxΩ, hΩ⟩ := h (e.val.symm z)
  exact hΩ e z hz hxΩ

/-- **The extension for `Y = X`** (FPT Step 0). -/
theorem exists_extension_of_eq [CompactSpace X] [ConnectedSpace X] (ωX : KahlerBackground n X)
    {Y : Set X} (hY : IsClosedConnectedSubmanifold n Y n) (φ : Y → EReal)
    (hKah : letI := submanifoldCharts hY
      haveI := submanifold_isComplexManifold hY
      IsKahlerCurrentPotential (restrictedKahler ωX hY).form φ) :
    ∃ φ' : X → EReal, ∃ ε : ℝ, 0 < ε ∧ IsThetaPshPotential ((1 - ε) • ωX.form).val φ' ∧
      (∀ y : Y, φ' y = φ y) ∧ ContinuousOn φ' Yᶜ ∧ (∀ x ∉ Y, φ' x ≠ ⊥) ∧
      ((letI := submanifoldCharts hY
        HasManifoldAnalyticSingularityType (n := n) φ) →
        HasManifoldAnalyticSingularityType (n := n) φ') := by
  classical
  let _ := submanifoldCharts hY
  have _ := submanifold_isComplexManifold hY
  have hk : n ≤ n := le_rfl
  have hreg := hY.2.2
  have hYu := eq_univ_of_isClosedConnectedSubmanifold hY
  have hmem : ∀ x : X, x ∈ Y := fun x => hYu ▸ mem_univ x
  have _ : CompactSpace Y := isCompact_iff_compactSpace.mp hY.1.isCompact
  obtain ⟨δ, hδ0, hδ1, hφδ⟩ := exists_margin_of_isKahlerCurrentPotential (restrictedKahler ωX hY) hKah
  set c : ℝ := 1 - δ with hc
  have hφc : ThetaPlurisubharmonic
      (c • ClosedRealOneOneForm.pullback (contMDiff_val hk hreg) ωX.form).val φ := hφδ.1
  let φ' : X → EReal := fun x => φ ⟨x, hmem x⟩
  -- local data
  have hloc : ∀ p : X, ∃ (G : FlatData n n X Y) (W : Set (ComplexModel n))
      (ρ : ComplexModel n → ℝ), IsSmoothLocalPotential ωX.form.val G.amb W ρ ∧
        p ∈ localDomain G W := by
    intro p
    let G := FlatData.ofRegularAtDim (hreg p (hmem p))
    have hpG : p ∈ G.ambSource := FlatData.mem_ambSource_ofRegularAtDim (hreg p (hmem p))
    obtain ⟨W, ρ, hpW, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials ωX.form G.amb
      (G.amb.val p) (G.amb.val.map_source hpG.1)
    exact ⟨G, W, ρ, hρ, mem_localDomain_of_mem hk G (hmem p) hpG hpW⟩
  choose G W ρ hρ hpΩ using hloc
  have hext : ∀ p : X, EqOn (localExt (G p) (ρ p) c φ) φ' (localDomain (G p) (W p)) := by
    intro p x hx
    exact localExt_of_mem hk (G p) (ρ p) c φ (hmem x) hx.1.1
  have hpsh : ThetaPlurisubharmonic (c • ωX.form).val φ' := by
    refine thetaPlurisubharmonic_of_locally fun p => ⟨localDomain (G p) (W p), hpΩ p, ?_⟩
    exact thetaOn_congr (isOpen_localDomain _ (hρ p).1)
      (thetaOn_localExt hk hreg ωX.form (G p) (hρ p) c hφc) (hext p)
  have hnd : LocallyNondegenerate φ' := by
    intro x U hU hxU
    obtain ⟨y, hyU, hy⟩ := hφδ.2 ⟨x, hmem x⟩ (Subtype.val ⁻¹' U)
      (hU.preimage continuous_subtype_val) hxU
    exact ⟨y.1, hyU, by simpa [φ'] using hy⟩
  refine ⟨φ', δ, hδ0, ⟨hpsh, hnd⟩, fun y => rfl, ?_, fun x hx => absurd (hmem x) hx, ?_⟩
  · intro x hx; exact absurd (hmem x) hx
  · intro hφan e z hz
    have hxe : e.val.symm z ∈ e.val.source := e.val.map_target hz
    let p := e.val.symm z
    have hxΩ := hpΩ p
    have h1 := hasAnalyticSingularityTypeAt_chart_comp_retr hk hreg (G p) hφan hxΩ.1 e hxe
    rw [e.val.right_inv hz] at h1
    have hcs : ContinuousAt e.val.symm z := e.val.continuousAt_symm hz
    have hcorr : ContinuousAt (fun w => localCorrection (G p) (ρ p) c (e.val.symm w)) z :=
      ((continuousOn_localCorrection (G p) (hρ p).2.2.1.continuousOn c).continuousAt
        ((isOpen_localDomain _ (hρ p).1).mem_nhds hxΩ)).comp hcs
    have h2 := hasAnalyticSingularityTypeAt_add_continuous h1 hcorr
    refine hasAnalyticSingularityTypeAt_congr h2 ?_
    have hev : ∀ᶠ w in 𝓝 z, e.val.symm w ∈ localDomain (G p) (W p) :=
      hcs.preimage_mem_nhds ((isOpen_localDomain _ (hρ p).1).mem_nhds hxΩ)
    filter_upwards [hev] with w hw
    exact hext p hw

/-- **The extension in all dimensions**, given the pole input. -/
theorem exists_extension [CompactSpace X] [ConnectedSpace X] (hpole : NormalPoleStatement.{u})
    (ωX : KahlerBackground n X) {Y : Set X} {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k)
    (φ : Y → EReal)
    (hKah : letI := submanifoldCharts hY
      haveI := submanifold_isComplexManifold hY
      IsKahlerCurrentPotential (restrictedKahler ωX hY).form φ)
    (hHol : letI := submanifoldCharts hY
      IsChartHolder (k := k) (expPotential φ)) :
    ∃ φ' : X → EReal, ∃ ε : ℝ, 0 < ε ∧ IsThetaPshPotential ((1 - ε) • ωX.form).val φ' ∧
      (∀ y : Y, φ' y = φ y) ∧ ContinuousOn φ' Yᶜ ∧ (∀ x ∉ Y, φ' x ≠ ⊥) ∧
      ((letI := submanifoldCharts hY
        HasManifoldAnalyticSingularityType (n := k) φ) →
        HasManifoldAnalyticSingularityType (n := n) φ') := by
  have hkn : k ≤ n := le_of_isClosedConnectedSubmanifold hY
  rcases hkn.lt_or_eq with hlt | heq
  · obtain ⟨F, hF⟩ := hpole n X ωX Y k hY hlt
    exact exists_extension_of_normalPole ωX hY hF φ hKah hHol
  · subst heq
    exact exists_extension_of_eq ωX hY φ hKah

/-- From `(1 - ε) ω`-psh to a Kähler current. -/
theorem isKahlerCurrentPotential_of_one_sub (ωX : KahlerBackground n X) {ε : ℝ} (hε : 0 < ε)
    {u : X → EReal} (hu : IsThetaPshPotential ((1 - ε) • ωX.form).val u) :
    IsKahlerCurrentPotential ωX.form u := by
  refine ⟨KahlerBackground.smul hε ωX, ?_⟩
  rw [KahlerBackground.smul_form]
  have heq : ωX.form - ε • ωX.form = (1 - ε) • ωX.form := by rw [sub_smul, one_smul]
  rw [heq]
  exact hu

theorem isThetaPshPotential_of_one_sub (ωX : KahlerBackground n X) {ε : ℝ} (hε : 0 < ε)
    {u : X → EReal} (hu : IsThetaPshPotential ((1 - ε) • ωX.form).val u) :
    IsThetaPshPotential ωX.form.val u := by
  have h := isThetaPshPotential_mono_smul ωX (show 1 - ε ≤ 1 by linarith) hu
  rwa [one_smul] at h

/-- **DRWNXZ Theorem 6.1, conditional on the pole input** (`tok:ct-extension`). -/
theorem hasContinuousKahlerCurrentExtension_of_normalPoleStatement [CompactSpace X]
    [ConnectedSpace X] (hpole : NormalPoleStatement.{u}) (ωX : KahlerBackground n X) {Y : Set X}
    {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k) :
    HasContinuousKahlerCurrentExtension ωX hY := by
  intro φ _ hKah hHol
  obtain ⟨φ', ε, hε, hpsh, hres, hcont, hne, han⟩ := exists_extension hpole ωX hY φ hKah hHol
  exact ⟨φ', isThetaPshPotential_of_one_sub ωX hε hpsh, hres,
    isKahlerCurrentPotential_of_one_sub ωX hε hpsh, han, hcont, hne⟩

/-- **The book's `thm:CT-thm-refined'`, conditional on the pole input.** -/
theorem hasKahlerCurrentExtension_of_normalPoleStatement [CompactSpace X] [ConnectedSpace X]
    (hpole : NormalPoleStatement.{u}) (ωX : KahlerBackground n X) {Y : Set X} {k : ℕ}
    (hY : IsClosedConnectedSubmanifold n Y k) : HasKahlerCurrentExtension ωX hY := by
  intro φ hφ hKah hHol
  obtain ⟨φ', h1, h2, h3, h4, -⟩ :=
    hasContinuousKahlerCurrentExtension_of_normalPoleStatement hpole ωX hY φ hφ hKah hHol
  exact ⟨φ', h1, h2, h3, h4⟩

/-- **Source `thm:CT-thm-refined'`** (book), **conditional** on `NormalPoleStatement`. -/
theorem kahlerCurrentExtensionStatement_of_normalPoleStatement
    (hpole : NormalPoleStatement.{u}) : KahlerCurrentExtensionStatement.{u} := by
  intro n X _ _ _ _ _ ωX Y k hY
  exact hasKahlerCurrentExtension_of_normalPoleStatement hpole ωX hY

/-- **DRWNXZ Theorem 6.1** (`tok:ct-extension`), **conditional** on `NormalPoleStatement`. -/
theorem continuousKahlerCurrentExtensionStatement_of_normalPoleStatement
    (hpole : NormalPoleStatement.{u}) : ContinuousKahlerCurrentExtensionStatement.{u} := by
  intro n X _ _ _ _ _ ωX Y k hY _
  exact hasContinuousKahlerCurrentExtension_of_normalPoleStatement hpole ωX hY

end SGPT.Okounkov.TranscendentalExtension

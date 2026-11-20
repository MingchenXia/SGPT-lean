import SGPT.Okounkov.PartialBodyGeneral
import SGPT.Okounkov.TranscendentalCoreRepresentative
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms

/-!
# Independence of the representative for partial Okounkov bodies

Source: the book's `def:POBanalsing`, `def:POBKahcurr` and `def:generalPOB` (chapter *The theory
of Okounkov bodies*, section *Transcendental partial Okounkov bodies*): the partial Okounkov body
`Δ_{Y•}(T)` is attached to the current `T ∈ 𝒵₊(X, α)`; blueprint chapter `claude-pob-ds`, node
`claude-pob-ds:representative`.

The Lean bodies (S51) are functions of a presentation `T = θ + dd^c φ` (`θ` a representative of
`α`, `φ ∈ PSH(X, θ)`). Another presentation of the same current is `T = θ' + dd^c (φ - g)` with
`θ' = θ + dd^c g`, `g` smooth (the hypotheses `hg`, `hθθ'` of TN's `thetaPshPotential_sub_smooth`;
a constant `g` with `θ' = θ` covers the normalisation of the potential). Here every body is shown
to be the same for both presentations:

* `partialOkounkovBody_sub_smooth`: the DRWNXZ bodies `Δ(ξ; T) = closure ν(Ω(ξ; T))`;
* `IsKahlerQEA.sub_smooth`: quasi-equisingular approximations by Kähler currents are transported
  (`φ_j ↦ φ_j - g`);
* `kahlerPartialBody_sub_smooth` (`def:POBKahcurr`), `analyticPartialBody_sub_smooth`
  (`def:POBanalsing`), `generalPartialBody_sub_smooth` (`def:generalPOB`);
* `generalPartialBody_add_const`: `Δ(θ; φ + c) = Δ(θ; φ)`;
* `generalPartialBody_eq_of_bottChernRel`: for `{θ} = {θ'}` (TN's `BottChernRel`) there is a smooth
  `g` with `θ' = θ + dd^c g` and `Δ(θ'; φ - g) = Δ(θ; φ)` for every `φ ∈ PSH(X, θ)`.

The proof is the one of `tok:rep-independence` (`TranscendentalCore.representativeIndependence`)
applied to `Ω(ξ; T)`: `φ ↦ φ - g` preserves gentle analytic singularities, Kähler currents, the
singularity order, multiplier ideals and the valuation.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.PartialBody

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial

/-! ### Arithmetic of the transport -/

/-- `(a - r) - (-r) = a` in `EReal` for real `r`. -/
theorem ereal_sub_coe_sub_coe_neg (a : EReal) (r : ℝ) :
    a - (r : EReal) - ((-r : ℝ) : EReal) = a := by
  rw [ereal_sub_coe_eq_add_coe_neg, ereal_sub_coe_eq_add_coe_neg, add_assoc, ← EReal.coe_add,
    neg_neg, neg_add_cancel, EReal.coe_zero, add_zero]

section Transport

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {θ θ' : ClosedRealOneOneForm n M} {g : M → ℝ}

/-- `θ = θ' + dd^c (-g)` if `θ' = θ + dd^c g`. -/
theorem coeff_shift_symm (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z) :
    ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ.val.coeff e z =
        θ'.val.coeff e z + smoothDDC (fun y => (fun x => -g x) (e.val.symm y)) z := by
  intro e z hz
  rw [smoothDDC_neg e.val.open_target (hg e) hz, hθθ' e z hz, add_neg_cancel_right]

/-- `θ' + γ = (θ + γ) + dd^c g` if `θ' = θ + dd^c g`. -/
theorem coeff_shift_add (hθθ' : ∀ (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    (γ : ClosedRealOneOneForm n M) :
    ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      (θ' + γ).val.coeff e z = (θ + γ).val.coeff e z +
        smoothDDC (fun y => g (e.val.symm y)) z := by
  intro e z hz
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, hθθ' e z hz]
  abel

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Pointwise decreasing convergence is preserved by subtracting a real function. -/
theorem decreasesPointwiseTo_sub {U : ℕ → M → EReal} {φ : M → EReal}
    (h : DecreasesPointwiseTo U φ) (g : M → ℝ) :
    DecreasesPointwiseTo (fun j x => U j x - (g x : EReal)) (fun x => φ x - (g x : EReal)) := by
  refine ⟨fun x i j hij => ?_, fun x => ?_⟩
  · simp only [ereal_sub_coe_eq_add_coe_neg]
    exact add_le_add (h.1 x hij) le_rfl
  · simp only [ereal_sub_coe_eq_add_coe_neg]
    have hc : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (φ x, ((-g x : ℝ) : EReal)) :=
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
    exact hc.tendsto.comp ((h.2 x).prodMk_nhds tendsto_const_nhds)

end Transport

section Flag

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n} {θ θ' : ClosedRealOneOneForm n F.carrier}
  {g : F.carrier → ℝ}

/-- `Ω(ξ; T)` is transported: `s ∈ Ω({θ}; φ)` gives `s - g ∈ Ω({θ'}; φ - g)`. -/
theorem sub_mem_gentleKahlerCurrentsBelow (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n F.carrier) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ s : F.carrier → EReal} (hs : s ∈ gentleKahlerCurrentsBelow θ φ) :
    (fun x => s x - (g x : EReal)) ∈ gentleKahlerCurrentsBelow θ' (fun x => φ x - (g x : EReal)) :=
  ⟨sub_mem_gentleKahlerCurrents hg hθθ' hs.1, (singularityLE_sub_smooth_iff hg).mpr hs.2⟩

/-- `ν(Ω({θ}; φ)) ⊆ ν(Ω({θ'}; φ - g))`. -/
theorem image_gentleKahlerCurrentsBelow_subset_sub (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n F.carrier) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    (φ : F.carrier → EReal) :
    flagValuation F '' gentleKahlerCurrentsBelow θ φ ⊆
      flagValuation F '' gentleKahlerCurrentsBelow θ' (fun x => φ x - (g x : EReal)) := by
  rintro _ ⟨s, hs, rfl⟩
  have hsθ := isThetaPshPotential_of_mem_gentleCurrents hs.1.1
  exact ⟨_, sub_mem_gentleKahlerCurrentsBelow hg hθθ' hs,
    flagValuation_sub_smooth hsθ hg (thetaPshPotential_sub_smooth hg hθθ' hsθ)⟩

/-- **Independence of the presentation, DRWNXZ bodies**: for `θ' = θ + dd^c g` (`g` smooth),
`Δ({θ'}; φ - g) = Δ({θ}; φ)`, i.e. `closure ν(Ω(ξ; T))` only depends on `T = θ + dd^c φ`. -/
theorem partialOkounkovBody_sub_smooth (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n F.carrier) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    (φ : F.carrier → EReal) :
    partialOkounkovBody F θ' (fun x => φ x - (g x : EReal)) = partialOkounkovBody F θ φ := by
  refine (closure_mono ?_).antisymm (closure_mono
    (image_gentleKahlerCurrentsBelow_subset_sub hg hθθ' φ))
  have hg' : ChartSmooth (n := n) (fun x => -g x) := fun e => (hg e).neg
  have h := image_gentleKahlerCurrentsBelow_subset_sub (θ := θ') (θ' := θ)
    (g := fun x => -g x) hg' (coeff_shift_symm hg hθθ') (fun x => φ x - (g x : EReal))
  have hfun : (fun x => φ x - (g x : EReal) - ((-g x : ℝ) : EReal)) = φ := by
    funext x
    exact ereal_sub_coe_sub_coe_neg (φ x) (g x)
  rwa [hfun] at h

/-- Multiplier-ideal inclusions are transported by subtracting a continuous function. -/
theorem multiplierIdealIncluded_sub {U φ : F.carrier → EReal}
    (hU : ManifoldQuasiPlurisubharmonic (n := n) U)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (hg : Continuous g)
    (hUg : ManifoldQuasiPlurisubharmonic (n := n) (fun x => U x - (g x : EReal)))
    (hφg : ManifoldQuasiPlurisubharmonic (n := n) (fun x => φ x - (g x : EReal)))
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (h : MultiplierIdealIncluded (n := n) U d φ c) :
    MultiplierIdealIncluded (n := n) (fun x => U x - (g x : EReal)) d
      (fun x => φ x - (g x : EReal)) c := by
  have h1 := (iEquivalentOnManifold_sub_continuous hU hg hUg).1 d hd
  have h2 := (iEquivalentOnManifold_sub_continuous hφ hg hφg).2 c hc
  intro e z hz f hf hmem
  exact h2 e z hz f hf (h e z hz f hf (h1 e z hz f hf hmem))

/-- **Quasi-equisingular approximations are transported**: if `(φ_j)` is a quasi-equisingular
approximation of `φ` in `PSH(X, θ)` (`def:quasiequsing`), then `(φ_j - g)` is one of `φ - g` in
`PSH(X, θ')`, `θ' = θ + dd^c g`. -/
theorem sourceQuasiEquisingularApproximation_sub_smooth (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n F.carrier) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : F.carrier → EReal} {U : ℕ → F.carrier → EReal}
    (h : SourceQuasiEquisingularApproximation θ φ U) :
    SourceQuasiEquisingularApproximation θ' (fun x => φ x - (g x : EReal))
      (fun j x => U j x - (g x : EReal)) := by
  obtain ⟨hφ, ha, hd, ⟨ω, ε, hε, ht⟩, hI⟩ := h
  have hgc := Pending.ProductTestForms.ChartSmooth.continuous hg
  have hφg := thetaPshPotential_sub_smooth hg hθθ' hφ
  have hU : ∀ j, IsThetaPshPotential (θ + ε j • ω.form).val (U j) := ht
  have hUg : ∀ j, IsThetaPshPotential (θ' + ε j • ω.form).val (fun x => U j x - (g x : EReal)) :=
    fun j => thetaPshPotential_sub_smooth hg (coeff_shift_add hθθ' (ε j • ω.form)) (hU j)
  refine ⟨hφg, fun j => hasManifoldAnalyticSingularityType_sub_continuous (ha j) hgc,
    decreasesPointwiseTo_sub hd g, ⟨ω, ε, hε, hUg⟩, fun c d hc hcd => ?_⟩
  obtain ⟨j, hj⟩ := hI c d hc hcd
  exact ⟨j, multiplierIdealIncluded_sub (hU j).quasiPshPotential.1 hφ.quasiPshPotential.1 hgc
    (hUg j).quasiPshPotential.1 hφg.quasiPshPotential.1 hc (hc.trans hcd) hj⟩

end Flag

section Body

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
  {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier} {g : F.carrier → ℝ}

/-- **Kähler approximations are transported** along `θ' = θ + dd^c g`. -/
theorem IsKahlerQEA.sub_smooth (hg : ChartSmooth (n := m + 1) g)
    (hθθ' : ∀ (e : ComplexChart (m + 1) F.carrier) (z : ComplexModel (m + 1)),
      z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : F.carrier → EReal} {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U) :
    IsKahlerQEA θ' (fun x => φ x - (g x : EReal)) (fun j x => U j x - (g x : EReal)) :=
  ⟨sourceQuasiEquisingularApproximation_sub_smooth hg hθθ' hU.1, fun j =>
    ⟨sub_mem_globalAnalyticCurrents hg hθθ' (hU.2 j).1,
      isKahlerCurrentPotential_sub_smooth hg hθθ' (hU.2 j).2⟩⟩

/-- **`def:POBKahcurr` depends only on the current**: for a Kähler current
`T = θ + dd^c φ = θ' + dd^c (φ - g)` (`θ' = θ + dd^c g`), `Δ_{Y•}(θ'; φ - g) = Δ_{Y•}(θ; φ)`. -/
theorem kahlerPartialBody_sub_smooth (hg : ChartSmooth (n := m + 1) g)
    (hθθ' : ∀ (e : ComplexChart (m + 1) F.carrier) (z : ComplexModel (m + 1)),
      z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    kahlerPartialBody F θ' (fun x => φ x - (g x : EReal)) = kahlerPartialBody F θ φ := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  rw [kahlerPartialBody_eq_iInter (hU.sub_smooth hg hθθ'), kahlerPartialBody_eq_iInter hU]
  exact iInter_congr fun j => partialOkounkovBody_sub_smooth hg hθθ' (U j)

/-- **`def:POBanalsing` depends only on the current**: for a Kähler current with analytic
singularities (of a global type) `T = θ + dd^c φ = θ' + dd^c (φ - g)`,
`Δ_{Y•}(θ'; φ - g) = Δ_{Y•}(θ; φ)`. -/
theorem analyticPartialBody_sub_smooth (hg : ChartSmooth (n := m + 1) g)
    (hθθ' : ∀ (e : ComplexChart (m + 1) F.carrier) (z : ComplexModel (m + 1)),
      z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : F.carrier → EReal} (hφA : φ ∈ globalAnalyticCurrents θ)
    (hφ : IsKahlerCurrentPotential θ φ) :
    analyticPartialBody F θ' (fun x => φ x - (g x : EReal)) = analyticPartialBody F θ φ := by
  rw [← kahlerPartialBody_eq_analyticPartialBody (sub_mem_globalAnalyticCurrents hg hθθ' hφA)
    (isKahlerCurrentPotential_sub_smooth hg hθθ' hφ),
    ← kahlerPartialBody_eq_analyticPartialBody hφA hφ]
  exact kahlerPartialBody_sub_smooth hg hθθ' hφ

/-- **`def:generalPOB` depends only on the current**: for `T = θ + dd^c φ ∈ 𝒵₊(X, α)` and another
representative `θ' = θ + dd^c g` of `α` (`g` smooth), `T = θ' + dd^c (φ - g)` and
`Δ_{Y•}(θ'; φ - g) = Δ_{Y•}(θ; φ)`. -/
theorem generalPartialBody_sub_smooth (hg : ChartSmooth (n := m + 1) g)
    (hθθ' : ∀ (e : ComplexChart (m + 1) F.carrier) (z : ComplexModel (m + 1)),
      z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    generalPartialBody F θ' (fun x => φ x - (g x : EReal)) = generalPartialBody F θ φ := by
  refine iInter_congr fun j => ?_
  exact kahlerPartialBody_sub_smooth hg (coeff_shift_add hθθ' _)
    (isKahlerCurrentPotential_add_smul hφ F.omega (by positivity))

/-- `Δ_{Y•}(θ; φ + c) = Δ_{Y•}(θ; φ)` for every real constant `c` (the body depends on the
current `θ + dd^c φ`, not on the normalisation of `φ`). -/
theorem generalPartialBody_add_const {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (c : ℝ) :
    generalPartialBody F θ (fun x => φ x + (c : EReal)) = generalPartialBody F θ φ := by
  have hg : ChartSmooth (n := m + 1) (fun _ : F.carrier => -c) := fun _ => contDiffOn_const
  have hθθ : ∀ (e : ComplexChart (m + 1) F.carrier) (z : ComplexModel (m + 1)),
      z ∈ e.val.target → θ.val.coeff e z = θ.val.coeff e z +
        smoothDDC (fun y => (fun _ : F.carrier => -c) (e.val.symm y)) z := by
    intro e z hz
    rw [GlobalPotentialTransforms.smoothDDC_const, add_zero]
  have h := generalPartialBody_sub_smooth hg hθθ hφ
  have hfun : (fun x => φ x - (((fun _ : F.carrier => -c) x : ℝ) : EReal)) =
      fun x => φ x + (c : EReal) := by
    funext x
    rw [ereal_sub_coe_eq_add_coe_neg, neg_neg]
  rwa [hfun] at h

/-- **Independence of the representative** (`def:generalPOB`): if `{θ} = {θ'}`, there is a smooth
`g` with `θ' = θ + dd^c g`, and then `Δ_{Y•}(θ'; φ - g) = Δ_{Y•}(θ; φ)` for every
`φ ∈ PSH(X, θ)`; i.e. `Δ_{Y•}(T)` only depends on `T ∈ 𝒵₊(X, α)`. -/
theorem generalPartialBody_eq_of_bottChernRel (h : ClosedRealOneOneForm.BottChernRel θ θ') :
    ∃ g : F.carrier → ℝ, ChartSmooth (n := m + 1) g ∧
      (∀ (e : ComplexChart (m + 1) F.carrier) (z : ComplexModel (m + 1)), z ∈ e.val.target →
        θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z) ∧
      ∀ φ : F.carrier → EReal, IsThetaPshPotential θ.val φ →
        IsThetaPshPotential θ'.val (fun x => φ x - (g x : EReal)) ∧
          generalPartialBody F θ' (fun x => φ x - (g x : EReal)) = generalPartialBody F θ φ := by
  obtain ⟨g, hg, hθθ'⟩ := h
  exact ⟨g, hg, hθθ', fun φ hφ =>
    ⟨thetaPshPotential_sub_smooth hg hθθ' hφ, generalPartialBody_sub_smooth hg hθθ' hφ⟩⟩

end Body

end SGPT.Okounkov.PartialBody

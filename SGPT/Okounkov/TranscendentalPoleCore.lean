import SGPT.Okounkov.TranscendentalPoleExtension
import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# The pole along a submanifold and the classes `𝒜`, `𝒜ᵍ`, `Ω`

Source: DRWNXZ, proof of Proposition 3.4 (the Kähler currents `T_i = ω + ε ddᶜ ψ_i` built from
the poles `ψ_i` of the members of the flag lie in `Ω(X, {ω})`). Blueprint nodes `tok:ext-pole`,
`tok:body-interior`, `tok:def-classes`.

For a pole `F` along `V` (`IsSubmanifoldPole`) and `c ∈ ℚ_{>0}`:

* `IsSubmanifoldPole.hasManifoldAnalyticSingularityType`: `c F` has analytic singularities in
  every holomorphic chart (the convention of `TranscendentalCore.analyticCurrents`);
* `IsSubmanifoldPole.mem_analyticCurrents`, `IsSubmanifoldPole.mem_globalAnalyticCurrents`: if
  `c F ∈ PSH(X, θ)`, then `c F ∈ 𝒜(θ)` and `c F ∈ 𝒜ᵍ(θ)` (type `(c, 𝓘_V)`);
* `IsSubmanifoldPole.exists_mem_gentleKahlerCurrents`: there is `ε₀ > 0` such that for every
  rational `0 < ε ≤ ε₀`, `ω + ddᶜ(ε F) ≥ ω / 2`, i.e. `ε F ∈ Ω({ω})`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPole

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {omega : KahlerBackground n X} {V : Set X} {F : X → EReal}

namespace IsSubmanifoldPole

/-- `c F` has analytic singularities of type `(c, 𝓘_V)`. -/
theorem hasAnalyticSingularitiesOfType_smul (hF : IsSubmanifoldPole omega V F) {c : ℚ}
    (hc : 0 < c) :
    HasAnalyticSingularitiesOfType (n := n) (fun x => ((c : ℝ) : EReal) * F x) c
      (vanishingIdeal (n := n) V) :=
  (hF.gentle c hc).2.2.1

/-- `c F` has analytic singularities in every holomorphic chart. -/
theorem hasManifoldAnalyticSingularityType (hF : IsSubmanifoldPole omega V F) {c : ℚ}
    (hc : 0 < c) :
    HasManifoldAnalyticSingularityType (n := n) (fun x => ((c : ℝ) : EReal) * F x) :=
  hasManifoldAnalyticSingularityType_of_hasAnalyticSingularitiesOfType
    (hF.hasAnalyticSingularitiesOfType_smul hc)

/-- `c F ∈ 𝒜(θ)` whenever `c F ∈ PSH(X, θ)`. -/
theorem mem_analyticCurrents (hF : IsSubmanifoldPole omega V F) {c : ℚ} (hc : 0 < c)
    {θ : ClosedRealOneOneForm n X}
    (hθ : IsThetaPshPotential θ.val (fun x => ((c : ℝ) : EReal) * F x)) :
    (fun x => ((c : ℝ) : EReal) * F x) ∈ TranscendentalCore.analyticCurrents θ :=
  ⟨hθ, hF.hasManifoldAnalyticSingularityType hc⟩

/-- `c F ∈ 𝒜ᵍ(θ)` (type `(c, 𝓘_V)`) whenever `c F ∈ PSH(X, θ)`. -/
theorem mem_globalAnalyticCurrents (hF : IsSubmanifoldPole omega V F) {c : ℚ} (hc : 0 < c)
    {θ : ClosedRealOneOneForm n X}
    (hθ : IsThetaPshPotential θ.val (fun x => ((c : ℝ) : EReal) * F x)) :
    (fun x => ((c : ℝ) : EReal) * F x) ∈ TranscendentalCore.globalAnalyticCurrents θ :=
  ⟨hθ, c, vanishingIdeal (n := n) V, hF.hasAnalyticSingularitiesOfType_smul hc⟩

/-- **Small rational multiples of a pole are gentle Kähler potentials of `ω`**: for
`0 < ε ≤ ε₀`, `ω + ddᶜ(ε F) ≥ ω/2` and `ε F` has gentle analytic singularities of type
`(ε, 𝓘_V)`, so `ε F ∈ Ω({ω})` (DRWNXZ Proposition 3.4: `T = ω + ε ddᶜ ψ` with `ε C < 1`). -/
theorem exists_mem_gentleKahlerCurrents (hF : IsSubmanifoldPole omega V F) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → (ε : ℝ) ≤ ε₀ →
      (fun x => ((ε : ℝ) : EReal) * F x) ∈ TranscendentalCore.gentleKahlerCurrents omega.form := by
  obtain ⟨C, hC, hpsh⟩ := hF.exists_thetaPsh
  refine ⟨1 / (2 * (C + 1)), by positivity, fun ε hε hεle => ?_⟩
  have hεR : (0 : ℝ) < ε := Rat.cast_pos.mpr hε
  have hεC : (ε : ℝ) * C ≤ 1 / 2 := by
    have h1 : (ε : ℝ) * (2 * (C + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hεle
      linarith
    nlinarith
  have h1 := PotentialMassComparison.isThetaPshPotential_smul hpsh hεR
  have hsemi : (((1 / 2 : ℝ) - ε * C) • omega.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omega.isSemipositive (by linarith)
  have h2 := LocalPotentials.isThetaPshPotential_add_of_semipositive h1 hsemi
  set omega' : KahlerBackground n X := KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 2) omega
  have heq : (ε : ℝ) • (C • omega.form) + ((1 / 2 : ℝ) - ε * C) • omega.form =
      omega.form - omega'.form := by
    rw [KahlerBackground.smul_form]
    module
  rw [heq] at h2
  have hsemi' : omega'.form.val.IsSemipositive := omega'.isSemipositive
  have h3 := LocalPotentials.isThetaPshPotential_add_of_semipositive h2 hsemi'
  rw [sub_add_cancel] at h3
  exact ⟨⟨h3, ε, vanishingIdeal (n := n) V, hF.gentle ε hε⟩, omega', h2⟩

end IsSubmanifoldPole

end SGPT.Okounkov.TranscendentalPole

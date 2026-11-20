import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.PSH.SourceGentleApproximation
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation

/-!
# Gentle Kähler currents below Kähler currents

Source: blueprint node `tok:sing-decrease`, parts (a) and (b) (DRWNXZ Theorem 2.7, Demailly
regularization via the book's `thm:qequi`, and Lemma 2.9).

(a) If `T = θ + dd^c φ ≥ κ` is a Kähler current (`κ` a Kähler form), the book's `thm:qequi`
(`SGPT.PSH.exists_sourceGentleQuasiEquisingularApproximation`) applied to
`φ ∈ PSH(X, θ - κ/2)` gives potentials `φ_j` with gentle analytic singularities of type
`(2^{-j}, 𝓘(2^j φ))`, decreasing to `φ`, with `φ_j ∈ PSH(X, θ - κ/2 + ε_j ω₀)`, `ε_j → 0`. Since
`ω₀ ≤ C κ` on the compact manifold (`KahlerDomination`), `θ + dd^c φ_j ≥ κ/4` as soon as
`ε_j C ≤ 1/4` (the *Kähler-preserving shift*).

(b) For two Kähler currents `θ + dd^c φ₁ ≥ κ₁`, `θ + dd^c φ₂ ≥ κ₂` of the same class,
`max(φ₁, φ₂) ∈ PSH(X, θ - t κ₁)` for `t > 0` with `t κ₁ ≤ κ₂`, `t ≤ 1`; (a) applied to the maximum
gives `ψ ∈ Ω(ξ)` less singular than both. In particular `Ω(ξ) ≠ ∅` for a big class `ξ`
(the class form is in `TranscendentalBodyConvex`).

Part (c) of the node (Demailly's Lelong number estimate) is not used by the items of
`thm:Okounkovtranmain` proved by the BODY package and is not formalized here.

## Main results

* `exists_gentle_approximation_of_kahlerCurrent`: part (a).
* `exists_mem_gentleKahlerCurrents_ge`: a gentle Kähler current less singular than (indeed
  pointwise above) a given Kähler current, with the explicit lower bound `κ/4`.
* `exists_mem_gentleKahlerCurrents_singularityLE`: part (b).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalBody

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.Okounkov.TranscendentalCore

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

omit [CompactSpace X] in
/-- Adding a semipositive form to the background preserves quasi-plurisubharmonicity, written
as a comparison `θ ≤ θ'` of backgrounds. -/
theorem isThetaPshPotential_of_le {θ θ' : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (h : (θ' - θ).val.IsSemipositive) :
    IsThetaPshPotential θ'.val φ := by
  have h' := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ h
  rwa [add_sub_cancel] at h'

/-- **Blueprint `tok:sing-decrease` (a)** (DRWNXZ Theorem 2.7; the book's `thm:qequi` with the
Kähler-preserving shift): if `θ + dd^c φ ≥ κ` for a Kähler form `κ`, there are potentials `φ_j`
with gentle analytic singularities of type `(2^{-(j+1)}, 𝓘(2^{j+1} φ))`, decreasing pointwise
to `φ` (so `φ ≤ φ_j`), with `θ + dd^c φ_j ≥ κ/4` for all large `j`. -/
theorem exists_gentle_approximation_of_kahlerCurrent {θ : ClosedRealOneOneForm n X}
    {κ : KahlerBackground n X} {φ : X → EReal} (hφ : IsThetaPshPotential (θ - κ.form).val φ) :
    ∃ v : ℕ → X → EReal, DecreasesPointwiseTo v φ ∧
      (∀ j, SourceGentleAnalyticSingularities (v j) (((2 ^ (j + 1) : ℕ) : ℚ)⁻¹)
        (multiplierIdeal (n := n) ((2 ^ (j + 1) : ℕ) : ℝ) φ)) ∧
      ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → IsThetaPshPotential (θ - (1 / 4 : ℝ) • κ.form).val (v j) := by
  -- `φ ∈ PSH(X, θ - κ/2)`
  have hφ2 : IsThetaPshPotential (θ - (1 / 2 : ℝ) • κ.form).val φ := by
    refine isThetaPshPotential_of_le hφ ?_
    have heq : θ - (1 / 2 : ℝ) • κ.form - (θ - κ.form) = (1 / 2 : ℝ) • κ.form := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num)
  obtain ⟨v, hqea, hgentle⟩ := exists_sourceGentleQuasiEquisingularApproximation κ _ hφ2
  obtain ⟨-, -, hdec, ⟨ω₀, ε, hε, hterm⟩, -⟩ := hqea
  refine ⟨v, hdec, hgentle, ?_⟩
  -- `ω₀ ≤ C κ`
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-ω₀.form)
  have hev : ∀ᶠ j in atTop, ε j < 1 / (4 * C) :=
    hε.2.2.eventually (gt_mem_nhds (by positivity))
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
  refine ⟨j₀, fun j hj => ?_⟩
  refine isThetaPshPotential_of_le (hterm j) ?_
  have hεj := hj₀ j hj
  have hε0 := hε.1 j
  have heq : θ - (1 / 4 : ℝ) • κ.form - (θ - (1 / 2 : ℝ) • κ.form + ε j • ω₀.form) =
      ε j • (-ω₀.form + C • κ.form) + (1 / 4 - ε j * C) • κ.form := by module
  rw [heq]
  refine UniformPerturbedKahlerLowerBound.isSemipositive_add
    (KahlerDomination.isSemipositive_smul hdom hε0)
    (KahlerDomination.isSemipositive_smul κ.isSemipositive ?_)
  have : ε j * C < 1 / 4 := by
    rw [lt_div_iff₀ (by positivity)] at hεj
    nlinarith
  linarith

/-- A potential of a Kähler current `θ + dd^c φ ≥ κ` lies below a gentle potential `ψ` with
`θ + dd^c ψ ≥ κ/4` (blueprint `tok:sing-decrease` (a)). -/
theorem exists_mem_gentleKahlerCurrents_ge {θ : ClosedRealOneOneForm n X}
    {κ : KahlerBackground n X} {φ : X → EReal} (hφ : IsThetaPshPotential (θ - κ.form).val φ) :
    ∃ ψ : X → EReal, ψ ∈ gentleKahlerCurrents θ ∧
      IsThetaPshPotential (θ - (1 / 4 : ℝ) • κ.form).val ψ ∧ ∀ x, φ x ≤ ψ x := by
  obtain ⟨v, hdec, hgentle, j₀, hj₀⟩ := exists_gentle_approximation_of_kahlerCurrent hφ
  have hψ := hj₀ j₀ le_rfl
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hψθ : IsThetaPshPotential θ.val (v j₀) := by
    refine isThetaPshPotential_of_le hψ ?_
    have heq : θ - (θ - (1 / 4 : ℝ) • κ.form) = (1 / 4 : ℝ) • κ.form := by abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ.isSemipositive hquarter.le
  refine ⟨v j₀, ⟨⟨hψθ, _, _, hgentle j₀⟩, KahlerBackground.smul hquarter κ, ?_⟩, hψ,
    fun x => ?_⟩
  · simpa only [KahlerBackground.smul_form] using hψ
  · exact (hdec.1 x).le_of_tendsto (hdec.2 x) j₀

/-- **Blueprint `tok:sing-decrease` (b)** (DRWNXZ Lemma 2.9): for two Kähler currents
`θ + dd^c φ₁`, `θ + dd^c φ₂` of the same class there is `ψ ∈ Ω(ξ)` less singular than both. -/
theorem exists_mem_gentleKahlerCurrents_singularityLE {θ : ClosedRealOneOneForm n X}
    {φ₁ φ₂ : X → EReal} (h₁ : IsKahlerCurrentPotential θ φ₁)
    (h₂ : IsKahlerCurrentPotential θ φ₂) :
    ∃ ψ ∈ gentleKahlerCurrents θ, SingularityLE φ₁ ψ ∧ SingularityLE φ₂ ψ := by
  obtain ⟨κ₁, hκ₁⟩ := h₁
  obtain ⟨κ₂, hκ₂⟩ := h₂
  -- a common Kähler lower bound `t κ₁`, `t ≤ 1`, `t κ₁ ≤ κ₂`
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ₂ (-κ₁.form)
  set t : ℝ := 1 / (C + 1) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; linarith
  have hφ₁ : IsThetaPshPotential (θ - (KahlerBackground.smul ht0 κ₁).form).val φ₁ := by
    refine isThetaPshPotential_of_le hκ₁ ?_
    have heq : θ - (KahlerBackground.smul ht0 κ₁).form - (θ - κ₁.form) = (1 - t) • κ₁.form := by
      rw [KahlerBackground.smul_form]; module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul κ₁.isSemipositive (by linarith)
  have hφ₂ : IsThetaPshPotential (θ - (KahlerBackground.smul ht0 κ₁).form).val φ₂ := by
    refine isThetaPshPotential_of_le hκ₂ ?_
    have heq : θ - (KahlerBackground.smul ht0 κ₁).form - (θ - κ₂.form) =
        t • (-κ₁.form + C • κ₂.form) + (1 - t * C) • κ₂.form := by
      rw [KahlerBackground.smul_form]; module
    rw [heq]
    refine UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hdom ht0.le)
      (KahlerDomination.isSemipositive_smul κ₂.isSemipositive ?_)
    have : t * C ≤ 1 := by
      rw [ht, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    linarith
  obtain ⟨ψ, hψ, -, hle⟩ := exists_mem_gentleKahlerCurrents_ge
    (SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max hφ₁ hφ₂)
  exact ⟨ψ, hψ, ⟨0, fun x _ => by simpa using (le_max_left _ _).trans (hle x)⟩,
    ⟨0, fun x _ => by simpa using (le_max_right _ _).trans (hle x)⟩⟩

end SGPT.Okounkov.TranscendentalBody

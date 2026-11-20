import SGPT.IGood.DXLowMass

/-!
# The lower bound of the asymptotic Riemann–Roch formula for Kähler currents smooth off their poles

Blueprint `claude-dx-low`, node `claude-dx-low:main`. Source `thm:DXmain1` / `prop:DXmainanalytic`
(chapter *`𝓘`-good singularities*), the inequality `≥`, in the book's analytic setting: `X` a
compact complex manifold with a Kähler form `ω`, `(L, h_L)`, `(T, h_T)` Hermitian holomorphic line
bundles with smooth metrics, `θ = c₁(L, h_L)`, `μ` a smooth positive volume.

`diagonalPotentialMass_le_liminf_finrank`: if `φ ∈ PSH(X, θ - δω)` for some `δ > 0` (so `θ_φ` is a
Kähler current) and `φ` is smooth off its pole set (e.g. `φ` has neat analytic singularities),
then

`∫_X θ_φⁿ ≤ liminf_{k → ∞} (n!/kⁿ) h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`,

with `h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) = dim LiteralTwistedMultiplierSections L T k φ` (the global sections
of the sheaf `L^k ⊗ T ⊗ 𝓘(kφ)`, `def:Bergman:L778`) and `∫_X θ_φⁿ` the non-pluripolar mass
`diagonalPotentialMass θ φ`.

`iVolume_le_liminf_finrank`: the same with `vol θ_φ = ∫_X θ_{P_θ[φ]_𝓘}ⁿ` (`iVolume`) on the left,
for `𝓘`-good `φ` (`vol θ_φ = ∫_X θ_φⁿ`, which holds for analytic singularities, `ex:analyIgood`).

Proof: the Fatou step (`sum_lintegral_le_liminf_finrank`, built on the sharp peak sections of
`DXLowPointwise` and the Bergman majorant of `DXLowTrace`) and the mass identification
(`diagonalPotentialMass_le_sum_lintegral`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
  SGPT.Bergman.PolynomialH0Growth
open SGPT.PSH.GlobalL2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

namespace SGPT.IGood.DXLow

/-- **The lower bound of the asymptotic Riemann–Roch formula, Kähler currents smooth off their
poles** (blueprint `claude-dx-low:main`; source `thm:DXmain1`, `prop:DXmainanalytic`, `≥`):
`∫_X θ_φⁿ ≤ liminf_k (n!/kⁿ) h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. -/
theorem diagonalPotentialMass_le_liminf_finrank (hn : 0 < n) (ωb : KahlerBackground n X)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {θ : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ) {δ : ℝ} (hδ : 0 < δ)
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (hφθ : IsThetaPshPotential θ.val φ) (hsm : SmoothOffPoleSet (n := n) φ) :
    diagonalPotentialMass θ φ hφθ ≤
      liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
        (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ≥0∞)) atTop := by
  obtain ⟨D⟩ := exists_coverData ωb hμ hL hT hθ (half_pos hδ)
  exact (D.diagonalPotentialMass_le_sum_lintegral hn hL hθ hφθ hsm).trans
    (sum_lintegral_le_liminf_finrank hn hμ hL hT hδ hφ hsm D)

/-- The same bound with `θ`-plurisubharmonicity derived from the Kähler-current hypothesis. -/
theorem diagonalPotentialMass_le_liminf_finrank' (hn : 0 < n) (ωb : KahlerBackground n X)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {θ : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ) {δ : ℝ} (hδ : 0 < δ)
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (hsm : SmoothOffPoleSet (n := n) φ) :
    ∃ hφθ : IsThetaPshPotential θ.val φ, diagonalPotentialMass θ φ hφθ ≤
      liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
        (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ≥0∞)) atTop := by
  have hφθ : IsThetaPshPotential θ.val φ := by
    have h := Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive hφ
      (Pending.KahlerDomination.isSemipositive_smul ωb.isSemipositive hδ.le)
    have hform : θ - δ • ωb.form + δ • ωb.form = θ := by module
    rwa [hform] at h
  exact ⟨hφθ, diagonalPotentialMass_le_liminf_finrank hn ωb hμ hL hT hθ hδ hφ hφθ hsm⟩

/-- **The lower bound in the volume form** (source `thm:DXmain1`, `≥`, for `𝓘`-good `φ`): if
`vol θ_φ = ∫_X θ_φⁿ` (e.g. `φ` with analytic singularities, `ex:analyIgood`), then
`vol θ_φ ≤ liminf_k (n!/kⁿ) h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. -/
theorem iVolume_le_liminf_finrank [Nonempty X] (hn : 0 < n) (ωb : KahlerBackground n X)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {θ : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ) {δ : ℝ} (hδ : 0 < δ)
    {φ : X → EReal} (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
    (hφθ : IsThetaPshPotential θ.val φ) (hsm : SmoothOffPoleSet (n := n) φ)
    (hgood : iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφθ =
      diagonalPotentialMass θ φ hφθ) :
    iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφθ ≤
      liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n) *
        (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ≥0∞)) atTop := by
  rw [hgood]
  exact diagonalPotentialMass_le_liminf_finrank hn ωb hμ hL hT hθ hδ hφ hφθ hsm

end SGPT.IGood.DXLow

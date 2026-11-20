import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Foundations.Analysis.Pending.IdealFunctionMaxGluing

/-!
# Global potentials of a coherent ideal

Source: blueprint node `tok:ideal-potential` (chapter `claude-okounkov-transcendental`; it replaces
the citation of Boucksom (2002), Proposition 2.2 in DRWNXZ Lemma 3.1): for a coherent ideal sheaf
`𝓘` on a compact Kähler manifold `(X, ω)` there is a quasi-plurisubharmonic `ψ` with
`dd^c ψ ≥ -Cω` such that near every point `ψ = log ∑_l |h_l|² + O(1)` for local generators `h_l`
of `𝓘`.

## Formal statement

`ψ = log ∑ |h_l|² + O(1)` for local generators is TN's
`HasAnalyticSingularitiesOfType ψ 1 𝓘`, and `dd^c ψ ≥ -Cω` is `ψ ∈ PSH(X, Cω)`.

* `exists_ideal_potential`: for every coherent ideal, `ψ` is `(Cω)`-plurisubharmonic (TN's
  `ThetaPlurisubharmonic`; for the zero ideal `ψ ≡ -∞`).
* `exists_isThetaPshPotential_ideal_potential`: if `𝓘` does not vanish identically (some point
  lies off its zero locus) and `X` is connected, `ψ` is a `(Cω)`-psh potential in the project's
  strong sense (`IsThetaPshPotential`: also locally nondegenerate), i.e. quasi-psh in the usual
  sense.

## Route

The blueprint glues the local weights with a cut-off sum `log ∑ |χ_α h_{α,l}|²` and the Levi
estimate of Xia, *Foundations of pluripotential theory*, `lem:logarithmic-cutoff-sum`. TN proves
the same statement by a **maximum gluing** `Ψ = max_j (log ∑ |g_{j,i}|² + A χ_j)` (Copy-4
`lem:ideal-function`, `SGPT.Foundations.Analysis.Pending.IdealFunctionMaxGluing`); this file packages
it. (The route of `tok:density` in `TranscendentalDensity.lean` does not need this node: its
potential `ψ` of `𝓘(mφ)` is `m` times a term of the gentle approximation of `φ`.)
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalDensity

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending.IdealFunctionMaxGluing

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- **`tok:ideal-potential`**: on a nonempty compact Kähler manifold `(X, ω)`, every coherent ideal
sheaf `𝓘` has a global potential: `ψ` with `dd^c ψ ≥ -Cω` (`ψ` is `(Cω)`-plurisubharmonic) and
`ψ = log ∑ |h_l|² + O(1)` near every point for local generators `h_l` of `𝓘`. -/
theorem exists_ideal_potential [Nonempty X] (ω : KahlerBackground n X) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) :
    ∃ (ψ : X → EReal) (C : ℝ), 0 < C ∧ ThetaPlurisubharmonic (C • ω.form).val ψ ∧
      HasAnalyticSingularitiesOfType (n := n) ψ 1 𝔞 := by
  obtain ⟨ψ, C, hC, hpsh, htype, -⟩ := exists_idealFunction ω h𝔞 (Classical.arbitrary X)
  exact ⟨ψ, C, hC, hpsh, htype⟩

/-- **`tok:ideal-potential`, quasi-psh form**: on a compact connected Kähler manifold, a coherent
ideal sheaf `𝓘` which does not vanish identically (`x₀ ∉ Z(𝓘)`) has a global potential `ψ` which
is a `(Cω)`-psh potential (`dd^c ψ ≥ -Cω`, `ψ` locally nondegenerate) with
`ψ = log ∑ |h_l|² + O(1)` near every point for local generators `h_l` of `𝓘`. -/
theorem exists_isThetaPshPotential_ideal_potential [ConnectedSpace X] (ω : KahlerBackground n X)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {x₀ : X} (hx₀ : x₀ ∉ 𝔞.zeroLocus) :
    ∃ (ψ : X → EReal) (C : ℝ), 0 < C ∧ IsThetaPshPotential (C • ω.form).val ψ ∧
      HasAnalyticSingularitiesOfType (n := n) ψ 1 𝔞 := by
  obtain ⟨ψ, C, hC, hpsh, htype, -⟩ := exists_isThetaPshPotential_idealFunction ω h𝔞 hx₀
  exact ⟨ψ, C, hC, hpsh, htype⟩

end SGPT.Okounkov.TranscendentalDensity

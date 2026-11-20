import SGPT.Siu.SiuModificationModifiedNef

/-!
# Classes of nef b-divisors are modified nef (`cor:mn_level_nefb`, (1) ⇒ (2))

Source `cor:mn_level_nefb` (chapter *The theory of b-divisors*): for a b-divisor `𝔻` over `X`,
`𝔻` is nef if and only if `𝔻_Y` is modified nef for every modification `π : Y → X`.

This file proves the implication (1) ⇒ (2) following the book: a nef b-divisor is a limit of nef
Cartier b-divisors, and modified nefness is a closed condition
(`SGPT.Siu.classModifiedNef_of_tendsto`); for a nef Cartier b-divisor realized by a nef class
`α` on `Y₀`, the class on `Y` is `h_* g^* α` for a common dominating model `Y'`
(`g : Y' → Y₀`, `h : Y' → Y`), which is modified nef by the push-forward criterion
`SGPT.Siu.classModifiedNefWithRespectTo_classPushforward_of_forall` (`prop:cones_modif`, item 2:
`g^*α + εg^*{κ}` contains the smooth semipositive current `g^*(θ + εκ + ddᶜh)`; no Kähler form
on `Y'` is needed).

Hypotheses beyond the book's: modified nefness of `𝔻_Y` is stated for every model `Y` carrying a
Kähler form (`def:mnclass` needs one; the book's models are Kähler), and the closedness step uses
that `H^{1,1}(Y, ℝ)` is finite-dimensional (Hodge theory, not formalized; it is also what
identifies the intrinsic topology `SGPT.BDivisor.euclideanTopology` with the Euclidean one).
The converse (2) ⇒ (1) needs `thm:bigandnefreal` and is not formalized.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

namespace WeilBDivisor

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] {hn : 0 < m + 1}

/-- **The classes of a nef Cartier b-divisor are modified nef**: on every model `Y` carrying a
Kähler form, `𝔻_Y = h_* g^* α` (for a realization `(Y₀, α)` with `α` nef and a common model
`Y'` dominating `Y` and `Y₀`) is modified nef. -/
theorem IsNefCartier.classModifiedNef {𝔻 : WeilBDivisor (m + 1) X hn} (h𝔻 : 𝔻.IsNefCartier)
    (π : Modification (m + 1) X) (ωY : KahlerBackground (m + 1) π.carrier) :
    Siu.ClassModifiedNefWithRespectTo ωY (𝔻.onModel π) := by
  obtain ⟨π₀, α, hr, κ, hα⟩ := h𝔻
  obtain ⟨π', h₁, h₂⟩ := exists_ge_ge π π₀
  rw [← 𝔻.pushforward_onModel h₁, hr π' h₂]
  induction α using Quotient.inductionOn with
  | h θ =>
  change NefWithRespectTo κ θ at hα
  change Siu.ClassModifiedNefWithRespectTo ωY
    (classPushforward (Modification.contMDiff_homOfLE h₁) (canonicalBasis (m + 1)) hn
      (classPullback (Modification.contMDiff_homOfLE h₂) (RealBottChern.ofRepresentative θ)))
  rw [classPullback_ofRepresentative]
  exact Siu.classModifiedNefWithRespectTo_classPushforward_of_forall
    (Modification.Dominates.isAnalyticModification h₁) ωY _ _
    (fun ε hε => Siu.exists_pullback_nef_potential (Modification.contMDiff_homOfLE h₂) κ hα ε hε)

/-- **Source `cor:mn_level_nefb`, implication (1) ⇒ (2): the classes of a nef b-divisor are
modified nef.** For a nef b-divisor `𝔻` over the compact connected manifold `X` and a model
`π : Y → X` carrying a Kähler form `ω`, the class `𝔻_Y` is modified nef, provided
`H^{1,1}(Y, ℝ)` is finite-dimensional. -/
theorem IsNef.classModifiedNef {𝔻 : WeilBDivisor (m + 1) X hn} (h𝔻 : 𝔻.IsNef)
    (π : Modification (m + 1) X) [FiniteDimensional ℝ (RealBottChern (m + 1) π.carrier)]
    (ωY : KahlerBackground (m + 1) π.carrier) :
    Siu.ClassModifiedNefWithRespectTo ωY (𝔻.onModel π) := by
  obtain ⟨ι, _, _, _, D, hD, hconv⟩ := h𝔻
  exact Siu.classModifiedNef_of_tendsto ωY (fun i => (hD i).classModifiedNef π ωY) (hconv π)

end WeilBDivisor

end SGPT.BDivisor

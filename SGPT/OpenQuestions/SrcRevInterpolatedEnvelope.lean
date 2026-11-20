import SGPT.Envelopes.DNTRegInterpolatedProjection

/-!
# The open question of `rmk:envelopes:L2443`

Source `rmk:envelopes:L2443` (chapter *The envelope operators*, snapshot `c88c7ff4`,
`author/chapter_envelopes.tex:2445–2456`; ERRATA C06, corrected upstream). For a connected
compact Kähler manifold `X` of dimension `n`, a smooth closed real `(1,1)`-form `θ`,
`φ ∈ PSH(X,θ)_{>0}` and `j ∈ {0, …, n}`, the remark defines the interpolating envelope
`P_{θ,j}[φ]` (`SGPT.PSH.VariableComplexAtlas.sourceInterpolatedEnvelope`), states the known
cases — `j = 0` and `j = n` give the `𝓘`- and `P`-envelopes
(`sourceInterpolatedEnvelope_zero`, `sourceInterpolatedEnvelope_last`) and
`P_{θ,j}[φ] = P_θ[φ]` for every `j` when `φ` is `𝓘`-good
(`sourceInterpolatedEnvelope_eq_of_iGood`) — and ends with the question

> Is `P_{θ,j}[•]` a projection operator for `0 < j < n` in general?

This file records the question as propositions. It does **not** answer it.

* `interpolatedEnvelopeProjectionQuestionAt θ`: the question for a fixed `(X, θ)`: every
  `P_{θ,j}` with `0 < j < n` is a projection operator on `PSH(X,θ)_{>0}`
  (`SourceInterpolatedEnvelopeProjection θ j`: positive output mass and
  `P_{θ,j}[P_{θ,j}[φ]] = P_{θ,j}[φ]`).
* `interpolatedEnvelopeProjectionQuestion`: the question "in general", for every connected
  compact Kähler manifold (of a fixed universe), every `θ` and every `0 < j < n`.
* `interpolatedEnvelopeProjectionQuestionAt_iff`: since the endpoint cases are proved, the
  question at `(X, θ)` is equivalent to "every `P_{θ,j}`, `0 ≤ j ≤ n`, is a projection operator";
  so the proposition records exactly the part of the old projection claim that is not proved.
* `interpolatedEnvelopeProjectionQuestionAt_of_le_one`: for `n ≤ 1` there is no `0 < j < n`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.OpenQuestions

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas

universe u

section Fixed

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The question of `rmk:envelopes:L2443` for a fixed `(X, θ)`: for every `0 < j < n`, the
interpolating envelope `P_{θ,j}` is a projection operator on `PSH(X,θ)_{>0}`. A proposition
statement only; it is not asserted. -/
def interpolatedEnvelopeProjectionQuestionAt
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) : Prop :=
  ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n → SourceInterpolatedEnvelopeProjection θ j

/-- With the proved endpoint cases `j = 0` and `j = n`, the question at `(X, θ)` is equivalent to
the projection property of every `P_{θ,j}`, `0 ≤ j ≤ n`. -/
theorem interpolatedEnvelopeProjectionQuestionAt_iff (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    interpolatedEnvelopeProjectionQuestionAt θ ↔
      ∀ j : Fin (n + 1), SourceInterpolatedEnvelopeProjection θ j := by
  refine ⟨fun h j => ?_, fun h j _ _ => h j⟩
  by_cases h0 : (j : ℕ) = 0
  · have hj : j = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext h0
    subst hj
    exact sourceInterpolatedEnvelopeProjection_zero ω
  · by_cases hn : (j : ℕ) = n
    · have hj : j = Fin.last n := Fin.ext hn
      subst hj
      exact sourceInterpolatedEnvelopeProjection_last ω
    · exact h j (Nat.pos_of_ne_zero h0) (lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) hn)

omit [BorelSpace M] in
/-- In dimension `n ≤ 1` the question is empty: there is no `0 < j < n`. -/
theorem interpolatedEnvelopeProjectionQuestionAt_of_le_one (hn : n ≤ 1)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    interpolatedEnvelopeProjectionQuestionAt θ := fun j h0 h1 => by omega

end Fixed

/-- The question of `rmk:envelopes:L2443` "in general": for every connected compact Kähler
manifold `X` (in the universe `u`), every smooth closed real `(1,1)`-form `θ` on `X` and every
`0 < j < n`, the interpolating envelope `P_{θ,j}` is a projection operator on `PSH(X,θ)_{>0}`.
A proposition statement only; it is not asserted. -/
def interpolatedEnvelopeProjectionQuestion : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    [ConnectedSpace M], Nonempty (KahlerBackground n M) →
      ∀ θ : AtlasClosedRealOneOneForm (ofFixedModel n M),
        interpolatedEnvelopeProjectionQuestionAt θ

end SGPT.OpenQuestions

end

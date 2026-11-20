import SGPT.Envelopes.SourceInterpolatedEnvelopeGenuine

/-!
# `rmk:envelopes:L2443`: the projection property reduces to mass preservation


Source `rmk:envelopes:L2443` (`chapter_envelopes.tex`) defines, for `φ ∈ PSH(X, θ)_{>0}` and
`j ∈ {0, …, n}`, the envelope `P_{θ,j}[φ]` as the usc supremum of the `ψ ≤ 0` with `φ ⪯ ψ` and
`F_j(ψ) = F_j(φ)`, `F_j(u) = ∫_X θ_u^j ∧ θ_{P_θ[u]_𝓘}^{n-j}`, and asserts without proof that
*one could show that `P_{θ,j}` is a projection operator*.  The definition, the cases `j ∈ {0, n}`
and the case of `𝓘`-good inputs are formalized in `SourceInterpolatedEnvelope*.lean`; there,
`F_j(φ) ≤ F_j(P_{θ,j}[φ])` is proved (`sourceInterpolatedMass_le_envelope`).

Here the open intermediate case is reduced to the reverse inequality: **if `P_{θ,j}` preserves
`F_j`, then it is idempotent** (`sourceInterpolatedEnvelope_idem_of_mass_eq`), hence a projection
operator in the sense of `SourceInterpolatedEnvelopeProjection`
(`sourceInterpolatedEnvelopeProjection_of_mass_eq`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}

/-- **Mass preservation implies idempotence**: if `F_j(P_{θ,j}[φ]) = F_j(φ)`, then
`P_{θ,j}[P_{θ,j}[φ]] = P_{θ,j}[φ]`.  (The competitors of `P_{θ,j}[φ]` are competitors of `φ`, and
`P_{θ,j}[φ]` is a competitor of itself.) -/
theorem sourceInterpolatedEnvelope_idem_of_mass_eq (ω : KahlerBackground n M) (j : Fin (n + 1))
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hmass : sourceInterpolatedMass θ j (sourceInterpolatedEnvelope θ j u hu)
      (isThetaPSH_sourceInterpolatedEnvelope ω j hu) = sourceInterpolatedMass θ j u hu) :
    sourceInterpolatedEnvelope θ j (sourceInterpolatedEnvelope θ j u hu)
        (isThetaPSH_sourceInterpolatedEnvelope ω j hu) =
      sourceInterpolatedEnvelope θ j u hu := by
  set hP := isThetaPSH_sourceInterpolatedEnvelope ω j hu
  set P := sourceInterpolatedEnvelope θ j u hu with hPdef
  apply le_antisymm
  · -- the competitors of `P` are competitors of `u`
    have hle : (fun x => ⨆ v : sourceInterpolatedEnvelopeCompetitors θ j P hP, v.1 x) ≤
        fun x => ⨆ v : sourceInterpolatedEnvelopeCompetitors θ j u hu, v.1 x := by
      intro x
      refine iSup_le fun v => ?_
      obtain ⟨hv, hv0, hPv, hmv⟩ := v.2
      have hc : ∃ hv' : (ofFixedModel n M).IsThetaPSH θ v.1, v.1 ≤ 0 ∧
          SGPT.PSH.SingularityLE u v.1 ∧
            sourceInterpolatedMass θ j u hu = sourceInterpolatedMass θ j v.1 hv' :=
        ⟨hv, hv0, SGPT.PSH.singularityLE_trans (singularityLE_sourceInterpolatedEnvelope ω j hu) hPv,
          hmass.symm.trans hmv⟩
      exact le_iSup (fun w : sourceInterpolatedEnvelopeCompetitors θ j u hu => w.1 x) ⟨v.1, hc⟩
    exact uscRegularization_mono hle
  · -- `P` is a competitor of itself
    have hc : ∃ hP' : (ofFixedModel n M).IsThetaPSH θ P, P ≤ 0 ∧ SGPT.PSH.SingularityLE P P ∧
        sourceInterpolatedMass θ j P hP = sourceInterpolatedMass θ j P hP' :=
      ⟨hP, sourceInterpolatedEnvelope_le_zero j hu, SGPT.PSH.singularityLE_refl P, rfl⟩
    intro x
    exact (le_iSup (fun w : sourceInterpolatedEnvelopeCompetitors θ j P hP => w.1 x) ⟨P, hc⟩).trans
      (le_uscRegularization
        (fun y => ⨆ w : sourceInterpolatedEnvelopeCompetitors θ j P hP, w.1 y) x)

/-- **The projection property of `rmk:envelopes:L2443` follows from mass preservation**: if
`F_j(P_{θ,j}[φ]) = F_j(φ)` for every `φ ∈ PSH(X, θ)_{>0}`, then `P_{θ,j}` is a projection operator
(`SourceInterpolatedEnvelopeProjection θ j`).  Since `F_j(φ) ≤ F_j(P_{θ,j}[φ])` always holds
(`sourceInterpolatedMass_le_envelope`), the open case `0 < j < n` reduces to
`F_j(P_{θ,j}[φ]) ≤ F_j(φ)`. -/
theorem sourceInterpolatedEnvelopeProjection_of_mass_eq (ω : KahlerBackground n M)
    (j : Fin (n + 1))
    (h : ∀ (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u),
      0 < sourcePotentialNonPluripolarMeasure θ u hu univ →
        sourceInterpolatedMass θ j (sourceInterpolatedEnvelope θ j u hu)
          (isThetaPSH_sourceInterpolatedEnvelope ω j hu) = sourceInterpolatedMass θ j u hu) :
    SourceInterpolatedEnvelopeProjection θ j := fun u hu hpos =>
  ⟨isThetaPSH_sourceInterpolatedEnvelope ω j hu, sourceInterpolatedEnvelope_positive ω j hu hpos,
    sourceInterpolatedEnvelope_idem_of_mass_eq ω j hu (h u hu hpos)⟩

end SGPT.PSH.VariableComplexAtlas

end

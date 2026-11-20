import SGPT.Envelopes.SourceEqualMassEnvelope
import SGPT.Envelopes.SourceRooftopContactMeasures
import SGPT.PSH.SourceCapacity
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeContact

/-!
# The non-pluripolar measure of a `P`-envelope is concentrated on `{P_θ[φ] = 0}`

Source: Chapter "The envelope operators", `thm:Pvarphisupport`:
`θ_{P_θ[φ]}^n ≤ 1_{\{P_θ[φ] = 0\}} θ^n`.

The source proof combines `cor:Pvarphisupport` (with `ψ = V_θ`) and the "in particular"
clause `θ_{V_θ}^n = 1_{\{V_θ = 0\}} θ^n` of `cor:DNTenvelope1`. We prove everything except
the last density comparison:

* `sourceSingularityEnvelope_measure_negative_null`: `θ_{P_θ[φ]}^n` gives no mass to
  `{P_θ[φ] < 0}` (it is carried by `{P_θ[φ] = 0}`);
* `sourceSingularityEnvelope_measure_le_minimal`:
  `θ_{P_θ[φ]}^n ≤ 1_{\{P_θ[φ] = 0\}} θ_{V_θ}^n` as measures.

Together with `1_{\{V_θ = 0\}} θ_{V_θ}^n ≤ 1_{\{V_θ = 0\}} θ^n` (the density estimate on the
contact set, which the source takes from the Di Nezza--Trapani contact theorem
`thm:DNTcontact`, and which also needs the signed measure `θ^n`) this is
`thm:Pvarphisupport`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}

omit [MeasurableSpace M] [BorelSpace M] in
/-- `V_θ ∈ PSH(X,θ)` as soon as `PSH(X,θ) ≠ ∅`. -/
theorem sourceMinimalEnvelope_thetaPSH_of_mem (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (ofFixedModel n M).IsThetaPSH θ (sourceMinimalEnvelope θ) := by
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  rw [sourceMinimalEnvelope_eq_native]
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  exact FirstPass.thetaPshSupremum_isThetaPshPotential _ (atlasClosedFormToNative θ).property.1
    (atlasClosedFormToNative θ).property.2 hn.1.hasSmoothLocalPotentials ⟨u, hn⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- With the obstacle `V_θ`, the generalized envelope is the `P`-envelope:
`P_θ[φ](V_θ) = P_θ[φ](0) = P_θ[φ]`. -/
theorem sourceRelativeEnvelope_minimal_eq_singularityEnvelope
    (hV : (ofFixedModel n M).IsThetaPSH θ (sourceMinimalEnvelope θ)) (u : M → EReal) :
    sourceRelativeEnvelope θ u (sourceMinimalEnvelope θ) = sourceSingularityEnvelope θ u := by
  rw [← sourceRelativeEnvelope_zero_eq_singularityEnvelope]
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro a
    have ha := (sourceQuasiEverywhere_le_iff a.2.1 hV).mp a.2.2.1
    exact le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ u 0 => b.1 x)
      ⟨a.1, a.2.1, sourceQuasiEverywhere_of_forall fun y =>
        (ha y).trans (sourceMinimalEnvelope_le_zero θ y), a.2.2.2⟩
  · apply iSup_le
    intro a
    have ha := (sourceQuasiEverywhere_le_iff_of_upperSemicontinuous a.2.1
      (continuous_const.upperSemicontinuous)).mp a.2.2.1
    exact le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ u (sourceMinimalEnvelope θ) =>
        b.1 x)
      ⟨a.1, a.2.1, sourceQuasiEverywhere_of_forall fun y =>
        le_iSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧ v ≤ 0} => v.1 y)
          ⟨a.1, a.2.1, ha⟩, a.2.2.2⟩

/-- Source `thm:Pvarphisupport`, support clause: `θ_{P_θ[φ]}^n` does not charge
`{P_θ[φ] < 0}`, i.e. it is carried by `{P_θ[φ] = 0}`. -/
theorem sourceSingularityEnvelope_measure_negative_null (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ (sourceSingularityEnvelope θ u)
      (sourceOrdinaryEnvelope_genuine hu) {x | sourceSingularityEnvelope θ u x < 0} = 0 := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hEq := sourceSingularityEnvelope_eq_native θ u
  have hP' : (ofFixedModel n M).IsThetaPSH θ
      (singularityEnvelope (atlasClosedFormToNative θ).val u) :=
    hEq ▸ sourceOrdinaryEnvelope_genuine hu
  rw [sourcePotentialNonPluripolarMeasure_congr hEq _ hP', hEq]
  exact SingularityEnvelopeContact.diagonalPotentialMeasure_singularityEnvelope_lt_zero ω
    (atlasClosedFormToNative θ) hn _

/-- `θ_{V_θ}^n` does not charge `{V_θ < 0}` (source `thm:concentration` with `f = 0`). -/
theorem sourceMinimalEnvelope_measure_negative_null (ω : KahlerBackground n M)
    (hV : (ofFixedModel n M).IsThetaPSH θ (sourceMinimalEnvelope θ)) :
    sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ) hV
      {x | sourceMinimalEnvelope θ x < 0} = 0 := by
  have hEq := sourceMinimalEnvelope_eq_native θ
  have hV' : (ofFixedModel n M).IsThetaPSH θ (thetaPshSupremum (atlasClosedFormToNative θ).val) :=
    hEq ▸ hV
  rw [sourcePotentialNonPluripolarMeasure_congr hEq _ hV', hEq]
  exact SingularityEnvelopeContact.diagonalPotentialMeasure_thetaPshSupremum_lt_zero ω
    (atlasClosedFormToNative θ) _

/-- Source `thm:Pvarphisupport`, reduced form:
`θ_{P_θ[φ]}^n ≤ 1_{\{P_θ[φ] = 0\}} θ_{V_θ}^n`. -/
theorem sourceSingularityEnvelope_measure_le_minimal (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ (sourceSingularityEnvelope θ u)
        (sourceOrdinaryEnvelope_genuine hu) ≤
      (sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
        (sourceMinimalEnvelope_thetaPSH_of_mem hu)).restrict
          {x | sourceSingularityEnvelope θ u x = 0} := by
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hu
  have heq := sourceRelativeEnvelope_minimal_eq_singularityEnvelope hV u
  have hne : sourceRelativeEnvelope θ u (sourceMinimalEnvelope θ) ≠ ⊥ := by
    rw [heq]
    intro hbot
    have hPn := (isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceOrdinaryEnvelope_genuine hu)
    obtain ⟨y, -, hy⟩ := hPn.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
    exact hy (congrFun hbot y)
  have hle := sourceRelativeEnvelope_measure_le ω hu hV hne
  rw [sourcePotentialNonPluripolarMeasure_congr heq _ (sourceOrdinaryEnvelope_genuine hu)] at hle
  simp only [heq] at hle
  refine hle.trans (Measure.le_iff.mpr fun E hE => ?_)
  rw [Measure.restrict_apply hE, Measure.restrict_apply hE]
  have hsub : E ∩ {x | sourceSingularityEnvelope θ u x = sourceMinimalEnvelope θ x} ⊆
      (E ∩ {x | sourceSingularityEnvelope θ u x = 0}) ∪ {x | sourceMinimalEnvelope θ x < 0} := by
    rintro x ⟨hxE, hx⟩
    rcases (sourceMinimalEnvelope_le_zero θ x).lt_or_eq with h | h
    · exact Or.inr h
    · exact Or.inl ⟨hxE, hx.trans h⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [sourceMinimalEnvelope_measure_negative_null ω hV, add_zero]

end SGPT.PSH.VariableComplexAtlas

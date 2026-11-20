import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import SGPT.Envelopes.SourceRelativeEnvelopeExhaustion
import SGPT.PSH.SourceOrdinaryObstacleFineUpper
import SGPT.PSH.SourceEnvelopeRooftop
import SGPT.Foundations.Analysis.Pending.EqualMassEnvelope

/-!
# The equal-mass characterization of the `P`-envelope

Source: Chapter "The envelope operators", `thm:Pvarphidiffdef` and
`ex:envelopes:L625`.

* `sourceSingularityEnvelope_eq_iSup_equalMass`: for `φ ∈ PSH(X,θ)` with
  `∫ θ_φ^n > 0`, the `P`-envelope `P_θ[φ]` is the (pointwise, not regularized)
  supremum of all `ψ ∈ PSH(X,θ)` with `ψ ≤ 0`, `φ ⪯ ψ` and `∫ θ_φ^n = ∫ θ_ψ^n`
  (equation `eq:Penvdef`); `sourceOrdinaryEnvelope_projection` is the
  projection identity `P_θ[P_θ[φ]] = P_θ[φ]` (`eq:Penvprojop`).
* `sourceRelativeEnvelope_zero_eq_singularityEnvelope`: `P_θ[φ](0) = P_θ[φ]`.
* `sourceRelativeEnvelope_minimal_eq_obstacle`: `P_θ[V_θ](f) = P_θ(f)` when
  `PSH(X,θ) ≠ ∅`.

The proof of the first point is the source's: every competitor is below
`P_θ[φ]` by the domination principle (`equalMassLeSingularityEnvelope`), and
`P_θ[φ]` itself is a competitor by mass preservation (`prop:Ppresmass`).
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

section Example

/-- Source `ex:envelopes:L625`, first claim: with obstacle `f = 0`, the generalized
envelope `P_θ[φ](0)` is the `P`-envelope `P_θ[φ]`. No hypothesis on `φ` is needed:
the two competitor families coincide because quasi-everywhere comparison with the
continuous obstacle `0` is pointwise comparison for genuine `θ`-psh functions. -/
theorem sourceRelativeEnvelope_zero_eq_singularityEnvelope
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal) :
    sourceRelativeEnvelope θ u 0 = sourceSingularityEnvelope θ u := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro a
    exact le_iSup (fun v : sourceSingularityCompetitors θ u => v.1 x)
      ⟨a.1, a.2.1, (sourceQuasiEverywhere_le_iff_of_upperSemicontinuous a.2.1
        (continuous_const.upperSemicontinuous)).mp a.2.2.1, a.2.2.2⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun a : sourceRelativeEnvelopeCompetitors θ u 0 => a.1 x)
      ⟨v.1, v.2.1, sourceQuasiEverywhere_of_forall v.2.2.1, v.2.2.2⟩

variable [CompactSpace M] [ConnectedSpace M]

/-- Every genuine `θ`-psh function is more singular than `V_θ` (the raw supremum of
all nonpositive `θ`-psh functions): subtract a global upper bound. -/
theorem singularityLE_sourceMinimalEnvelope_of_thetaPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {a : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a) :
    SGPT.PSH.SingularityLE a (sourceMinimalEnvelope θ) := by
  have han := (isThetaPSH_iff_nativeThetaPotential θ a).mp ha
  obtain ⟨C, hC⟩ := han.exists_global_upper_bound
  have hsub : (ofFixedModel n M).IsThetaPSH θ (fun x => a x - (C : EReal)) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr (han.sub_const C)
  have hsub0 : (fun x => a x - (C : EReal)) ≤ 0 := by
    intro x
    exact EReal.sub_nonpos.mpr (hC x)
  refine (singularityLE_iff_exists_real _ _).mpr ⟨C, fun x => ?_⟩
  have hx : a x - (C : EReal) ≤ sourceMinimalEnvelope θ x :=
    le_iSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧ v ≤ 0} => v.1 x)
      ⟨fun y => a y - (C : EReal), hsub, hsub0⟩
  exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot C))
    (Or.inl (EReal.coe_ne_top C))).mp hx

/-- Source `ex:envelopes:L625`, second claim: when `PSH(X,θ) ≠ ∅` (so that
`V_θ ∈ PSH(X,θ)`), `P_θ[V_θ](f) = P_θ(f)` for every obstacle `f`. Here
`P_θ(f)` is `sourceRelativeEnvelope θ ⊤ f` (source `def:Pthetaf`, see
`sourceObstacleEnvelope_eq_uscSup_qeCompetitors`). In fact the identity holds
for every `f` without any hypothesis on `θ`: the comparison `η ⪯ V_θ` is
automatic for every genuine competitor `η`. -/
theorem sourceRelativeEnvelope_minimal_eq_obstacle
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (f : M → EReal) :
    sourceRelativeEnvelope θ (sourceMinimalEnvelope θ) f =
      sourceRelativeEnvelope θ (fun _ => ⊤) f := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro a
    exact le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ (fun _ => ⊤) f => b.1 x)
      ⟨a.1, a.2.1, a.2.2.1, sourceObstacle_topReference a.1⟩
  · apply iSup_le
    intro a
    exact le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ (sourceMinimalEnvelope θ) f =>
        b.1 x)
      ⟨a.1, a.2.1, a.2.2.1, singularityLE_sourceMinimalEnvelope_of_thetaPSH a.2.1⟩

end Example

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}

omit [BorelSpace M] [ConnectedSpace M] in
/-- Measures of the same background only depend on the potential. -/
theorem sourcePotentialNonPluripolarMeasure_congr {v w : M → EReal} (hvw : v = w)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (hw : (ofFixedModel n M).IsThetaPSH θ w) :
    sourcePotentialNonPluripolarMeasure θ v hv = sourcePotentialNonPluripolarMeasure θ w hw := by
  subst hvw
  rfl

/-- The competitors of source `eq:Penvdef`: all `ψ ∈ PSH(X,θ)` with `ψ ≤ 0`,
`φ ⪯ ψ` and `∫_X θ_φ^n = ∫_X θ_ψ^n`. -/
def sourceEqualMassCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) :=
  {v : M → EReal // ∃ hv : (ofFixedModel n M).IsThetaPSH θ v, v ≤ 0 ∧
    SGPT.PSH.SingularityLE u v ∧
    sourcePotentialNonPluripolarMeasure θ u hu univ =
      sourcePotentialNonPluripolarMeasure θ v hv univ}

/-- The `≥` direction of source `eq:Penvdef`: every equal-mass competitor lies
below `P_θ[φ]` (domination principle). -/
theorem le_sourceSingularityEnvelope_of_equalMass (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (v : sourceEqualMassCompetitors θ u hu) :
    v.1 ≤ sourceSingularityEnvelope θ u := by
  obtain ⟨hv, hv0, huv, hmass⟩ := v.2
  rw [sourceSingularityEnvelope_eq_native]
  exact equalMassLeSingularityEnvelope ω (atlasClosedFormToNative θ) u v.1
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v.1).mp hv) hpos hv0 huv hmass

/-- `P_θ[φ]` is itself an equal-mass competitor (source `prop:Ppresmass`). -/
def sourceEnvelopeEqualMassCompetitor (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : sourceEqualMassCompetitors θ u hu :=
  ⟨sourceSingularityEnvelope θ u, sourceOrdinaryEnvelope_genuine hu,
    sourceSingularityEnvelope_le_zero θ u,
    by simpa only [sourceSingularityEnvelope_eq_native, SGPT.PSH.SingularityLE] using
      moreSingularOn_singularityEnvelope ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu),
    (sourceOrdinaryEnvelope_diagonalMass_eq ω hu).symm⟩

/-- Source `thm:Pvarphidiffdef`, equation `eq:Penvdef`: for `φ ∈ PSH(X,θ)_{>0}`,
`P_θ[φ]` is the pointwise supremum of all `ψ ∈ PSH(X,θ)` with `ψ ≤ 0`, `φ ⪯ ψ`
and `∫_X θ_φ^n = ∫_X θ_ψ^n`. The supremum is attained (by `P_θ[φ]`). -/
theorem sourceSingularityEnvelope_eq_iSup_equalMass (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceSingularityEnvelope θ u =
      fun x => ⨆ v : sourceEqualMassCompetitors θ u hu, v.1 x := by
  funext x
  apply le_antisymm
  · exact le_iSup (fun v : sourceEqualMassCompetitors θ u hu => v.1 x)
      (sourceEnvelopeEqualMassCompetitor ω hu)
  · exact iSup_le fun v => le_sourceSingularityEnvelope_of_equalMass ω hu hpos v x

/-- Source `thm:Pvarphidiffdef`, the greatest-element form of `eq:Penvdef`:
`P_θ[φ]` is the greatest equal-mass competitor. -/
theorem isGreatest_sourceSingularityEnvelope_equalMass (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    IsGreatest {v : M → EReal | ∃ hv : (ofFixedModel n M).IsThetaPSH θ v, v ≤ 0 ∧
        SGPT.PSH.SingularityLE u v ∧
        sourcePotentialNonPluripolarMeasure θ u hu univ =
          sourcePotentialNonPluripolarMeasure θ v hv univ}
      (sourceSingularityEnvelope θ u) :=
  ⟨(sourceEnvelopeEqualMassCompetitor ω hu).2,
    fun v hv => le_sourceSingularityEnvelope_of_equalMass ω hu hpos ⟨v, hv⟩⟩

/-- Source `thm:Pvarphidiffdef`, equation `eq:Penvprojop`: for
`φ ∈ PSH(X,θ)_{>0}`, `P_θ[P_θ[φ]] = P_θ[φ]`. -/
theorem sourceOrdinaryEnvelope_projection (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    sourceSingularityEnvelope θ (sourceSingularityEnvelope θ u) =
      sourceSingularityEnvelope θ u :=
  sourceOrdinaryEnvelope_idempotent_of_positive_mass ω hu hpos

end SGPT.PSH.VariableComplexAtlas

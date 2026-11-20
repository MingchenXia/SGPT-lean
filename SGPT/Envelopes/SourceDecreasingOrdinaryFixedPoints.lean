import SGPT.Envelopes.SourceRooftopMassCalculus
import SGPT.Foundations.Analysis.Pending.ModelRaySupremum

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual ordinary fixed-point equation gives spatial supremum zero,
with NO positive-mass model predicate or finite-supremum certificate. -/
theorem sourceOrdinaryFixedPoint_globalSup_zero {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hfix : sourceSingularityEnvelope θ u = u) : (⨆ x, u x) = 0 := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hd := ModelRaySupremum.differenceSup_eq_iSup_of_envelope_eq hn
    (hfix.symm.trans (sourceSingularityEnvelope_eq_native θ u)) hn (MoreSingularOn.refl u univ)
  exact hd.symm.trans (FiniteUpperGapGeodesicSupremum.differenceSup_self hn)

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (ui : I → M → EReal) (hui : ∀ i, (ofFixedModel n M).IsThetaPSH θ (ui i))
  (hfix : ∀ i, sourceSingularityEnvelope θ (ui i) = ui i)
  (hanti : ∀ x, Antitone (fun i => ui i x))

include hui hfix hanti

/-- The internally manufactured zero supremum bound and the existing compact
WHOLE-directed-infimum producer give genuine source PSH, including zero masses. -/
theorem sourceOrdinaryFixedPoint_directedInf_thetaPSH :
    (ofFixedModel n M).IsThetaPSH θ (fun x => ⨅ i, ui i x) := by
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  apply (SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    (fun i => (isThetaPSH_iff_nativeThetaPotential θ (ui i)).mp (hui i)) hanti 0 ?_).1
  intro i
  simpa only [EReal.coe_zero] using
    (sourceOrdinaryFixedPoint_globalSup_zero (hui i) (hfix i)).symm.le

/-- WHOLE original decreasing-net ordinary fixed-point equation, without
positive stage/limit mass, uniform mass, metric limit or countable cofinality. -/
theorem sourceOrdinaryFixedPoint_directedInf_eq :
    sourceSingularityEnvelope θ (fun x => ⨅ i, ui i x) = fun x => ⨅ i, ui i x := by
  have hinf := sourceOrdinaryFixedPoint_directedInf_thetaPSH ui hui hfix hanti
  have hbelow (i : I) : (fun x => ⨅ j, ui j x) ≤ ui i := fun x => iInf_le _ i
  have hinf0 : (fun x => ⨅ j, ui j x) ≤ 0 := by
    let i := Classical.arbitrary I
    exact (hbelow i).trans ((hfix i) ▸ sourceSingularityEnvelope_le_zero θ (ui i))
  apply le_antisymm
  · intro x
    apply le_iInf
    intro i
    exact ((sourceOrdinaryEnvelope_mono (θ := θ)
      (MoreSingularOn.of_le fun y _ => hbelow i y)).trans_eq (hfix i)) x
  · exact le_sourceSingularityEnvelope hinf hinf0 (MoreSingularOn.refl _ univ)

/-- The original whole assertion and its genuine original infimum reader,
on exactly the same arbitrary nonempty directed net. -/
theorem sourceOrdinaryFixedPoint_directedInf :
    (ofFixedModel n M).IsThetaPSH θ (fun x => ⨅ i, ui i x) ∧
      sourceSingularityEnvelope θ (fun x => ⨅ i, ui i x) = fun x => ⨅ i, ui i x :=
  ⟨sourceOrdinaryFixedPoint_directedInf_thetaPSH ui hui hfix hanti,
    sourceOrdinaryFixedPoint_directedInf_eq ui hui hfix hanti⟩

end SGPT.PSH.VariableComplexAtlas

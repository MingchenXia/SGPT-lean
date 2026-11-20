import SGPT.PSH.SourceSingularityDistance
import SGPT.PSH.SourceGenericLelong
import SGPT.Foundations.Analysis.Pending.AnalyticModificationNativeLelongLimit

/-! Universal source-reader convergence on every actual analytic modification.

This includes arbitrary whole carriers, empty carriers, infinite values and
dimension zero. It constructs neither the prime-over-X equivalence quotient
nor descent of the reader to that quotient; those definition-level obligations
are recorded separately. No whole-source coverage promotion is made here.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy DemaillyApproximantDivisorialLelong
open SquaredLogLelongSourceNormalization

private theorem sourceGenericLelong_eq_half_native
    {m : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    (a : Y → EReal) (E : Set Y) :
    (ofFixedModel (m + 1) Y).sourceGenericLelong a E =
      (2 : ℝ≥0∞)⁻¹ * divisorialLelongNumber m a E := by
  simp only [sourceGenericLelong, sourceLelong_ofFixedModel_eq]
  rw [divisorialLelongNumber, iInf_lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
  symm
  exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)

private theorem sourceGenericLelong_zero_input_independent
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
    (a b : Y → EReal) (E : Set Y) :
    (ofFixedModel 0 Y).sourceGenericLelong a E =
      (ofFixedModel 0 Y).sourceGenericLelong b E := by
  simp only [sourceGenericLelong, sourceLelong_ofFixedModel_eq,
    squaredLogLelongNumber, ite_true]

/-- Literal original all-point generic readers converge on every actual
proper holomorphic analytic modification, for every carrier. There is no
finite-blowup, positive mass, Kähler structure on Y or nonempty-carrier premise.
The prime-equivalence quotient is not constructed by this reader theorem. -/
theorem tendsto_sourceGenericLelong_comp_of_sourceSingularityTopology
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (omega : KahlerBackground n X) (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hlim : Tendsto w F (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology omega θ hbig) v)) (E : Set Y) :
    Tendsto (fun i => (ofFixedModel n Y).sourceGenericLelong
      (fun y => (w i).val (π y)) E) F
      (𝓝 ((ofFixedModel n Y).sourceGenericLelong (fun y => v.val (π y)) E)) := by
  cases n with
  | zero =>
      have hreader (a : Y → EReal) : (ofFixedModel 0 Y).sourceGenericLelong a E =
          (ofFixedModel 0 Y).sourceGenericLelong (fun _ => 0) E :=
        sourceGenericLelong_zero_input_independent a (fun _ => 0) E
      simpa only [hreader] using (tendsto_const_nhds : Tendsto
        (fun _ : I => (ofFixedModel 0 Y).sourceGenericLelong (fun _ => 0) E) F
        (𝓝 ((ofFixedModel 0 Y).sourceGenericLelong (fun _ => 0) E)))
  | succ m =>
      let := sourceSingularityPseudoMetricSpace omega θ hbig
      let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace omega θ hbig
      let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology omega θ hbig
      let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
        omega (atlasClosedFormToNative θ) hbig
      let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
        (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
          omega (atlasClosedFormToNative θ) hbig).toUniformSpace
      let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
        (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
          omega (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
      have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
        Topology.IsInducing.induced _
      have hn := hmap.tendsto_nhds_iff.mp hlim
      have hnative := AnalyticModificationNativeLelongLimit.tendsto_divisorialLelongNumber_comp_of_native
        omega (atlasClosedFormToNative θ) hbig hπ F
        (fun i => sourceThetaPotentialL1EquivNative θ (w i))
        (sourceThetaPotentialL1EquivNative θ v) hn E
      have hcont : Continuous (fun a : ℝ≥0∞ => (2 : ℝ≥0∞)⁻¹ * a) :=
        ENNReal.continuous_const_mul (by norm_num)
      have hhalf := (hcont.tendsto
        (divisorialLelongNumber m (fun y => v.val (π y)) E)).comp hnative
      have hread (a : SourceThetaPotentialL1 θ) :
          (sourceThetaPotentialL1EquivNative θ a).val = a.val := rfl
      simpa only [Function.comp_def, sourceGenericLelong_eq_half_native, hread] using hhalf

end SGPT.PSH.VariableComplexAtlas

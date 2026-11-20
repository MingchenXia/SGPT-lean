import SGPT.Checks.Comparison.TraceGenericLelongLimit
import SGPT.NAPotential.BJPrepInfimum

/-! Actual original infimum slices: native dS and generic readers produced
internally. The mass/dS proof is a narrow source port of the checked original
BJPrepInfimum proof preceding its prime-only reader conclusion.
Blueprint: `trace-na-decreasing-limit.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SourceTraceRepresentativeDefinition
open scoped Topology ENNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {α : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Original actual decreasing curve data produce the ACTUAL entire-carrier
source dS slice limit, including genuine bigness internally. -/
theorem exists_sourceSingularityLimit_curve_decreasingInf (omega : KahlerBackground n M)
    (G : I → SourcePositiveIModelTestCurve α)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb)
    {τ : ℝ} (hτ : τ < (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.max) :
    ∃ hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative α)),
      Tendsto (fun i => (⟨(G i).val.potential
        ⟨τ, hτ.trans_le (sourceTestCurveInfCutoff_le (fun i => (G i).val) hb i)⟩,
          (G i).val.thetaPSH _⟩ : SourceThetaPotentialL1 α)) atTop
        (@nhds (SourceThetaPotentialL1 α) (sourceSingularityTopology omega α hbig)
          ⟨(SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.potential ⟨τ,hτ⟩,
            (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.thetaPSH _⟩) := by
  let D := SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm
  have hti : ∀ i, τ < (G i).val.max := fun i =>
    hτ.trans_le (sourceTestCurveInfCutoff_le (fun i => (G i).val) hb i)
  set u : I → M → EReal := fun i => (G i).val.potential ⟨τ, hti i⟩ with hu_def
  have hDpot : D.val.potential ⟨τ, hτ⟩ = fun x => ⨅ i, u i x := rfl
  -- masses converge (`prop:vol_limit_model`)
  set T : ClosedRealOneOneForm n M := atlasClosedFormToNative α with hT_def
  have hT0 : T + (0 : ℝ) • omega.form = T := by rw [zero_smul, add_zero]
  have hφ : ∀ i, IsThetaPshPotential (T + (0 : ℝ) • omega.form).val (u i) := fun i => by
    rw [hT0]
    exact (G i).val.native_thetaPSH _
  have hfix : ∀ i, singularityEnvelope (T + (0 : ℝ) • omega.form).val (u i) = u i := fun i => by
    rw [hT0, hT_def, ← sourceSingularityEnvelope_eq_native]
    exact (G i).val.fixedPoint _
  have hinf : IsThetaPshPotential T.val (fun x => ⨅ i, u i x) := D.val.native_thetaPSH ⟨τ, hτ⟩
  have hanti : Antitone u := fun i j hij x =>
    sourceTestCurveInfSlice_antitone omega (fun i => (G i).val) ha hb ⟨τ, hτ⟩ x hij
  have hlimM := SGPT.Envelopes.PerturbedModelLimit.tendsto_diagonalPotentialMass_iInf omega T
    (ε := fun _ : I => (0 : ℝ)) (φ := u) (fun _ => le_rfl) (fun _ _ _ => le_rfl)
    tendsto_const_nhds hanti hφ hfix hinf
  have hmass : Tendsto (fun i => sourcePotentialNonPluripolarMeasure α (u i)
      ((G i).val.thetaPSH _) univ) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure α (D.val.potential ⟨τ, hτ⟩)
        (D.val.thetaPSH ⟨τ, hτ⟩) univ)) := by
    refine hlimM.congr (fun i => ?_)
    exact sourceNA_diagonalMass_congr_form hT0 _ _
  -- convergence in `d_S` (`cor:decnetdS`)
  have hpos := D.val.mass_positive omega ⟨τ, hτ⟩
  have hbig := BJPrep.isBigClass_of_sourceMass_pos omega (D.val.thetaPSH ⟨τ, hτ⟩) hpos
  let w : I → SourceThetaPotentialL1 α := fun i => ⟨u i, (G i).val.thetaPSH _⟩
  let v : SourceThetaPotentialL1 α := ⟨D.val.potential ⟨τ, hτ⟩, D.val.thetaPSH ⟨τ, hτ⟩⟩
  have horder : ∀ i, SGPT.PSH.GlobalPComparison.sourcePOrder (n := n) v.val (w i).val := fun i =>
    SGPT.PSH.GlobalPComparison.sourcePOrder_of_moreSingular omega
      (D.val.native_thetaPSH ⟨τ, hτ⟩).quasiPshPotential
      ((G i).val.native_thetaPSH _).quasiPshPotential
      ⟨0, fun x _ => by
        rw [EReal.coe_zero, add_zero]
        exact iInf_le (fun i => u i x) i⟩
  have hdS := (tendsto_sourceSingularityTopology_iff_mass_of_sourcePOrder_of_positive_target
    omega α hbig atTop w v horder hpos).mpr hmass
  exact ⟨hbig, hdS⟩

/-- EVERY actual whole-target generic reader of the SAME actual original
infimum slice converges, without a supplied dS or reader limit. -/
theorem tendsto_sourceGenericLelongNumber_curve_decreasingInf (omega : KahlerBackground n M)
    (G : I → SourcePositiveIModelTestCurve α)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb)
    {τ : ℝ} (hτ : τ < (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.max)
    {V : Type*} (ι : V → M) :
    Tendsto (fun i => sourceGenericLelongNumber (n := n) ι ((G i).val.potential
      ⟨τ, hτ.trans_le (sourceTestCurveInfCutoff_le (fun i => (G i).val) hb i)⟩)) atTop
      (𝓝 (sourceGenericLelongNumber (n := n) ι
        ((SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.potential ⟨τ,hτ⟩))) := by
  obtain ⟨hbig, hlim⟩ := exists_sourceSingularityLimit_curve_decreasingInf omega G ha hb hm hτ
  exact tendsto_sourceGenericLelongNumber_of_sourceSingularityTopology omega α hbig atTop
    (fun i => ⟨(G i).val.potential
      ⟨τ, hτ.trans_le (sourceTestCurveInfCutoff_le (fun i => (G i).val) hb i)⟩, (G i).val.thetaPSH _⟩)
    ⟨(SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.potential ⟨τ,hτ⟩,
      (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.thetaPSH _⟩ hlim ι

/-- The original ACTUAL NA infimum supplies every same-component slice
reader limit along an arbitrary target map, in every ambient dimension. -/
theorem tendsto_sourceGenericLelongNumber_na_decreasingInf
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (κ : SourceKahlerForm n M) {τ : ℝ}
    (hτ : τ < ((SourceNAPotential.decreasingInf omega Γ ha hb).component κ).val.max)
    {V : Type*} (ι : V → M) :
    Tendsto (fun i => sourceGenericLelongNumber (n := n) ι (((Γ i).component κ).val.potential
      ⟨τ, hτ.trans_le (sourceTestCurveInfCutoff_le
        (fun i => ((Γ i).component κ).val) (sourceNAFamily_component_bddBelow omega Γ hb κ) i)⟩)) atTop
      (𝓝 (sourceGenericLelongNumber (n := n) ι
        (((SourceNAPotential.decreasingInf omega Γ ha hb).component κ).val.potential ⟨τ,hτ⟩))) :=
  tendsto_sourceGenericLelongNumber_curve_decreasingInf (sourceKahlerFormRepresentative κ)
    (fun i => (Γ i).component κ) (sourceNAFamily_component_antitone Γ ha κ)
    (sourceNAFamily_component_bddBelow omega Γ hb κ)
    (sourceNAFamily_component_massCondition omega Γ hb κ) hτ ι

end SGPT.NAPotential.TraceComparison

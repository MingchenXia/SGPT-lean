import SGPT.PSH.SourceTestCurveDecreasingInf
import SGPT.PSH.SourceTestCurveSemipositiveProjection
import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.PSH.SourceSingularityBackgroundChange
import SGPT.Envelopes.SourcePositiveMassCurrents

/-! # Projection of original decreasing test-curve infima

Exact original-index slice mass limits manufacture all premises of the existing
positive-target singularity-distance and background-change readers. The existing
P-envelope infimum identity identifies actual projected slices. A previously
constructed positive projected lower curve supplies the projected family's
uniform mass condition independently of the identity being proved.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- The actual constructed positive infimum lies intrinsically below EVERY original input. -/
theorem SourceTestCurve.decreasingInf_le (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb)
    (i : I) : SourceTestCurvePOrder (SourceTestCurve.decreasingInf omega Γ ha hb hmass) (Γ i) := by
  apply (sourceTestCurvePOrder_iff omega _ _).mpr
  refine ⟨sourceTestCurveInfCutoff_le Γ hb i, ?_⟩
  intro r hr x
  exact iInf_le _ i

/-- The genuine contact lower bound and ordinary mass monotonicity give the exact whole infimum mass. -/
theorem sourceTestCurveInfPotential_mass_eq_iInf (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (r : Iio (sourceTestCurveInfCutoff Γ)) :
    sourcePotentialNonPluripolarMeasure θ (sourceTestCurveInfPotential Γ hb r)
      (sourceTestCurveInfPotential_ordinary_fields omega Γ ha hb r).1 univ =
    ⨅ i, sourcePotentialNonPluripolarMeasure θ
      ((Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩)
      ((Γ i).thetaPSH _) univ := by
  apply le_antisymm
  · apply le_iInf
    intro i
    exact sourcePotentialNonPluripolarMass_mono omega
      (sourceTestCurveInfPotential_ordinary_fields omega Γ ha hb r).1 ((Γ i).thetaPSH _)
      (MoreSingularOn.of_le fun x _ => iInf_le _ i)
  · exact sourceTestCurveInfPotential_mass_lower_bound omega Γ ha hb r

/-- Actual original-index mass convergence follows without sequence cofinality or an output limit premise. -/
theorem sourceTestCurveInfPotential_mass_tendsto (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (r : Iio (sourceTestCurveInfCutoff Γ)) :
    Tendsto (fun i => sourcePotentialNonPluripolarMeasure θ
      ((Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩)
      ((Γ i).thetaPSH _) univ) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ (sourceTestCurveInfPotential Γ hb r)
        (sourceTestCurveInfPotential_ordinary_fields omega Γ ha hb r).1 univ)) := by
  have hm : Antitone (fun i => sourcePotentialNonPluripolarMeasure θ
      ((Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩)
      ((Γ i).thetaPSH _) univ) := by
    intro i j hij
    exact sourcePotentialNonPluripolarMass_mono omega ((Γ j).thetaPSH _) ((Γ i).thetaPSH _)
      (MoreSingularOn.of_le fun x _ => sourceTestCurveInfSlice_antitone omega Γ ha hb r x hij)
  have hlim := tendsto_atTop_iInf hm
  rwa [← sourceTestCurveInfPotential_mass_eq_iInf omega Γ ha hb r] at hlim

/-- Old positive-target dS and background readers yield the actual envelope identity on original functions. -/
theorem sourceTestCurveInfPotential_semipositiveProjection (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (r : Iio (sourceTestCurveInfCutoff Γ)) :
    sourceSingularityEnvelope (θ.add η) (sourceTestCurveInfPotential Γ hb r) =
      fun x => ⨅ i, sourceSingularityEnvelope (θ.add η)
        ((Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩) x := by
  let G := SourceTestCurve.decreasingInf omega Γ ha hb hmass
  let w : I → SourceThetaPotentialL1 θ := fun i =>
    ⟨(Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩,
      (Γ i).thetaPSH _⟩
  let v : SourceThetaPotentialL1 θ := ⟨G.potential r, G.thetaPSH r⟩
  have hpos : 0 < sourcePotentialNonPluripolarMeasure θ v.val v.property univ :=
    G.mass_positive omega r
  have hbig := sourcePositiveMass_isBig omega v.property hpos
  have horder (i : I) : GlobalPComparison.sourcePOrder (n := n) v.val (w i).val :=
    (SourceTestCurve.decreasingInf_le omega Γ ha hb hmass i).slice_le r.val r.property
  have hanti (i j : I) (hij : i ≤ j) :
      GlobalPComparison.sourcePOrder (n := n) (w j).val (w i).val :=
    (ha i j hij).slice_le r.val (r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb j))
  have hlim : Tendsto w atTop
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) v) :=
    (tendsto_sourceSingularityTopology_iff_mass_of_sourcePOrder_of_positive_target
      omega θ hbig atTop w v horder hpos).mpr
      (sourceTestCurveInfPotential_mass_tendsto omega Γ ha hb r)
  have hlimη := (tendsto_sourceSingularityTopology_iff_semipositive_enlargement
    omega θ η hbig hη atTop w v).mp hlim
  have henv := sourcePEnvelope_eq_iInf_of_antitone_sourcePOrder_tendsto
    omega (θ.add η) (sourceBigClass_add_semipositive θ η hbig hη)
    (fun i => sourceSemipositiveBackgroundPotential η hη (w i))
    (sourceSemipositiveBackgroundPotential η hη v) hanti hlimη
    (G.semipositiveProjectionInput_positive omega η hη r)
  funext x
  simpa only [sourceSemipositiveBackgroundPotential, Subtype.coe_mk, w, v, G,
    SourceTestCurve.decreasingInf, sourceTestCurveDecreasingInfPredata, iInf_apply] using
    congrFun henv x

omit [IsDirectedOrder I] [Nonempty I] in
/-- Actual ordinary-envelope monotonicity preserves the ORIGINAL decreasing direction. -/
theorem sourceTestCurveSemipositiveProjectedFamily_antitone (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    ∀ i j, i ≤ j → SourceTestCurvePOrder
      ((Γ j).semipositiveProjection omega η hη) ((Γ i).semipositiveProjection omega η hη) := by
  intro i j hij
  obtain ⟨hc, hs⟩ := (sourceTestCurvePOrder_iff omega (Γ j) (Γ i)).mp (ha i j hij)
  apply (sourceTestCurvePOrder_iff omega _ _).mpr
  refine ⟨hc, ?_⟩
  intro r hr
  exact sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun x _ => hs r hr x)

/-- A previously produced positive projected lower curve manufactures the target's uniform mass condition. -/
theorem sourceTestCurveSemipositiveProjectedFamily_inf_massCondition (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    SourceTestCurveInfMassCondition (fun i => (Γ i).semipositiveProjection omega η hη) hb := by
  let G := SourceTestCurve.decreasingInf omega Γ ha hb hmass
  let H := G.semipositiveProjection omega η hη
  let r : Iio (sourceTestCurveInfCutoff (fun i => (Γ i).semipositiveProjection omega η hη)) :=
    ⟨sourceTestCurveInfCutoff Γ - 1, by
      change sourceTestCurveInfCutoff Γ - 1 < sourceTestCurveInfCutoff Γ
      linarith⟩
  have hpos := H.mass_positive omega r
  refine ⟨r, hpos.trans_le ?_⟩
  apply le_iInf
  intro i
  have h := (sourceTestCurvePOrder_iff omega G (Γ i)).mp
    (SourceTestCurve.decreasingInf_le omega Γ ha hb hmass i)
  have hbelow : H.potential r ≤ ((Γ i).semipositiveProjection omega η hη).potential
      ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le
        (fun i => (Γ i).semipositiveProjection omega η hη) hb i)⟩ :=
    sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun x _ => h.choose_spec r.val r.property x)
  exact sourcePotentialNonPluripolarMass_mono omega (H.thetaPSH r)
    (((Γ i).semipositiveProjection omega η hη).thetaPSH _)
    (MoreSingularOn.of_le fun x _ => hbelow x)

/-- WHOLE original lma:testcurinfcompatible, with the book's non-strict positive-form convention. -/
theorem source_test_curve_decreasingInf_semipositive_projection_compatible (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    (SourceTestCurve.decreasingInf omega Γ ha hb hmass).semipositiveProjection omega η hη =
      SourceTestCurve.decreasingInf omega (fun i => (Γ i).semipositiveProjection omega η hη)
        (sourceTestCurveSemipositiveProjectedFamily_antitone omega Γ ha η hη) hb
        (sourceTestCurveSemipositiveProjectedFamily_inf_massCondition omega Γ ha hb hmass η hη) := by
  apply SourceTestCurve.ext_of_max_potential _ _
  · rfl
  · intro r hr _hs
    exact sourceTestCurveInfPotential_semipositiveProjection omega Γ ha hb hmass η hη ⟨r, hr⟩

end SGPT.PSH.VariableComplexAtlas

#print axioms SGPT.PSH.VariableComplexAtlas.SourceTestCurve.decreasingInf_le
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfPotential_mass_eq_iInf
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfPotential_mass_tendsto
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfPotential_semipositiveProjection
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveSemipositiveProjectedFamily_antitone
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveSemipositiveProjectedFamily_inf_massCondition
#print axioms SGPT.PSH.VariableComplexAtlas.source_test_curve_decreasingInf_semipositive_projection_compatible

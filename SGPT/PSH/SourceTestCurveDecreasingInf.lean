import SGPT.PSH.SourceTestCurveBackgroundProjection
import SGPT.PSH.SourceIModelTestCurves
import SGPT.PSH.DecreasingNets
import SGPT.Foundations.Analysis.Pending.ActualDecreasingModelPositiveInfimum
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum

/-! # The original positive decreasing test-curve infimum

Whole directed ordinary-model infima produce preliminary curves. Existing
monotone original-index selection and fixed-background sequence contact bounds
produce positive actual limit mass from the original uniform stage condition.
Existing I-envelope infimum closure preserves the original positive I-model
collection. No generic varying-background model-net producer is introduced.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual real infimum of all original cutoffs. -/
def sourceTestCurveInfCutoff {I : Type*} (Γ : I → SourceTestCurve θ) : ℝ :=
  sInf (range fun i => (Γ i).max)

omit [BorelSpace M] [ConnectedSpace M] in
/-- The original lower cutoff bound gives every actual common-interval inclusion. -/
theorem sourceTestCurveInfCutoff_le {I : Type*} (Γ : I → SourceTestCurve θ)
    (hb : BddBelow (range fun i => (Γ i).max)) (i : I) :
    sourceTestCurveInfCutoff Γ ≤ (Γ i).max := csInf_le hb (mem_range_self i)

/-- The literal original strict-slice infimum, indexed over the entire input family. -/
def sourceTestCurveInfPotential {I : Type*} (Γ : I → SourceTestCurve θ)
    (hb : BddBelow (range fun i => (Γ i).max))
    (r : Iio (sourceTestCurveInfCutoff Γ)) : M → EReal :=
  fun x => ⨅ i, (Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩ x

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

omit [IsDirectedOrder I] [Nonempty I] in
/-- The existing intrinsic-order reader produces literal decreasing strict slices. -/
theorem sourceTestCurveInfSlice_antitone (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max))
    (r : Iio (sourceTestCurveInfCutoff Γ)) :
    ∀ x, Antitone (fun i => (Γ i).potential
      ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩ x) := by
  intro x i j hij
  obtain ⟨hc, hs⟩ := (sourceTestCurvePOrder_iff omega (Γ j) (Γ i)).mp (ha i j hij)
  exact hs r.val (r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb j)) x

/-- Genuine PSH and ordinary fixedness of the entire directed infimum are produced. -/
theorem sourceTestCurveInfPotential_ordinary_fields (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max))
    (r : Iio (sourceTestCurveInfCutoff Γ)) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveInfPotential Γ hb r) ∧
      sourceSingularityEnvelope θ (sourceTestCurveInfPotential Γ hb r) =
        sourceTestCurveInfPotential Γ hb r := by
  exact sourceOrdinaryFixedPoint_directedInf _
    (fun i => (Γ i).thetaPSH _) (fun i => (Γ i).fixedPoint _)
    (sourceTestCurveInfSlice_antitone omega Γ ha hb r)

omit [BorelSpace M] [ConnectedSpace M] [Preorder I] [IsDirectedOrder I] [Nonempty I] in
/-- Genuine extended-real convex combinations preserve the actual infimum chord. -/
theorem sourceTestCurveInfPotential_convexComb_le (Γ : I → SourceTestCurve θ)
    (hb : BddBelow (range fun i => (Γ i).max))
    (p q : Iio (sourceTestCurveInfCutoff Γ)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (sourceTestCurveInfPotential Γ hb p) (sourceTestCurveInfPotential Γ hb q) ≤
      sourceTestCurveInfPotential Γ hb ⟨t*p.val+(1-t)*q.val, by
        change t*p.val+(1-t)*q.val < sourceTestCurveInfCutoff Γ
        nlinarith [mul_pos ht0 (sub_pos.mpr p.property),
          mul_pos (sub_pos.mpr ht1) (sub_pos.mpr q.property)]⟩ := by
  intro x
  apply le_iInf
  intro i
  have hp : sourceTestCurveInfPotential Γ hb p ≤ (Γ i).potential
      ⟨p.val, p.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩ :=
    fun y => iInf_le _ i
  have hq : sourceTestCurveInfPotential Γ hb q ≤ (Γ i).potential
      ⟨q.val, q.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩ :=
    fun y => iInf_le _ i
  exact (convexComb_mono ht0.le ht1.le hp hq x).trans
    ((Γ i).toSourceTestCurvePredata.convexComb_le _ _ ht0 ht1 x)

/-- All actual preliminary original fields, without an assumed positive output. -/
def sourceTestCurveDecreasingInfPredata (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) : SourceTestCurvePredata θ where
  max := sourceTestCurveInfCutoff Γ
  potential := sourceTestCurveInfPotential Γ hb
  thetaPSH r := (sourceTestCurveInfPotential_ordinary_fields omega Γ ha hb r).1
  antitone x _p _q hpq := iInf_mono fun i => (Γ i).antitone x hpq
  concave x := sourceTestCurveNegativeTrace_convex_of_chords _
    (fun p q _ ht0 ht1 => sourceTestCurveInfPotential_convexComb_le Γ hb p q ht0 ht1) x
  fixedPoint r := (sourceTestCurveInfPotential_ordinary_fields omega Γ ha hb r).2

/-- Actual monotone original indices retain the WHOLE literal infimum, without cofinality. -/
theorem sourceTestCurveInfPotential_exists_monotone_sequence (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max))
    (r : Iio (sourceTestCurveInfCutoff Γ)) :
    ∃ a : ℕ → I, Monotone a ∧
      (⨅ k, (Γ (a k)).potential
        ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb (a k))⟩) =
        sourceTestCurveInfPotential Γ hb r := by
  obtain ⟨a, ham, heq⟩ := SGPT.PSH.exists_monotone_subfamily_iInf
    (fun i => (Γ i).potential
      ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩)
    (fun i => ((Γ i).native_thetaPSH _).1.quasiPlurisubharmonic.upperSemicontinuous)
    (sourceTestCurveInfSlice_antitone omega Γ ha hb r)
  refine ⟨a, ham, ?_⟩
  funext x
  simpa only [iInf_apply, sourceTestCurveInfPotential] using heq x

/-- Existing sequence contact semicontinuity transfers the ORIGINAL whole-family mass bound. -/
theorem sourceTestCurveInfPotential_mass_lower_bound (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max))
    (r : Iio (sourceTestCurveInfCutoff Γ)) :
    (⨅ i, sourcePotentialNonPluripolarMeasure θ
      ((Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩)
      ((Γ i).thetaPSH _) univ) ≤
      sourcePotentialNonPluripolarMeasure θ (sourceTestCurveInfPotential Γ hb r)
        (sourceTestCurveInfPotential_ordinary_fields omega Γ ha hb r).1 univ := by
  obtain ⟨a, ham, heq⟩ := sourceTestCurveInfPotential_exists_monotone_sequence omega Γ ha hb r
  let u : ℕ → M → EReal := fun k => (Γ (a k)).potential
    ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb (a k))⟩
  have hu (k : ℕ) : IsModelPotential (atlasClosedFormToNative θ) (u k) :=
    ((Γ (a k)).slice_model omega _).toNative
  have hanti : Antitone u := by
    intro k l hkl x
    exact sourceTestCurveInfSlice_antitone omega Γ ha hb r x (ham hkl)
  have hbound (k : ℕ) :
      (⨅ i, sourcePotentialNonPluripolarMeasure θ
        ((Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩)
        ((Γ i).thetaPSH _) univ) ≤
      DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative θ) (u k)
        (hu k).plurisubharmonic := iInf_le _ (a k)
  have hlow := ActualDecreasingModelPositiveInfimum.le_diagonalPotentialMass_iInf_of_le_stage_masses
    omega hu hanti hbound
  change (⨅ k, u k) = sourceTestCurveInfPotential Γ hb r at heq
  simpa only [heq, DiagonalMass.diagonalPotentialMass,
    sourcePotentialNonPluripolarMeasure] using hlow

/-- Precisely the printed original uniform positive mass condition at SOME strict parameter. -/
def SourceTestCurveInfMassCondition (Γ : I → SourceTestCurve θ)
    (hb : BddBelow (range fun i => (Γ i).max)) : Prop :=
  ∃ r : Iio (sourceTestCurveInfCutoff Γ),
    0 < ⨅ i, sourcePotentialNonPluripolarMeasure θ
      ((Γ i).potential ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩)
      ((Γ i).thetaPSH _) univ

/-- Actual original mass lower bound produces positive mass of the preliminary curve's limit. -/
theorem sourceTestCurveDecreasingInfPredata_positiveLimitMass (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb) :
    0 < sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveLimit (sourceTestCurveDecreasingInfPredata omega Γ ha hb))
      (sourceTestCurveDecreasingInfPredata omega Γ ha hb).limit_thetaPSH univ := by
  obtain ⟨r, hr⟩ := hmass
  let P := sourceTestCurveDecreasingInfPredata omega Γ ha hb
  have hpos := hr.trans_le (sourceTestCurveInfPotential_mass_lower_bound omega Γ ha hb r)
  have hbelow : P.potential r ≤ sourceTestCurveLimit P := by
    intro x
    change P.potential r x ≤ uscRegularization (fun y => ⨆ s, P.potential s y) x
    exact (le_iSup (fun s => P.potential s x) r).trans
      (le_uscRegularization (fun y => ⨆ s, P.potential s y) x)
  exact hpos.trans_le (sourcePotentialNonPluripolarMass_mono omega
    (P.thetaPSH r) P.limit_thetaPSH (MoreSingularOn.of_le fun x _ => hbelow x))

/-- The actual original decreasing infimum, with every field produced from the source hypotheses. -/
def SourceTestCurve.decreasingInf (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb) :
    SourceTestCurve θ :=
  { sourceTestCurveDecreasingInfPredata omega Γ ha hb with
    positiveLimitMass := sourceTestCurveDecreasingInfPredata_positiveLimitMass omega Γ ha hb hmass }

/-- Literal original cutoff, without a replacement cofinal sequence or representative. -/
theorem SourceTestCurve.decreasingInf_max (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb) :
    (SourceTestCurve.decreasingInf omega Γ ha hb hmass).max =
      sInf (range fun i => (Γ i).max) := rfl

/-- Every original strict slice is the ENTIRE original-index infimum. -/
theorem SourceTestCurve.decreasingInf_potential (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb)
    (r : Iio (sourceTestCurveInfCutoff Γ)) :
    (SourceTestCurve.decreasingInf omega Γ ha hb hmass).potential r =
      fun x => ⨅ i, (Γ i).potential
        ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩ x := rfl

/-- Existing genuine I-envelope infimum closure retains ALL original I-model slices. -/
theorem SourceTestCurve.decreasingInf_isIModel (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb)
    (hI : ∀ i, SourceTestCurveIsIModel (Γ i)) :
    SourceTestCurveIsIModel (SourceTestCurve.decreasingInf omega Γ ha hb hmass) := by
  let G := SourceTestCurve.decreasingInf omega Γ ha hb hmass
  have : Nonempty M := by
    by_contra hn
    have hempty : (univ : Set M) = ∅ := by
      ext x
      exact False.elim (hn ⟨x⟩)
    have hpos := G.positiveLimitMass
    rw [hempty, measure_empty] at hpos
    exact (lt_irrefl 0) hpos
  intro r
  let v : I → M → EReal := fun i => (Γ i).potential
    ⟨r.val, r.property.trans_le (sourceTestCurveInfCutoff_le Γ hb i)⟩
  have hfun : (⨅ i, v i) = G.potential r := by
    funext x
    simp only [iInf_apply, v, G, SourceTestCurve.decreasingInf,
      sourceTestCurveDecreasingInfPredata, sourceTestCurveInfPotential]
  have hθ : IsThetaPshPotential (atlasClosedFormToNative θ).val (⨅ i, v i) :=
    hfun.symm ▸ G.native_thetaPSH r
  have hmodel := ActualIEnvelopeOrderInfimum.isIModelPotential_iInf_of_isThetaPshPotential
    (atlasClosedFormToNative θ) (v := v) (fun i => hI i _) hθ
  simpa only [hfun] using hmodel

/-- BOTH original prop:inftcistc assertions on the actual constructed entire curve. -/
theorem source_test_curve_decreasing_inf_whole (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hmass : SourceTestCurveInfMassCondition Γ hb) :
    (SourceTestCurve.decreasingInf omega Γ ha hb hmass ∈ SourceTestCurvesPositive θ) ∧
    ((∀ i, Γ i ∈ SourceIModelTestCurvesPositive θ) →
      SourceTestCurve.decreasingInf omega Γ ha hb hmass ∈ SourceIModelTestCurvesPositive θ) :=
  ⟨(SourceTestCurve.decreasingInf omega Γ ha hb hmass).mem_positive omega,
    fun hI => (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
      (SourceTestCurve.decreasingInf_isIModel omega Γ ha hb hmass
        (fun i => (sourceIModelTestCurvesPositive_iff_slices omega _).mp (hI i)))⟩

end SGPT.PSH.VariableComplexAtlas

#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfCutoff
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfCutoff_le
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfPotential
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfSlice_antitone
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfPotential_ordinary_fields
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfPotential_convexComb_le
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveDecreasingInfPredata
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfPotential_exists_monotone_sequence
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveInfPotential_mass_lower_bound
#print axioms SGPT.PSH.VariableComplexAtlas.SourceTestCurveInfMassCondition
#print axioms SGPT.PSH.VariableComplexAtlas.sourceTestCurveDecreasingInfPredata_positiveLimitMass
#print axioms SGPT.PSH.VariableComplexAtlas.SourceTestCurve.decreasingInf
#print axioms SGPT.PSH.VariableComplexAtlas.SourceTestCurve.decreasingInf_max
#print axioms SGPT.PSH.VariableComplexAtlas.SourceTestCurve.decreasingInf_potential
#print axioms SGPT.PSH.VariableComplexAtlas.SourceTestCurve.decreasingInf_isIModel
#print axioms SGPT.PSH.VariableComplexAtlas.source_test_curve_decreasing_inf_whole

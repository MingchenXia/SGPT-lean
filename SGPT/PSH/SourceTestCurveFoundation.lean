import SGPT.Envelopes.SourceDecreasingOrdinaryFixedPoints
import SGPT.Convex.Epigraph
import SGPT.PSH.Supremum
import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

/-- The negative of the ORIGINAL open-interval family, with top only
outside that domain. Genuine epigraph convexity expresses source concavity. -/
def sourceTestCurveNegativeTrace {X : Type*} (m : ℝ)
    (family : Iio m → X → EReal) (x : X) (τ : ℝ) : EReal :=
  if hτ : τ < m then -family ⟨τ, hτ⟩ x else ⊤

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original REAL cutoff and actual source-PSH family with precisely
its pointwise concavity, decreasingness and ordinary-P fixedpoint clauses.
No positive slice mass or limit conclusion is input data. -/
structure SourceTestCurvePredata (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) where
  max : ℝ
  potential : Iio max → M → EReal
  thetaPSH : ∀ τ, (ofFixedModel n M).IsThetaPSH θ (potential τ)
  antitone : ∀ x, Antitone (fun τ ↦ potential τ x)
  concave : ∀ x, SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace max potential x)
  fixedPoint : ∀ τ, sourceSingularityEnvelope θ (potential τ) = potential τ

/-- The printed fixedpoint clause PRODUCES the actual normalization bound. -/
theorem SourceTestCurvePredata.le_zero
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) (τ : Iio Γ.max) : Γ.potential τ ≤ 0 := by
  rw [← Γ.fixedPoint τ]
  exact sourceSingularityEnvelope_le_zero θ (Γ.potential τ)

/-- SAME original slice, under the complete actual source/native dictionary. -/
theorem SourceTestCurvePredata.native_thetaPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) (τ : Iio Γ.max) :
    IsThetaPshPotential (atlasClosedFormToNative θ).val (Γ.potential τ) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mp (Γ.thetaPSH τ)

/-- The literal ORIGINAL spatial usc-regularized supremum over ALL original
sub-cutoff parameters, retaining every actual pole and source value. -/
def sourceTestCurveLimit {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) : M → EReal := SGPT.PSH.uscSup Γ.potential

/-- Genuine existing arbitrary-family supremum PSH and SAME-member local ND
manufacture full original source PSH BEFORE its actual measure is used. -/
theorem SourceTestCurvePredata.limit_thetaPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveLimit Γ) := by
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  exact SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
    Γ.native_thetaPSH (C := 0)
      (fun τ x ↦ by simpa only [EReal.coe_zero, Pi.zero_apply] using Γ.le_zero τ x)

variable [MeasurableSpace M] [CompactSpace M]

/-- ENTIRE original test-curve definition: the actual preliminary family
and precisely the printed positive ACTUAL mass of its PRODUCED PSH limit. -/
structure SourceTestCurve (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    extends SourceTestCurvePredata θ where
  positiveLimitMass :
    0 < sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit toSourceTestCurvePredata)
      toSourceTestCurvePredata.limit_thetaPSH univ

/-- The literal ORIGINAL based class, with original positive-mass model
and equality of actual limit FUNCTIONS, not normalized representatives. -/
def SourceTestCurvesBased (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (_hφ : SourceModelPotential θ φ) : Set (SourceTestCurve θ) :=
  {Γ | sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ}

/-- The ORIGINAL union of based classes over ALL original positive models.
No increasing-model output theorem is silently built into the object. -/
def SourceTestCurvesPositive (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    Set (SourceTestCurve θ) :=
  {Γ | ∃ (φ : M → EReal) (hφ : SourceModelPotential θ φ), Γ ∈ SourceTestCurvesBased θ φ hφ}

/-- Exact original union reader, on the SAME underlying source test curve. -/
theorem sourceTestCurvesPositive_iff
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ) :
    Γ ∈ SourceTestCurvesPositive θ ↔
      ∃ (φ : M → EReal) (hφ : SourceModelPotential θ φ),
        Γ ∈ SourceTestCurvesBased θ φ hφ := Iff.rfl

/-- The source mass condition is read as the SAME original actual NP mass. -/
theorem SourceTestCurve.limit_mass_positive
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ) :
    0 < sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit Γ.toSourceTestCurvePredata)
      Γ.toSourceTestCurvePredata.limit_thetaPSH univ := Γ.positiveLimitMass

/-- The LITERAL original cutoff infimum over ALL original sub-cutoff
parameters; no choice of sequence or replacement representative. -/
def sourceTestCurveCutoff {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) : M → EReal := fun x ↦ ⨅ τ, Γ.potential τ x

variable [ConnectedSpace M]

omit [MeasurableSpace M] in
/-- Actual normalization and compact directed-infimum noncollapse produce
genuine source PSH at the cutoff, with ZERO mass explicitly permitted. -/
theorem SourceTestCurvePredata.cutoff_thetaPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurvePredata θ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveCutoff Γ) := by
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  exact sourceOrdinaryFixedPoint_directedInf_thetaPSH
    Γ.potential Γ.thetaPSH Γ.fixedPoint Γ.antitone

omit [MeasurableSpace M] in
/-- The same zero-mass-allowed actual infimum retains its ordinary-P fixedpoint. -/
theorem SourceTestCurvePredata.cutoff_fixedPoint
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurvePredata θ) :
    sourceSingularityEnvelope θ (sourceTestCurveCutoff Γ) = sourceTestCurveCutoff Γ := by
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  exact sourceOrdinaryFixedPoint_directedInf_eq
    Γ.potential Γ.thetaPSH Γ.fixedPoint Γ.antitone

/-- EXACT original three branches: same family below the cutoff, literal
infimum AT it, and bottom ABOVE it. The original domain is unchanged. -/
def sourceTestCurveAt {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) (τ : ℝ) : M → EReal :=
  if hτ : τ < Γ.max then Γ.potential ⟨τ, hτ⟩
  else if τ = Γ.max then sourceTestCurveCutoff Γ else ⊥

omit [MeasurableSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Actual original family value at EVERY original sub-cutoff parameter. -/
theorem sourceTestCurveAt_of_lt {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) {τ : ℝ} (hτ : τ < Γ.max) :
    sourceTestCurveAt Γ τ = Γ.potential ⟨τ, hτ⟩ := by
  simp only [sourceTestCurveAt, dif_pos hτ]

omit [MeasurableSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Actual original cutoff value, retaining the entire literal infimum. -/
theorem sourceTestCurveAt_eq_max {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) :
    sourceTestCurveAt Γ Γ.max = sourceTestCurveCutoff Γ := by
  rw [sourceTestCurveAt, dif_neg (lt_irrefl Γ.max), if_pos rfl]

omit [MeasurableSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The original bottom branch at EVERY strictly super-cutoff parameter. -/
theorem sourceTestCurveAt_of_gt {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceTestCurvePredata θ) {τ : ℝ} (hτ : Γ.max < τ) :
    sourceTestCurveAt Γ τ = ⊥ := by
  simp only [sourceTestCurveAt, dif_neg (not_lt.mpr hτ.le), if_neg (ne_of_gt hτ)]

omit [MeasurableSpace M] in
/-- WHOLE original extension remark, including produced full source PSH
AT the cutoff and the literal bottom branch beyond it. -/
theorem source_test_curve_extension_whole
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurvePredata θ) :
    (∀ (τ : ℝ) (hτ : τ < Γ.max), sourceTestCurveAt Γ τ = Γ.potential ⟨τ, hτ⟩) ∧
      sourceTestCurveAt Γ Γ.max = sourceTestCurveCutoff Γ ∧
      (∀ τ : ℝ, Γ.max < τ → sourceTestCurveAt Γ τ = ⊥) ∧
      (∀ τ : ℝ, τ ≤ Γ.max → (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveAt Γ τ)) := by
  refine ⟨fun _ hτ ↦ sourceTestCurveAt_of_lt Γ hτ, sourceTestCurveAt_eq_max Γ,
    fun _ hτ ↦ sourceTestCurveAt_of_gt Γ hτ, ?_⟩
  intro τ hτ
  rcases hτ.eq_or_lt with heq | hlt
  · rw [heq, sourceTestCurveAt_eq_max]
    exact Γ.cutoff_thetaPSH
  · rw [sourceTestCurveAt_of_lt Γ hlt]
    exact Γ.thetaPSH ⟨τ, hlt⟩

end SGPT.PSH.VariableComplexAtlas

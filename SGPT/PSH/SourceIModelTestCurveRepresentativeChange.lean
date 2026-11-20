import SGPT.PSH.SourceTestCurveRepresentativeChange
import SGPT.Envelopes.SourceIEnvelopeRepresentativeChange
import SGPT.PSH.SourcePIComparison

/-! # Original positive I-model test-curve representative independence

The already accepted ordinary curve equivalence preserves I-model slices:
smooth I-envelope comparison and the existing P[I]=I law identify each
actual target slice. Restrict the same maps to the original positive unions,
retaining the actual inverse, cocycle and every printed smooth-gauge formula.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- For every actual smooth gauge, I-fixed original slices become exactly
the actual target I-envelope. Genuine target PSH is produced on u-g first. -/
theorem SourceTestCurve.changeRepresentative_potential_iEnvelope (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    {g : M → ℝ} (hchange : SourceSmoothBackgroundChange θ η g)
    (Γ : SourceTestCurve θ) (hI : SourceTestCurveIsIModel Γ) (r : Iio Γ.max) :
    (Γ.changeRepresentative ω hc).potential r =
      sourceIEnvelope η (fun x ↦ Γ.potential r x - (g x : EReal)) := by
  have hs := sourceThetaPSH_sub_smooth hchange (Γ.thetaPSH r)
  have hfix : sourceIEnvelope θ (Γ.potential r) = Γ.potential r :=
    ((sourceIModel_iff_native θ _).mpr (hI r)).2.symm
  have ht := (sourceIEnvelope_changeRepresentative hchange (Γ.thetaPSH r)).2
  rw [hfix] at ht
  calc
    _ = sourceSingularityEnvelope η (Γ.potential r) := Γ.changeRepresentative_potential ω hc r
    _ = sourceSingularityEnvelope η (sourceIEnvelope η (fun x ↦ Γ.potential r x - (g x : EReal))) :=
      le_antisymm (sourceOrdinaryEnvelope_mono ht.1) (sourceOrdinaryEnvelope_mono ht.2)
    _ = _ := sourcePEnvelope_iEnvelope hs

/-- Actual cohomology equality manufactures a smooth gauge; the preceding
literal slice identity and old genuine I-envelope projection produce ALL
native I-model output slices. The parent curve is already positive. -/
theorem SourceTestCurve.changeRepresentative_isIModel (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceTestCurve θ) (hI : SourceTestCurveIsIModel Γ) :
    SourceTestCurveIsIModel (Γ.changeRepresentative ω hc) := by
  obtain ⟨g, hg, hθη⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hc
  have hs : SourceSmoothBackgroundChange θ η g :=
    (sourceSmoothBackgroundChange_iff_native θ η g).mpr ⟨hg, hθη⟩
  intro r
  have he := Γ.changeRepresentative_potential_iEnvelope ω hc hs hI r
  exact (sourceIModel_iff_native η _).mp
    (he.symm ▸ sourceIEnvelope_isIModel (sourceThetaPSH_sub_smooth hs (Γ.thetaPSH r)))

/-- The already proved ordinary inverse reflects original I-modelness. -/
theorem SourceTestCurve.changeRepresentative_isIModel_iff (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    SourceTestCurveIsIModel (Γ.changeRepresentative ω hc) ↔ SourceTestCurveIsIModel Γ := by
  constructor
  · intro hI
    have hi := (Γ.changeRepresentative ω hc).changeRepresentative_isIModel ω hc.symm hI
    exact (sourceTestCurveRepresentativeEquiv ω hc).symm_apply_apply Γ ▸ hi
  · exact Γ.changeRepresentative_isIModel ω hc

/-- The endpoints are the EXACT original positive unions, including genuine
produced positive model bases; this is not merely a slice proxy. -/
theorem SourceTestCurve.changeRepresentative_mem_positiveIModel_iff (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceTestCurve θ) :
    Γ.changeRepresentative ω hc ∈ SourceIModelTestCurvesPositive η ↔
      Γ ∈ SourceIModelTestCurvesPositive θ :=
  (sourceIModelTestCurvesPositive_iff_slices ω _).trans
    ((Γ.changeRepresentative_isIModel_iff ω hc).trans
      (sourceIModelTestCurvesPositive_iff_slices ω Γ).symm)

/-- Restriction of the SAME canonical ordinary equivalence to the original
positive I-model unions, with actual reverse transport as inverse. -/
def sourceIModelTestCurveRepresentativeEquiv (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) :
    SourceIModelTestCurvesPositive θ ≃ SourceIModelTestCurvesPositive η where
  toFun Γ := ⟨Γ.val.changeRepresentative ω hc,
    (Γ.val.changeRepresentative_mem_positiveIModel_iff ω hc).mpr Γ.property⟩
  invFun Δ := ⟨Δ.val.changeRepresentative ω hc.symm,
    (Δ.val.changeRepresentative_mem_positiveIModel_iff ω hc.symm).mpr Δ.property⟩
  left_inv Γ := Subtype.ext ((sourceTestCurveRepresentativeEquiv ω hc).symm_apply_apply Γ.val)
  right_inv Δ := Subtype.ext ((sourceTestCurveRepresentativeEquiv ω hc).apply_symm_apply Δ.val)

/-- Literal underlying-curve reader of the actual subtype equivalence. -/
theorem sourceIModelTestCurveRepresentativeEquiv_val (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceIModelTestCurvesPositive θ) :
    (sourceIModelTestCurveRepresentativeEquiv ω hc Γ).val = Γ.val.changeRepresentative ω hc := rfl

/-- The source positive I-model cocycle is equality of the actual canonical
equivalences, proved using the SAME ordinary underlying-curve cocycle. -/
theorem sourceIModelTestCurveRepresentativeEquiv_trans (ω : KahlerBackground n M)
    (hθη : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (hηζ : RealBottChern.ofRepresentative (atlasClosedFormToNative η) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative ζ)) :
    (sourceIModelTestCurveRepresentativeEquiv ω hθη).trans
        (sourceIModelTestCurveRepresentativeEquiv ω hηζ) =
      sourceIModelTestCurveRepresentativeEquiv ω (hθη.trans hηζ) := by
  apply Equiv.ext
  intro Γ
  apply Subtype.ext
  calc
    _ = (sourceIModelTestCurveRepresentativeEquiv ω hηζ
        (sourceIModelTestCurveRepresentativeEquiv ω hθη Γ)).val := rfl
    _ = (sourceIModelTestCurveRepresentativeEquiv ω hθη Γ).val.changeRepresentative ω hηζ :=
      sourceIModelTestCurveRepresentativeEquiv_val ω hηζ _
    _ = (Γ.val.changeRepresentative ω hθη).changeRepresentative ω hηζ :=
      congrArg (fun Δ : SourceTestCurve η ↦ Δ.changeRepresentative ω hηζ)
        (sourceIModelTestCurveRepresentativeEquiv_val ω hθη Γ)
    _ = Γ.val.changeRepresentative ω (hθη.trans hηζ) := Γ.val.changeRepresentative_comp ω hθη hηζ
    _ = _ := (sourceIModelTestCurveRepresentativeEquiv_val ω (hθη.trans hηζ) Γ).symm

/-- The exact printed original ordinary-envelope formula holds for EVERY
admissible smooth gauge on the SAME original I-model input object. -/
theorem sourceIModelTestCurveRepresentativeEquiv_potential_sub_smooth (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    {g : M → ℝ} (hchange : SourceSmoothBackgroundChange θ η g)
    (Γ : SourceIModelTestCurvesPositive θ) (r : Iio Γ.val.max) :
    (sourceIModelTestCurveRepresentativeEquiv ω hc Γ).val.potential r =
      sourceSingularityEnvelope η (fun x ↦ Γ.val.potential r x - (g x : EReal)) :=
  Γ.val.changeRepresentative_potential_sub_smooth ω hc hchange r

/-- WHOLE original prop:Imodeltestcurveindeptheta: genuine bijection of the
actual positive I-model unions, exact cocycle and printed gauge formula. -/
theorem source_I_model_test_curve_representative_independence_whole (ω : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) :
    Function.Bijective (sourceIModelTestCurveRepresentativeEquiv ω hc) ∧
      (∀ (ξ : AtlasClosedRealOneOneForm (ofFixedModel n M))
        (hηξ : RealBottChern.ofRepresentative (atlasClosedFormToNative η) =
          RealBottChern.ofRepresentative (atlasClosedFormToNative ξ)),
        (sourceIModelTestCurveRepresentativeEquiv ω hc).trans
            (sourceIModelTestCurveRepresentativeEquiv ω hηξ) =
          sourceIModelTestCurveRepresentativeEquiv ω (hc.trans hηξ)) ∧
      (∀ (g : M → ℝ) (_hchange : SourceSmoothBackgroundChange θ η g)
        (Γ : SourceIModelTestCurvesPositive θ) (r : Iio Γ.val.max),
        (sourceIModelTestCurveRepresentativeEquiv ω hc Γ).val.potential r =
          sourceSingularityEnvelope η (fun x ↦ Γ.val.potential r x - (g x : EReal))) := by
  refine ⟨(sourceIModelTestCurveRepresentativeEquiv ω hc).bijective, ?_, ?_⟩
  · intro ξ hηξ
    exact sourceIModelTestCurveRepresentativeEquiv_trans ω hc hηξ
  · intro g hchange Γ r
    exact sourceIModelTestCurveRepresentativeEquiv_potential_sub_smooth ω hc hchange Γ r


end SGPT.PSH.VariableComplexAtlas

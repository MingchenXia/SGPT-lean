import SGPT.PSH.SourceTestCurveSumIGood
import SGPT.PSH.SourceTestCurveSemipositiveProjection
import SGPT.PSH.SourceGlobalOrderAddition
import SGPT.PSH.SourceGlobalOrderSupremum

/-! # The whole original compatibility of test-curve sum and projection

Strict-open raw-convolution recovery avoids assumptions at zero-mass cutoffs.
The two added forms are arbitrary semipositive forms, and may both vanish.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Addition preserves semipositivity of the entire original closed form. -/
theorem sourceSemipositiveSum_isSemipositive
    (η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (hζ : (atlasClosedFormToNative ζ).val.IsSemipositive) :
    (atlasClosedFormToNative (η.add ζ)).val.IsSemipositive := by
  rw [sourceNativeClosedForm_add]
  intro e z hz v
  simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
    add_nonneg (hη e z hz v) (hζ e z hz v)

/-- The actual sum/enlargement backgrounds agree as full original atlas forms. -/
theorem sourceSumSemipositiveProjectionBackground_eq
    (θ σ η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)).add
        (η.add ζ) =
      nativeClosedFormToAtlas
        (atlasClosedFormToNative (θ.add η) + atlasClosedFormToNative (σ.add ζ)) := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip]
  abel

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Genuine global P-equivalence of the SAME raw all-real convolutions after
projection of both inputs; only their strict open slices are used. -/
theorem sourceTestCurveRawSum_semipositive_sourcePEquivalent
    (omega : KahlerBackground n M)
    (η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (hζ : (atlasClosedFormToNative ζ).val.IsSemipositive)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    {r : ℝ} (hr : r < Γ.max + Δ.max) :
    GlobalPComparison.sourcePEquivalent (n := n)
      (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r)
      (sourceTestCurveRawSum
        (Γ.semipositiveProjection omega η hη).toSourceTestCurvePredata
        (Δ.semipositiveProjection omega ζ hζ).toSourceTestCurvePredata r) := by
  let G := Γ.semipositiveProjection omega η hη
  let D := Δ.semipositiveProjection omega ζ hζ
  let J := Ioo (r - Δ.max) Γ.max
  have : Nonempty J := ⟨⟨((r - Δ.max) + Γ.max) / 2, by constructor <;> linarith⟩⟩
  let u : J → M → EReal := fun d x ↦ sourceTestCurveAt Γ.toSourceTestCurvePredata d.val x +
    sourceTestCurveAt Δ.toSourceTestCurvePredata (r - d.val) x
  let v : J → M → EReal := fun d x ↦ sourceTestCurveAt G.toSourceTestCurvePredata d.val x +
    sourceTestCurveAt D.toSourceTestCurvePredata (r - d.val) x
  let T := nativeClosedFormToAtlas
    (atlasClosedFormToNative (θ.add η) + atlasClosedFormToNative (σ.add ζ))
  have hd (d : J) : r - d.val < Δ.max := by linarith [d.property.1]
  have hu (d : J) : (ofFixedModel n M).IsThetaPSH T (u d) := by
    dsimp [u]
    rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata d.property.2,
      sourceTestCurveAt_of_lt Δ.toSourceTestCurvePredata (hd d)]
    exact sourceIndependentSum_thetaPSH
      (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH _))
      (sourceThetaPSH_add_semipositive ζ hζ (Δ.thetaPSH _))
  have hv (d : J) : (ofFixedModel n M).IsThetaPSH T (v d) := by
    dsimp [v]
    rw [sourceTestCurveAt_of_lt G.toSourceTestCurvePredata d.property.2,
      sourceTestCurveAt_of_lt D.toSourceTestCurvePredata (hd d)]
    exact sourceIndependentSum_thetaPSH (G.thetaPSH _) (D.thetaPSH _)
  have hpair (d : J) : GlobalPComparison.sourcePEquivalent (n := n) (u d) (v d) := by
    let a : Iio Γ.max := ⟨d.val, d.property.2⟩
    let b : Iio Δ.max := ⟨r - d.val, hd d⟩
    let aG : Iio G.max := ⟨d.val, d.property.2⟩
    let bD : Iio D.max := ⟨r - d.val, hd d⟩
    have hG : GlobalPComparison.sourcePEquivalent (n := n) (Γ.potential a) (G.potential aG) := by
      change GlobalPComparison.sourcePEquivalent (n := n) (Γ.potential a)
        (sourceSingularityEnvelope (θ.add η) (Γ.potential a))
      simpa only [sourceSingularityEnvelope_eq_native] using
        SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
          (atlasClosedFormToNative (θ.add η))
          ((isThetaPSH_iff_nativeThetaPotential _ _).mp
            (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH a)))
    have hD : GlobalPComparison.sourcePEquivalent (n := n) (Δ.potential b) (D.potential bD) := by
      change GlobalPComparison.sourcePEquivalent (n := n) (Δ.potential b)
        (sourceSingularityEnvelope (σ.add ζ) (Δ.potential b))
      simpa only [sourceSingularityEnvelope_eq_native] using
        SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
          (atlasClosedFormToNative (σ.add ζ))
          ((isThetaPSH_iff_nativeThetaPotential _ _).mp
            (sourceThetaPSH_add_semipositive ζ hζ (Δ.thetaPSH b)))
    have h := SGPT.PSH.GlobalOrderAddition.sourcePEquivalent_add omega
      ⟨θ, Γ.thetaPSH a⟩ ⟨σ, Δ.thetaPSH b⟩
      ⟨θ.add η, G.thetaPSH aG⟩ ⟨σ.add ζ, D.thetaPSH bD⟩ hG hD
    simpa only [u, v, a, b, aG, bD, sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata d.property.2,
      sourceTestCurveAt_of_lt Δ.toSourceTestCurvePredata (hd d),
      sourceTestCurveAt_of_lt G.toSourceTestCurvePredata d.property.2,
      sourceTestCurveAt_of_lt D.toSourceTestCurvePredata (hd d)] using h
  have huBound : ∃ C : ℝ, ∀ d x, u d x ≤ (C : EReal) := by
    refine ⟨0, ?_⟩
    intro d x
    change u d x ≤ (0 : EReal)
    exact add_nonpos (Γ.at_le_zero d.val x) (Δ.at_le_zero (r - d.val) x)
  have hvBound : ∃ C : ℝ, ∀ d x, v d x ≤ (C : EReal) := by
    refine ⟨0, ?_⟩
    intro d x
    change v d x ≤ (0 : EReal)
    exact add_nonpos (G.at_le_zero d.val x) (D.at_le_zero (r - d.val) x)
  have hforward := sourcePOrder_uscSup omega hu hv huBound hvBound (fun d ↦ (hpair d).1)
  have hreverse := sourcePOrder_uscSup omega hv hu hvBound huBound (fun d ↦ (hpair d).2)
  have hrawu : sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r =
      uscSup u := sourceTestCurveRawSum_eq_uscSup_open _ _ hr
  have hrawv : sourceTestCurveRawSum G.toSourceTestCurvePredata D.toSourceTestCurvePredata r =
      uscSup v := sourceTestCurveRawSum_eq_uscSup_open _ _ hr
  rw [← hrawu, ← hrawv] at hforward hreverse
  exact ⟨hforward, hreverse⟩

/-- Whole original `lma:testcursumcomp`, with every added smooth closed
semipositive form, exact whole-background equality and the literal original sum. -/
theorem source_test_curve_sum_semipositive_projection_compatible
    (omega : KahlerBackground n M)
    (η ζ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (hζ : (atlasClosedFormToNative ζ).val.IsSemipositive)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    ((SourceTestCurve.sum omega Γ Δ).semipositiveProjection omega (η.add ζ)
        (sourceSemipositiveSum_isSemipositive η ζ hη hζ)).castBackground
          (sourceSumSemipositiveProjectionBackground_eq θ σ η ζ) =
      SourceTestCurve.sum omega (Γ.semipositiveProjection omega η hη)
        (Δ.semipositiveProjection omega ζ hζ) := by
  let S := SourceTestCurve.sum omega Γ Δ
  let G := Γ.semipositiveProjection omega η hη
  let D := Δ.semipositiveProjection omega ζ hζ
  let T₀ := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  let T := nativeClosedFormToAtlas
    (atlasClosedFormToNative (θ.add η) + atlasClosedFormToNative (σ.add ζ))
  have hηζ := sourceSemipositiveSum_isSemipositive η ζ hη hζ
  have hforms := sourceSumSemipositiveProjectionBackground_eq θ σ η ζ
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.castBackground_max, SourceTestCurve.semipositiveProjection_max,
      SourceTestCurve.sum_max]
  · intro r hr hs
    have hrl : r < (S.semipositiveProjection omega (η.add ζ) hηζ).max := by
      simpa only [SourceTestCurve.castBackground_max] using hr
    have hrS : r < S.max := hrl
    have hrΓΔ : r < Γ.max + Δ.max := hrS
    rw [SourceTestCurve.castBackground_potential _ _ r hrl hr]
    change sourceSingularityEnvelope (T₀.add (η.add ζ)) (S.potential ⟨r, hrS⟩) =
      sourceSingularityEnvelope T (sourceTestCurveRawSum G.toSourceTestCurvePredata
        D.toSourceTestCurvePredata r)
    rw [hforms]
    have huL := sourceThetaPSH_add_semipositive (η.add ζ) hηζ (S.thetaPSH ⟨r, hrS⟩)
    have hu : (ofFixedModel n M).IsThetaPSH T (S.potential ⟨r, hrS⟩) := by
      simpa only [hforms] using huL
    have hup : 0 < sourcePotentialNonPluripolarMeasure T (S.potential ⟨r, hrS⟩) hu univ := by
      simpa only [hforms] using
        S.semipositiveProjectionInput_positive omega (η.add ζ) hηζ ⟨r, hrS⟩
    have hv : (ofFixedModel n M).IsThetaPSH T
        (sourceTestCurveRawSum G.toSourceTestCurvePredata D.toSourceTestCurvePredata r) :=
      sourceTestCurveRawSum_thetaPSH _ _ hrΓΔ.le
    have hvp := sourceTestCurveRawSum_mass_positive omega G D hrΓΔ
    have hraw₀ := sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata hrΓΔ.le
    have henvelope := SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
      (atlasClosedFormToNative T₀) ((isThetaPSH_iff_nativeThetaPotential T₀ _).mp hraw₀)
    have hsraw : GlobalPComparison.sourcePEquivalent (n := n) (S.potential ⟨r, hrS⟩)
        (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r) := by
      change GlobalPComparison.sourcePEquivalent (n := n)
        (sourceSingularityEnvelope T₀
          (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r)) _
      rw [sourceSingularityEnvelope_eq_native]
      exact ⟨henvelope.2, henvelope.1⟩
    have hraw := sourceTestCurveRawSum_semipositive_sourcePEquivalent omega η ζ hη hζ Γ Δ hrΓΔ
    have hequiv : GlobalPComparison.sourcePEquivalent (n := n) (S.potential ⟨r, hrS⟩)
        (sourceTestCurveRawSum G.toSourceTestCurvePredata D.toSourceTestCurvePredata r) :=
      ⟨GlobalPComparison.sourcePOrder_trans omega hsraw.1 hraw.1,
        GlobalPComparison.sourcePOrder_trans omega hraw.2 hsraw.2⟩
    have hfixed := (SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith omega
      (atlasClosedFormToNative T)
      ((isThetaPSH_iff_nativeThetaPotential T _).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential T _).mp hv) hup hvp).mp hequiv
    simpa only [sourceSingularityEnvelope_eq_native] using
      POrder.pEquivalentWith_iff_envelope_eq.mp hfixed

end SGPT.PSH.VariableComplexAtlas

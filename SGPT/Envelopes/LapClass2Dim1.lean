import SGPT.Envelopes.LapClass2Chart
import SGPT.Envelopes.DNTC11Envelopes
import SGPT.Envelopes.DNTC11Mixed
import SGPT.Envelopes.C11RealRoofContact

/-!
# The DNT circle for the book's `C^{1,1̄}(X)` on compact Kähler curves

Lane LAP-CLASS2 (`claude-lap-class2`, node `lap-class2:dim-one-dnt`).  Source:
`references/sgpt-d3f272c3/source/author/chapter_npp.tex`, `lma:DNTroof`, `thm:DNTcontact`,
`cor:DNTenvelope1`, `prop:DNTenvelope2`, `prop:DNTenvelope3`.

The earlier lanes (S48, S53/DNT-C11, NPP-DNT, C11-REAL) proved these statements for obstacles
with bounded complex Hessian (`DNTC11.HasBoundedComplexHessian`).  The book's class `C^{1,1̄}(X)`
is the class of continuous functions with bounded `ω`-Laplacian (`HasBoundedMetricLaplacian`,
lane LAP-CLASS).  In dimension one the two classes coincide
(`hasBoundedMetricLaplacian_iff_hasBoundedComplexHessian_of_dim_one`), so all the proved clauses
hold for the book's class when `n = dim X = 1`:

* `sourcePotentialNonPluripolarMeasure_restrict_contact_eq_of_dim_one`,
  `diagonalPotentialMeasure_restrict_contact_eq_of_dim_one`,
  `sourceMixedNonPluripolarMeasure_restrict_mixedContact_toReal_eq_of_dim_one`
  (`thm:DNTcontact`, `n = 1`: a single factor);
* `sourceObstacleEnvelope_measure_eq_of_dim_one` (`cor:DNTenvelope1`);
* `sourceGeneralizedEnvelope_measure_eq_of_dim_one` (`prop:DNTenvelope2`);
* `sourceObstacleEnvelope_contact_measure_eq_of_dim_one`,
  `sourceGeneralizedEnvelope_contact_measure_eq_of_dim_one` (`prop:DNTenvelope3`);
* `roofEnvelope_measure_eq_of_dim_one`, `roofEnvelope_coincideToSecondOrder_of_dim_one`,
  `sourceObstacleEnvelope_coincideToSecondOrder_of_dim_one` (`lma:DNTroof`, all assertions).

`θ_fⁿ` is `DNTC11.c11TopMeasure`, as in the earlier clauses (for `n = 1`, the measure
`(θ + ddᶜf)⁺`, whose density is nonnegative almost everywhere on the contact sets).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg
open SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.DNTC11 SGPT.Analysis.CZ

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel 1) Y]
  [IsComplexManifold 1 Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- **For `n = 1`, `C^{1,1̄}(X)` is the class of bounded complex Hessians**: on a compact connected
Kähler curve, a function has bounded `ω`-Laplacian iff it has bounded complex Hessian. -/
theorem hasBoundedMetricLaplacian_iff_hasBoundedComplexHessian_of_dim_one [ConnectedSpace Y]
    (w : KahlerBackground 1 Y) {f : Y → ℝ} :
    HasBoundedMetricLaplacian w f ↔ HasBoundedComplexHessian (n := 1) f :=
  ⟨fun hf => hf.hasBoundedComplexHessian_of_dim_one w,
    fun hf => HasBoundedComplexHessian.hasBoundedMetricLaplacian w hf⟩

/-! ### `thm:DNTcontact` for `n = 1` -/

/-- **`thm:DNTcontact` for `n = 1`, native form**: `𝟙_E ⟨θ + ddᶜφ⟩ = 𝟙_E (θ + ddᶜf)` on
`E = {φ = f}`, for `φ ∈ PSH(X, θ)` and `f ∈ C^{1,1̄}(X)` with `φ ≤ f`. -/
theorem diagonalPotentialMeasure_restrict_contact_eq_of_dim_one (w : KahlerBackground 1 Y)
    (θ : ClosedRealOneOneForm 1 Y) {u : Y → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (c11TopMeasure w θ f).restrict {x | u x = (f x : EReal)} :=
  diagonalPotentialMeasure_restrict_contact_eq w θ hu (hf.hasBoundedComplexHessian_of_dim_one w)
    hle

/-- **`thm:DNTcontact` for `n = 1`, source form**: for `φ ∈ PSH(X, θ)` (source) and
`f ∈ C^{1,1̄}(X)` with `φ ≤ f`, `𝟙_{φ = f} θ_φ = 𝟙_{φ = f} θ_f`. -/
theorem sourcePotentialNonPluripolarMeasure_restrict_contact_eq_of_dim_one
    (w : KahlerBackground 1 Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel 1 Y)) {u : Y → EReal}
    (hu : (ofFixedModel 1 Y).IsThetaPSH θ u) {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f)
    (hle : ∀ x, u x ≤ (f x : EReal)) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (c11TopMeasure w (atlasClosedFormToNative θ) f).restrict {x | u x = (f x : EReal)} :=
  DNTC11.sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hu
    (hf.hasBoundedComplexHessian_of_dim_one w) hle

/-- **`thm:DNTcontact` for `n = 1`, mixed source form** (the statement with the factor indexed by
`Fin 1`). -/
theorem sourceMixedNonPluripolarMeasure_restrict_mixedContact_toReal_eq_of_dim_one
    (w : KahlerBackground 1 Y) (θ : Fin 1 → AtlasClosedRealOneOneForm (ofFixedModel 1 Y))
    {u : Fin 1 → Y → EReal} (hu : ∀ i, (ofFixedModel 1 Y).IsThetaPSH (θ i) (u i))
    {f : Fin 1 → Y → ℝ} (hf : ∀ i, HasBoundedMetricLaplacian w (f i))
    (hle : ∀ i x, u i x ≤ (f i x : EReal)) {A : Set Y} (hA : MeasurableSet A) :
    ((sourceMixedNonPluripolarMeasure θ u hu).restrict (DNT.mixedContactSet u f) A).toReal =
      c11MixedReal w (fun i => atlasClosedFormToNative (θ i)) f (A ∩ DNT.mixedContactSet u f) :=
  DNTC11.sourceMixedNonPluripolarMeasure_restrict_mixedContact_toReal_eq w θ hu
    (fun i => (hf i).hasBoundedComplexHessian_of_dim_one w) hle hA

variable [ConnectedSpace Y]

/-! ### `cor:DNTenvelope1`, `prop:DNTenvelope2`, `prop:DNTenvelope3` for `n = 1` -/

/-- **`cor:DNTenvelope1` for `n = 1`**: if `PSH(X, θ) ≠ ∅` and `f ∈ C^{1,1̄}(X)`, the source
envelope `P = P_θ(f)` is `θ`-psh and `θ_P = 𝟙_{P = f} θ_f`. -/
theorem sourceObstacleEnvelope_measure_eq_of_dim_one (w : KahlerBackground 1 Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 1 Y))
    (hne : ∃ φ : Y → EReal, (ofFixedModel 1 Y).IsThetaPSH θ φ) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    ∃ hP : (ofFixedModel 1 Y).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP =
        (c11TopMeasure w (atlasClosedFormToNative θ) f).restrict
          {x | sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x = (f x : EReal)} :=
  DNTC11.sourceObstacleEnvelope_measure_eq w θ hne (hf.hasBoundedComplexHessian_of_dim_one w)

/-- **`prop:DNTenvelope2` for `n = 1`**: for `φ ∈ PSH(X, θ)` and `f ∈ C^{1,1̄}(X)` with `φ ≤ f`,
`η = P_θ[φ](f)` is `θ`-psh and `θ_η = 𝟙_{η = f} θ_f`. -/
theorem sourceGeneralizedEnvelope_measure_eq_of_dim_one (w : KahlerBackground 1 Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 1 Y))
    {φ : Y → EReal} (hφ : (ofFixedModel 1 Y).IsThetaPSH θ φ) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel 1 Y).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)) hη =
        (c11TopMeasure w (atlasClosedFormToNative θ) f).restrict
          {x | sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x = (f x : EReal)} :=
  DNTC11.sourceGeneralizedEnvelope_measure_eq w θ hφ (hf.hasBoundedComplexHessian_of_dim_one w) hle

/-- **`prop:DNTenvelope3` for `n = 1`, first equality**: with `P = P_θ(f)`,
`𝟙_{φ = P} θ_P = 𝟙_{φ = P} θ_φ`. -/
theorem sourceObstacleEnvelope_contact_measure_eq_of_dim_one (w : KahlerBackground 1 Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 1 Y))
    {φ : Y → EReal} (hφ : (ofFixedModel 1 Y).IsThetaPSH θ φ) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hP : (ofFixedModel 1 Y).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP).restrict
          {x | φ x = sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x} :=
  DNTC11.sourceObstacleEnvelope_contact_measure_eq w θ hφ (hf.hasBoundedComplexHessian_of_dim_one w)
    hle

/-- **`prop:DNTenvelope3` for `n = 1`, second equality**: with `η = P_θ[φ](f)`,
`𝟙_{φ = η} θ_η = 𝟙_{φ = η} θ_φ`. -/
theorem sourceGeneralizedEnvelope_contact_measure_eq_of_dim_one (w : KahlerBackground 1 Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 1 Y))
    {φ : Y → EReal} (hφ : (ofFixedModel 1 Y).IsThetaPSH θ φ) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel 1 Y).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal))
          hη).restrict {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} :=
  DNTC11.sourceGeneralizedEnvelope_contact_measure_eq w θ hφ
    (hf.hasBoundedComplexHessian_of_dim_one w) hle

/-! ### `lma:DNTroof` for `n = 1` -/

/-- **`lma:DNTroof`, measure assertions, for `n = 1`** (`f₁, f₂ ∈ C^{1,1̄}(X)`,
`P = P_ω(min{f₁, f₂})`): `𝟙_{P = f₁ = f₂} ω_{f₁} = 𝟙_{P = f₁ = f₂} ω_{f₂}`, `eq:DNTroof_Pomega` for
`j = 1, 2` (subtraction-free form) and `ω_P ≥ 𝟙_{P = f_j} ω_{f_j}`. -/
theorem roofEnvelope_measure_eq_of_dim_one (w : KahlerBackground 1 Y) {f₁ f₂ : Y → ℝ}
    (hf₁ : HasBoundedMetricLaplacian w f₁) (hf₂ : HasBoundedMetricLaplacian w f₂) :
    ∃ hP : IsThetaPshPotential w.form.val (DNT.roofEnvelope w f₁ f₂),
      (c11TopMeasure w w.form f₁).restrict
          {x | DNT.roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
            DNT.roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (c11TopMeasure w w.form f₂).restrict
          {x | DNT.roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
            DNT.roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ∧
      (diagonalPotentialMeasure w.form (DNT.roofEnvelope w f₁ f₂) hP +
          (c11TopMeasure w w.form f₁).restrict
            {x | DNT.roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              DNT.roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (c11TopMeasure w w.form f₁).restrict {x | DNT.roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (c11TopMeasure w w.form f₂).restrict
            {x | DNT.roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (diagonalPotentialMeasure w.form (DNT.roofEnvelope w f₁ f₂) hP +
          (c11TopMeasure w w.form f₂).restrict
            {x | DNT.roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              DNT.roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (c11TopMeasure w w.form f₁).restrict {x | DNT.roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (c11TopMeasure w w.form f₂).restrict
            {x | DNT.roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (c11TopMeasure w w.form f₁).restrict {x | DNT.roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} ≤
        diagonalPotentialMeasure w.form (DNT.roofEnvelope w f₁ f₂) hP ∧
      (c11TopMeasure w w.form f₂).restrict {x | DNT.roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ≤
        diagonalPotentialMeasure w.form (DNT.roofEnvelope w f₁ f₂) hP :=
  DNTC11.roofEnvelope_measure_eq w (hf₁.hasBoundedComplexHessian_of_dim_one w)
    (hf₂.hasBoundedComplexHessian_of_dim_one w)

/-- **`lma:DNTroof`, first assertion, for `n = 1`**: for `f₁, f₂ ∈ C^{1,1̄}(X)` and
`P = P_ω(min{f₁, f₂})`, in every chart the three functions pairwise coincide up to second order at
almost every point of `{P = f₁ = f₂}`. -/
theorem roofEnvelope_coincideToSecondOrder_of_dim_one (w : KahlerBackground 1 Y) {f₁ f₂ : Y → ℝ}
    (hf₁ : HasBoundedMetricLaplacian w f₁) (hf₂ : HasBoundedMetricLaplacian w f₂)
    (e : ComplexChart 1 Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target →
      DNT.roofEnvelope w f₁ f₂ (e.val.symm z) = (f₁ (e.val.symm z) : EReal) →
      DNT.roofEnvelope w f₁ f₂ (e.val.symm z) = (f₂ (e.val.symm z) : EReal) →
      CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z))
          (fun z => (DNT.roofEnvelope w f₁ f₂ (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₂ (e.val.symm z))
          (fun z => (DNT.roofEnvelope w f₁ f₂ (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z)) (fun z => f₂ (e.val.symm z)) z :=
  C11Real.roofEnvelope_coincideToSecondOrder w (hf₁.hasBoundedComplexHessian_of_dim_one w)
    (hf₂.hasBoundedComplexHessian_of_dim_one w) e

/-- **`lma:DNTroof`, first assertion, for `n = 1`, source envelope**
`P = sourceRelativeEnvelope ω ⊤ (min{f₁, f₂})` (`def:Pthetaf`). -/
theorem sourceObstacleEnvelope_coincideToSecondOrder_of_dim_one
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 1 Y))
    (hK : (atlasClosedFormToNative θ).val.IsKahler) {f₁ f₂ : Y → ℝ}
    (hf₁ : HasBoundedMetricLaplacian ⟨atlasClosedFormToNative θ, hK⟩ f₁)
    (hf₂ : HasBoundedMetricLaplacian ⟨atlasClosedFormToNative θ, hK⟩ f₂)
    (e : ComplexChart 1 Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target →
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal))
          (e.val.symm z) = (f₁ (e.val.symm z) : EReal) →
      sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal))
          (e.val.symm z) = (f₂ (e.val.symm z) : EReal) →
      CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z))
          (fun z => (sourceRelativeEnvelope θ (fun _ => ⊤)
            (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₂ (e.val.symm z))
          (fun z => (sourceRelativeEnvelope θ (fun _ => ⊤)
            (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z)) (fun z => f₂ (e.val.symm z)) z :=
  C11Real.sourceObstacleEnvelope_coincideToSecondOrder θ hK
    (hf₁.hasBoundedComplexHessian_of_dim_one _) (hf₂.hasBoundedComplexHessian_of_dim_one _) e

end SGPT.Envelopes.LapClass

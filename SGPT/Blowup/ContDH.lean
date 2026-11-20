import SGPT.Blowup.PointBlowupFlag
import SGPT.NAPotential.DHSourceModificationContinuity

/-!
# The Duistermaat–Heckman measure on an arbitrary compact Kähler manifold

Source `chapter_NApotential.tex`, `eq:DHmgeneral` and `prop:contDH`.  When `X` admits no smooth
flag, the book chooses a modification `π : Y → X` such that `Y` admits a flag and sets
`DH(Γ) = DH(π^*Γ)`; by `thm:pobmain` (5) this does not depend on `π`.

Here the modification is produced, not assumed: `SGPT.Blowup.exists_flagBearingModification`
blows up a point of `X` and equips the blow-up with a Kähler form and its linear flag (in
dimension zero `Y = X`).  `naDuistermaatHeckmanGeneral` is the literal `eq:DHmgeneral` on this
chosen model, `naDuistermaatHeckmanGeneral_eq_onModification` shows that every other
flag-bearing analytic modification gives the same measure, and
`naDuistermaatHeckmanGeneral_tendsto_of_order_infimum` / `_supremum` are the two cases of
`prop:contDH` for an arbitrary connected compact Kähler `X`, with no flag or modification
hypothesis.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Blowup

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov SGPT.NAPotential

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]

/-- The chosen flag-bearing modification of `X` (the blow-up of a point with its linear flag in
positive dimension). -/
def flagModel (omega : KahlerBackground n X) : OriginalFlagGeometry.{u} n :=
  (exists_flagBearingModification omega).choose

/-- The projection of the chosen flag-bearing modification. -/
def flagModelProj (omega : KahlerBackground n X) : (flagModel omega).carrier → X :=
  (exists_flagBearingModification omega).choose_spec.choose

theorem isAnalyticModification_flagModelProj (omega : KahlerBackground n X) :
    IsAnalyticModification (n := n) (flagModelProj omega) :=
  (exists_flagBearingModification omega).choose_spec.choose_spec

/-- The Borel structure of the chosen model. -/
instance flagModelMeasurableSpace (omega : KahlerBackground n X) :
    MeasurableSpace (flagModel omega).carrier :=
  borel _

instance flagModelBorelSpace (omega : KahlerBackground n X) :
    BorelSpace (flagModel omega).carrier :=
  ⟨rfl⟩

variable [MeasurableSpace X] [BorelSpace X] {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

/-- **Source `eq:DHmgeneral`**: the Duistermaat–Heckman measure of a positive-mass `𝓘`-model
test curve `Γ` on an arbitrary connected compact Kähler manifold `X`, defined as the flag
measure `DH(π^*Γ)` on the chosen flag-bearing modification `π : Y → X`. -/
def naDuistermaatHeckmanGeneral (omega : KahlerBackground n X)
    (Γ : SourcePositiveIModelTestCurve θ) : Measure ℝ :=
  DHSource.naDuistermaatHeckmanOnModification (flagModel omega)
    (isAnalyticModification_flagModelProj omega) Γ

instance naDuistermaatHeckmanGeneral_finite (omega : KahlerBackground n X)
    (Γ : SourcePositiveIModelTestCurve θ) :
    IsFiniteMeasure (naDuistermaatHeckmanGeneral omega Γ) := by
  unfold naDuistermaatHeckmanGeneral
  infer_instance

/-- **Independence of the model** (`eq:DHmgeneral`, via `thm:pobmain` (5)): every flag-bearing
analytic modification of `X` gives the same measure. -/
theorem naDuistermaatHeckmanGeneral_eq_onModification (omega : KahlerBackground n X)
    (F : OriginalFlagGeometry.{u} n) [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {π : F.carrier → X} (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckmanGeneral omega Γ = DHSource.naDuistermaatHeckmanOnModification F hπ Γ :=
  DHSource.naDuistermaatHeckmanOnModification_independent omega _ hπ Γ

/-- The measure does not depend on the Kähler form used to choose the model. -/
theorem naDuistermaatHeckmanGeneral_kahler_independent (omega omega' : KahlerBackground n X)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckmanGeneral omega Γ = naDuistermaatHeckmanGeneral omega' Γ :=
  naDuistermaatHeckmanGeneral_eq_onModification omega _ _ Γ

/-- The general measure agrees with the intrinsic slice-mass measure. -/
theorem naDuistermaatHeckmanGeneral_eq_intrinsic (omega : KahlerBackground n X)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckmanGeneral omega Γ = DH.naIntrinsicDuistermaatHeckman omega Γ :=
  DHSource.naDuistermaatHeckmanOnModification_eq_intrinsic _ omega _ Γ

/-- `eq:DHmgeneral` as a finite measure. -/
def naFiniteDuistermaatHeckmanGeneral (omega : KahlerBackground n X)
    (Γ : SourcePositiveIModelTestCurve θ) : FiniteMeasure ℝ :=
  ⟨naDuistermaatHeckmanGeneral omega Γ, naDuistermaatHeckmanGeneral_finite omega Γ⟩

theorem naFiniteDuistermaatHeckmanGeneral_eq_onModification (omega : KahlerBackground n X)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naFiniteDuistermaatHeckmanGeneral omega Γ =
      DHSource.naFiniteDuistermaatHeckmanOnModification (flagModel omega)
        (isAnalyticModification_flagModelProj omega) Γ :=
  rfl

/-- **Source `prop:contDH` (1)** on an arbitrary connected compact Kähler `X`: for a decreasing
sequence `Γ^i` with infimum `Γ` and `vol Γ = lim vol Γ^i`, `DH(Γ^i) ⇀ DH(Γ)`. -/
theorem naDuistermaatHeckmanGeneral_tendsto_of_order_infimum (omega : KahlerBackground n X)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j))
      (sourcePositiveTestCurveToNA (Γs i)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA Γ)
      (sourcePositiveTestCurveToNA (Γs i)))
    (hgreatest : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder Ξ (sourcePositiveTestCurveToNA (Γs i))) →
      SourceNAPOrder Ξ (sourcePositiveTestCurveToNA Γ))
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ)))) :
    Tendsto (fun i => naFiniteDuistermaatHeckmanGeneral omega (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckmanGeneral omega Γ)) :=
  DHSource.naDuistermaatHeckmanOnModification_tendsto_of_order_infimum (flagModel omega) omega
    (isAnalyticModification_flagModelProj omega) Γs Γ ha hbound hgreatest hvol

/-- **Source `prop:contDH` (2)** on an arbitrary connected compact Kähler `X`: for an increasing
sequence `Γ^i` with `Γ = usc-sup Γ^i`, `DH(Γ^i) ⇀ DH(Γ)`. -/
theorem naDuistermaatHeckmanGeneral_tendsto_of_order_supremum (omega : KahlerBackground n X)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA (Γs j)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ))
    (hleast : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) Ξ) →
      SourceNAPOrder (sourcePositiveTestCurveToNA Γ) Ξ) :
    Tendsto (fun i => naFiniteDuistermaatHeckmanGeneral omega (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckmanGeneral omega Γ)) :=
  DHSource.naDuistermaatHeckmanOnModification_tendsto_of_order_supremum (flagModel omega) omega
    (isAnalyticModification_flagModelProj omega) Γs Γ hmono hbound hleast

end SGPT.Blowup

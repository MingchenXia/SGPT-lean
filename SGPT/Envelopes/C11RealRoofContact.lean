import SGPT.Analysis.CZContact
import SGPT.Envelopes.DNTRegQuasiPsh
import SGPT.Envelopes.DNTEnvelopes
import SGPT.Envelopes.SourceObstacleConcentration

/-!
# `lma:DNTroof`: second-order coincidence on the contact set

Lane C11-REAL (`claude-c11-real`, node `c11r:dntroof-second-order`).  Source:
`references/sgpt-d3f272c3/source/author/chapter_npp.tex`, `lma:DNTroof`, first assertion:

> Assume that `ω` is a Kähler form on `X` and let `f₁, f₂ ∈ C^{1,1̄}(X)`.  Then the functions
> `f₁`, `f₂` and `P_ω(min{f₁, f₂})` coincide up to second order at almost every point of the
> contact set `{P_ω(min{f₁, f₂}) = f₁ = f₂}`.

The measure assertions of the lemma (the "in particular" and `eq:DNTroof_Pomega`) are proved by
lane NPP-DNT (`SGPT.Envelopes.DNT.roofEnvelope_measure_eq`,
`SGPT.Envelopes.DNTC11.roofEnvelope_measure_eq`) for obstacles with bounded complex Hessian; this
file proves the remaining **first assertion** for the same class.

* `IsCOneOneBar.hasLocallyBoundedLeviTraceOn` — a `C^{1,1̄}` function (WN-REG's `IsCOneOneBar`:
  continuous, with locally bounded distributional complex Hessian in every chart) has locally
  bounded Laplacian in every chart.
* `roofEnvelope_coincideToSecondOrder_left/right` — the book's Step 1 claim for
  `Ψ₁ = φ - f₁` and `Ψ₂ = φ - f₂`: in every holomorphic chart, at almost every point of
  `{P_ω(min{f₁,f₂}) = fᵢ}`, `fᵢ` and the envelope coincide up to second order.
* `roofEnvelope_coincideToSecondOrder` — **the first assertion of `lma:DNTroof`** (native
  envelope `DNT.roofEnvelope`, equal to the source envelope of `def:Pthetaf`):
  in every chart, at almost every point of `{P = f₁ = f₂}` the three functions pairwise coincide
  up to second order.
* `sourceObstacleEnvelope_coincideToSecondOrder` — the same for the source envelope
  `sourceRelativeEnvelope ω ⊤ (min{f₁, f₂})` of `def:Pthetaf`.

"Almost every point" of the manifold is read in charts: Lebesgue-almost every point of every
chart target (this is chart-independent, since holomorphic transition maps preserve Lebesgue
null sets).  "Coincide up to second order at `x`" is `CoincideToSecondOrderAt`: equal values and
`fᵢ(x + h) - fⱼ(x + h) = o(|h|²)` in the chart, so that one function has a second-order Taylor
expansion at `x` exactly when the other has, with the same coefficients
(`CoincideToSecondOrderAt.hasPeanoExpansionAt`).

The class of obstacles is `HasBoundedComplexHessian` (continuous, with a locally bounded density of
the distributional complex Hessian in every chart; `C^{1,1̄} ∩ QPSH`), the class for which the
envelope is known to be `C^{1,1̄}` (`prop:DR16_C11bar`, lane NPP-DNT).  For obstacles with bounded
metric Laplacian but unbounded complex Hessian (possible when `n ≥ 2`) the regularity of the
envelope is still open in the library; given it, `SGPT.Analysis.CZ.ae_coincideToSecondOrderAt_of_le`
applies verbatim to any obstacle with locally bounded flat Laplacian in charts.

## Proof

`P ≤ fᵢ`, both are continuous with locally bounded Laplacian in every chart (`P` is `C^{1,1̄}` by
NPP-DNT's `isCOneOneBar_envelopeReal_min_of_hasBoundedComplexHessian`), so the second-order contact
theorem `SGPT.Analysis.CZ.ae_coincideToSecondOrderAt_of_le` (mean-value inequalities and Lebesgue
density points; no `W^{2,1}` theory or Stampacchia lemma) applies to `(P, fᵢ)` on each chart target.
On `{P = f₁ = f₂}` the two statements combine by transitivity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Envelopes.C11Real

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.TranscendentalWNReg
open SGPT.Envelopes.DNTC11 SGPT.Envelopes.DNTReg
open SGPT.Analysis.CZ

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]

/-- A `C^{1,1̄}` function has locally bounded Laplacian in every holomorphic chart. -/
theorem IsCOneOneBar.hasLocallyBoundedLeviTraceOn {f : Y → ℝ} (hf : IsCOneOneBar (N := N) f)
    (e : ComplexChart N Y) :
    HasLocallyBoundedLeviTraceOn (fun z => f (e.val.symm z)) e.val.target :=
  hasLocallyBoundedLeviTraceOn_of_complexHessian e.val.open_target
    (hf.1.comp_continuousOn e.val.continuousOn_symm) (hf.2 e)

/-- **Second-order contact for `C^{1,1̄}` functions on a manifold.**  If `u ≤ f` are `C^{1,1̄}`,
then in every holomorphic chart `u` and `f` coincide up to second order at almost every point of
the contact set `{u = f}`. -/
theorem ae_coincideToSecondOrderAt_of_isCOneOneBar {u f : Y → ℝ} (hu : IsCOneOneBar (N := N) u)
    (hf : IsCOneOneBar (N := N) f) (hle : ∀ x, u x ≤ f x) (e : ComplexChart N Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target → u (e.val.symm z) = f (e.val.symm z) →
      CoincideToSecondOrderAt (fun z => f (e.val.symm z)) (fun z => u (e.val.symm z)) z :=
  ae_coincideToSecondOrderAt_of_le e.val.open_target
    (hu.1.comp_continuousOn e.val.continuousOn_symm) (hf.1.comp_continuousOn e.val.continuousOn_symm)
    (fun _ _ => hle _) (IsCOneOneBar.hasLocallyBoundedLeviTraceOn hu e)
    (IsCOneOneBar.hasLocallyBoundedLeviTraceOn hf e)

variable [IsComplexManifold N Y]

section Roof

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- The envelope `P_ω(min{f₁, f₂})` is real-valued. -/
theorem roofEnvelope_eq_coe (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedComplexHessian (n := N) f₁) (h₂ : HasBoundedComplexHessian (n := N) f₂)
    (x : Y) :
    DNT.roofEnvelope A f₁ f₂ x = ((DNT.roofEnvelope A f₁ f₂ x).toReal : EReal) := by
  have h : DNT.roofEnvelope A f₁ f₂ x = _ :=
    (isCOneOneBar_envelopeReal_min_of_hasBoundedComplexHessian A h₁ h₂).1 x
  rw [h, EReal.toReal_coe]

/-- The real envelope `x ↦ (P_ω(min{f₁, f₂}) x).toReal` is `C^{1,1̄}` and lies below `f₁`, `f₂`. -/
theorem roofEnvelope_toReal_props (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedComplexHessian (n := N) f₁) (h₂ : HasBoundedComplexHessian (n := N) f₂) :
    IsCOneOneBar (N := N) (fun x => (DNT.roofEnvelope A f₁ f₂ x).toReal) ∧
      (∀ x, (DNT.roofEnvelope A f₁ f₂ x).toReal ≤ f₁ x) ∧
      ∀ x, (DNT.roofEnvelope A f₁ f₂ x).toReal ≤ f₂ x := by
  obtain ⟨hreal, hC⟩ := isCOneOneBar_envelopeReal_min_of_hasBoundedComplexHessian A h₁ h₂
  have heq : (fun x => (DNT.roofEnvelope A f₁ f₂ x).toReal) =
      envelopeReal A.form (fun y => min (f₁ y) (f₂ y)) := by
    funext x
    change (rooftopEnvelope A.form.val (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x).toReal = _
    rw [hreal x, EReal.toReal_coe]
  obtain ⟨_, hle₁, hle₂⟩ := DNT.roofEnvelope_genuine A h₁.1 h₂.1
  refine ⟨heq ▸ hC, fun x => ?_, fun x => ?_⟩
  · have := hle₁ x
    rw [roofEnvelope_eq_coe A h₁ h₂ x] at this
    exact EReal.coe_le_coe_iff.mp this
  · have := hle₂ x
    rw [roofEnvelope_eq_coe A h₁ h₂ x] at this
    exact EReal.coe_le_coe_iff.mp this

/-- **Step 1 of `lma:DNTroof` for `Ψ₁ = φ - f₁`**: in every chart, `f₁` and
`φ = P_ω(min{f₁, f₂})` coincide up to second order at almost every point of `{φ = f₁}`. -/
theorem roofEnvelope_coincideToSecondOrder_left (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedComplexHessian (n := N) f₁) (h₂ : HasBoundedComplexHessian (n := N) f₂)
    (e : ComplexChart N Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target →
      DNT.roofEnvelope A f₁ f₂ (e.val.symm z) = (f₁ (e.val.symm z) : EReal) →
      CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z))
        (fun z => (DNT.roofEnvelope A f₁ f₂ (e.val.symm z)).toReal) z := by
  obtain ⟨hP, hle₁, _⟩ := roofEnvelope_toReal_props A h₁ h₂
  filter_upwards [ae_coincideToSecondOrderAt_of_isCOneOneBar hP h₁.isCOneOneBar hle₁ e]
    with z hz hzt hc
  exact hz hzt (by rw [hc, EReal.toReal_coe])

/-- **Step 1 of `lma:DNTroof` for `Ψ₂ = φ - f₂`**: in every chart, `f₂` and
`φ = P_ω(min{f₁, f₂})` coincide up to second order at almost every point of `{φ = f₂}`. -/
theorem roofEnvelope_coincideToSecondOrder_right (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedComplexHessian (n := N) f₁) (h₂ : HasBoundedComplexHessian (n := N) f₂)
    (e : ComplexChart N Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target →
      DNT.roofEnvelope A f₁ f₂ (e.val.symm z) = (f₂ (e.val.symm z) : EReal) →
      CoincideToSecondOrderAt (fun z => f₂ (e.val.symm z))
        (fun z => (DNT.roofEnvelope A f₁ f₂ (e.val.symm z)).toReal) z := by
  obtain ⟨hP, _, hle₂⟩ := roofEnvelope_toReal_props A h₁ h₂
  filter_upwards [ae_coincideToSecondOrderAt_of_isCOneOneBar hP h₂.isCOneOneBar hle₂ e]
    with z hz hzt hc
  exact hz hzt (by rw [hc, EReal.toReal_coe])

/-- **Source `lma:DNTroof`, first assertion** (obstacles with bounded complex Hessian): for a
Kähler form `ω` on a compact connected complex manifold and `f₁, f₂` with bounded complex Hessian,
in every holomorphic chart the functions `f₁`, `f₂` and `P_ω(min{f₁, f₂})` (`DNT.roofEnvelope`)
pairwise coincide up to second order at almost every point of the contact set
`{P_ω(min{f₁, f₂}) = f₁ = f₂}`. -/
theorem roofEnvelope_coincideToSecondOrder (A : KahlerBackground N Y) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedComplexHessian (n := N) f₁) (h₂ : HasBoundedComplexHessian (n := N) f₂)
    (e : ComplexChart N Y) :
    ∀ᵐ z ∂volume, z ∈ e.val.target →
      DNT.roofEnvelope A f₁ f₂ (e.val.symm z) = (f₁ (e.val.symm z) : EReal) →
      DNT.roofEnvelope A f₁ f₂ (e.val.symm z) = (f₂ (e.val.symm z) : EReal) →
      CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z))
          (fun z => (DNT.roofEnvelope A f₁ f₂ (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₂ (e.val.symm z))
          (fun z => (DNT.roofEnvelope A f₁ f₂ (e.val.symm z)).toReal) z ∧
        CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z)) (fun z => f₂ (e.val.symm z)) z := by
  filter_upwards [roofEnvelope_coincideToSecondOrder_left A h₁ h₂ e,
    roofEnvelope_coincideToSecondOrder_right A h₁ h₂ e] with z hz₁ hz₂ hzt hc₁ hc₂
  have c₁ := hz₁ hzt hc₁
  have c₂ := hz₂ hzt hc₂
  exact ⟨c₁, c₂, c₁.trans c₂.symm⟩

end Roof

section Source

open SGPT.PSH.VariableComplexAtlas

variable [CompactSpace Y] [ConnectedSpace Y]

/-- **Source `lma:DNTroof`, first assertion, source envelope** (obstacles with bounded complex
Hessian): for an atlas form `ω` that is Kähler and `f₁, f₂` with bounded complex Hessian, with
`P = P_ω(min{f₁, f₂})` the source envelope `sourceRelativeEnvelope ω ⊤ (min{f₁, f₂})` of
`def:Pthetaf`, in every chart the functions `f₁`, `f₂` and `P` pairwise coincide up to second order
at almost every point of `{P = f₁ = f₂}`. -/
theorem sourceObstacleEnvelope_coincideToSecondOrder
    (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hK : (atlasClosedFormToNative θ).val.IsKahler) {f₁ f₂ : Y → ℝ}
    (h₁ : HasBoundedComplexHessian (n := N) f₁) (h₂ : HasBoundedComplexHessian (n := N) f₂)
    (e : ComplexChart N Y) :
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
        CoincideToSecondOrderAt (fun z => f₁ (e.val.symm z)) (fun z => f₂ (e.val.symm z)) z := by
  let _ : MeasurableSpace Y := borel Y
  have _ : BorelSpace Y := ⟨rfl⟩
  have hsrc : ∀ x, sourceRelativeEnvelope θ (fun _ => ⊤)
      (fun y => ((min (f₁ y) (f₂ y) : ℝ) : EReal)) x =
        DNT.roofEnvelope ⟨atlasClosedFormToNative θ, hK⟩ f₁ f₂ x := by
    intro x
    rw [sourceObstacleEnvelope_eq_native]
    rfl
  simp only [hsrc]
  exact roofEnvelope_coincideToSecondOrder ⟨atlasClosedFormToNative θ, hK⟩ h₁ h₂ e

end Source

end SGPT.Envelopes.C11Real

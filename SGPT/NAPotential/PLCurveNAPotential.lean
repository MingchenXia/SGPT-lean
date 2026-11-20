import SGPT.NAPotential.WholePiecewiseLinearHull
import SGPT.NAPotential.Homogeneous
import SGPT.PSH.SourceIEnvelopeMonotonicity
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling
import SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

/-! # The non-Archimedean metric of the regularized concave envelope of a piecewise linear curve

Source `lma:psieqpsiprimeondiv` (`chapter_NApotential.tex`, Section *The transcendental
setting*), first assertion: let `A` be a piecewise linear curve in `PSH(X, θ)` with data
`A_0, …, A_N`, `τ_0 > ⋯ > τ_N` (`def:piecewiselincurv`), and let `A'` be its regularized concave
envelope (`rmk:pwlinhull`: the pointwise upper concave envelope of `τ ↦ A_τ`, followed by upper
semicontinuous regularization in `X`).  Define `Ã` by
`Ã^{θ+ω}_τ := P_{θ+ω}[A'_τ]_𝓘` for `ω ∈ Kah(X)` and `τ < τ_0`.  Then `Ã ∈ PSH^NA(X, θ)`, and
(from the proof) `Ã_max = τ_0`.

## Proof

By `rmk:pwlinhull` (`SimplexRevision.WholeHull.source_pwlinhull_whole`) `A'_τ` is the finite
simplex maximum `B_τ = max_{λ ∈ Λ_τ} ∑ λ_i A_i`, which is `θ`-psh, decreasing and concave in `τ`.
For every Kähler index `ω` the slices `P_{θ+ω}[B_τ]_𝓘`:

* are `(θ+ω)`-psh and `𝓘`-model, with mass at least `∫ ω^n > 0`
  (`sourceNA_iEnvelope_component_mass_pos`); hence they are `𝓘`-good and model;
* decrease in `τ` (`lma:PIenvmono1`);
* are concave in `τ`: a convex combination of two slices is `𝓘`-below the corresponding convex
  combination of the `B_τ`, which lies below `B` at the combined parameter, so it lies below the
  `𝓘`-envelope there.

The cocycle property of the `𝓘`-projection gives the compatibility of the components.

## Main results

* `PiecewiseLinearData.hullNAComponent`: the component `τ ↦ P_{θ+ω}[A'_τ]_𝓘`, a positive
  `𝓘`-model test curve in `θ + ω` with cutoff `τ_0`.
* `PiecewiseLinearData.hullNAPotential`: the element `Ã ∈ PSH^NA(X, θ)`.
* `PiecewiseLinearData.hullNAPotential_component_potential`: its slices are
  `P_{θ+ω}[A'_τ]_𝓘`, with `A'_τ` the literal regularized concave envelope
  `uscRegularization (D.pointwiseUpperConcaveEnvelope τ)`.
* `PiecewiseLinearData.hullNAPotential_max`, `hullNAPotential_unique`, and
  `PiecewiseLinearData.source_psieqpsiprimeondiv_mem`: source `lma:psieqpsiprimeondiv`, first
  assertion (`Ã ∈ PSH^NA(X, θ)` exists and is unique with the given components, `Ã_max = τ_0`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas
open SimplexRevision SimplexRevision.WholeHull

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-! ### Chords of the simplex maximum and of `𝓘`-envelopes -/

/-- The chord inequality for the simplex maximum `B_τ` of `rmk:pwlinhull`:
`t B_p + (1-t) B_q ≤ B_{tp + (1-t)q}` pointwise, for `p, q ≤ τ_0`. -/
theorem simplexValue_chord (D : PiecewiseLinearData θ) {p q : ℝ} (hp : p ≤ D.τ 0)
    (hq : q ≤ D.τ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (x : M) :
    convexComb t (simplexValue D p) (simplexValue D q) x ≤
      simplexValue D (t * p + (1 - t) * q) x := by
  obtain ⟨w, hw, hwx⟩ := simplexValue_attained_feasible D p hp x
  obtain ⟨v, hv, hvx⟩ := simplexValue_attained_feasible D q hq x
  have ht1' : 0 ≤ 1 - t := (sub_pos.mpr ht1).le
  rw [convexComb_apply, hwx, hvx, ← weightedValue_mixedWeights D x t (1 - t) w v ht0.le ht1'
    (fun i => (hw.1 i).1) (fun i => (hv.1 i).1)]
  exact le_iSup_of_le (mixedWeights t (1 - t) w v)
    (le_iSup_of_le (mixedWeights_mem D hw hv ht0.le ht1' (by ring)) le_rfl)

private theorem thetaPSH_convexComb {α : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH α u) (hv : (ofFixedModel n M).IsThetaPSH α v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (ofFixedModel n M).IsThetaPSH α (convexComb t u v) :=
  (isThetaPSH_iff_nativeThetaPotential α _).mpr
    (isThetaPshPotential_convexComb ((isThetaPSH_iff_nativeThetaPotential α u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential α v).mp hv) ht0 ht1)

/-- The `𝓘`-order is compatible with convex combinations of potentials in one class. -/
theorem sourceIOrder_convexComb' {α : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u v φ ψ : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH α u) (hv : (ofFixedModel n M).IsThetaPSH α v)
    (hφ : (ofFixedModel n M).IsThetaPSH α φ) (hψ : (ofFixedModel n M).IsThetaPSH α ψ)
    (huφ : sourceIOrder (ofFixedModel n M) u φ) (hvψ : sourceIOrder (ofFixedModel n M) v ψ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    sourceIOrder (ofFixedModel n M) (convexComb t u v) (convexComb t φ ψ) := by
  have hun := (isThetaPSH_iff_nativeThetaPotential α u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential α v).mp hv
  have hφn := (isThetaPSH_iff_nativeThetaPotential α φ).mp hφ
  have hψn := (isThetaPSH_iff_nativeThetaPotential α ψ).mp hψ
  have hIu := (sourceIOrder_iff_native ⟨α, hu⟩ ⟨α, hφ⟩).mp huφ
  have hIv := (sourceIOrder_iff_native ⟨α, hv⟩ ⟨α, hψ⟩).mp hvψ
  apply (sourceIOrder_iff_native ⟨α, thetaPSH_convexComb hu hv ht0 ht1⟩
    ⟨α, thetaPSH_convexComb hφ hψ ht0 ht1⟩).mpr
  exact ActualMultiplierOrderAddition.iOrderOnManifold_add
    (RestrictedApproximantComparison.isThetaPshPotential_smul hun ht0)
    (RestrictedApproximantComparison.isThetaPshPotential_smul hvn (sub_pos.mpr ht1))
    (RestrictedApproximantComparison.isThetaPshPotential_smul hφn ht0)
    (RestrictedApproximantComparison.isThetaPshPotential_smul hψn (sub_pos.mpr ht1))
    (ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hIu ht0)
    (ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hIv (sub_pos.mpr ht1))

/-- A pointwise inequality between `α`-psh functions gives the `𝓘`-order. -/
theorem sourceIOrder_of_le {α : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH α u) (hv : (ofFixedModel n M).IsThetaPSH α v)
    (huv : u ≤ v) : sourceIOrder (ofFixedModel n M) u v := by
  apply (sourceIOrder_iff_native ⟨α, hu⟩ ⟨α, hv⟩).mpr
  exact iOrderOnManifold_of_le_add (C := 0)
    ((isThetaPSH_iff_nativeThetaPotential α v).mp hv).1.quasiPlurisubharmonic
    (fun x => by simpa only [EReal.coe_zero, add_zero] using huv x)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
private theorem convexComb_nonpos {u v : M → EReal} (hu : u ≤ 0) (hv : v ≤ 0) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : convexComb t u v ≤ 0 := by
  intro x
  rw [convexComb_apply]
  have hux : u x ≤ 0 := hu x
  have hvx : v x ≤ 0 := hv x
  have h1 : (t : EReal) * u x ≤ 0 := by
    simpa only [mul_zero] using
      mul_le_mul_of_nonneg_left hux (EReal.coe_nonneg.mpr ht0.le)
  have h2 : ((1 - t : ℝ) : EReal) * v x ≤ 0 := by
    simpa only [mul_zero] using
      mul_le_mul_of_nonneg_left hvx (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le)
  simpa only [add_zero, Pi.zero_apply] using add_le_add h1 h2

variable [CompactSpace M] [Nonempty M]

/-- The `𝓘`-envelope of a curve with concave chords has concave chords: if
`t φ + (1-t) ψ ≤ χ` for `α`-psh `φ, ψ, χ`, then
`t P_α[φ]_𝓘 + (1-t) P_α[ψ]_𝓘 ≤ P_α[χ]_𝓘`. -/
theorem convexComb_sourceIEnvelope_le {α : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {φ ψ χ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH α φ) (hψ : (ofFixedModel n M).IsThetaPSH α ψ)
    (hχ : (ofFixedModel n M).IsThetaPSH α χ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hchord : convexComb t φ ψ ≤ χ) :
    convexComb t (sourceIEnvelope α φ) (sourceIEnvelope α ψ) ≤ sourceIEnvelope α χ := by
  have hu := isThetaPSH_sourceIEnvelope hφ
  have hv := isThetaPSH_sourceIEnvelope hψ
  have hw := thetaPSH_convexComb hu hv ht0 ht1
  have hcomb : sourceIOrder (ofFixedModel n M)
      (convexComb t (sourceIEnvelope α φ) (sourceIEnvelope α ψ)) (convexComb t φ ψ) :=
    sourceIOrder_convexComb' hu hv hφ hψ (sourceIEquivalent_iEnvelope hφ).2
      (sourceIEquivalent_iEnvelope hψ).2 ht0 ht1
  have hI : sourceIOrder (ofFixedModel n M)
      (convexComb t (sourceIEnvelope α φ) (sourceIEnvelope α ψ)) χ :=
    sourceIOrder_trans hcomb
      (sourceIOrder_of_le (thetaPSH_convexComb hφ hψ ht0 ht1) hχ hchord)
  have h0 : convexComb t (sourceIEnvelope α φ) (sourceIEnvelope α ψ) ≤ 0 :=
    convexComb_nonpos (sourceIEnvelope_le_zero α φ) (sourceIEnvelope_le_zero α ψ) ht0 ht1
  exact (le_sourceIEnvelope hw h0 (sourceIEquivalent_refl ⟨α, hw⟩)).trans
    ((sourceIOrder_iff_sourceIEnvelope_le hw hχ).mp hI)

/-! ### The components `τ ↦ P_{θ+ω}[A'_τ]_𝓘` -/

variable [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

omit [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- `A'_τ = B_τ` is `(θ+ω)`-psh for `τ ≤ τ_0`. -/
theorem simplexValue_componentPSH (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M)
    {s : ℝ} (hs : s ≤ D.τ 0) :
    (ofFixedModel n M).IsThetaPSH (sourceNAComponentBackground θ κ) (simplexValue D s) :=
  sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ κ)
    (isThetaPSH_simplexValue D s hs)

/-- The preliminary test-curve data of the component `τ ↦ P_{θ+ω}[A'_τ]_𝓘`, `τ < τ_0`. -/
def hullNAComponentPredata (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) :
    SourceTestCurvePredata (sourceNAComponentBackground θ κ) where
  max := D.τ 0
  potential τ := sourceIEnvelope (sourceNAComponentBackground θ κ) (simplexValue D τ)
  thetaPSH τ := isThetaPSH_sourceIEnvelope (simplexValue_componentPSH D κ τ.2.le)
  antitone x := by
    intro p q hpq
    have hle : simplexValue D q ≤ simplexValue D p := fun y => simplexValue_antitone D y hpq
    exact sourceIEnvelope_mono_of_singularityLE (simplexValue_componentPSH D κ q.2.le)
      (simplexValue_componentPSH D κ p.2.le)
      ((SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
        ⟨0, fun y => by simpa only [EReal.coe_zero, add_zero] using hle y⟩) x
  concave x := by
    apply sourceTestCurveNegativeTrace_convex_of_chords _ _ x
    intro p q t ht0 ht1
    have hmid : t * p.1 + (1 - t) * q.1 ≤ D.τ 0 := by
      nlinarith [mul_pos ht0 (sub_pos.mpr p.2), mul_pos (sub_pos.mpr ht1) (sub_pos.mpr q.2)]
    exact convexComb_sourceIEnvelope_le (simplexValue_componentPSH D κ p.2.le)
      (simplexValue_componentPSH D κ q.2.le) (simplexValue_componentPSH D κ hmid) ht0 ht1
      (fun y => simplexValue_chord D p.2.le q.2.le ht0 ht1 y)
  fixedPoint τ := by
    have hB := isThetaPSH_simplexValue D τ τ.2.le
    have hu := sourceIEnvelope_isIModel (simplexValue_componentPSH D κ τ.2.le)
    have hpos := sourceNA_iEnvelope_component_mass_pos hB κ
    have hg := (sourceIModel_positive_iGood _ _ hu hpos).2
    rw [(sourceIGood_iff_PI_eq (sourceKahlerFormRepresentative κ) hu.1 hpos).mp hg]
    exact hu.2.symm

theorem hullNAComponentPredata_max (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) :
    (hullNAComponentPredata D κ).max = D.τ 0 := rfl

theorem hullNAComponentPredata_potential (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M)
    (τ : Iio (hullNAComponentPredata D κ).max) :
    (hullNAComponentPredata D κ).potential τ =
      sourceIEnvelope (sourceNAComponentBackground θ κ) (simplexValue D τ) := rfl

/-- The component of `Ã` at a Kähler index, as an actual test curve: the limit has positive
mass since it dominates every slice, whose mass is at least `∫ ω^n`. -/
def hullNAComponentCurve (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) :
    SourceTestCurve (sourceNAComponentBackground θ κ) where
  toSourceTestCurvePredata := hullNAComponentPredata D κ
  positiveLimitMass := by
    let p : Iio (hullNAComponentPredata D κ).max :=
      ⟨D.τ 0 - 1, by change D.τ 0 - 1 < D.τ 0; linarith⟩
    have hB := isThetaPSH_simplexValue D p p.2.le
    have hpos := sourceNA_iEnvelope_component_mass_pos hB κ
    refine hpos.trans_le (sourcePotentialNonPluripolarMass_mono (sourceKahlerFormRepresentative κ)
      _ _ ((SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨0, fun y => ?_⟩))
    rw [EReal.coe_zero, add_zero]
    exact (le_iSup (fun j => (hullNAComponentPredata D κ).potential j y) p).trans
      (le_uscRegularization (fun z => ⨆ j, (hullNAComponentPredata D κ).potential j z) y)

/-- The component is a positive `𝓘`-model test curve. -/
theorem hullNAComponentCurve_mem (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) :
    hullNAComponentCurve D κ ∈ SourceIModelTestCurvesPositive (sourceNAComponentBackground θ κ) :=
  (sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative κ) _).mpr
    fun τ => (sourceIModel_iff_native _ _).mp
      (sourceIEnvelope_isIModel (simplexValue_componentPSH D κ τ.2.le))

/-- The component of `Ã` at the Kähler index `ω`: `τ ↦ P_{θ+ω}[A'_τ]_𝓘`, `τ < τ_0`. -/
def hullNAComponent (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) :
    SourcePositiveIModelTestCurve (sourceNAComponentBackground θ κ) :=
  ⟨hullNAComponentCurve D κ, hullNAComponentCurve_mem D κ⟩

theorem hullNAComponent_max (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) :
    (hullNAComponent D κ).val.max = D.τ 0 := rfl

theorem hullNAComponent_potential (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M)
    (τ : Iio (hullNAComponent D κ).val.max) :
    (hullNAComponent D κ).val.potential τ =
      sourceIEnvelope (sourceNAComponentBackground θ κ) (simplexValue D τ) := rfl

/-- The element `Ã ∈ PSH^NA(X, θ)` of `lma:psieqpsiprimeondiv`. -/
def hullNAPotential (D : PiecewiseLinearData θ) : SourceNAPotential θ where
  component κ := hullNAComponent D κ
  compatible κ ζ h := by
    apply Subtype.ext
    apply SourceTestCurve.ext_of_max_potential
    · rw [sourceIModelTestCurveTransition_max, hullNAComponent_max, hullNAComponent_max]
    · intro r hr hs
      have hr' : r < (hullNAComponent D κ).val.max := by
        rw [sourceIModelTestCurveTransition_max] at hr
        exact hr
      have e1 := sourceIModelTestCurveTransition_potential (sourceKahlerFormRepresentative ζ)
        (sourceNAComponentBackground_difference θ h) (hullNAComponent D κ) r hr' hr
      have e2 := hullNAComponent_potential D κ ⟨r, hr'⟩
      have e3 := hullNAComponent_potential D ζ ⟨r, hs⟩
      rw [e1, e2, e3]
      exact sourceIEnvelope_eq_of_equivalent
        (sourceIEquivalent_symm (sourceIEquivalent_iEnvelope (simplexValue_componentPSH D κ
          (le_of_lt (show r < D.τ 0 from hr')))))

/-- `Ã_max = τ_0` at every Kähler index. -/
theorem hullNAPotential_max (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) :
    ((hullNAPotential D).component κ).val.max = D.τ 0 := rfl

/-- `Ã_max = τ_0`, read with any Kähler form. -/
theorem sourceNAPotentialCutoff_hullNAPotential (omega : KahlerBackground n M)
    (D : PiecewiseLinearData θ) : sourceNAPotentialCutoff omega (hullNAPotential D) = D.τ 0 :=
  rfl

/-- The slices of `Ã`: `Ã^{θ+ω}_τ = P_{θ+ω}[A'_τ]_𝓘` with `A'_τ` the regularized concave
envelope of `rmk:pwlinhull` (the usc regularization of the pointwise upper concave envelope). -/
theorem hullNAPotential_component_potential (D : PiecewiseLinearData θ)
    (κ : SourceKahlerForm n M) (τ : Iio ((hullNAPotential D).component κ).val.max) :
    ((hullNAPotential D).component κ).val.potential τ =
      sourceIEnvelope (sourceNAComponentBackground θ κ)
        (uscRegularization (D.pointwiseUpperConcaveEnvelope τ)) := by
  rw [(source_pwlinhull_whole D).2.1 τ]
  rfl

/-- The constant left tail of each component of `Ã`: for `τ ≤ τ_N`,
`Ã^{θ+ω}_τ = P_{θ+ω}[max_i A_i]_𝓘`. -/
theorem hullNAPotential_component_potential_of_le_last (D : PiecewiseLinearData θ)
    (κ : SourceKahlerForm n M) (τ : Iio ((hullNAPotential D).component κ).val.max)
    (hτ : (τ : ℝ) ≤ D.τ (Fin.last D.N)) :
    ((hullNAPotential D).component κ).val.potential τ =
      sourceIEnvelope (sourceNAComponentBackground θ κ) (nodeMaximum D) := by
  change sourceIEnvelope _ (simplexValue D τ) = _
  rw [(source_pwlinhull_whole D).2.2.2.2.2.2.2.2.1 τ hτ]

/-- `Ã` is the unique element of `PSH^NA(X, θ)` with cutoff `τ_0` and the components
`P_{θ+ω}[A'_τ]_𝓘`. -/
theorem hullNAPotential_unique (D : PiecewiseLinearData θ) (Γ : SourceNAPotential θ)
    (hmax : ∀ κ : SourceKahlerForm n M, (Γ.component κ).val.max = D.τ 0)
    (hpot : ∀ (κ : SourceKahlerForm n M) (r : ℝ) (hr : r < (Γ.component κ).val.max),
      (Γ.component κ).val.potential ⟨r, hr⟩ = sourceIEnvelope (sourceNAComponentBackground θ κ)
        (uscRegularization (D.pointwiseUpperConcaveEnvelope r))) :
    Γ = hullNAPotential D := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · exact (hmax κ).trans (hullNAPotential_max D κ).symm
  · intro r hr hs
    exact (hpot κ r hr).trans (hullNAPotential_component_potential D κ ⟨r, hs⟩).symm

/-- Source `lma:psieqpsiprimeondiv`, first assertion: for a piecewise linear curve `A` in
`PSH(X, θ)` with regularized concave envelope `A'`, there is a unique `Ã ∈ PSH^NA(X, θ)` with
`Ã^{θ+ω}_τ = P_{θ+ω}[A'_τ]_𝓘` for every Kähler form `ω` and `τ < τ_0`; moreover
`Ã_max = τ_0`. -/
theorem source_psieqpsiprimeondiv_mem (D : PiecewiseLinearData θ) :
    ∃! Γ : SourceNAPotential θ, (∀ κ : SourceKahlerForm n M, (Γ.component κ).val.max = D.τ 0) ∧
      ∀ (κ : SourceKahlerForm n M) (r : ℝ) (hr : r < (Γ.component κ).val.max),
        (Γ.component κ).val.potential ⟨r, hr⟩ = sourceIEnvelope (sourceNAComponentBackground θ κ)
          (uscRegularization (D.pointwiseUpperConcaveEnvelope r)) :=
  ⟨hullNAPotential D, ⟨hullNAPotential_max D, fun κ r hr =>
      hullNAPotential_component_potential D κ ⟨r, hr⟩⟩,
    fun Γ hΓ => hullNAPotential_unique D Γ hΓ.1 hΓ.2⟩

end SGPT.NAPotential.Berkovich.PiecewiseLinearData

end

import SGPT.Okounkov.TranscendentalCoreSiu
import SGPT.Okounkov.TranscendentalMainStatement
import SGPT.Okounkov.SmoothDivisorTrace
import SGPT.Okounkov.PotentialFlagValuation
import SGPT.Trace.SmoothTarget
import SGPT.Foundations.Analysis.Pending.CompactAnalyticPoleLelongGap
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

/-!
# Valuations of currents with analytic singularities

Source: blueprint node `tok:valuation-analytic` (agreement of the book's `def:valcurr` with the
valuative map of DRWNXZ §3, "successive restrictions"; uses the book's `ex:resanalyt`).

Let `T = θ + dd^c φ ∈ 𝒜(ξ)` and `c = ν(T, Y₁)`. Then `c ∈ ℚ_{≥ 0}`, the potential of `T - c[Y₁]`
(the residual `φ - c log |s_{Y₁}|²` extended across `Y₁`, for any smooth metric of `𝒪(Y₁)`) is
not identically `-∞` on `Y₁`, its restriction to `Y₁` lies in `𝒜(Y₁, (ξ - c{Y₁})|_{Y₁})`, and
`ν(T) = (c, ν_{Y₁ ⊇ ⋯ ⊇ Yₙ}((T - c[Y₁])|_{Y₁}))`. In particular `ν(T) ∈ ℚⁿ_{≥ 0}`.

The trace of the residual along `Y₁` (used in `def:valcurr`) is `P`-equivalent to its restriction
(`ex:resanalyt`, `SGPT.Trace.sourcePEquivalent_trace_restriction_of_analytic`), because the residual
has analytic singularities (`residual_rational_and_hasManifoldAnalyticSingularityType`); and the
valuation only depends on the multiplier ideals.

## Main results

* `flagValuation_of_analytic`: the recursive description of `ν` on `𝒜(ξ)`.
* `exists_flagValuation_eq_cons_of_analytic`: the same with some metric of `𝒪(Y₁)`.
* `flagValuation_rational_of_analytic`: `ν(T) ∈ ℚⁿ_{≥ 0}`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalCore

open Set Filter
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension

/-- **Blueprint `tok:valuation-analytic`.** For `T = θ + dd^c φ ∈ 𝒜(ξ)` on a flag geometry of
dimension `m + 1` and any smooth metric `E` of `𝒪(Y₁)`: the first coordinate
`c = ν(T, Y₁)` is a nonnegative rational, the restriction to `Y₁` of the potential of
`T - c[Y₁]` lies in `𝒜(Y₁, (θ - c{Y₁})|_{Y₁})`, and the remaining coordinates of `ν(T)` are the
valuation of this restriction for the tail flag. -/
theorem flagValuation_of_analytic {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : φ ∈ analyticCurrents θ) (D : EffectiveDivisor (m + 1) F.carrier)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))))
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hEW : E.support = F.flag (1 : Fin (m + 2))) (hmetric : DivisorMetric.IsDivisorMetric D E) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) φ).toNNReal
    let w : F.tail.carrier → EReal := fun y =>
      extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ) (Subtype.val y)
    (∃ c₀ : ℚ, 0 ≤ c₀ ∧ (c : ℝ) = c₀) ∧ flagValuation F φ 0 = c ∧
      w ∈ analyticCurrents (TranscendentalMain.firstFlagRestriction F (θ - (c : ℝ) • E.curvature)) ∧
      (fun i => flagValuation F φ i.succ) = flagValuation F.tail w := by
  intro c w
  obtain ⟨hu, hA⟩ := hφ
  have hW := F.firstDivisor
  obtain ⟨hrat, hAv⟩ :=
    residual_rational_and_hasManifoldAnalyticSingularityType hu hA hW D hDI E hEW hmetric
  have hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
      (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ)) :=
    SGPT.Okounkov.isThetaPshPotential_smooth_divisor_residual_of_unit_metric hu hW D hDI E hEW
      hmetric
  have hzero := SGPT.Okounkov.sourceGeneric_smooth_divisor_residual_eq_zero hu hW D hDI E hEW
    hmetric hv
  have hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m)
    F.firstDivisor.2.2
  let : CompactSpace (F.flag (1 : Fin (m + 2))) := F.tail.compact
  let : ConnectedSpace (F.flag (1 : Fin (m + 2))) := F.tail.connected
  -- the restriction is plurisubharmonic for the restricted form, with analytic singularities
  have hgeneric : (⨅ y : F.tail.carrier, lelongNumber (n := m + 1)
      (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ))
        (Subtype.val y)) = 0 := by
    have h : (⨅ y : F.flag (1 : Fin (m + 2)),
        SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1)
          (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ))
            y.val) = 0 := hzero
    simp_rw [SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
      (Nat.succ_ne_zero m)]
    rw [← ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
    change 2 * (⨅ y : F.flag (1 : Fin (m + 2)),
        SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1)
          (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ))
            y.val) = 0
    rw [h, mul_zero]
  have hres : IsThetaPshPotential
      (TranscendentalMain.firstFlagRestriction F (θ - (c : ℝ) • E.curvature)).val w :=
    CompactAnalyticPoleLelongGap.isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
      hι hv.1
      (fun x _ => hAv (complexChartAt (n := m + 1) x) _
        ((complexChartAt (n := m + 1) x).val.map_source (mem_complexChartAt_source x)))
      hgeneric
  have hAw : HasManifoldAnalyticSingularityType (n := m) w :=
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hι hAv
  -- the trace of the residual and the flag step
  obtain ⟨τ, hτ⟩ :=
    NaturalSourceTraceExistenceAllDimensions.exists_naturalSourceTrace_of_isThetaPshPotential
      F.omega hW hv hzero
  have hstep : OriginalFlagStep F φ τ := ⟨θ, hu, D, hDI, E, hEW, hmetric, hτ⟩
  have hτ' := hτ
  unfold IsNaturalSourceTraceRepresentative at hτ'
  obtain ⟨_hg, _θ', _ε, _seq, _hqea, β, _hadm, hβτ, _hterms, _hlim⟩ := hτ'
  have htail := potentialFlagValuation_tail_of_originalFlagStep F hu hstep hβτ
  -- the trace is `P`-equivalent to the restriction
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have : BorelSpace F.tail.carrier := ⟨rfl⟩
  have htrace : IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι
      (extensionAcross (F.flag (1 : Fin (m + 2))) (smoothDivisorOffResidual E c φ)) τ := hτ
  have hP := SGPT.Trace.sourcePEquivalent_trace_restriction_of_analytic (Nat.le_succ m)
    F.tail.omega hι htrace hAv
  have hI := GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hP
  refine ⟨hrat, ?_, ⟨hres, hAw⟩, ?_⟩
  · rw [flagValuation_eq hu]
    have h0 := (potentialFlagValuation_spec F hu).1
    change ((potentialFlagValuation F hu 0 : ℝ≥0) : ℝ) = (c : ℝ)
    rw [h0]
  · rw [flagValuation_eq_of_iEquivalent (F := F.tail) hres hβτ hI.symm,
      flagValuation_eq (F := F.tail) hβτ, ← htail, flagValuation_eq (F := F) hu]

/-- The recursive description with some smooth metric of `𝒪(Y₁)`: `ν(T) = (c, ν(w))` with
`c ∈ ℚ_{≥ 0}` and `w ∈ 𝒜(Y₁, β)` the restriction of the potential of `T - c[Y₁]`. -/
theorem exists_flagValuation_eq_cons_of_analytic {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : φ ∈ analyticCurrents θ) :
    ∃ (c₀ : ℚ) (β : ClosedRealOneOneForm m F.tail.carrier) (w : F.tail.carrier → EReal),
      0 ≤ c₀ ∧ w ∈ analyticCurrents β ∧
        flagValuation F φ = Fin.cons (c₀ : ℝ) (flagValuation F.tail w) := by
  obtain ⟨D, hDI, E, hEW, hmetric, -, -⟩ :=
    SGPT.Okounkov.exists_normalized_smooth_divisor_residual_generic_zero hφ.1 F.firstDivisor
  obtain ⟨⟨c₀, hc₀, hcc₀⟩, h0, hw, htail⟩ := flagValuation_of_analytic F hφ D hDI E hEW hmetric
  refine ⟨c₀, _, _, hc₀, hw, ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero, h0, hcc₀]
  · rw [Fin.cons_succ]
    exact congrFun htail j

/-- **`ν(T) ∈ ℚⁿ_{≥ 0}` for `T ∈ 𝒜(ξ)`** (blueprint `tok:valuation-analytic`). -/
theorem flagValuation_rational_of_analytic :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n) (θ : ClosedRealOneOneForm n F.carrier)
      (φ : F.carrier → EReal), φ ∈ analyticCurrents θ →
        ∀ i, ∃ q : ℚ, 0 ≤ q ∧ flagValuation F φ i = q := by
  intro n
  induction n with
  | zero => intro F θ φ _ i; exact Fin.elim0 i
  | succ m ih =>
      intro F θ φ hφ i
      obtain ⟨c₀, β, w, hc₀, hw, heq⟩ := exists_flagValuation_eq_cons_of_analytic F hφ
      rw [heq]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨c₀, hc₀, by rw [Fin.cons_zero]⟩
      · rw [Fin.cons_succ]
        exact ih F.tail β w hw j

end SGPT.Okounkov.TranscendentalCore

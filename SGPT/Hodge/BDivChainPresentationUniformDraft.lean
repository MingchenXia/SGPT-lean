import SGPT.Hodge.BDivChainZeroPresentationDraft
import SGPT.Foundations.Analysis.Pending.FullSmoothNativeCurrentDifferential

/-!
# Uniform theta-potential presentations of actual chart currents

The predicate compares the actual chart coefficients with the
actual smooth-form plus dd-c regular distributions in every dimension and
requires the original theta-PSH predicate. Its positive-dimensional comparison
uses both existing inverse current-pairing theorems and the actual theta-current
coefficient formula; this is not a name-only identification.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

omit [CompactSpace X] in
/-- Chart integrability is derived from the actual theta-PSH potential in
positive dimension and from the actual zero-dimensional coordinate space in
zero dimension. -/
theorem presentationChartIntegrable (θ : ClosedRealOneOneForm n X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) : ChartLocallyIntegrable (canonicalBasis n) u := by
  cases n with
  | zero => exact chartLocallyIntegrable_zero u
  | succ m =>
    exact GlobalCurrentPotentials.quasiPsh_chart_locallyIntegrable (n := m + 1) (M := X)
      (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu.quasiPshPotential

/-- The actual distribution coefficients of the same θ and u in each chart. -/
def presentationCoefficients (θ : ClosedRealOneOneForm n X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) (e : ComplexChart n X) :
    DistributionForm (chartTarget e) 2 :=
  smoothFormDistribution (canonicalBasis n) θ.val e +
    chartDDC (canonicalBasis n) u e (presentationChartIntegrable θ u hu e)

/-- A presentation requires the source theta-PSH predicate and every actual
chart coefficient equality; no presentation equality is assumed separately. -/
def IsPresentationAny (T : ClosedPositive (n := n) (X := X))
    (θ : ClosedRealOneOneForm n X) (u : X → EReal) : Prop :=
  ∃ hu : IsThetaPshPotential θ.val u, ∀ e, T.val.val e = presentationCoefficients θ u hu e

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

omit [CompactSpace X] in
/-- The original theta-potential current has exactly those same actual
regular-distribution coefficients, by the two existing coefficient theorems. -/
theorem thetaPotentialCurrent_coefficients_any
    (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal)
    (hu : IsThetaPshPotential θ.val u) (e : ComplexChart (m + 1) X) :
    (thetaPotentialCurrent θ.val u hu).coefficients (canonicalBasis (m + 1)) e =
      presentationCoefficients θ u hu e := by
  rw [thetaPotentialCurrent, GlobalCurrent.coefficients_add,
    FullSmoothNativeCurrentDifferential.coefficients_smoothGlobalCurrent,
    GlobalCurrentPotentials.globalDDC_coefficients]
  rfl

omit [CompactSpace X] in
/-- Extraction after the actual chart-pairing map recovers the original
coefficients. -/
theorem toGlobal_coefficients_any (A : GlobalDistributionTwo (n := m + 1) (X := X))
    (e : ComplexChart (m + 1) X) :
    (A.toGlobal (Nat.succ_pos m)).coefficients (canonicalBasis (m + 1)) e = A.val e := by
  exact CurrentPairing.fromLocalCurrent_toLocalCurrent
    (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m)) (A.val e)

omit [CompactSpace X] in
/-- The chartwise theta-potential presentation is equivalent to the existing
book presentation of the same current, form and potential. -/
theorem isPresentationAny_iff_book
    (T : ClosedPositive (n := m + 1) (X := X))
    (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal) :
    IsPresentationAny T θ u ↔ SGPT.PSH.BookCurrent.IsPresentation (toBookCurrent T) θ u := by
  constructor
  · rintro ⟨hu, hchart⟩
    refine ⟨hu, ?_⟩
    apply GlobalCurrent.ext
    intro e η
    have hc : (T.val.toGlobal (Nat.succ_pos m)).coefficients (canonicalBasis (m + 1)) e =
        (thetaPotentialCurrent θ.val u hu).coefficients (canonicalBasis (m + 1)) e := by
      rw [toGlobal_coefficients_any, thetaPotentialCurrent_coefficients_any]
      exact hchart e
    have hp := congrArg (toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) hc
    simp only [GlobalCurrent.coefficients, CurrentPairing.toLocalCurrent_fromLocalCurrent] at hp
    exact congrArg (fun L => L η) hp
  · rintro ⟨hu, hcurrent⟩
    refine ⟨hu, ?_⟩
    intro e
    have hc := congrArg (fun C : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)) =>
      C.coefficients (canonicalBasis (m + 1)) e) hcurrent
    change (T.val.toGlobal (Nat.succ_pos m)).coefficients (canonicalBasis (m + 1)) e =
      (thetaPotentialCurrent θ.val u hu).coefficients (canonicalBasis (m + 1)) e at hc
    rw [toGlobal_coefficients_any, thetaPotentialCurrent_coefficients_any] at hc
    exact hc

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X]

omit [CompactSpace X] in
/-- The uniform chartwise presentation reduces to the actual zero-dimensional
presentation, with the same θ and u. -/
theorem isPresentationAny_iff_zero
    (T : ClosedPositive (n := 0) (X := X)) (θ : ClosedRealOneOneForm 0 X) (u : X → EReal) :
    IsPresentationAny T θ u ↔ IsPresentationZero T θ u := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, ?_⟩
    apply Subtype.ext
    funext e
    exact h e
  · rintro ⟨hu, h⟩
    refine ⟨hu, ?_⟩
    intro e
    exact congrFun (congrArg Subtype.val h) e

end SGPT.Hodge.BDivChain.NativeDraft

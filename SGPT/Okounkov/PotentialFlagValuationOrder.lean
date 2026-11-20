import SGPT.Okounkov.PotentialFlagValuationIndependence
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.PiLex

set_option autoImplicit false

noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition
open NaturalThetaPshGeometricCurrent

/-- Actual source tail order in the equal-first-coefficient branch of the
original lexicographic proof. All genuine unit metrics and plain traces
remain arbitrary. -/
theorem originalFlagStep_iOrder_of_iOrder_and_coefficient_eq {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {u v : F.carrier → EReal} {τu τv : F.tail.carrier → EReal}
    (hI : IOrderOnManifold (n := m + 1) u v)
    (hcoef : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u =
      sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) v)
    (hTu : OriginalFlagStep F u τu) (hTv : OriginalFlagStep F v τv) :
    IOrderOnManifold (n := m) τu τv := by
  obtain ⟨θ, hu, D₀, hDI₀, E₀, hEW₀, hmetric₀, hTu⟩ := hTu
  obtain ⟨σ, hv, D₁, hDI₁, E₁, hEW₁, hmetric₁, hTv⟩ := hTv
  let : MeasurableSpace F.carrier := borel F.carrier
  let : BorelSpace F.carrier := ⟨rfl⟩
  have hcommon := iOrder_smooth_divisor_residuals_of_iOrder_and_coefficient_eq
    hu hv hI F.firstDivisor hcoef D₀ hDI₀ E₀ hEW₀ hmetric₀
  have hv₀ := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hv F.firstDivisor D₀ hDI₀ E₀ hEW₀ hmetric₀
  have hv₁ := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hv F.firstDivisor D₁ hDI₁ E₁ hEW₁ hmetric₁
  have hchoices := iEquivalent_smooth_divisor_residuals_of_thetaPotentialCurrent_eq
    F.omega hv hv rfl F.firstDivisor D₀ D₁ hDI₀ hDI₁ E₀ E₁
    hEW₀ hEW₁ hmetric₀ hmetric₁ hv₀ hv₁
  let W := F.flag (1 : Fin (m + 2))
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_succ m) F.firstDivisor.2.2
  let : CompactSpace W := F.tail.compact
  let : ConnectedSpace W := F.tail.connected
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  let : BorelSpace F.tail.carrier := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τu at hTu
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τv at hTv
  exact GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
    (sourcePOrder_of_iOrder_of_sourceTraceRepresentatives
      (Nat.succ_ne_zero m) F.tail.omega F.tail.omega hι hTu hTv (hcommon.trans hchoices.1))

/-- True original lexicographic order, with the first strict coefficient
or genuine tail induction in the equal-coefficient branch. -/
theorem originalPotentialFlagValuation_lex_le_of_iOrder :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n)
      (u v : F.carrier → EReal) (ν μ : Fin n → ℝ≥0),
      OriginalPotentialFlagValuation n F u ν →
      OriginalPotentialFlagValuation n F v μ →
      IOrderOnManifold (n := n) u v → toLex μ ≤ toLex ν := by
  intro n
  induction n with
  | zero =>
      intro F u v ν μ _hν _hμ _hI
      have h : μ = ν := by funext i; exact Fin.elim0 i
      exact le_of_eq (congrArg toLex h)
  | succ m ih =>
      intro F u v ν μ hν hμ hI
      obtain ⟨hν₀, τu, hTu, hνtail⟩ := hν
      obtain ⟨hμ₀, τv, hTv, hμtail⟩ := hμ
      have hTuKeep := hTu
      have hTvKeep := hTv
      obtain ⟨θ, hu, _D₀, _hDI₀, _E₀, _hEW₀, _hmetric₀, _hTu⟩ := hTu
      obtain ⟨σ, hv, _D₁, _hDI₁, _E₁, _hEW₁, _hmetric₁, _hTv⟩ := hTv
      have hfiniteu := sourceGeneric_subtype_ne_top F.firstDivisor hu.quasiPshPotential
      have hfinitev := sourceGeneric_subtype_ne_top F.firstDivisor hv.quasiPshPotential
      have hheadu : (ν 0 : ℝ≥0∞) = sourceGenericLelongNumber (n := m + 1)
          (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u := by
        rw [hν₀, ENNReal.coe_toNNReal hfiniteu]
      have hheadv : (μ 0 : ℝ≥0∞) = sourceGenericLelongNumber (n := m + 1)
          (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) v := by
        rw [hμ₀, ENNReal.coe_toNNReal hfinitev]
      have hhead : μ 0 ≤ ν 0 := by
        apply ENNReal.coe_le_coe.mp
        rw [hheadu, hheadv]
        exact sourceGeneric_subtype_le_of_iOrder F.firstDivisor
          hu.quasiPshPotential hv.quasiPshPotential hI
      have hνcons : Fin.cons (ν 0) (fun i => ν i.succ) = ν := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have hμcons : Fin.cons (μ 0) (fun i => μ i.succ) = μ := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rcases hhead.lt_or_eq with hstrict | heq
      · apply le_of_lt
        change Pi.Lex (· < ·) (· < ·) μ ν
        rw [← hμcons, ← hνcons]
        exact (Fin.pi_lex_lt_cons_cons (s := (· < ·))).mpr (Or.inl hstrict)
      · have hcoef : sourceGenericLelongNumber (n := m + 1)
            (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u =
            sourceGenericLelongNumber (n := m + 1)
              (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) v :=
          hheadu.symm.trans ((congrArg (fun c : ℝ≥0 => (c : ℝ≥0∞)) heq).symm.trans hheadv)
        have htarget := originalFlagStep_iOrder_of_iOrder_and_coefficient_eq
          F hI hcoef hTuKeep hTvKeep
        have htail := ih F.tail τu τv (fun i => ν i.succ) (fun i => μ i.succ)
          hνtail hμtail htarget
        rcases htail.lt_or_eq with hstrict | hsame
        · apply le_of_lt
          change Pi.Lex (· < ·) (· < ·) μ ν
          change Pi.Lex (· < ·) (· < ·) (fun i : Fin m => μ i.succ)
            (fun i : Fin m => ν i.succ) at hstrict
          rw [← hμcons, ← hνcons]
          exact (Fin.pi_lex_lt_cons_cons (s := (· < ·))).mpr (Or.inr ⟨heq, hstrict⟩)
        · apply le_of_eq
          congr 1
          funext i
          exact Fin.cases heq (fun j => congrFun hsame j) i

/-- The actual produced finite-vector assignment obeys the source order. -/
theorem potentialFlagValuation_lex_le_of_iOrder {n : ℕ}
    (F : OriginalFlagGeometry.{u} n)
    {θ σ : ClosedRealOneOneForm n F.carrier} {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hI : IOrderOnManifold (n := n) u v) :
    toLex (potentialFlagValuation F hv) ≤ toLex (potentialFlagValuation F hu) :=
  originalPotentialFlagValuation_lex_le_of_iOrder n F u v _ _
    (potentialFlagValuation_spec F hu) (potentialFlagValuation_spec F hv) hI

end SGPT.Okounkov

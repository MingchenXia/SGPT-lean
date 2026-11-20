import SGPT.PSH.CompactPrimeMultiplierOrder
import SGPT.Foundations.Analysis.Pending.MultiplierIdealLimit


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.PSH.CompactPrimeMultiplierLimit

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.BlowupSequences CompactPrimeOver CompactPrimeMultiplierOrder
  MultiplierIdealLowerBound MultiplierIdealLimit VariableComplexAtlas

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Every actual presentation reads the same original ALL-positive-integer whole-ideal limit. -/
theorem tendsto_presentationMultiplierOrder_ratio {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (p : PrimePresentation n X) :
    Tendsto (fun k : ℕ =>
      (presentationMultiplierOrder hφ (show (0 : ℝ) < (k + 1 : ℕ) by positivity) p : ℝ≥0∞) /
        (k + 1 : ℕ)) atTop (𝓝 (presentationReader φ p)) := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 0 p.dimension_pos)
  | succ m =>
      have hdim : p.divisorDimension = m := by
        have h := p.codimension_one
        omega
      have hE : IsClosedConnectedSubmanifold (m + 1) p.divisor m := by
        simpa only [hdim] using p.smooth
      have h := tendsto_actualMultiplierCoefficient_ratio_squaredLog p.modification hE hφ
      simpa only [presentationMultiplierOrder, presentationReader, sourceGenericLelong,
        sourceLelong_ofFixedModel_eq, Function.comp_def] using h

variable [ConnectedSpace X] [CompactSpace X]

/-- The actual DIRECT quotient and its independently defined original reader satisfy the integer formula. -/
theorem tendsto_directMultiplierOrder_ratio {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (E : DirectPrimeOver n X) :
    Tendsto (fun k : ℕ =>
      (directMultiplierOrder hφ (show (0 : ℝ) < (k + 1 : ℕ) by positivity) E : ℝ≥0∞) /
        (k + 1 : ℕ)) atTop (𝓝 (directReader φ hφ.1 E)) := by
  refine Quot.inductionOn E ?_
  intro p
  exact tendsto_presentationMultiplierOrder_ratio hφ p

omit [ConnectedSpace X] [CompactSpace X] in
private theorem genuine_of_sourcePSH {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsPSH φ) : IsGlobalQuasiPshPotential (n := n) φ := by
  have hnative : ManifoldPSH (n := n) φ := (ofFixedModel_isPSH_iff n X φ).mp hφ
  refine ⟨?_, hnative.locallyNondegenerate⟩
  intro e z hz
  exact (hnative.chartPlurisubharmonic e z hz).quasiPlurisubharmonicAt

/-- The entire original multiplier ideal order from the original source PSH input alone. -/
def directSourcePSHMultiplierOrder (φ : X → EReal) (hφ : (ofFixedModel n X).IsPSH φ)
    (c : ℝ) (hc : 0 < c) : DirectPrimeOver n X → ℕ :=
  directMultiplierOrder (genuine_of_sourcePSH hφ) hc

/-- Every representative reads the SAME original whole pulled multiplier ideal. -/
theorem directSourcePSHMultiplierOrder_mk (φ : X → EReal)
    (hφ : (ofFixedModel n X).IsPSH φ) (c : ℝ) (hc : 0 < c) (p : PrimePresentation n X) :
    directSourcePSHMultiplierOrder φ hφ c hc (Quot.mk commonResolutionRelation p) =
      presentationMultiplierOrder (genuine_of_sourcePSH hφ) hc p := rfl

/-- The original source PSH function and actual direct prime class obey the literal ALL-integer limit. -/
theorem tendsto_directSourcePSHMultiplierOrder_ratio (φ : X → EReal)
    (hφ : (ofFixedModel n X).IsPSH φ) (E : DirectPrimeOver n X) :
    Tendsto (fun k : ℕ =>
      (directSourcePSHMultiplierOrder φ hφ (k + 1 : ℕ)
        (show (0 : ℝ) < (k + 1 : ℕ) by positivity) E : ℝ≥0∞) /
          (k + 1 : ℕ)) atTop (𝓝 (directSourcePSHReader φ hφ E)) := by
  exact tendsto_directMultiplierOrder_ratio (genuine_of_sourcePSH hφ) E

end SGPT.PSH.CompactPrimeMultiplierLimit

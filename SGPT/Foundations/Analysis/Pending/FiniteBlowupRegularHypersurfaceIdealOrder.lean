import SGPT.Foundations.Analysis.Pending.BlowupSequenceLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.IOrderDivisorialLelongForward

set_option autoImplicit false

/-!
# Actual regular-hypersurface ideal-order comparison on finite blowups

Local discrepancy is produced at each actual regular point. The dyadic
approximation limit is taken there before the actual infimum on E,
so no uniform discrepancy certificate is required. No all-prime or
arbitrary-modification/reverse valuative result is claimed.
-/

noncomputable section

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.FiniteBlowupRegularHypersurfaceIdealOrder

open FirstPass FirstPass.PositiveClasses FirstPass.BlowupSequences FirstPass.IEnvelope
  FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation DemaillyApproximantDivisorialLelong
  BlowupSequenceLocalDiscrepancy IOrderDivisorialLelongForward


/-- Actual regular hypersurface geometry and finite blowups supply all
local discrepancy bounds internally. The dyadic limit is taken at each
fixed point before the infimum, so no uniform bound is required. -/
theorem divisorialLelongNumber_comp_le_of_iOrder_regular_blowupSequence
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    (omega : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    {u v : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hI : IOrderOnManifold (n := m + 1) u v)
    {π : Y → X} (hπ : IsBlowupSequence (m + 1) X Y π) {E : Set Y}
    (hreg : ∀ x ∈ E, RegularAtDim (n := m + 1) E x m) :
    divisorialLelongNumber m (fun y => v (π y)) E ≤
      divisorialLelongNumber m (fun y => u (π y)) E := by
  obtain ⟨ε, vk, happ, htype⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType
      (Nat.succ_pos m) omega θ hv
  have hkbound (k : ℕ) (x : Y) :
      lelongNumber (n := m + 1) (fun y => vk k (π y)) x ≤
        lelongNumber (n := m + 1) (fun y => u (π y)) x := by
    have hle : v ≤ vk k := fun z =>
      (happ.term_antitone z).le_of_tendsto (happ.term_tendsto z) k
    have hi : IOrderOnManifold (n := m + 1) u (vk k) :=
      hI.trans (iOrderOnManifold_of_le (happ.term k).1.quasiPlurisubharmonic hle)
    exact lelongNumber_comp_le_of_iOrder_analytic_reference hu (happ.term k)
      (happ.term_hasAnalyticSingularityType k) hi π x
  have hp : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
    have h := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
    exact h.congr fun k => by push_cast; rfl
  refine le_iInf₂ fun x hx => ?_
  obtain ⟨A, hA⟩ := exists_logDiscrepancyLE_of_isBlowupSequence_regular hπ (hreg x hx)
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have he : Tendsto (fun k : ℕ => 2 * (A : ℝ) / ((2 ^ k : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hp).const_mul (2 * (A : ℝ))
  have hlim : Tendsto (fun k : ℕ =>
      ENNReal.ofReal ((r : ℝ) - 2 * (A : ℝ) / ((2 ^ k : ℕ) : ℝ))) atTop
      (𝓝 (r : ℝ≥0∞)) := by
    have hsub : Tendsto (fun k : ℕ => (r : ℝ) -
        2 * (A : ℝ) / ((2 ^ k : ℕ) : ℝ)) atTop (𝓝 (r : ℝ)) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (r : ℝ)) atTop (𝓝 (r : ℝ))).sub he
    simpa using ENNReal.tendsto_ofReal hsub
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun k =>
    (ofReal_sub_le_lelongNumber_comp hπ.contMDiff
      (BlowupSequenceInjectiveOffNull.isInjectiveOffNull_of_isBlowupSequence hπ) hv.1
      (show 0 < (2 ^ k : ℕ) by positivity) (htype k) hA hr).trans (hkbound k x)

end SGPT.Foundations.Analysis.Pending.FiniteBlowupRegularHypersurfaceIdealOrder

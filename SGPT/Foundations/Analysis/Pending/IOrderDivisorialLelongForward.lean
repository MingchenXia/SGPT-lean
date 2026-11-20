import SGPT.Foundations.Analysis.Pending.AnalyticReferenceIdealGlobalPOrder
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly

set_option autoImplicit false

/-! # Actual geometric forward ideal-order Lelong comparison -/

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.IOrderDivisorialLelongForward

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation DemaillyApproximantDivisorialLelong
  ActualLelongPositiveScaling

noncomputable section

/-- Every actual strict analytic-reference comparison survives arbitrary
composition, and finite positive coefficients tend to one before the
extended logarithmic exponent is bounded. -/
theorem lelongNumber_comp_le_of_iOrder_analytic_reference
    {n r : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel r) Y]
    {θ ζ : ClosedRealOneOneForm n X} {ψ Φ : X → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) (hΦ : IsThetaPshPotential ζ.val Φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) Φ)
    (hI : IOrderOnManifold (n := n) ψ Φ) (π : Y → X) (y : Y) :
    lelongNumber (n := r) (fun z => Φ (π z)) y ≤
      lelongNumber (n := r) (fun z => ψ (π z)) y := by
  have hbound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
      ENNReal.ofReal s * lelongNumber (n := r) (fun z => Φ (π z)) y ≤
        lelongNumber (n := r) (fun z => ψ (π z)) y := by
    obtain ⟨C, hC⟩ :=
      AnalyticReferenceIdealGlobalPOrder.moreSingularOn_scaled_of_iOrderOnManifold
        hψ hΦ hA hI hs0 hs1
    have hle : ∀ᶠ z in 𝓝[≠] y,
        ψ (π z) ≤ (s : EReal) * Φ (π z) + (C : EReal) :=
      Eventually.of_forall fun z => hC (π z) (mem_univ _)
    have hh := LelongNumberScaling.lelongNumber_le_add_of_eventually_le_const
      (n := r) (u := fun z => (s : EReal) * Φ (π z)) (x := y)
      (v := fun _ => (C : EReal)) (c := C) (Eventually.of_forall fun _ => le_rfl)
    have ho := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := r) hle
    rw [lelongNumber_smul_eq hs0] at hh
    exact hh.trans ho
  have hs : Tendsto (fun s : ℝ => ENNReal.ofReal s) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hid : Tendsto (fun s : ℝ => s) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [ENNReal.ofReal_one] using
      ENNReal.tendsto_ofReal hid
  have hm : Tendsto (fun s : ℝ => ENNReal.ofReal s *
      lelongNumber (n := r) (fun z => Φ (π z)) y) (𝓝[<] (1 : ℝ))
      (𝓝 (lelongNumber (n := r) (fun z => Φ (π z)) y)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hs (Or.inl one_ne_zero)
  apply le_of_tendsto hm
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with s hs0 hs1
  exact hbound s hs0 hs1

/-- The actual Demailly approximation, analytic ideal comparison and
vanishing dyadic discrepancy error produce the forward inequality from
all-level ideal order.  The geometric data are the literal existing
holomorphic/null-injectivity/Jacobian-factorization predicates. -/
theorem divisorialLelongNumber_comp_le_of_iOrder
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    (omega : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    {u v : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hI : IOrderOnManifold (n := m + 1) u v)
    {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (hinj : IsInjectiveOffNull m π) {E : Set Y} {A : ℕ}
    (hA : ∀ x ∈ E, LogDiscrepancyLE m π E x A) :
    divisorialLelongNumber m (fun y => v (π y)) E ≤
      divisorialLelongNumber m (fun y => u (π y)) E := by
  obtain ⟨ε, vk, happ, htype⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType
      (Nat.succ_pos m) omega θ hv
  have hkbound (k : ℕ) : divisorialLelongNumber m (fun y => vk k (π y)) E ≤
      divisorialLelongNumber m (fun y => u (π y)) E := by
    have hle : v ≤ vk k := fun z =>
      (happ.term_antitone z).le_of_tendsto (happ.term_tendsto z) k
    have hi : IOrderOnManifold (n := m + 1) u (vk k) :=
      hI.trans (iOrderOnManifold_of_le (happ.term k).1.quasiPlurisubharmonic hle)
    exact iInf₂_mono fun y _ =>
      lelongNumber_comp_le_of_iOrder_analytic_reference hu (happ.term k)
        (happ.term_hasAnalyticSingularityType k) hi π y
  have hbound (k : ℕ) : divisorialLelongNumber m (fun y => v (π y)) E ≤
      divisorialLelongNumber m (fun y => u (π y)) E +
        ENNReal.ofReal (2 * (A : ℝ) / ((2 ^ k : ℕ) : ℝ)) := by
    have hlow := divisorialLelongNumber_comp_sub_le hπ hinj hv.1
      (show 0 < (2 ^ k : ℕ) by positivity) (htype k) hA
    exact tsub_le_iff_right.mp (hlow.trans (hkbound k))
  have hp : Tendsto (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) atTop atTop := by
    have h := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
    exact h.congr fun k => by push_cast; rfl
  have he : Tendsto (fun k : ℕ => 2 * (A : ℝ) / ((2 ^ k : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hp).const_mul (2 * (A : ℝ))
  have hrhs : Tendsto (fun k : ℕ =>
      divisorialLelongNumber m (fun y => u (π y)) E +
        ENNReal.ofReal (2 * (A : ℝ) / ((2 ^ k : ℕ) : ℝ))) atTop
      (𝓝 (divisorialLelongNumber m (fun y => u (π y)) E)) := by
    simpa only [ENNReal.ofReal_zero, add_zero] using
      tendsto_const_nhds.add (ENNReal.tendsto_ofReal he)
  exact ge_of_tendsto hrhs (Eventually.of_forall hbound)

end
end SGPT.Foundations.Analysis.Pending.IOrderDivisorialLelongForward

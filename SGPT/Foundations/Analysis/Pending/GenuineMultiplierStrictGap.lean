import SGPT.Foundations.Analysis.Pending.GenuinePshUniformSmallMultiplier
import SGPT.Foundations.Analysis.Pending.UniformLelongBound
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.MultiplierSubadditivity

set_option autoImplicit false

/-! # Natural compact affine multiplier comparison at any positive real gap -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.GenuineMultiplierStrictGap
open FirstPass FirstPass.HolomorphicIdealSheaves

noncomputable section

/-- A natural compact affine comparison supplies every strict positive real
multiplier gap, including actual dimension-zero unit ideals. -/
theorem exists_multiplierIdeal_le_of_convexComb_le
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M]
    (θ : ClosedRealOneOneForm n M) {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∀ {v w φ : M → EReal}, IsThetaPshPotential θ.val v →
      IsThetaPshPotential θ.val w → IsThetaPshPotential θ.val φ →
      (∀ x, ((1 - t : ℝ) : EReal) * v x + (t : EReal) * w x ≤ φ x) →
      (multiplierIdeal (n := n) q v).Le (multiplierIdeal (n := n) p φ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro t ht htt v w φ hv hw hφ hconv x g hg
    have hunit := GenuinePshUniformSmallMultiplier.one_mem_multiplierIdeal_of_dim_zero hφ hp x
    simpa only [mul_one] using
      MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul hg.1 hunit
  · let α : ℝ := q - p
    have hα : 0 < α := sub_pos.mpr hpq
    let r : ℝ := p / α
    have hr : 0 < r := div_pos hp hα
    have hrα : r * α = p := div_mul_cancel₀ p hα.ne'
    have hr1α : (r + 1) * α = q := by
      rw [add_mul, hrα, one_mul]
      dsimp [α]
      ring
    have hN := UniformLelongBound.hasUniformLelongBound hn (α • θ)
    obtain ⟨t₀, ht₀, hcompare⟩ :=
      MultiplierIdealConvexShift.exists_multiplierIdeal_le_of_convexComb_le_of_hasUniformLelongBound
        (α • θ) hN hr
    refine ⟨t₀, ht₀, ?_⟩
    intro t ht htt v w φ hv hw hφ hconv
    let vα : M → EReal := fun x => (α : EReal) * v x
    let wα : M → EReal := fun x => (α : EReal) * w x
    let φα : M → EReal := fun x => (α : EReal) * φ x
    have hvα : IsThetaPshPotential (α • θ).val vα :=
      RestrictedApproximantComparison.isThetaPshPotential_smul hv hα
    have hwα : IsThetaPshPotential (α • θ).val wα :=
      RestrictedApproximantComparison.isThetaPshPotential_smul hw hα
    have hφα : IsThetaPshPotential (α • θ).val φα :=
      RestrictedApproximantComparison.isThetaPshPotential_smul hφ hα
    have hcα : ∀ x, ((1 - t : ℝ) : EReal) * vα x + (t : EReal) * wα x ≤ φα x := by
      intro x
      have h := mul_le_mul_of_nonneg_left (hconv x) (EReal.coe_nonneg.mpr hα.le)
      rw [EReal.left_distrib_of_nonneg_of_ne_top
        (EReal.coe_nonneg.mpr hα.le) (EReal.coe_ne_top α)] at h
      dsimp [vα, wα, φα]
      convert h using 1; ac_rfl
    have hI := hcompare t ht htt hvα.1.quasiPlurisubharmonic hwα
      hφα.1.quasiPlurisubharmonic hcα
    have hweight : ∀ (a : M → EReal) (c : ℝ) (e : ComplexChart n M) (z : ComplexModel n),
        multiplierWeight c (chartFunction (fun x => (α : EReal) * a x) e z) =
        multiplierWeight (c * α) (chartFunction a e z) := by
      intro a c e z
      simp only [chartFunction, multiplierWeight, ← mul_assoc, ← EReal.coe_mul]
    intro x g hg
    have hgα : (multiplierIdeal (n := n) (r + 1) vα).mem x g := by
      refine ⟨hg.1, ?_⟩
      exact MultiplierSubadditivity.multiplierIntegrableAt_of_weight_eq (by linarith : 0 < r + 1)
        (fun z => by rw [hweight v (r + 1), hr1α]) hg.2
    have htarget := hI x g hgα
    refine ⟨htarget.1, ?_⟩
    exact MultiplierSubadditivity.multiplierIntegrableAt_of_weight_eq hp
      (fun z => by rw [hweight φ r, hrα]) htarget.2

end
end SGPT.Foundations.Analysis.Pending.GenuineMultiplierStrictGap

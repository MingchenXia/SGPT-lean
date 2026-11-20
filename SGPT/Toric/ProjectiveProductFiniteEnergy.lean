import SGPT.Toric.ProjectiveProductSingularEnergy

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativeEnergy
open SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open scoped Topology ENNReal RealInnerProductSpace

variable {n : ℕ}
local notation "X" => projectiveProductSpace n
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ En

private theorem zero_bounded : IsBoundedPotential (fun _ : X => (0 : EReal)) :=
  ⟨0, 0, fun _ => by simp⟩
private theorem zero_invariant : ProjectiveProductCircleInvariant (fun _ : X => (0 : EReal)) :=
  fun _ _ _ => rfl

private theorem sub_coe_add_coe (z : EReal) (r : ℝ) :
    (z - (r : EReal)) + (r : EReal) = z := by
  cases z using EReal.rec with
  | bot => simp
  | top => simp
  | coe a =>
    rw [← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    ring

/-- Finite bounds for the genuine zero-reference conjugate compare actual
extended positive-part and gap integrals, without discarding infinite values. -/
theorem projectiveProduct_gap_lintegral_lt_top_iff_positive_lintegral (u : X → EReal) :
    (∫⁻ m in (euclideanUnitCube n),
      (projectiveProductToricLegendre u m -
        projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m).toENNReal) < ⊤ ↔
      (∫⁻ m in (euclideanUnitCube n), (projectiveProductToricLegendre u m).toENNReal) < ⊤ := by
  let G : En → EReal := projectiveProductToricLegendre u
  let G0 : En → EReal := projectiveProductToricLegendre (fun _ : X => (0 : EReal))
  let q : En → ℝ≥0∞ := fun m => (G m - G0 m).toENNReal
  let p : En → ℝ≥0∞ := fun m => (G m).toENNReal
  have hG : Measurable G := measurable_conjugate B _
  have hG0 : Measurable G0 := measurable_conjugate B _
  have hp : Measurable p := EReal.continuous_toENNReal.measurable.comp hG
  have hq : Measurable q := EReal.continuous_toENNReal.measurable.comp (hG.sub hG0)
  have hg0 := projectiveProductToricProfile_mem_boundedGrowthClass
    (isThetaPshPotential_projectiveProductZero n) zero_invariant zero_bounded
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B
    (isCompact_euclideanUnitCube n) (convex_euclideanUnitCube n) hg0
  let M : ℝ := |a| + |b|
  let K : ℝ≥0∞ := ENNReal.ofReal M
  have hMb : b ≤ M := by
    change b ≤ |a| + |b|
    linarith [le_abs_self b, abs_nonneg a]
  have hMa : -a ≤ M := by
    change -a ≤ |a| + |b|
    linarith [neg_abs_le a, abs_nonneg b]
  have hK : (∫⁻ _m : En, K ∂volume.restrict (euclideanUnitCube n)) < ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (by simpa using (isCompact_euclideanUnitCube n).measure_lt_top (μ := volume))
  have h0f := projectiveProductToricLegendre_finite_of_bounded
    (isThetaPshPotential_projectiveProductZero n) zero_invariant zero_bounded
  have hbnd : ∀ m ∈ (euclideanUnitCube n), p m ≤ q m + K ∧ q m ≤ p m + K := by
    intro m hm
    have h0p : (G0 m).toENNReal ≤ K := by
      apply le_trans (EReal.toENNReal_le_toENNReal
        ((hab m hm).2.trans (EReal.coe_le_coe_iff.mpr hMb)))
      exact le_of_eq (EReal.real_coe_toENNReal M)
    have h0n : (-G0 m).toENNReal ≤ K := by
      have hn := EReal.neg_le_neg_iff.mpr (hab m hm).1
      rw [← EReal.coe_neg] at hn
      apply le_trans (EReal.toENNReal_le_toENNReal
        (hn.trans (EReal.coe_le_coe_iff.mpr hMa)))
      exact le_of_eq (EReal.real_coe_toENNReal M)
    have hcancel : (G m - G0 m) + G0 m = G m := by
      change (G m - projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m) +
        projectiveProductToricLegendre (fun _ : X => (0 : EReal)) m = G m
      rw [h0f m hm]
      exact sub_coe_add_coe _ _
    constructor
    · calc
        p m = ((G m - G0 m) + G0 m).toENNReal := congrArg EReal.toENNReal hcancel.symm
        _ ≤ q m + (G0 m).toENNReal := EReal.toENNReal_add_le
        _ ≤ q m + K := add_le_add le_rfl h0p
    · exact EReal.toENNReal_add_le.trans (add_le_add le_rfl h0n)
  have hb1 : (∫⁻ m, p m ∂volume.restrict (euclideanUnitCube n)) ≤
      (∫⁻ m, q m ∂volume.restrict (euclideanUnitCube n)) +
        ∫⁻ _m : En, K ∂volume.restrict (euclideanUnitCube n) := by
    rw [← lintegral_add_left hq (fun _ => K)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (isCompact_euclideanUnitCube n).isClosed.measurableSet]
      with m hm
    exact (hbnd m hm).1
  have hb2 : (∫⁻ m, q m ∂volume.restrict (euclideanUnitCube n)) ≤
      (∫⁻ m, p m ∂volume.restrict (euclideanUnitCube n)) +
        ∫⁻ _m : En, K ∂volume.restrict (euclideanUnitCube n) := by
    rw [← lintegral_add_left hp (fun _ => K)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (isCompact_euclideanUnitCube n).isClosed.measurableSet]
      with m hm
    exact (hbnd m hm).2
  change (∫⁻ m, q m ∂volume.restrict (euclideanUnitCube n)) < ⊤ ↔
    (∫⁻ m, p m ∂volume.restrict (euclideanUnitCube n)) < ⊤
  constructor
  · intro h
    exact lt_of_le_of_lt hb1 (ENNReal.add_lt_top.mpr ⟨h, hK⟩)
  · intro h
    exact lt_of_le_of_lt hb2 (ENNReal.add_lt_top.mpr ⟨h, hK⟩)

private theorem bot_lt_neg_coe_ennreal_iff (a : ℝ≥0∞) :
    ⊥ < -(a : EReal) ↔ a < ⊤ := by
  constructor
  · intro h
    have h' : (a : EReal) < ⊤ := by simpa using EReal.lt_neg_of_lt_neg h
    exact EReal.coe_ennreal_lt_coe_ennreal_iff.mp h'
  · intro h
    have h' : (a : EReal) < ⊤ := EReal.coe_ennreal_lt_coe_ennreal_iff.mpr h
    have h'' : -(-(a : EReal)) < ⊤ := by simpa using h'
    simpa using EReal.neg_lt_of_neg_lt h''


private theorem factorial_mul_lt_top_iff (a : ENNReal) :
    (n.factorial : ENNReal) * a < ⊤ ↔ a < ⊤ := by
  constructor
  · intro h
    by_contra ha
    have hatop : a = ⊤ := top_le_iff.mp (le_of_not_gt ha)
    simp [hatop, Nat.factorial_ne_zero] at h
  · intro h
    exact ENNReal.mul_lt_top (by simp) h

/-- Actual native finite energy is exactly finite extended positive conjugate integral;
the genuine reference model and the literal positive factorial are manufactured. -/
theorem projectiveProduct_mem_relativeFiniteEnergy_iff_legendre_positive {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeFiniteEnergy (projectiveProductFSBackground n).form (fun _ : X => (0 : EReal)) u
      (isModelPotential_projectiveProductZero n) ↔
      (∫⁻ m in euclideanUnitCube n, (projectiveProductToricLegendre u m).toENNReal) < ⊤ := by
  have hrel : RelativePSH (projectiveProductFSBackground n).form (fun _ : X => (0 : EReal)) u :=
    ⟨hu, hle⟩
  rw [FiniteEnergyCharacterization.relativeFiniteEnergy_iff_bot_lt_energy
    (projectiveProductFSBackground n) (projectiveProductFSBackground n).form
    (isModelPotential_projectiveProductZero n) zero_bounded hrel,
    ← RelativeDarvasDistance.energy_eq hrel,
    projectiveProduct_energy_eq_neg_gap_lintegral_of_nonpos hu hi hle,
    bot_lt_neg_coe_ennreal_iff, factorial_mul_lt_top_iff,
    projectiveProduct_gap_lintegral_lt_top_iff_positive_lintegral u]

/-- Genuine original proper growth produces the finite negative conjugate part;
the actual native E1 criterion keeps every extended value in both L1 parts. -/
theorem projectiveProduct_mem_relativeFiniteEnergy_iff_legendre_L1 {u : X → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (hle : u ≤ fun _ => (0 : EReal)) :
    RelativeFiniteEnergy (projectiveProductFSBackground n).form (fun _ : X => (0 : EReal)) u
      (isModelPotential_projectiveProductZero n) ↔
      (∫⁻ m in euclideanUnitCube n,
        (projectiveProductToricLegendre u m).toENNReal +
          (-projectiveProductToricLegendre u m).toENNReal) < ⊤ := by
  rw [projectiveProduct_mem_relativeFiniteEnergy_iff_legendre_positive hu hi hle]
  have hm : Measurable (fun m => (projectiveProductToricLegendre u m).toENNReal) :=
    EReal.continuous_toENNReal.measurable.comp (measurable_conjugate B _)
  rw [lintegral_add_left hm]
  have hn := lintegral_neg_conjugate_lt_top_of_mem_growthClass volume B
    (isCompact_euclideanUnitCube n) (nonempty_euclideanUnitCube n)
    (projectiveProductToricProfile_mem_growthClass hu hi)
  exact ⟨fun h => ENNReal.add_lt_top.mpr ⟨h, hn⟩,
    fun h => (ENNReal.add_lt_top.mp h).1⟩

end SGPT.Toric

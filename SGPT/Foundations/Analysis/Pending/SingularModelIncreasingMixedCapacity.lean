import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedGap
import SGPT.Foundations.Analysis.Pending.StrictReferenceCapacityComparison

set_option autoImplicit false

/-!
# Actual uniform mixed capacity control in a singular box

Lu's actual positive finite-family capacity mechanism, applied to a fixed
singular pointwise box. Genuine references and their strict scaling margin
produce uniform zero-reference capacity control; no measure modulus is an
input. No model or boundedness of any individual potential is required.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelIncreasingMixedCapacity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
open GlobalMultilinearExpansion MixedSummandCapacityDomination ThetaCapacity
open CoalescingMixedCapacity StrictReferenceCapacityComparison CapacityWeightedConvergence
open SingularModelFiniteEnergyMixedGap

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual positive five-family expansion controls every binary mixed
measure in a pointwise box by the capacity of one fixed genuine reference. -/
theorem binaryMixedMeasure_apply_le_commonReferenceCapacity
    {θ : ClosedRealOneOneForm n M} (hθ : θ.val.IsSemipositive)
    {a b r : M → EReal}
    (hb : IsThetaPshPotential θ.val b) (hr : IsThetaPshPotential θ.val r)
    (har : a ≤ r) (hrb : r ≤ b) {B : ℝ} (hB : 0 ≤ B)
    (hba : ∀ x, b x ≤ a x + (B : EReal)) (σ : Fin n → Bool) (E : Set M) :
    binaryMixedMeasure hr hb σ E ≤ ENNReal.ofReal ((5 * (B + 1)) ^ n) *
      thetaCapacity θ (commonReference b b b b) E := by
  classical
  let F := fivePotentialFamily b b b b
  let G := fivePotentialFamily r b r b
  have hF := isThetaPshPotential_fivePotentialFamily hθ hb hb hb hb
  have hG := isThetaPshPotential_fivePotentialFamily hθ hr hb hr hb
  have hself : ∀ f : M → EReal, ∀ x, f x ≤ f x + (B : EReal) := by
    intro f x
    simpa only [add_zero] using add_le_add (le_refl (f x)) (EReal.coe_nonneg.mpr hB)
  have hbox : ∀ x, b x ≤ r x + (B : EReal) := fun x =>
    (hba x).trans (add_le_add (har x) le_rfl)
  have hGF : ∀ i, G i ≤ F i := by
    intro i
    fin_cases i
    · exact hrb
    · exact le_rfl
    · exact hrb
    · exact le_rfl
    · exact le_rfl
  have hFG : ∀ i x, F i x ≤ G i x + (B : EReal) := by
    intro i
    fin_cases i
    · exact hbox
    · exact hself b
    · exact hbox
    · exact hself b
    · exact hself (fun _ => 0)
  let s : Fin n → Fin 5 := fun i => if σ i then 0 else 1
  have hs : ∀ i, s i ∈ (Finset.univ : Finset (Fin 5)) := fun _ => Finset.mem_univ _
  have hC : 1 ≤ B + 1 := by linarith
  have hBC : ∑ i ∈ (Finset.univ : Finset (Fin 5)), (1 / 5 : ℝ) * B ≤ B + 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have h := selectedMixedMeasure_apply_le_capacity_of_box Finset.univ_nonempty
    (fun _ : Fin 5 => (by norm_num : (0 : ℝ) < 1 / 5)) hF hG hGF hFG hC hBC s hs E
  have hpot : (fun i => G (s i)) = fun i => if σ i then r else b := by
    funext i
    cases hσ : σ i <;> simp [G, s, fivePotentialFamily, hσ]
  have hmeasure : globalMixedMeasure (fun _ : Fin n => θ) (fun i => G (s i))
      (fun i => (hG (s i)).1) = binaryMixedMeasure hr hb σ := by
    exact GlobalDiagonalScaling.globalMixedMeasure_congr rfl hpot _ _
  simp only [sumForm_five_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  change ENNReal.ofReal ((1 / 5 : ℝ) ^ n) *
    globalMixedMeasure (fun _ : Fin n => θ) (fun i => G (s i))
      (fun i => (hG (s i)).1) E ≤ ENNReal.ofReal ((B + 1) ^ n) *
      thetaCapacity θ (commonReference b b b b) E at h
  rw [hmeasure] at h
  have hcancel : ENNReal.ofReal ((5 : ℝ) ^ n) * ENNReal.ofReal ((1 / 5 : ℝ) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    norm_num
  calc
    binaryMixedMeasure hr hb σ E = ENNReal.ofReal ((5 : ℝ) ^ n) *
        (ENNReal.ofReal ((1 / 5 : ℝ) ^ n) * binaryMixedMeasure hr hb σ E) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ ENNReal.ofReal ((5 : ℝ) ^ n) *
        (ENNReal.ofReal ((B + 1) ^ n) * thetaCapacity θ (commonReference b b b b) E) :=
      mul_le_mul_of_nonneg_left h zero_le
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]

/-- A fixed genuine margin and actual positive mixed domination produce a
uniform zero-reference capacity modulus for all measures in a singular box. -/
theorem uniformCapacityControl_binaryMixedMeasure_of_box
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    (hθ : θ.val.IsSemipositive) {a b : M → EReal} {u : ℕ → M → EReal}
    (hb : IsThetaPshPotential θ.val b)
    (hu : ∀ j, IsThetaPshPotential θ.val (u j))
    (hax : ∀ j, a ≤ u j) (hxb : ∀ j, u j ≤ b) (hb0 : b ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hba : ∀ x, b x ≤ a x + (B : EReal))
    (σ : Fin n → Bool) :
    UniformCapacityControl (thetaCapacity θ (fun _ => 0))
      (fun j => binaryMixedMeasure (hu j) hb σ) (diagonalPotentialMeasure θ b hb) := by
  have hV := isThetaPshPotential_commonReference hθ hb hb hb hb
  have hV0 := commonReference_le_zero hb0 hb0 hb0 hb0
  apply uniformCapacityControl_of_strictReference omega hθ hV hV0
    (by norm_num : (1 : ℝ) < 6 / 5)
    (isThetaPshPotential_scaled_commonReference hθ hb hb hb hb)
    (L := (5 * (B + 1)) ^ n) (by positivity)
  · intro j E
    exact binaryMixedMeasure_apply_le_commonReferenceCapacity hθ hb (hu j)
      (hax j) (hxb j) hB hba σ E
  · intro E
    have hab : a ≤ b := (hax 0).trans (hxb 0)
    have h := binaryMixedMeasure_apply_le_commonReferenceCapacity hθ hb hb
      hab le_rfl hB hba σ E
    simpa only [binaryMixedMeasure, ite_self, diagonalPotentialMeasure] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelIncreasingMixedCapacity

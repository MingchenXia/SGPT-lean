import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.RelativeEnergy
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

set_option autoImplicit false

/-! # Actual endpoint mixed mass polynomials for convex combinations

SGPT PDF0233--0234, finite-selector adaptation of the actual binomial
expansion. Actual global mixed-product symmetry and polynomial calculus
produce the measure identification and real mass polynomial internally.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination

open FirstPass FirstPass.PositiveClasses RelativeEnergy GlobalNonPluripolar
  GlobalMultilinearExpansion GlobalDiagonalScaling MixedMassProductCalculus
  ThetaPshConvexCombination

noncomputable section

private theorem exists_perm_binary {n : ℕ} (σ : Fin n → Bool) (j : Fin (n + 1))
    (hj : Fintype.card {i : Fin n // σ i = true} = j.val) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, σ (e i) = decide (i.val < j.val) := by
  classical
  let b : Fin n → Bool := fun i => decide (i.val < j.val)
  have hbt : Fintype.card {i : Fin n // b i = true} = j.val := by
    simp only [Fintype.card_subtype, b, decide_eq_true_eq]
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt_succ j.isLt)]
  have hfalse (q : Fin n → Bool) :
      Fintype.card {i : Fin n // q i = false} =
        n - Fintype.card {i : Fin n // q i = true} := by
    have h := Fintype.card_subtype_compl (fun i : Fin n => q i = true)
    simpa only [Bool.eq_false_eq_not_eq_true, Fintype.card_fin] using h
  have hcard (c : Bool) : Fintype.card {i : Fin n // b i = c} =
      Fintype.card {i : Fin n // σ i = c} := by
    cases c
    · rw [hfalse, hfalse, hbt, hj]
    · exact hbt.trans hj.symm
  let ef : ∀ c : Bool, {i : Fin n // b i = c} ≃ {i : Fin n // σ i = c} :=
    fun c => Fintype.equivOfCardEq (hcard c)
  exact ⟨Equiv.ofFiberEquiv ef, fun i => Equiv.ofFiberEquiv_map ef i⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- True finite fiber permutations and actual mixed-product slot symmetry
identify any selected binary tuple with the corresponding endpoint measure. -/
theorem globalMixedMeasure_binary_eq_endpointMixedMeasure
    {θ : ClosedRealOneOneForm n M} {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (σ : Fin n → Bool) (j : Fin (n + 1))
    (hj : Fintype.card {i : Fin n // σ i = true} = j.val) :
    globalMixedMeasure (fun _ : Fin n => θ) (fun i => if σ i then u else p)
      (fun i => by split_ifs <;> first | exact hu.1 | exact hp.1) =
        endpointMixedMeasure θ p u hp hu j := by
  classical
  let P : Fin n → M → EReal := fun i => if σ i then u else p
  have hP : ∀ i, ThetaPlurisubharmonic θ.val (P i) := by
    intro i
    dsimp only [P]
    split_ifs <;> first | exact hu.1 | exact hp.1
  obtain ⟨e, he⟩ := exists_perm_binary σ j hj
  have ht : (fun i => P (e i)) = endpointMixedPotential j u p := by
    funext i
    simp only [P, he, decide_eq_true_eq, endpointMixedPotential]
  have hperm := GlobalSlotPerm.globalMixedMeasure_perm hP e
  have hmeas := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple ht
    (fun i => hP (e i))
    (endpointMixedPotential_thetaPlurisubharmonic θ j u p hu hp)
  exact hperm.symm.trans hmeas

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Genuine PSH convexity includes both coefficient endpoints, with actual
extended-real zero coefficients interpreted by the defining convention. -/
theorem isThetaPshPotential_convexComb_closed {theta : SmoothRealForm n M 2}
    {u p : M → EReal} (hu : IsThetaPshPotential theta u)
    (hp : IsThetaPshPotential theta p) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsThetaPshPotential theta (convexComb a u p) := by
  by_cases h0 : a = 0
  · subst a
    have hq : convexComb 0 u p = p := by
      funext x
      simp only [convexComb, EReal.coe_zero, zero_mul, sub_zero, EReal.coe_one,
        one_mul, zero_add]
    rw [hq]
    exact hp
  by_cases h1 : a = 1
  · subst a
    have hq : convexComb 1 u p = u := by
      funext x
      simp only [convexComb, EReal.coe_one, one_mul, sub_self, EReal.coe_zero,
        zero_mul, add_zero]
    rw [hq]
    exact hu
  exact isThetaPshPotential_convexComb hu hp (lt_of_le_of_ne ha0 (Ne.symm h0))
    (lt_of_le_of_ne ha1 h1)

/-- Nonnegative slot weights, including zeros, give the actual finite
selector polynomial for every endpoint mass of a genuine convex combination. -/
theorem endpointMixedMass_convexComb_eq_sum (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (j : Fin (n + 1)) :
    (endpointMixedMass θ p (convexComb a u p) hp
      (isThetaPshPotential_convexComb_closed hu hp ha0 ha1) j).toReal =
      ∑ σ : Fin n → Bool,
        (∏ i, if i.val < j.val then (if σ i then a else 1 - a)
          else (if σ i then 0 else 1)) *
        (MixedMass.globalMixedMass (fun _ : Fin n => θ) (fun i => if σ i then u else p)
          (fun i => by split_ifs <;> first | exact hu.1 | exact hp.1)).toReal := by
  classical
  let pots : Bool → M → EReal := fun b => if b then u else p
  let c : Fin n → Bool → ℝ := fun i b =>
    if i.val < j.val then (if b then a else 1 - a) else (if b then 0 else 1)
  have hpots (b : Bool) : IsThetaPshPotential θ.val (pots b) := by
    cases b
    · exact hp
    · exact hu
  have hc : ∀ i b, 0 ≤ c i b := by
    intro i b
    dsimp only [c]
    split_ifs <;> first | exact ha0 | exact sub_nonneg.mpr ha1 | norm_num
  have hF : (fun i : Fin n => sumForm Finset.univ (c i) (fun _ : Bool => θ)) =
      fun _ : Fin n => θ := by
    funext i
    by_cases hi : i.val < j.val
    · simp only [sumForm, Fintype.sum_bool, c, if_pos hi, Bool.false_eq_true,
        ↓reduceIte]
      rw [← add_smul, show a + (1 - a) = 1 by ring, one_smul]
    · simp [sumForm, c, hi]
  have hQ : (fun i => sumPot Finset.univ (c i) pots) =
      endpointMixedPotential j (convexComb a u p) p := by
    funext i x
    by_cases hi : i.val < j.val
    · simp only [sumPot, Fintype.sum_bool, c, pots, if_pos hi, Bool.false_eq_true,
        ↓reduceIte, endpointMixedPotential, convexComb]
    · simp [sumPot, c, pots, hi, endpointMixedPotential]
  have h := globalMixedMass_sumPot_expand_toReal omega hc hpots
  unfold MixedMass.globalMixedMass at h
  rw [globalMixedMeasure_congr hF hQ _
    (endpointMixedPotential_thetaPlurisubharmonic θ j (convexComb a u p) p
      (isThetaPshPotential_convexComb_closed hu hp ha0 ha1) hp)] at h
  simpa only [endpointMixedMass, endpointMixedMeasure, MixedMass.globalMixedMass, c, pots]
    using h

end

end SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination

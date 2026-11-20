import SGPT.Foundations.Analysis.Pending.RemainingSlotCanonicalPolarization

set_option autoImplicit false

/-!
# Actual singular integration by parts with independent mixed slots

Lu, arXiv:2005.04264v1, Theorem 1.2. Actual general-background
one-slot IBP, positive remaining-subset expansion and actual slot symmetry
produce the complete mixed identity, with no IBP or polynomial premise.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.FullMixedSingularIntegrationByParts

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
open RelativeEnergyIntegrability GeneralBackgroundOneSlotIntegrationByParts
open RemainingSlotCanonicalPolarization RemainingSlotPolarizationAlgebra

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Produce genuine updated slots from the original genuine remaining currents. -/
theorem isThetaPshPotential_update {eta : Fin n → ClosedRealOneOneForm n M}
    {psi : Fin n → M → EReal} (k : Fin n)
    (hother : ∀ i, i ≠ k → IsThetaPshPotential (eta i).val (psi i))
    {alpha : ClosedRealOneOneForm n M} {r : M → EReal}
    (hr : IsThetaPshPotential alpha.val r) :
    ∀ i, IsThetaPshPotential (Function.update eta k alpha i).val (Function.update psi k r i) := by
  intro i
  by_cases hi : i = k
  · subst hi
    simpa only [Function.update_self] using hr
  · simpa only [Function.update_of_ne hi] using hother i hi

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Actual mixed product after replacing only the distinguished original current. -/
def updatedMixedMeasure {eta : Fin n → ClosedRealOneOneForm n M}
    {psi : Fin n → M → EReal} (k : Fin n)
    (hother : ∀ i, i ≠ k → IsThetaPshPotential (eta i).val (psi i))
    {alpha : ClosedRealOneOneForm n M} {r : M → EReal}
    (hr : IsThetaPshPotential alpha.val r) : Measure M :=
  globalMixedMeasure (Function.update eta k alpha) (Function.update psi k r)
    (fun i => (isThetaPshPotential_update k hother hr i).1)

end

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Actual mixed IBP for independent labeled remaining currents. -/
theorem integral_sub_selectedRemainingMeasure_symm (omega : KahlerBackground (m + 1) M)
    {alpha beta : ClosedRealOneOneForm (m + 1) M}
    {theta : Fin m → ClosedRealOneOneForm (m + 1) M}
    {a b p q : M → EReal} {phi : Fin m → M → EReal}
    (ha : IsThetaPshPotential alpha.val a) (hb : IsThetaPshPotential alpha.val b)
    (hp : IsThetaPshPotential beta.val p) (hq : IsThetaPshPotential beta.val q)
    (hphi : ∀ j, IsThetaPshPotential (theta j).val (phi j))
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ)
    (k : Fin (m + 1)) :
    ((∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂selectedRemainingMeasure ha hphi (remainingMap k id)) -
     (∫ x, canonicalERealDiffToReal (p x) (q x)
        ∂selectedRemainingMeasure hb hphi (remainingMap k id))) =
    (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂selectedRemainingMeasure hp hphi (remainingMap k id)) -
    (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂selectedRemainingMeasure hq hphi (remainingMap k id)) := by
  classical
  have hS (S : Finset (Fin m)) := integral_sub_referenceMixedMeasure_symm
    omega ha hb hp hq (isThetaPshPotential_remainingSubset hphi S) hab hpq k
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl fun S _ =>
    congrArg (fun t : ℝ => (-1 : ℝ) ^ (m - S.card) * t) (hS S)
  simp_rw [mul_sub, Finset.sum_sub_distrib] at h
  rw [sum_signed_integral_referenceSubset omega hp hq hpq ha hphi k,
    sum_signed_integral_referenceSubset omega hp hq hpq hb hphi k,
    sum_signed_integral_referenceSubset omega ha hb hab hp hphi k,
    sum_signed_integral_referenceSubset omega ha hb hab hq hphi k] at h
  rw [← mul_sub, ← mul_sub] at h
  have hfac : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  exact mul_left_cancel₀ hfac h

omit [BorelSpace M] in
/-- The labeled original mixed tuple is the actual arbitrary updated tuple. -/
theorem selectedRemainingMeasure_eq_updated
    {eta : Fin (m + 1) → ClosedRealOneOneForm (m + 1) M}
    {psi : Fin (m + 1) → M → EReal} (k : Fin (m + 1))
    (hother : ∀ i, i ≠ k → IsThetaPshPotential (eta i).val (psi i))
    {alpha : ClosedRealOneOneForm (m + 1) M} {r : M → EReal}
    (hr : IsThetaPshPotential alpha.val r) :
    selectedRemainingMeasure hr (fun j => hother (k.succAbove j) (Fin.succAbove_ne k j))
        (remainingMap k id) = updatedMixedMeasure k hother hr := by
  refine globalMixedMeasure_congr ?_ ?_ _ _
  · funext i
    obtain ⟨o, rfl⟩ := (finSuccEquiv' k).symm.surjective i
    cases o with
    | none => simp [remainingMap, labelData]
    | some j => simp [remainingMap, labelData, Fin.succAbove_ne]
  · funext i
    obtain ⟨o, rfl⟩ := (finSuccEquiv' k).symm.surjective i
    cases o with
    | none => simp [remainingMap, labelData]
    | some j => simp [remainingMap, labelData, Fin.succAbove_ne]

end

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Lu's full singular mixed IBP: genuine independent remaining currents,
genuine weight pairs and their same singularity types are the only inputs. -/
theorem integral_sub_mixed_update_symm (omega : KahlerBackground n M)
    {eta : Fin n → ClosedRealOneOneForm n M} {psi : Fin n → M → EReal}
    (k : Fin n) (hother : ∀ i, i ≠ k → IsThetaPshPotential (eta i).val (psi i))
    {alpha beta : ClosedRealOneOneForm n M} {a b p q : M → EReal}
    (ha : IsThetaPshPotential alpha.val a) (hb : IsThetaPshPotential alpha.val b)
    (hp : IsThetaPshPotential beta.val p) (hq : IsThetaPshPotential beta.val q)
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ) :
    ((∫ x, canonicalERealDiffToReal (p x) (q x) ∂updatedMixedMeasure k hother ha) -
     (∫ x, canonicalERealDiffToReal (p x) (q x) ∂updatedMixedMeasure k hother hb)) =
    (∫ x, canonicalERealDiffToReal (a x) (b x) ∂updatedMixedMeasure k hother hp) -
    (∫ x, canonicalERealDiffToReal (a x) (b x) ∂updatedMixedMeasure k hother hq) := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ m =>
    have h := integral_sub_selectedRemainingMeasure_symm omega ha hb hp hq
      (fun j => hother (k.succAbove j) (Fin.succAbove_ne k j)) hab hpq k
    rw [selectedRemainingMeasure_eq_updated k hother ha,
      selectedRemainingMeasure_eq_updated k hother hb,
      selectedRemainingMeasure_eq_updated k hother hp,
      selectedRemainingMeasure_eq_updated k hother hq] at h
    exact h

end

end SGPT.Foundations.Analysis.Pending.FullMixedSingularIntegrationByParts

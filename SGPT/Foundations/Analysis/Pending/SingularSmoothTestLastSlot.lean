import SGPT.Foundations.Analysis.Pending.SingularSmoothTestStokes
import SGPT.Foundations.Analysis.Pending.GlobalSlotPerm

set_option autoImplicit false

/-! # The actual compact Stokes hybrid has a genuine last-slot model -/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularSmoothTestLastSlot

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalSlotPerm GlobalDiagonalScaling
  SingularSmoothTestStokes FullMixedSingularIntegrationByParts DeepCoincidenceIntegrationByParts

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]

/-- The actual singular backgrounds in the first slots and the test background in the last. -/
def lastHybridForms (α β : ClosedRealOneOneForm (n + 1) M) :
    Fin (n + 1) → ClosedRealOneOneForm (n + 1) M :=
  Function.update (fun _ => α) (Fin.last n) β

/-- The genuine k-prefix of singular potentials with the actual test potential in the last slot. -/
def lastHybridPotentials (k : Fin (n + 1)) (W Φ r : M → EReal) :
    Fin (n + 1) → M → EReal :=
  Function.update (prefixPotentialTuple k.val W Φ) (Fin.last n) r

/-- The actual last-slot hybrid is a genuine global PSH tuple. -/
theorem lastHybridThetaPlurisubharmonic {α β : ClosedRealOneOneForm (n + 1) M}
    {W Φ r : M → EReal} (hW : IsThetaPshPotential α.val W)
    (hΦ : IsThetaPshPotential α.val Φ) (hr : IsThetaPshPotential β.val r)
    (k : Fin (n + 1)) :
    ∀ i, ThetaPlurisubharmonic (lastHybridForms α β i).val (lastHybridPotentials k W Φ r i) := by
  classical
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    simpa only [lastHybridForms, lastHybridPotentials, Function.update_self] using hr.1
  · simp only [lastHybridForms, lastHybridPotentials, Function.update_of_ne hi]
    exact thetaPlurisubharmonic_prefixPotentialTuple α hW.1 hΦ.1 k.val i

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual canonical global mixed NP measure of the last-slot hybrid tuple. -/
def lastHybridMixedMeasure {α β : ClosedRealOneOneForm (n + 1) M}
    {W Φ r : M → EReal} (hW : IsThetaPshPotential α.val W)
    (hΦ : IsThetaPshPotential α.val Φ) (hr : IsThetaPshPotential β.val r)
    (k : Fin (n + 1)) : Measure M :=
  globalMixedMeasure (lastHybridForms α β) (lastHybridPotentials k W Φ r)
    (lastHybridThetaPlurisubharmonic hW hΦ hr k)

/-- Swapping the actual distinguished Stokes slot with the last gives the genuine last-slot hybrid measure. -/
theorem hybridUpdatedMixedMeasure_eq_last {α β : ClosedRealOneOneForm (n + 1) M}
    {W Φ r : M → EReal} (hW : IsThetaPshPotential α.val W)
    (hΦ : IsThetaPshPotential α.val Φ) (k : Fin (n + 1))
    (hr : IsThetaPshPotential β.val r) :
    hybridUpdatedMixedMeasure hW hΦ k hr = lastHybridMixedMeasure hW hΦ hr k := by
  classical
  let η₀ := Function.update (fun _ : Fin (n + 1) => α) k β
  let s₀ := Function.update (prefixPotentialTuple k.val W Φ) k r
  have hother (i : Fin (n + 1)) (_hi : i ≠ k) :
      IsThetaPshPotential α.val (prefixPotentialTuple k.val W Φ i) := by
    dsimp only [prefixPotentialTuple]
    split_ifs
    · exact hW
    · exact hΦ
  have hs₀ (i : Fin (n + 1)) : ThetaPlurisubharmonic (η₀ i).val (s₀ i) :=
    (isThetaPshPotential_update k hother hr i).1
  have hold : hybridUpdatedMixedMeasure hW hΦ k hr = globalMixedMeasure η₀ s₀ hs₀ := rfl
  let σ := Equiv.swap k (Fin.last n)
  have hforms : (fun i => η₀ (σ i)) = lastHybridForms α β := by
    funext i
    by_cases hi : i = Fin.last n
    · subst i
      simp only [σ, Equiv.swap_apply_right, η₀, lastHybridForms, Function.update_self]
    · by_cases hik : i = k
      · subst i
        have hk : Fin.last n ≠ k := Ne.symm hi
        simp only [σ, Equiv.swap_apply_left, η₀, lastHybridForms,
          Function.update_of_ne hi, Function.update_of_ne hk]
      · simp only [σ, Equiv.swap_apply_of_ne_of_ne hik hi, η₀, lastHybridForms,
          Function.update_of_ne hi, Function.update_of_ne hik]
  have hslots : (fun i => s₀ (σ i)) = lastHybridPotentials k W Φ r := by
    funext i
    by_cases hi : i = Fin.last n
    · subst i
      simp only [σ, Equiv.swap_apply_right, s₀, lastHybridPotentials, Function.update_self]
    · by_cases hik : i = k
      · subst i
        have hk : Fin.last n ≠ k := Ne.symm hi
        have hn : ¬ (Fin.last n).val < k.val := by
          simp only [Fin.val_last]
          omega
        simp only [σ, Equiv.swap_apply_left, s₀, lastHybridPotentials,
          Function.update_of_ne hi, Function.update_of_ne hk,
          prefixPotentialTuple, hn, if_false, lt_self_iff_false]
      · simp only [σ, Equiv.swap_apply_of_ne_of_ne hik hi, s₀, lastHybridPotentials,
          Function.update_of_ne hi, Function.update_of_ne hik]
  rw [hold]
  exact (globalMixedMeasure_perm hs₀ σ).symm.trans
    (globalMixedMeasure_congr hforms hslots _ (lastHybridThetaPlurisubharmonic hW hΦ hr k))

end

end SGPT.Foundations.Analysis.Pending.SingularSmoothTestLastSlot

import SGPT.Foundations.Analysis.Pending.GeneralBackgroundOneSlotIntegrationByParts
import SGPT.Foundations.Analysis.Pending.CanonicalMixedIntegralExpansion
import SGPT.Foundations.Analysis.Pending.RemainingSlotPolarizationAlgebra
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination

set_option autoImplicit false

/-!
# Actual canonical integral polarization retaining a distinguished current

Lu, arXiv:2005.04264v1, proof of Theorem 1.2. Actual nonnegative
remaining-current subset expansions and permutations fixing the original slot.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.RemainingSlotCanonicalPolarization

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
open GlobalMultilinearExpansion MixedMassProductCalculus RelativeEnergyIntegrability
open MixedSummandCapacityDomination CanonicalMixedIntegralExpansion
open RemainingSlotPolarizationAlgebra GeneralBackgroundOneSlotIntegrationByParts

noncomputable section

/-- The distinguished datum has label `none`; remaining data have labels `some j`. -/
def labelData {m : ℕ} {V : Type*} (r : V) (f : Fin m → V) (o : Option (Fin m)) : V :=
  o.elim r f

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine subset sums include the empty zero current, for any number of labels. -/
theorem isThetaPshPotential_remainingSubset
    {theta : Fin m → ClosedRealOneOneForm n M} {phi : Fin m → M → EReal}
    (hphi : ∀ j, IsThetaPshPotential (theta j).val (phi j)) (S : Finset (Fin m)) :
    IsThetaPshPotential (sumForm S (fun _ => 1) theta).val (sumPot S (fun _ => 1) phi) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have hz : sumPot (∅ : Finset (Fin m)) (fun _ => 1) phi = fun _ => 0 := by
      funext x
      simp [sumPot]
    rw [hz]
    simpa only [sumForm, Finset.sum_empty] using
      (LocalPotentials.isThetaPshPotential_zero_iff (0 : ClosedRealOneOneForm n M)).mpr
        (fun _ _ _ _ => le_rfl)
  · exact isThetaPshPotential_sumPot hS (fun _ => one_pos) hphi

/-- Every labeled current is genuine, including the original distinguished one. -/
theorem isThetaPshPotential_labelData {alpha : ClosedRealOneOneForm n M}
    {theta : Fin m → ClosedRealOneOneForm n M} {r : M → EReal}
    {phi : Fin m → M → EReal} (hr : IsThetaPshPotential alpha.val r)
    (hphi : ∀ j, IsThetaPshPotential (theta j).val (phi j)) :
    ∀ o, IsThetaPshPotential (labelData alpha theta o).val (labelData r phi o) := by
  intro o
  cases o with
  | none => exact hr
  | some j => exact hphi j

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Actual mixed measure of a selected tuple of genuine labeled currents. -/
def selectedRemainingMeasure {alpha : ClosedRealOneOneForm n M}
    {theta : Fin m → ClosedRealOneOneForm n M} {r : M → EReal}
    {phi : Fin m → M → EReal} (hr : IsThetaPshPotential alpha.val r)
    (hphi : ∀ j, IsThetaPshPotential (theta j).val (phi j))
    (h : Fin n → Option (Fin m)) : Measure M :=
  globalMixedMeasure (fun i => labelData alpha theta (h i))
    (fun i => labelData r phi (h i))
    (fun i => (isThetaPshPotential_labelData hr hphi (h i)).1)

/-- Actual selected products are invariant under true ambient slot permutations. -/
theorem selectedRemainingMeasure_perm {alpha : ClosedRealOneOneForm n M}
    {theta : Fin m → ClosedRealOneOneForm n M} {r : M → EReal}
    {phi : Fin m → M → EReal} (hr : IsThetaPshPotential alpha.val r)
    (hphi : ∀ j, IsThetaPshPotential (theta j).val (phi j))
    (h : Fin n → Option (Fin m)) (sigma : Equiv.Perm (Fin n)) :
    selectedRemainingMeasure hr hphi (fun i => h (sigma i)) =
      selectedRemainingMeasure hr hphi h :=
  GlobalSlotPerm.globalMixedMeasure_perm
    (fun i => (isThetaPshPotential_labelData hr hphi (h i)).1) sigma

end

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Every remaining permutation coefficient is the actual original mixed product. -/
theorem selectedRemainingMeasure_remainingMap_perm
    {alpha : ClosedRealOneOneForm (m + 1) M}
    {theta : Fin m → ClosedRealOneOneForm (m + 1) M} {r : M → EReal}
    {phi : Fin m → M → EReal} (hr : IsThetaPshPotential alpha.val r)
    (hphi : ∀ j, IsThetaPshPotential (theta j).val (phi j))
    (k : Fin (m + 1)) (sigma : Equiv.Perm (Fin m)) :
    selectedRemainingMeasure hr hphi (remainingMap k sigma) =
      selectedRemainingMeasure hr hphi (remainingMap k id) := by
  have eh : remainingMap k sigma = fun i => finSuccEquiv' k (remainingPermutation k sigma i) :=
    funext (remainingMap_perm k sigma)
  have eid : remainingMap k id = finSuccEquiv' k := by
    funext i
    simp [remainingMap]
  rw [eh, eid]
  exact selectedRemainingMeasure_perm hr hphi (finSuccEquiv' k) (remainingPermutation k sigma)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual indicator form sums retain the original distinguished background. -/
theorem sumForm_remainingSubsetCoeff (k : Fin (m + 1)) (S : Finset (Fin m))
    (alpha : ClosedRealOneOneForm (m + 1) M)
    (theta : Fin m → ClosedRealOneOneForm (m + 1) M) :
    (fun i => sumForm Finset.univ (remainingSubsetCoeff k S i) (labelData alpha theta)) =
      Function.update (fun _ => sumForm S (fun _ => 1) theta) k alpha := by
  classical
  funext i
  obtain ⟨o, rfl⟩ := (finSuccEquiv' k).symm.surjective i
  cases o with
  | none => simp [sumForm, Fintype.sum_option, remainingSubsetCoeff, labelData]
  | some j =>
    have hne : k.succAbove j ≠ k := Fin.succAbove_ne _ _
    simp [sumForm, Fintype.sum_option, remainingSubsetCoeff, labelData, hne]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual indicator potential sums retain the original distinguished potential. -/
theorem sumPot_remainingSubsetCoeff (k : Fin (m + 1)) (S : Finset (Fin m))
    (r : M → EReal) (phi : Fin m → M → EReal) :
    (fun i => sumPot Finset.univ (remainingSubsetCoeff k S i) (labelData r phi)) =
      Function.update (fun _ => sumPot S (fun _ => 1) phi) k r := by
  classical
  funext i x
  obtain ⟨o, rfl⟩ := (finSuccEquiv' k).symm.surjective i
  cases o with
  | none => simp [sumPot, Fintype.sum_option, remainingSubsetCoeff, labelData]
  | some j =>
    have hne : k.succAbove j ≠ k := Fin.succAbove_ne _ _
    simp [sumPot, Fintype.sum_option, remainingSubsetCoeff, labelData, hne, apply_ite, ite_mul]

/-- Produce the actual canonical integral expansion of each remaining subset sum. -/
theorem integral_referenceSubset_eq_sum_selected (omega : KahlerBackground (m + 1) M)
    {eta xi : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential eta u) (hv : IsThetaPshPotential xi v)
    (htype : SameSingularityTypeOn u v univ)
    {alpha : ClosedRealOneOneForm (m + 1) M}
    {theta : Fin m → ClosedRealOneOneForm (m + 1) M} {r : M → EReal}
    {phi : Fin m → M → EReal} (hr : IsThetaPshPotential alpha.val r)
    (hphi : ∀ j, IsThetaPshPotential (theta j).val (phi j))
    (k : Fin (m + 1)) (S : Finset (Fin m)) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂referenceMixedMeasure (isThetaPshPotential_remainingSubset hphi S) hr k) =
    ∑ g : Fin m → Fin m with ∀ j, g j ∈ S,
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂selectedRemainingMeasure hr hphi (remainingMap k g) := by
  classical
  have hexp := integral_canonicalDiff_sumPot_expand omega hu hv htype
    (remainingSubsetCoeff_nonneg k S) (isThetaPshPotential_labelData hr hphi)
  have hmeasure := globalMixedMeasure_congr (sumForm_remainingSubsetCoeff k S alpha theta)
    (sumPot_remainingSubsetCoeff k S r phi)
    (fun i => thetaPlurisubharmonic_sumPot_of_nonneg
      (remainingSubsetCoeff_nonneg k S i)
      (fun o => (isThetaPshPotential_labelData hr hphi o).1))
    (fun i => (isThetaPshPotential_referenceTuple
      (isThetaPshPotential_remainingSubset hphi S) hr k i).1)
  calc
    _ = ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure
          (fun i => sumForm Finset.univ (remainingSubsetCoeff k S i) (labelData alpha theta))
          (fun i => sumPot Finset.univ (remainingSubsetCoeff k S i) (labelData r phi))
          (fun i => thetaPlurisubharmonic_sumPot_of_nonneg
            (remainingSubsetCoeff_nonneg k S i)
            (fun o => (isThetaPshPotential_labelData hr hphi o).1)) :=
      congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (u x) (v x) ∂mu) hmeasure.symm
    _ = ∑ h, (∏ i, remainingSubsetCoeff k S i (h i)) *
        ∫ x, canonicalERealDiffToReal (u x) (v x) ∂selectedRemainingMeasure hr hphi h := hexp
    _ = _ := sum_remainingSubsetCoeff k S
      (fun h => ∫ x, canonicalERealDiffToReal (u x) (v x) ∂selectedRemainingMeasure hr hphi h)

/-- Actual canonical subset integrals recover the original independent mixed currents. -/
theorem sum_signed_integral_referenceSubset (omega : KahlerBackground (m + 1) M)
    {eta xi : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential eta u) (hv : IsThetaPshPotential xi v)
    (htype : SameSingularityTypeOn u v univ)
    {alpha : ClosedRealOneOneForm (m + 1) M}
    {theta : Fin m → ClosedRealOneOneForm (m + 1) M} {r : M → EReal}
    {phi : Fin m → M → EReal} (hr : IsThetaPshPotential alpha.val r)
    (hphi : ∀ j, IsThetaPshPotential (theta j).val (phi j)) (k : Fin (m + 1)) :
    ∑ S : Finset (Fin m), (-1 : ℝ) ^ (m - S.card) *
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂referenceMixedMeasure (isThetaPshPotential_remainingSubset hphi S) hr k =
    (m.factorial : ℝ) * ∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂selectedRemainingMeasure hr hphi (remainingMap k id) := by
  classical
  simp_rw [integral_referenceSubset_eq_sum_selected omega hu hv htype hr hphi]
  apply PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul
  intro sigma
  exact congrArg (fun mu : Measure M => ∫ x, canonicalERealDiffToReal (u x) (v x) ∂mu)
    (selectedRemainingMeasure_remainingMap_perm hr hphi k sigma)

end

end SGPT.Foundations.Analysis.Pending.RemainingSlotCanonicalPolarization

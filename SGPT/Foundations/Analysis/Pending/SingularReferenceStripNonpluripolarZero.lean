import SGPT.Foundations.Analysis.Pending.BedfordTaylorStripCovariance
import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

set_option autoImplicit false

/-! # Actual singular base pullbacks have zero canonical strip non-pluripolar measure -/

open Set MeasureTheory TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.SingularReferenceStripNonpluripolarZero

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  FirstPass.MixedNonPluripolar BedfordTaylorStripCovariance BedfordTaylor
  MixedMongeAmpere MixedNonPluripolar

noncomputable section

variable {n : ℕ} {A : Opens (ComplexModel n)} {S : Set ℂ}

/-- The actual extended-real truncation is performed before taking the real representative, and commutes with the actual projection. -/
theorem truncationReal_comp_stripFst (u : ComplexModel n → EReal) (k : ℕ) :
    truncationReal (fun q => u (stripFst n q)) k =
      fun q => truncationReal u k (stripFst n q) := rfl

/-- Actual extended-real PSH, including poles, pulls back by the genuine complex-linear strip projection. -/
theorem plurisubharmonicOn_comp_stripFst (hS : IsOpen S)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u A) :
    PlurisubharmonicOn (fun q => u (stripFst n q)) (stripLift A S hS) :=
  HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (stripLift A S hS).isOpen
    (stripFst n).differentiable.differentiableOn (fun _ hq => hq.1) hu

/-- The independently constructed canonical bounded mixed truncation measure is the genuine zero strip BT limit. -/
theorem canonicalMixedBedfordTaylorMeasure_truncation_comp_stripFst_eq_zero
    (hS : IsOpen S) {u : Fin (n + 1) → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) A) (k : ℕ) :
    canonicalMixedBedfordTaylorMeasure (stripLift A S hS)
      (mixedTruncationReal (fun i q => u i (stripFst n q)) k)
      (mixedTruncationReal_isLocallyBounded
        (fun i => plurisubharmonicOn_comp_stripFst hS (hu i)) k) = 0 := by
  have hb := isBTLimit_comp_stripFst_eq_zero hS
    (fun i => truncationReal_isLocallyBoundedPshOn (hu i) k)
  have hc := IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (canonicalMixedBedfordTaylorMeasure_spec (stripLift A S hS)
      (mixedTruncationReal (fun i q => u i (stripFst n q)) k)
      (mixedTruncationReal_isLocallyBounded
        (fun i => plurisubharmonicOn_comp_stripFst hS (hu i)) k))
  exact hc.unique hb

/-- Restricting each actual canonical zero BT measure to its genuine common strict truncation locus gives zero. -/
theorem mixedTruncationMeasure_comp_stripFst_eq_zero
    (hS : IsOpen S) {u : Fin (n + 1) → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) A) (k : ℕ) :
    mixedTruncationMeasure (stripLift A S hS) (fun i q => u i (stripFst n q))
      (fun i => plurisubharmonicOn_comp_stripFst hS (hu i)) k = 0 := by
  unfold mixedTruncationMeasure
  rw [canonicalMixedBedfordTaylorMeasure_truncation_comp_stripFst_eq_zero hS hu k]
  simp

/-- The genuine increasing limit of the actual zero truncation measures is zero for an arbitrary singular base tuple. -/
theorem mixedTruncationLimitMeasure_comp_stripFst_eq_zero
    (hS : IsOpen S) {u : Fin (n + 1) → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) A) :
    mixedTruncationLimitMeasure (stripLift A S hS) (fun i q => u i (stripFst n q))
      (fun i => plurisubharmonicOn_comp_stripFst hS (hu i)) = 0 := by
  apply Measure.ext
  intro s _
  simp only [Measure.coe_zero, Pi.zero_apply]
  apply (mixedTruncationLimitMeasure_zero_iff
    (fun i => plurisubharmonicOn_comp_stripFst hS (hu i)) s).mpr
  intro k
  rw [mixedTruncationMeasure_comp_stripFst_eq_zero hS hu k]
  rfl

/-- An actual singular reference potential pulled only from the base has zero actual diagonal mixed strip measure in every base dimension. -/
theorem mixedTruncationLimitMeasure_diagonal_comp_stripFst_eq_zero
    (hS : IsOpen S) {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u A) :
    mixedTruncationLimitMeasure (stripLift A S hS) (fun _ q => u (stripFst n q))
      (fun _ => plurisubharmonicOn_comp_stripFst hS hu) = 0 :=
  mixedTruncationLimitMeasure_comp_stripFst_eq_zero hS (fun _ => hu)

/-- Genuine diagonal identification gives the scalar NP equation; the strip dimension is always positive. -/
theorem truncationLimitMeasure_comp_stripFst_eq_zero
    (hS : IsOpen S) {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u A) :
    MongeAmpere.truncationLimitMeasure (stripLift A S hS) (fun q => u (stripFst n q))
      (plurisubharmonicOn_comp_stripFst hS hu) = 0 := by
  rw [← mixedTruncationLimitMeasure_diagonal (Nat.succ_pos n)
    (plurisubharmonicOn_comp_stripFst hS hu)]
  exact mixedTruncationLimitMeasure_diagonal_comp_stripFst_eq_zero hS hu

end

end SGPT.Foundations.Analysis.Pending.SingularReferenceStripNonpluripolarZero

import SGPT.PSH.HermitianComparisonOneFactor
import SGPT.Foundations.Analysis.Pending.PositiveCurrentBorelAddition

/-!
# Bounded Borel extension of actual distinguished-factor transgression

Residual forms on the majorizing correction patches have a genuine signed
positive presentation. Rearranging an unweighted current identity into an
equality of finite positive sums allows bounded Borel multiplication using
only its checked positive-current additivity. Smooth wedging is used only
with the resulting positive form before restoring each original sign.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms LocalBedfordTaylorLocality
  LocalBedfordTaylorSmooth LocalBedfordTaylorSmoothProductDensity
  PositiveCurrentBorelAddition CoordinateWedgeAssoc ConstantFormProducts TopDegreeDensity
open HermitianComparisonOneFactor

variable {n q : ℕ} {U : Opens (ComplexModel n)}

private theorem positive_sum {ι : Type*} [Fintype ι]
    (S : ι → LocalProductCurrent n U q) (hS : ∀ i, IsPositive (S i)) :
    IsPositive (∑ i, S i) := by
  intro κ _ γ φ hγ
  simp only [LinearMap.sum_apply, _root_.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_nonneg fun i _ => hS i κ γ φ hγ

/-- A difference identity among actual positive currents extends to every
locally bounded Borel weight by positive-current additivity. The premise is
the unweighted current identity, not the desired weighted conclusion. -/
theorem mulBorel_difference_of_positive_presentation {ι : Type*} [Fintype ι]
    {A B : LocalProductCurrent n U q} (hA : IsPositive A) (hB : IsPositive B)
    (S T : ι → LocalProductCurrent n U q)
    (hS : ∀ i, IsPositive (S i)) (hT : ∀ i, IsPositive (T i))
    (heq : A - B = ∑ i, (S i - T i))
    {f : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) :
    mulBorel A f - mulBorel B f = ∑ i, (mulBorel (S i) f - mulBorel (T i) f) := by
  have hbal : A + ∑ i, T i = B + ∑ i, S i := by
    rw [Finset.sum_sub_distrib] at heq
    have hh := sub_eq_sub_iff_add_eq_add.mp heq
    simpa only [add_comm] using hh
  have hw := congrArg (fun C : LocalProductCurrent n U q => mulBorel C f) hbal
  rw [mulBorel_add_currents hA (positive_sum T hT) hf hfb,
    mulBorel_add_currents hB (positive_sum S hS) hf hfb,
    mulBorel_finsetSum_positive Finset.univ T (fun i _ => hT i) hf hfb,
    mulBorel_finsetSum_positive Finset.univ S (fun i _ => hS i) hf hfb] at hw
  rw [Finset.sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using hw

private theorem wedgeForm_neg {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m) {α : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm h T hα.neg = -wedgeForm h T hα := by
  have hsm := wedgeForm_smul h T hα (-1)
  simpa only [neg_one_smul] using hsm

/-- The positive orientation of an actual smooth residual form. -/
def orientedForm (D : Residual n U) (orientation : Bool) :
    ComplexModel n → RealForm n (2 * D.degree) :=
  if orientation then D.form else fun z => -D.form z

theorem orientedForm_smooth (D : Residual n U) (orientation : Bool) :
    ContDiffOn ℝ ∞ (orientedForm D orientation) U := by
  cases orientation
  · exact D.smooth.neg
  · exact D.smooth

/-- One actual positive term in the oriented distinguished-slot expansion. -/
def orientedDdcCurrent (D : Residual n U) (orientation : Bool)
    (v : ComplexModel n → ℝ) : LocalProductCurrent n U 0 :=
  wedgeForm (r := 0) (k := D.degree) (Nat.zero_add D.degree)
    (ddcMul D.current v) (orientedForm_smooth D orientation)

theorem orientedDdcCurrent_isPositive (D : Residual n U) (orientation : Bool)
    (hform : ∀ z ∈ U, orientedForm D orientation z ∈ spCone D.degree)
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn U v) :
    IsPositive (orientedDdcCurrent D orientation v) :=
  isPositive_wedgeForm (Nat.zero_add D.degree)
    (isPositive_ddcMul D.positive D.closed hv).1 (orientedForm_smooth D orientation) hform

def residualDdcCurrent (D : Residual n U) (v : ComplexModel n → ℝ) :
    LocalProductCurrent n U 0 :=
  wedgeForm (r := 0) (k := D.degree) (Nat.zero_add D.degree) (ddcMul D.current v) D.smooth

def residualWeightedDdcCurrent (D : Residual n U) (v f : ComplexModel n → ℝ) :
    LocalProductCurrent n U 0 :=
  wedgeForm (r := 0) (k := D.degree) (Nat.zero_add D.degree)
    (mulBorel (ddcMul D.current v) f) D.smooth

private theorem oriented_difference (D : Residual n U) (orientation : Bool)
    (a b : ComplexModel n → ℝ) :
    orientedDdcCurrent D orientation (if orientation then b else a) -
      orientedDdcCurrent D orientation (if orientation then a else b) =
      residualDdcCurrent D b - residualDdcCurrent D a := by
  cases orientation
  · change wedgeForm (Nat.zero_add D.degree) (ddcMul D.current a) D.smooth.neg -
      wedgeForm (Nat.zero_add D.degree) (ddcMul D.current b) D.smooth.neg = _
    rw [wedgeForm_neg _ (ddcMul D.current a) D.smooth,
      wedgeForm_neg _ (ddcMul D.current b) D.smooth]
    unfold residualDdcCurrent
    abel_nf
  · rfl

private theorem oriented_weighted_difference (D : Residual n U) (orientation : Bool)
    (hform : ∀ z ∈ U, orientedForm D orientation z ∈ spCone D.degree)
    {a b f : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn U a) (hb : IsLocallyBoundedPshOn U b)
    (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) :
    mulBorel (orientedDdcCurrent D orientation (if orientation then b else a)) f -
      mulBorel (orientedDdcCurrent D orientation (if orientation then a else b)) f =
      residualWeightedDdcCurrent D b f - residualWeightedDdcCurrent D a f := by
  have hpa := (isPositive_ddcMul D.positive D.closed ha).1
  have hpb := (isPositive_ddcMul D.positive D.closed hb).1
  cases orientation
  · change mulBorel (wedgeForm (Nat.zero_add D.degree) (ddcMul D.current a) D.smooth.neg) f -
      mulBorel (wedgeForm (Nat.zero_add D.degree) (ddcMul D.current b) D.smooth.neg) f = _
    rw [mulBorel_wedgeForm _ hpa D.smooth.neg hform hf hfb,
      mulBorel_wedgeForm _ hpb D.smooth.neg hform hf hfb,
      wedgeForm_neg _ (mulBorel (ddcMul D.current a) f) D.smooth,
      wedgeForm_neg _ (mulBorel (ddcMul D.current b) f) D.smooth]
    unfold residualWeightedDdcCurrent
    abel_nf
  · change mulBorel (wedgeForm (Nat.zero_add D.degree) (ddcMul D.current b) D.smooth) f -
      mulBorel (wedgeForm (Nat.zero_add D.degree) (ddcMul D.current a) D.smooth) f = _
    rw [mulBorel_wedgeForm _ hpb D.smooth hform hf hfb,
      mulBorel_wedgeForm _ hpa D.smooth hform hf hfb]
    rfl

/-- An actual finite residual transgression extends to every bounded Borel
weight when its smooth forms admit their genuine positive orientations.
No multiplication of a signed residual current is used in the proof. -/
theorem mulBorel_difference_of_oriented_residuals {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (orientation : ι → Bool)
    (hform : ∀ i z, z ∈ U → orientedForm (D i) (orientation i) z ∈ spCone (D i).degree)
    {A B : LocalProductCurrent n U 0} (hA : IsPositive A) (hB : IsPositive B)
    {a b : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn U a) (hb : IsLocallyBoundedPshOn U b)
    (heq : A - B = ∑ i, (residualDdcCurrent (D i) b - residualDdcCurrent (D i) a))
    {f : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) :
    mulBorel A f - mulBorel B f =
      ∑ i, (residualWeightedDdcCurrent (D i) b f - residualWeightedDdcCurrent (D i) a f) := by
  let S i := orientedDdcCurrent (D i) (orientation i) (if orientation i then b else a)
  let T i := orientedDdcCurrent (D i) (orientation i) (if orientation i then a else b)
  have hS (i : ι) : IsPositive (S i) := by
    apply orientedDdcCurrent_isPositive (D i) (orientation i) (hform i)
    cases orientation i <;> assumption
  have hT (i : ι) : IsPositive (T i) := by
    apply orientedDdcCurrent_isPositive (D i) (orientation i) (hform i)
    cases orientation i <;> assumption
  have heq' : A - B = ∑ i, (S i - T i) := by
    rw [heq]
    apply Finset.sum_congr rfl
    intro i _
    exact (oriented_difference (D i) (orientation i) a b).symm
  rw [mulBorel_difference_of_positive_presentation hA hB S T hS hT heq' hf hfb]
  apply Finset.sum_congr rfl
  intro i _
  exact oriented_weighted_difference (D i) (orientation i) (hform i) ha hb hf hfb

/-- The actual alternating sign of a residual power, with the empty
product positively oriented. -/
def residualOrientation : ℕ → Bool
  | 0 => true
  | d + 1 => !(residualOrientation d)

theorem oriented_wedgeProd_const (d : ℕ) (α : RealForm n 2) :
    (if residualOrientation d then wedgeProd d (fun _ => α) else
      -wedgeProd d (fun _ => α)) = wedgeProd d (fun _ => -α) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [wedgeProd_succ, residualOrientation]
    by_cases h : residualOrientation d = true
    · have ih' : wedgeProd d (fun _ => α) = wedgeProd d (fun _ => -α) := by
        simpa only [h, ↓reduceIte] using ih
      simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← ih', coordinateWedge_neg_right]
    · have hfalse : residualOrientation d = false := Bool.eq_false_iff.mpr h
      have ih' : -wedgeProd d (fun _ => α) = wedgeProd d (fun _ => -α) := by
        simpa only [hfalse, Bool.false_eq_true, ↓reduceIte] using ih
      simp only [hfalse, Bool.not_false, ↓reduceIte]
      rw [← ih', coordinateWedge_neg_left, coordinateWedge_neg_right, neg_neg]

/-- Majorizing correction patches supply the positive orientation of every
actual residual power internally from `-sigma ≥ 0`. -/
theorem backgroundResidual_orientedForm_mem_spCone
    (p : ℕ) (T : LocalProductCurrent n U (1 + p))
    (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hnegσ : ∀ z ∈ U, IsSemipositiveOneOne (-σ z))
    (s : Finset (Fin p)) (z : ComplexModel n) (hz : z ∈ U) :
    orientedForm (backgroundResidual p T hT hTc v hv hσ s)
      (residualOrientation (p - s.card)) z ∈ spCone (p - s.card) := by
  simp only [orientedForm, ite_apply]
  change (if residualOrientation (p - s.card) then wedgeProd (p - s.card) (fun _ => σ z)
    else -wedgeProd (p - s.card) (fun _ => σ z)) ∈ spCone (p - s.card)
  rw [oriented_wedgeProd_const]
  rw [← formPower_eq_wedgeProd]
  exact formPower_mem_spCone (hnegσ z hz) _

private theorem mulBorel_unit_weight {r : ℕ} {T : LocalProductCurrent n U r}
    (hT : IsPositive T) :
    mulBorel T ((U : Set (ComplexModel n)).indicator (fun _ => (1 : ℝ))) = T := by
  have he := mulBorel_congr hT
    (measurable_const.indicator U.isOpen.measurableSet)
    (isLocallyBoundedOn_indicator_of_continuousOn
      (continuousOn_const : ContinuousOn (fun _ : ComplexModel n => (1 : ℝ)) U))
    measurable_const (fun K _ _ => ⟨1, by intros; simp⟩)
    (fun x hx => indicator_of_mem hx _)
  rw [he, mulBorel_const hT, one_smul]

private theorem weightedDdcResidual_one_eq (D : Residual n U)
    (v a b : ComplexModel n → ℝ) (hv : IsLocallyBoundedPshOn U v) :
    weightedDdcResidual D.current D.smooth v a b (fun _ => 1) = residualDdcCurrent D v := by
  unfold weightedDdcResidual
  rw [mulBorel_unit_weight (isPositive_ddcMul D.positive D.closed hv).1]
  rfl

/-- The actual unweighted residual identity extends to the original
bounded Borel difference weight, in the comparison module's native form. -/
theorem mulBorel_weightedDifference_of_oriented_residuals {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (orientation : ι → Bool)
    (hform : ∀ i z, z ∈ U → orientedForm (D i) (orientation i) z ∈ spCone (D i).degree)
    {A B : LocalProductCurrent n U 0} (hA : IsPositive A) (hB : IsPositive B)
    {a b : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn U a) (hb : IsLocallyBoundedPshOn U b)
    (heq : A - B = weightedDifference D a b (fun _ => 1)) (H : ℝ → ℝ)
    (hH : Measurable ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))))
    (hHb : IsLocallyBoundedOn ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) U) :
    mulBorel A ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) -
      mulBorel B ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) =
      weightedDifference D a b H := by
  have heq' : A - B = ∑ i, (residualDdcCurrent (D i) b - residualDdcCurrent (D i) a) := by
    rw [heq, weightedDifference]
    apply Finset.sum_congr rfl
    intro i _
    rw [weightedDdcResidual_one_eq (D i) b a b hb,
      weightedDdcResidual_one_eq (D i) a a b ha]
  exact mulBorel_difference_of_oriented_residuals D orientation hform hA hB ha hb heq' hH hHb

/-- The native majorizing correction's negative-semipositive residual
produces every positive orientation internally. Applying this theorem to
the actual unweighted transgression gives the genuine weighted insertion
identity, without a weighted-result certificate or a signed-current fallback. -/
theorem mulBorel_backgroundResidual_transgression
    (p : ℕ) (T : LocalProductCurrent n U (1 + p))
    (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hnegσ : ∀ z ∈ U, IsSemipositiveOneOne (-σ z))
    {A B : LocalProductCurrent n U 0} (hA : IsPositive A) (hB : IsPositive B)
    {a b : ComplexModel n → ℝ}
    (ha : IsLocallyBoundedPshOn U a) (hb : IsLocallyBoundedPshOn U b)
    (heq : A - B = weightedDifference (backgroundResidual p T hT hTc v hv hσ) a b (fun _ => 1))
    (H : ℝ → ℝ)
    (hH : Measurable ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))))
    (hHb : IsLocallyBoundedOn ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) U) :
    mulBorel A ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) -
      mulBorel B ((U : Set (ComplexModel n)).indicator (fun z => H (b z - a z))) =
      weightedDifference (backgroundResidual p T hT hTc v hv hσ) a b H := by
  exact mulBorel_weightedDifference_of_oriented_residuals
    (backgroundResidual p T hT hTc v hv hσ) (fun s => residualOrientation (p - s.card))
    (fun s z hz => backgroundResidual_orientedForm_mem_spCone p T hT hTc v hv hσ hnegσ s z hz)
    hA hB ha hb heq H hH hHb

end SGPT.PSH.HermitianProducts

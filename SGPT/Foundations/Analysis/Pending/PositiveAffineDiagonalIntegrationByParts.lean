import SGPT.Foundations.Analysis.Pending.BackgroundPolynomialIntegrationByParts
import SGPT.Foundations.Analysis.Pending.PositiveCombinationCanonicalWeights

set_option autoImplicit false

/-!
# Actual positive affine diagonal integration by parts

Lu, arXiv:2005.04264v1, Theorem 1.2. Apply the actual diagonal identity
to unnormalized positive affine combinations and scaled weights. Actual
canonical weight scaling and distinguished-slot measure homogeneity cancel
the common background scale, yielding the identity to expand polynomially.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.PositiveAffineDiagonalIntegrationByParts

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar
open GlobalMultilinearExpansion NonPluripolarMixedCutoffs DeepCoincidenceIntegrationByParts
open PositiveCombinationCanonicalWeights BackgroundPolynomialIntegrationByParts

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine positive affine combinations in their actual scaled background. -/
theorem isThetaPshPotential_positiveAffine {theta : ClosedRealOneOneForm n M}
    {a phi : M → EReal} (ha : IsThetaPshPotential theta.val a)
    (hphi : IsThetaPshPotential theta.val phi) {t : ℝ} (ht : 0 < t) :
    IsThetaPshPotential ((t + 1) • theta).val (positiveCombination t 1 a phi) := by
  simpa only [← add_smul] using isThetaPshPotential_positiveCombination ha hphi ht one_pos

/-- All actual mixed affine slots are genuine, with an unscaled distinguished slot. -/
theorem isThetaPshPotential_affineBinary {theta : ClosedRealOneOneForm n M}
    {a b phi r : M → EReal} (ha : IsThetaPshPotential theta.val a)
    (hb : IsThetaPshPotential theta.val b) (hphi : IsThetaPshPotential theta.val phi)
    (hr : IsThetaPshPotential theta.val r) {t : ℝ} (ht : 0 < t)
    (sigma : Fin n → Bool) (k : Fin n) :
    ∀ i, IsThetaPshPotential (Function.update (fun _ => (t + 1) • theta) k theta i).val
      (Function.update (binaryPotentialTuple sigma (positiveCombination t 1 a phi)
        (positiveCombination t 1 b phi)) k r i) := by
  intro i
  by_cases hi : i = k
  · subst hi
    simpa only [Function.update_self] using hr
  · simp only [Function.update_of_ne hi, binaryPotentialTuple]
    split
    · exact isThetaPshPotential_positiveAffine ha hphi ht
    · exact isThetaPshPotential_positiveAffine hb hphi ht

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual expanded affine mixed product, with original curvature in its
distinguished slot and scaled curvature in the remaining slots. -/
def affineBinaryMixedMeasure {theta : ClosedRealOneOneForm n M} {a b phi r : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hphi : IsThetaPshPotential theta.val phi) (hr : IsThetaPshPotential theta.val r)
    {t : ℝ} (ht : 0 < t) (sigma : Fin n → Bool) (k : Fin n) : Measure M :=
  globalMixedMeasure (Function.update (fun _ => (t + 1) • theta) k theta)
    (Function.update (binaryPotentialTuple sigma (positiveCombination t 1 a phi)
      (positiveCombination t 1 b phi)) k r)
    (fun i => (isThetaPshPotential_affineBinary ha hb hphi hr ht sigma k i).1)

/-- Actual distinguished-slot homogeneity removes the common background scale. -/
theorem binaryMixedMeasure_positiveScale {theta : ClosedRealOneOneForm n M}
    {a b phi r : M → EReal} (ha : IsThetaPshPotential theta.val a)
    (hb : IsThetaPshPotential theta.val b) (hphi : IsThetaPshPotential theta.val phi)
    (hr : IsThetaPshPotential theta.val r) {t : ℝ} (ht : 0 < t)
    (sigma : Fin n → Bool) (k : Fin n) :
    binaryMixedMeasure ((t + 1) • theta)
      (isThetaPshPotential_positiveAffine ha hphi ht).1
      (isThetaPshPotential_positiveAffine hb hphi ht).1
      (isThetaPshPotential_positiveScale hr (show 0 < t + 1 by linarith)).1 sigma k =
    ENNReal.ofReal (t + 1) • affineBinaryMixedMeasure ha hb hphi hr ht sigma k := by
  classical
  have hother (i : Fin n) (_ : i ≠ k) :
      ThetaPlurisubharmonic ((t + 1) • theta).val
        (binaryPotentialTuple sigma (positiveCombination t 1 a phi)
          (positiveCombination t 1 b phi) i) := by
    simp only [binaryPotentialTuple]
    split
    · exact (isThetaPshPotential_positiveAffine ha hphi ht).1
    · exact (isThetaPshPotential_positiveAffine hb hphi ht).1
  have hscale := globalMixedMeasure_update_smul k hother (show 0 < t + 1 by linarith)
    hr.1 hr.quasiPshPotential
  have hforms : Function.update (fun _ : Fin n => (t + 1) • theta) k
      ((t + 1) • theta) = fun _ => (t + 1) • theta := Function.update_eq_self _ _
  exact (GlobalDiagonalScaling.globalMixedMeasure_congr hforms.symm rfl _ _).trans hscale

/-- Actual positive affine diagonal IBP supplies the polynomial identity
whose first coefficient is the one-slot formula; no IBP premise is assumed. -/
theorem diagonal_integral_sub_eq_mul_sum_positiveAffine
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {a b p q phi : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    (hphi : IsThetaPshPotential theta.val phi)
    (hab : SameSingularityTypeOn a b univ) (hpq : SameSingularityTypeOn p q univ)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => (t + 1) • theta)
        (fun _ => positiveCombination t 1 a phi)
        (fun _ => (isThetaPshPotential_positiveAffine ha hphi ht).1)) -
    (∫ x, canonicalERealDiffToReal (p x) (q x)
      ∂globalMixedMeasure (fun _ => (t + 1) • theta)
        (fun _ => positiveCombination t 1 b phi)
        (fun _ => (isThetaPshPotential_positiveAffine hb hphi ht).1)) =
    t * ∑ k : Fin n,
      ((∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂affineBinaryMixedMeasure ha hb hphi hp ht (stepSelector k) k) -
       (∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂affineBinaryMixedMeasure ha hb hphi hq ht (stepSelector k) k)) := by
  have ht1 : 0 < t + 1 := by linarith
  have ha' := isThetaPshPotential_positiveAffine ha hphi ht
  have hb' := isThetaPshPotential_positiveAffine hb hphi ht
  have hp' := isThetaPshPotential_positiveScale hp ht1
  have hq' := isThetaPshPotential_positiveScale hq ht1
  have h := diagonal_integral_sub_eq_sum_of_sameType omega ha' hb' hp' hq'
    (sameSingularityTypeOn_positiveCombination hab ht.le 1)
    (StepFourLogSingularities.sameSingularityTypeOn_const_mul hpq ht1.le)
  simp_rw [canonicalDiff_positiveScale hp hq hpq ht1, integral_const_mul] at h
  have hright (k : Fin n) (r : M → EReal) (hr : IsThetaPshPotential theta.val r) :
      (∫ x, canonicalERealDiffToReal (positiveCombination t 1 a phi x)
        (positiveCombination t 1 b phi x)
        ∂binaryMixedMeasure ((t + 1) • theta) ha'.1 hb'.1
          (isThetaPshPotential_positiveScale hr ht1).1 (stepSelector k) k) =
      t * (t + 1) * ∫ x, canonicalERealDiffToReal (a x) (b x)
        ∂affineBinaryMixedMeasure ha hb hphi hr ht (stepSelector k) k := by
    calc
      _ = t * ∫ x, canonicalERealDiffToReal (a x) (b x)
          ∂binaryMixedMeasure ((t + 1) • theta) ha'.1 hb'.1
            (isThetaPshPotential_positiveScale hr ht1).1 (stepSelector k) k :=
        integral_canonicalDiff_positiveCombination_globalMixedMeasure ha hb hphi hab
          (thetaPlurisubharmonic_binaryUpdatedTuple ((t + 1) • theta) ha'.1 hb'.1
            (isThetaPshPotential_positiveScale hr ht1).1 (stepSelector k) k) t 1
      _ = _ := by
        rw [binaryMixedMeasure_positiveScale ha hb hphi hr ht (stepSelector k) k,
          integral_smul_measure, ENNReal.toReal_ofReal ht1.le, smul_eq_mul]
        ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl fun k _ =>
    congrArg₂ (fun x y : ℝ => x - y) (hright k p hp) (hright k q hq)
  have hscaled := h.trans hsum
  simp only [← mul_sub, ← Finset.mul_sum] at hscaled
  apply (mul_left_cancel₀ ht1.ne')
  convert hscaled using 1
  ring

end

end SGPT.Foundations.Analysis.Pending.PositiveAffineDiagonalIntegrationByParts

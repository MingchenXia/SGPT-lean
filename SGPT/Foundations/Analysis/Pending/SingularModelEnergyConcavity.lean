import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCocycle
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

set_option autoImplicit false

/-!
# Concavity of actual finite-type energy for singular references

Xia SGPT PDF0119--0120, Lemma 3.1.5. The actual supporting inequalities
proved from the singular cocycle imply concavity directly. Genuine convex
combinations and same-type comparisons are produced; the reference need not
be bounded or a model. Extended-energy concavity is a separate target.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyConcavity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
  RelativeEnergyIntegrability SingularModelEnergyCocycle ThetaPshConvexCombination

noncomputable section

/-- Positive convex combinations preserve the common singularity type. -/
theorem sameSingularityTypeOn_convexComb {X : Type*} {φ u v : X → EReal}
    (hu : SameSingularityTypeOn u φ univ) (hv : SameSingularityTypeOn v φ univ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    SameSingularityTypeOn (convexComb t u v) φ univ := by
  have ht1' : 0 < 1 - t := by linarith
  have h := StepFourLogSingularities.sameSingularityTypeOn_add
    (StepFourLogSingularities.sameSingularityTypeOn_const_mul hu ht0.le)
    (StepFourLogSingularities.sameSingularityTypeOn_const_mul hv ht1'.le)
  have href : (fun x => (t : EReal) * φ x + ((1 - t : ℝ) : EReal) * φ x) = φ := by
    funext x
    induction φ x using EReal.rec with
    | bot => simp only [EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    | top =>
      rw [EReal.coe_mul_top_of_pos ht0, EReal.coe_mul_top_of_pos ht1']
      simp
    | coe r =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring
  change SameSingularityTypeOn
    (fun x => (t : EReal) * u x + ((1 - t : ℝ) : EReal) * v x) φ univ
  rw [href] at h
  exact h

/-- The canonical weighted difference from a convex combination cancels at common poles too. -/
theorem canonicalDiff_convexComb_cancel {X : Type*} {u v : X → EReal}
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤)
    (huv : SameSingularityTypeOn u v univ) {t : ℝ} (ht0 : 0 < t)
    (x : X) :
    t * canonicalERealDiffToReal (u x) (convexComb t u v x) +
      (1 - t) * canonicalERealDiffToReal (v x) (convexComb t u v x) = 0 := by
  by_cases hux : u x = ⊥
  · have hvx : v x = ⊥ := (sameSingularityTypeOn_eq_bot_iff huv (mem_univ x)).mp hux
    simp [convexComb, hux, hvx, EReal.coe_mul_bot_of_pos ht0]
  · have hvx : v x ≠ ⊥ := fun h =>
      hux ((sameSingularityTypeOn_eq_bot_iff huv (mem_univ x)).mpr h)
    simp only [convexComb]
    rw [← EReal.coe_toReal (hu x) hux, ← EReal.coe_toReal (hv x) hvx]
    simp only [← EReal.coe_mul, ← EReal.coe_add, canonicalERealDiffToReal_coe_coe]
    ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual finite-type energy is concave on every genuine singular same-type class. -/
theorem relativeEnergyOfMinimalType_concave (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (huφ : SameSingularityTypeOn u φ univ) (hvφ : SameSingularityTypeOn v φ univ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    t * relativeEnergyOfMinimalType θ φ u hφ hu +
      (1 - t) * relativeEnergyOfMinimalType θ φ v hφ hv ≤
      relativeEnergyOfMinimalType θ φ (convexComb t u v) hφ
        (isThetaPshPotential_convexComb hu hv ht0 ht1) := by
  let w := convexComb t u v
  have hw : IsThetaPshPotential θ.val w := isThetaPshPotential_convexComb hu hv ht0 ht1
  have hwφ : SameSingularityTypeOn w φ univ := sameSingularityTypeOn_convexComb huφ hvφ ht0 ht1
  have hU := (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hu hw huφ hwφ).2
  have hV := (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hv hw hvφ hwφ).2
  let μ := globalMixedMeasure (fun _ : Fin n => θ) (fun _ => w) (fun _ => hw.1)
  have huInt : Integrable (fun x => canonicalERealDiffToReal (u x) (w x)) μ :=
    integrable_canonicalDiff_globalMixedMeasure omega hu.1 hw.1 (huφ.trans hwφ.symm)
      (fun _ => hw.1)
  have hvInt : Integrable (fun x => canonicalERealDiffToReal (v x) (w x)) μ :=
    integrable_canonicalDiff_globalMixedMeasure omega hv.1 hw.1 (hvφ.trans hwφ.symm)
      (fun _ => hw.1)
  have hzero : t * (∫ x, canonicalERealDiffToReal (u x) (w x) ∂μ) +
      (1 - t) * (∫ x, canonicalERealDiffToReal (v x) (w x) ∂μ) = 0 := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (huInt.const_mul t) (hvInt.const_mul (1 - t))]
    have heq : (fun x => t * canonicalERealDiffToReal (u x) (w x) +
        (1 - t) * canonicalERealDiffToReal (v x) (w x)) = fun _ => (0 : ℝ) :=
      funext fun x => canonicalDiff_convexComb_cancel hu.1.quasiPlurisubharmonic.ne_top
        hv.1.quasiPlurisubharmonic.ne_top (huφ.trans hvφ.symm) ht0 x
    rw [heq, integral_zero]
  have hU' := mul_le_mul_of_nonneg_left hU ht0.le
  have hV' := mul_le_mul_of_nonneg_left hV (show 0 ≤ 1 - t by linarith)
  nlinarith

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyConcavity

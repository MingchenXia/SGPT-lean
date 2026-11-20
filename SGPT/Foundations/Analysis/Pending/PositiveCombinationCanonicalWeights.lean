import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.StepFourLogSingularities

set_option autoImplicit false

/-!
# Actual canonical weights of genuine positive combinations

The affine input in Lu, arXiv:2005.04264v1, proof of Theorem 1.2.
Genuine positive combinations and same-type comparisons are produced.
Actual pole nullity gives the canonical scaling identity almost everywhere
and hence for actual mixed integrals, including singular reference potentials.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.PositiveCombinationCanonicalWeights

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
open GlobalMultilinearExpansion MixedSummandCapacityDomination RelativeEnergyIntegrability

noncomputable section

/-- The actual positive combination, retaining extended-real pole values. -/
def positiveCombination {X : Type*} (c d : ℝ) (u w : X → EReal) : X → EReal :=
  fun x => (c : EReal) * u x + (d : EReal) * w x

/-- Same-type comparisons survive nonnegative scaling and a common summand. -/
theorem sameSingularityTypeOn_positiveCombination {X : Type*} {u v w : X → EReal}
    {U : Set X} (htype : SameSingularityTypeOn u v U) {c : ℝ} (hc : 0 ≤ c) (d : ℝ) :
    SameSingularityTypeOn (positiveCombination c d u w) (positiveCombination c d v w) U :=
  StepFourLogSingularities.sameSingularityTypeOn_add
    (StepFourLogSingularities.sameSingularityTypeOn_const_mul htype hc)
    (SameSingularityTypeOn.refl (fun x => (d : EReal) * w x) U)

private theorem canonicalDiff_positiveCombination_of_finite {a b w : EReal}
    (hat : a ≠ ⊤) (hbt : b ≠ ⊤) (hwt : w ≠ ⊤)
    (hab : a ≠ ⊥) (hbb : b ≠ ⊥) (hwb : w ≠ ⊥) (c d : ℝ) :
    canonicalERealDiffToReal ((c : EReal) * a + (d : EReal) * w)
        ((c : EReal) * b + (d : EReal) * w) = c * canonicalERealDiffToReal a b := by
  rw [← EReal.coe_toReal hat hab, ← EReal.coe_toReal hbt hbb,
    ← EReal.coe_toReal hwt hwb]
  simp only [← EReal.coe_mul, ← EReal.coe_add, canonicalERealDiffToReal_coe_coe]
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual finite positive-sum nondegeneracy produces the genuine combination,
even when the summands have different backgrounds. -/
theorem isThetaPshPotential_positiveCombination {alpha gamma : ClosedRealOneOneForm n M}
    {u w : M → EReal} (hu : IsThetaPshPotential alpha.val u)
    (hw : IsThetaPshPotential gamma.val w) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    IsThetaPshPotential (c • alpha + d • gamma).val (positiveCombination c d u w) := by
  let forms : Bool → ClosedRealOneOneForm n M := fun i => if i then alpha else gamma
  let pots : Bool → M → EReal := fun i => if i then u else w
  let coeff : Bool → ℝ := fun i => if i then c else d
  have hcoeff : ∀ i, 0 < coeff i := fun i => by cases i <;> assumption
  have hpots : ∀ i, IsThetaPshPotential (forms i).val (pots i) :=
    fun i => by cases i <;> assumption
  have h := isThetaPshPotential_sumPot (T := Finset.univ) Finset.univ_nonempty hcoeff hpots
  have hform : sumForm Finset.univ coeff forms = c • alpha + d • gamma := by
    simp [sumForm, forms, coeff]
  have hpot : sumPot Finset.univ coeff pots = positiveCombination c d u w := by
    funext x
    simp [sumPot, pots, coeff, positiveCombination]
  rw [hform, hpot] at h
  exact h

/-- Positive scaling preserves genuine local nondegeneracy. -/
theorem isThetaPshPotential_positiveScale {alpha : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential alpha.val u) {c : ℝ} (hc : 0 < c) :
    IsThetaPshPotential (c • alpha).val (fun x => (c : EReal) * u x) := by
  refine ⟨thetaPlurisubharmonic_smul hc hu.1, ?_⟩
  intro x U hU hx
  obtain ⟨y, hy, huy⟩ := hu.2 x U hU hx
  exact ⟨y, hy, fun h => huy (ThetaPshConvexCombination.eq_bot_of_coe_mul_eq_bot hc h)⟩

/-- Scaling alone is pointwise, since common poles give zero on both sides. -/
theorem canonicalDiff_positiveScale {alpha beta : SmoothRealForm n M 2}
    {u v : M → EReal} (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (htype : SameSingularityTypeOn u v univ) {c : ℝ} (hc : 0 < c) (x : M) :
    canonicalERealDiffToReal ((c : EReal) * u x) ((c : EReal) * v x) =
      c * canonicalERealDiffToReal (u x) (v x) := by
  by_cases hux : u x = ⊥
  · have hvx : v x = ⊥ := (sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mp hux
    simp [hux, hvx, EReal.coe_mul_bot_of_pos hc]
  · have hvx : v x ≠ ⊥ := fun h => hux
      ((sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mpr h)
    rw [← EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hux,
      ← EReal.coe_toReal (hv.1.quasiPlurisubharmonic.ne_top x) hvx]
    simp only [← EReal.coe_mul, canonicalERealDiffToReal_coe_coe]
    ring

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Genuine pole nullity produces the actual almost-everywhere affine weight
identity; the reference potential's poles are handled explicitly. -/
theorem canonicalDiff_positiveCombination_ae_globalMixedMeasure
    {alpha beta gamma : SmoothRealForm n M 2} {u v w : M → EReal}
    (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (hw : IsThetaPshPotential gamma w) (htype : SameSingularityTypeOn u v univ)
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, ThetaPlurisubharmonic (eta i).val (s i)) (c d : ℝ) :
    (fun x => canonicalERealDiffToReal (positiveCombination c d u w x)
      (positiveCombination c d v w x)) =ᵐ[globalMixedMeasure eta s hs]
      (fun x => c * canonicalERealDiffToReal (u x) (v x)) := by
  have hu0 : ∀ᵐ x ∂globalMixedMeasure eta s hs, u x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not] using globalMixedMeasure_pole_null_of_nondegenerate hs hu
  have hw0 : ∀ᵐ x ∂globalMixedMeasure eta s hs, w x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not] using globalMixedMeasure_pole_null_of_nondegenerate hs hw
  filter_upwards [hu0, hw0] with x hux hwx
  have hvx : v x ≠ ⊥ := fun h => hux
    ((sameSingularityTypeOn_eq_bot_iff htype (mem_univ x)).mpr h)
  exact canonicalDiff_positiveCombination_of_finite
    (hu.1.quasiPlurisubharmonic.ne_top x) (hv.1.quasiPlurisubharmonic.ne_top x)
    (hw.1.quasiPlurisubharmonic.ne_top x) hux hvx hwx c d

/-- Actual affine canonical weights are integrable, including their singular
reference potentials and arbitrary real coefficients. -/
theorem integrable_canonicalDiff_positiveCombination_globalMixedMeasure
    (omega : KahlerBackground n M) {alpha beta gamma : SmoothRealForm n M 2}
    {u v w : M → EReal} (hu : IsThetaPshPotential alpha u)
    (hv : IsThetaPshPotential beta v) (hw : IsThetaPshPotential gamma w)
    (htype : SameSingularityTypeOn u v univ)
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, ThetaPlurisubharmonic (eta i).val (s i)) (c d : ℝ) :
    Integrable (fun x => canonicalERealDiffToReal (positiveCombination c d u w x)
      (positiveCombination c d v w x)) (globalMixedMeasure eta s hs) :=
  ((integrable_canonicalDiff_globalMixedMeasure omega hu.1 hv.1 htype hs).const_mul c).congr
    (canonicalDiff_positiveCombination_ae_globalMixedMeasure hu hv hw htype hs c d).symm

/-- The actual mixed integral of the affine canonical weight scales by its
first coefficient, with genuine pole-nullity produced. -/
theorem integral_canonicalDiff_positiveCombination_globalMixedMeasure
    {alpha beta gamma : SmoothRealForm n M 2} {u v w : M → EReal}
    (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (hw : IsThetaPshPotential gamma w) (htype : SameSingularityTypeOn u v univ)
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, ThetaPlurisubharmonic (eta i).val (s i)) (c d : ℝ) :
    (∫ x, canonicalERealDiffToReal (positiveCombination c d u w x)
      (positiveCombination c d v w x) ∂globalMixedMeasure eta s hs) =
    c * ∫ x, canonicalERealDiffToReal (u x) (v x) ∂globalMixedMeasure eta s hs := by
  rw [integral_congr_ae
    (canonicalDiff_positiveCombination_ae_globalMixedMeasure hu hv hw htype hs c d),
    integral_const_mul]

end

end SGPT.Foundations.Analysis.Pending.PositiveCombinationCanonicalWeights

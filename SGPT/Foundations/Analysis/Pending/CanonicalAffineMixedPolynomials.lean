import SGPT.Foundations.Analysis.Pending.PositiveAffineDiagonalIntegrationByParts
import SGPT.Foundations.Analysis.Pending.CanonicalMixedIntegralExpansion
import SGPT.Foundations.Analysis.Pending.BinarySlotPolynomialCoefficients

set_option autoImplicit false

/-!
# Actual canonical affine mixed integral polynomials

Lu, arXiv:2005.04264v1, proof of Theorem 1.2. Expand the actual
positive affine diagonal and distinguished-slot mixed products. Their
coefficients are genuine canonical integrals of the actual selected tuples.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.CanonicalAffineMixedPolynomials

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
open GlobalMultilinearExpansion MixedMassProductCalculus RelativeEnergyIntegrability
open NonPluripolarMixedCutoffs DeepCoincidenceIntegrationByParts
open PositiveCombinationCanonicalWeights PositiveAffineDiagonalIntegrationByParts
open CanonicalMixedIntegralExpansion BinarySlotPolynomialCoefficients

noncomputable section

/-- Each true binary slot contributes exactly one factor of the parameter. -/
theorem prod_binaryWeight {n : ℕ} (t : ℝ) (g : Fin n → Bool) :
    (∏ i, if g i then t else 1) = t ^ binaryDegree g := by
  classical
  rw [Finset.prod_ite]
  simp [binaryDegree]

/-- The distinguished slot has one original choice; all others have two. -/
def affineChoices {n : ℕ} (k i : Fin n) : Finset (Fin n × Bool) :=
  if i = k then {(i, false)} else {(i, false), (i, true)}

/-- Supported actual slot labels are precisely the binary maps false at `k`. -/
theorem sum_affineChoices {n : ℕ} (k : Fin n)
    (d : (Fin n → Fin n × Bool) → ℝ) :
    (∑ f ∈ Fintype.piFinset (affineChoices k), d f) =
      ∑ g : Fin n → Bool with g k = false, d (fun i => (i, g i)) := by
  classical
  symm
  refine Finset.sum_bij (fun g _ i => (i, g i)) ?_ ?_ ?_ ?_
  · intro g hg
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hi : i = k
    · subst hi
      simp [affineChoices, (Finset.mem_filter.mp hg).2]
    · cases g i <;> simp [affineChoices, hi]
  · intro g _ h _ heq
    exact funext fun i => congrArg Prod.snd (congrFun heq i)
  · intro f hf
    have hmem (i : Fin n) : f i ∈ affineChoices k i := (Fintype.mem_piFinset.mp hf) i
    have hfirst (i : Fin n) : (f i).1 = i := by
      by_cases hi : i = k
      · have he : f i = (i, false) := by simpa [affineChoices, hi] using hmem i
        exact congrArg Prod.fst he
      · have he : f i = (i, false) ∨ f i = (i, true) :=
          by simpa [affineChoices, hi] using hmem i
        rcases he with he | he <;> exact congrArg Prod.fst he
    have hk : (f k).2 = false := by
      have he : f k = (k, false) := by simpa [affineChoices] using hmem k
      exact congrArg Prod.snd he
    refine ⟨fun i => (f i).2, by simp [hk], funext fun i => ?_⟩
    exact Prod.ext (hfirst i).symm rfl
  · intro g _
    rfl

/-- The actual potential belonging to one affine slot label. -/
def affineChoicePot {n : ℕ} {X : Type*} (sigma : Fin n → Bool) (k : Fin n)
    (a b phi r : X → EReal) (z : Fin n × Bool) : X → EReal :=
  if z.1 = k then r else if z.2 then binaryPotentialTuple sigma a b z.1 else phi

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Every selected affine coefficient is a genuine original-background potential. -/
theorem isThetaPshPotential_affineChoicePot {theta : ClosedRealOneOneForm n M}
    {a b phi r : M → EReal} (ha : IsThetaPshPotential theta.val a)
    (hb : IsThetaPshPotential theta.val b) (hphi : IsThetaPshPotential theta.val phi)
    (hr : IsThetaPshPotential theta.val r) (sigma : Fin n → Bool) (k : Fin n)
    (z : Fin n × Bool) : IsThetaPshPotential theta.val (affineChoicePot sigma k a b phi r z) := by
  unfold affineChoicePot
  split
  · exact hr
  · split
    · unfold binaryPotentialTuple
      split
      · exact ha
      · exact hb
    · exact hphi

/-- The actual canonical affine diagonal integral is a binary slot polynomial. -/
theorem integral_canonicalDiff_positiveAffine_diagonal (omega : KahlerBackground n M)
    {alpha beta : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (htype : SameSingularityTypeOn u v univ)
    {theta : ClosedRealOneOneForm n M} {a phi : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hphi : IsThetaPshPotential theta.val phi)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun _ => (t + 1) • theta)
        (fun _ => positiveCombination t 1 a phi)
        (fun _ => (isThetaPshPotential_positiveAffine ha hphi ht).1)) =
    ∑ g : Fin n → Bool, t ^ binaryDegree g *
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure (fun _ => theta) (binaryPotentialTuple g a phi)
          (fun i => if hi : g i = true then by simpa [binaryPotentialTuple, hi] using ha.1
            else by simpa [binaryPotentialTuple, hi] using hphi.1) := by
  classical
  let coeff : Bool → ℝ := fun e => if e then t else 1
  let pots : Bool → M → EReal := fun e => if e then a else phi
  have hcoeff (_ : Fin n) (e : Bool) : 0 ≤ coeff e := by cases e <;> simp [coeff, ht.le]
  have hpots (e : Bool) : IsThetaPshPotential theta.val (pots e) := by
    cases e
    · exact hphi
    · exact ha
  have hexp := integral_canonicalDiff_sumPot_expand omega hu hv htype hcoeff hpots
  have hforms : (fun _ : Fin n => sumForm Finset.univ coeff (fun _ : Bool => theta)) =
      fun _ => (t + 1) • theta := by
    funext i
    simp [sumForm, coeff, add_smul, add_comm]
  have hpot : (fun _ : Fin n => sumPot Finset.univ coeff pots) =
      fun _ => positiveCombination t 1 a phi := by
    funext i x
    simp [sumPot, coeff, pots, positiveCombination, add_comm]
  rw [globalMixedMeasure_congr hforms hpot _
    (fun _ => (isThetaPshPotential_positiveAffine ha hphi ht).1)] at hexp
  exact hexp.trans (Finset.sum_congr rfl fun g _ =>
    congrArg₂ (fun x y : ℝ => x * y) (prod_binaryWeight t g) rfl)

/-- The actual affine mixed integral has the original distinguished slot
in every coefficient, including its constant reference coefficient. -/
theorem integral_canonicalDiff_affineBinaryMixedMeasure (omega : KahlerBackground n M)
    {alpha beta : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (htype : SameSingularityTypeOn u v univ)
    {theta : ClosedRealOneOneForm n M} {a b phi r : M → EReal}
    (ha : IsThetaPshPotential theta.val a) (hb : IsThetaPshPotential theta.val b)
    (hphi : IsThetaPshPotential theta.val phi) (hr : IsThetaPshPotential theta.val r)
    {t : ℝ} (ht : 0 < t) (sigma : Fin n → Bool) (k : Fin n) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂affineBinaryMixedMeasure ha hb hphi hr ht sigma k) =
    ∑ g with g k = false, t ^ binaryDegree g *
      ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂globalMixedMeasure (fun _ => theta)
          (fun i => affineChoicePot sigma k a b phi r (i, g i))
          (fun i => (isThetaPshPotential_affineChoicePot ha hb hphi hr sigma k (i, g i)).1) := by
  classical
  let coeff : Fin n × Bool → ℝ := fun z => if z.2 then t else 1
  let pots := affineChoicePot sigma k a b phi r
  have hcoeff (_ : Fin n) (z : Fin n × Bool) : 0 < coeff z := by
    cases hz : z.2 <;> simp [coeff, hz, ht]
  have hT (i : Fin n) : (affineChoices k i).Nonempty := by
    refine ⟨(i, false), ?_⟩
    by_cases hi : i = k <;> simp [affineChoices, hi]
  have hpots (z : Fin n × Bool) : IsThetaPshPotential theta.val (pots z) :=
    isThetaPshPotential_affineChoicePot ha hb hphi hr sigma k z
  have hexp := globalMixedMeasure_sumPot_slots hT hcoeff (fun z => (hpots z).1)
    (fun z => (hpots z).quasiPshPotential)
  have hforms : (fun i => sumForm (affineChoices k i) coeff
      (fun _ : Fin n × Bool => theta)) = Function.update (fun _ => (t + 1) • theta) k theta := by
    funext i
    by_cases hi : i = k
    · subst hi
      simp [affineChoices, sumForm, coeff]
    · simp [affineChoices, sumForm, coeff, hi, add_smul, add_comm]
  have hpot : (fun i => sumPot (affineChoices k i) coeff pots) =
      Function.update (binaryPotentialTuple sigma (positiveCombination t 1 a phi)
        (positiveCombination t 1 b phi)) k r := by
    funext i x
    by_cases hi : i = k
    · subst hi
      simp [affineChoices, sumPot, coeff, pots, affineChoicePot]
    · cases hsi : sigma i <;>
        simp [affineChoices, sumPot, coeff, pots, affineChoicePot, hi, hsi,
          binaryPotentialTuple, positiveCombination, add_comm]
  rw [globalMixedMeasure_congr hforms hpot _
    (fun i => (isThetaPshPotential_affineBinary ha hb hphi hr ht sigma k i).1)] at hexp
  have hint : (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂affineBinaryMixedMeasure ha hb hphi hr ht sigma k) =
      ∑ f ∈ Fintype.piFinset (affineChoices k), (∏ i, coeff (f i)) *
        ∫ x, canonicalERealDiffToReal (u x) (v x)
          ∂globalMixedMeasure (fun _ => theta) (fun i => pots (f i))
            (fun i => (hpots (f i)).1) := by
    change (∫ x, canonicalERealDiffToReal (u x) (v x) ∂globalMixedMeasure _ _ _) = _
    rw [hexp, integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun f _ => ?_
      rw [integral_smul_measure]
      simp only [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => (hcoeff i (f i)).le),
        smul_eq_mul]
    · intro f _
      exact (integrable_canonicalDiff_globalMixedMeasure omega hu.1 hv.1 htype
        (fun i => (hpots (f i)).1)).smul_measure ENNReal.ofReal_ne_top
  rw [sum_affineChoices] at hint
  exact hint.trans (Finset.sum_congr rfl fun g _ =>
    congrArg₂ (fun x y : ℝ => x * y) (prod_binaryWeight t g) rfl)

end

end SGPT.Foundations.Analysis.Pending.CanonicalAffineMixedPolynomials

import SGPT.Foundations.Analysis.Pending.MixedMassBoundedDifference
import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability

set_option autoImplicit false

/-!
# Actual canonical weighted mixed background polynomials

Lu, arXiv:2005.04264v1, Lemma 4.1 Step 2. Slotwise positive
multilinearity expands the actual products in a Kähler background parameter.
The actual canonical weights are integrable by the same-type producer.
The unique term with no Kähler slots recovers the original mixed integral.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.CanonicalBackgroundPolynomial

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling
open GlobalMultilinearExpansion MixedMassProductCalculus MixedMassBoundedDifference
open RelativeEnergyIntegrability KahlerDomination

noncomputable section

/-- The two actual choices in each background-expanded slot. -/
def backgroundChoices {n : ℕ} (i : Fin n) : Finset (Option (Fin n)) := {none, some i}

/-- The degree in the Kähler background parameter of a selected product. -/
def backgroundDegree {n : ℕ} (g : Fin n → Option (Fin n)) : ℕ :=
  (Finset.univ.filter fun j => g j = none).card

/-- The constant coefficient retains precisely the original slots,
including the unique empty tuple in dimension zero. -/
theorem sum_zero_background_degree {n : ℕ} (d : (Fin n → Option (Fin n)) → ℝ) :
    (∑ g with backgroundDegree g = 0,
      if ∀ i, g i ∈ backgroundChoices i then d g else 0) = d (fun i => some i) := by
  classical
  rw [Finset.sum_eq_single (fun i => some i)]
  · simp [backgroundChoices]
  · intro g hg hne
    by_cases hs : ∀ i, g i ∈ backgroundChoices i
    · have hdegree : backgroundDegree g = 0 := (Finset.mem_filter.mp hg).2
      have hnone : ∀ i, g i ≠ none := by
        intro i hi
        have hempty : (Finset.univ.filter fun j => g j = none) = ∅ :=
          Finset.card_eq_zero.mp hdegree
        have : i ∈ (Finset.univ.filter fun j => g j = none) := by simp [hi]
        simp [hempty] at this
      have heq : g = fun i => some i := by
        funext i
        have hi := hs i
        simp only [backgroundChoices, Finset.mem_insert, Finset.mem_singleton] at hi
        exact hi.resolve_left (hnone i)
      exact (hne heq).elim
    · simp [hs]
  · simp [backgroundDegree]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual sum of the original and Kähler forms in one slot. -/
theorem sumForm_backgroundChoices (omega : KahlerBackground n M)
    (eta : Fin n → ClosedRealOneOneForm n M) (N : ℝ) (i : Fin n) :
    sumForm (backgroundChoices i) (optWeight N) (optForm omega eta) =
      eta i + N • omega.form := by
  simp [sumForm, backgroundChoices, optWeight, optForm, add_comm]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The Kähler slot has zero potential, so the actual potential is unchanged. -/
theorem sumPot_backgroundChoices (s : Fin n → M → EReal) (N : ℝ) (i : Fin n) :
    sumPot (backgroundChoices i) (optWeight N) (optPot s) = s i := by
  funext x
  simp [sumPot, backgroundChoices, optWeight, optPot]

/-- Semipositive background enlargement preserves each genuine potential. -/
theorem isThetaPshPotential_add_background (omega : KahlerBackground n M)
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, IsThetaPshPotential (eta i).val (s i)) {N : ℝ} (hN : 0 ≤ N) :
    ∀ i, IsThetaPshPotential (eta i + N • omega.form).val (s i) :=
  fun i => LocalPotentials.isThetaPshPotential_add_of_semipositive (hs i)
    (isSemipositive_smul omega.isSemipositive hN)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Expand the actual canonical weighted mixed integral in the background
parameter, with all integrability inputs produced from genuine same-type weights. -/
theorem integral_canonicalDiff_add_background (omega : KahlerBackground n M)
    {alpha beta : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential alpha u) (hv : IsThetaPshPotential beta v)
    (htype : SameSingularityTypeOn u v univ)
    {eta : Fin n → ClosedRealOneOneForm n M} {s : Fin n → M → EReal}
    (hs : ∀ i, IsThetaPshPotential (eta i).val (s i)) {N : ℝ} (hN : 0 < N) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂globalMixedMeasure (fun i => eta i + N • omega.form) s
        (fun i => (isThetaPshPotential_add_background omega hs hN.le i).1)) =
    ∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)),
      N ^ backgroundDegree g *
        ∫ x, canonicalERealDiffToReal (u x) (v x)
          ∂globalMixedMeasure (fun j => optForm omega eta (g j))
            (fun j => optPot s (g j)) (fun j => optPot_psh omega hs (g j)) := by
  classical
  have hT : ∀ i : Fin n, (backgroundChoices i).Nonempty := fun i =>
    ⟨none, by simp [backgroundChoices]⟩
  have hexp := globalMixedMeasure_sumPot_slots hT
    (fun _ => optWeight_pos (n := n) hN) (optPot_psh omega hs) (optPot_quasiPsh hs)
  rw [globalMixedMeasure_congr
    (funext (sumForm_backgroundChoices omega eta N))
    (funext (sumPot_backgroundChoices s N)) _
    (fun i => (isThetaPshPotential_add_background omega hs hN.le i).1)] at hexp
  rw [hexp, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_smul_measure, prod_optWeight]
    simp only [backgroundDegree, ENNReal.toReal_ofReal (pow_nonneg hN.le _), smul_eq_mul]
  · intro g _
    exact (integrable_canonicalDiff_globalMixedMeasure omega hu.1 hv.1 htype
      (fun j => optPot_psh omega hs (g j))).smul_measure ENNReal.ofReal_ne_top

end

end SGPT.Foundations.Analysis.Pending.CanonicalBackgroundPolynomial

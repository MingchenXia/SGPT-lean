import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.RelativeEnergy
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false

/-! # Actual endpoint mass polynomials of a scaled genuine potential sum

SGPT PDF0242 (6.26), the actual finite independent mixed-product
constant-term ingredient. Both summands can be singular genuine potentials.
No native or mass limit is assumed here.
-/

open Set MeasureTheory Polynomial
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualPotentialSumMassPolynomial

open FirstPass FirstPass.PositiveClasses RelativeEnergy MixedMass GlobalNonPluripolar
  GlobalDiagonalScaling GlobalMultilinearExpansion MixedMassProductCalculus
  MixedSummandCapacityDomination

noncomputable section

private def weightPolynomial {n : ℕ} (j : Fin (n + 1)) (k : Fin n) :
    Option Bool → ℝ[X] := fun o =>
  if k.val < j.val then o.elim 0 (fun b => if b then X else 1)
  else o.elim 1 (fun _ => 0)

private def pairForm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (θ σ : ClosedRealOneOneForm n M) : Option Bool → ClosedRealOneOneForm n M :=
  fun o => o.elim σ (fun b => if b then θ else σ)

private def pairPot {M : Type*} (u v R : M → EReal) : Option Bool → M → EReal :=
  fun o => o.elim R (fun b => if b then u else v)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
private theorem pairPsh {θ σ : ClosedRealOneOneForm n M} {u v R : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hR : IsThetaPshPotential σ.val R) (o : Option Bool) :
    IsThetaPshPotential (pairForm θ σ o).val (pairPot u v R o) := by
  cases o with
  | none => exact hR
  | some b => cases b <;> first | exact hv | exact hu

/-- The coefficients are finite real values of actual selected mixed masses;
the first `j` slots use the scaled singular pair and the second singular pair. -/
def potentialSumEndpointMassPolynomial (θ σ : ClosedRealOneOneForm n M)
    (u v R : M → EReal) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential σ.val v) (hR : IsThetaPshPotential σ.val R)
    (j : Fin (n + 1)) : ℝ[X] :=
  ∑ g : Fin n → Option Bool,
    C ((globalMixedMass (fun k => pairForm θ σ (g k))
      (fun k => pairPot u v R (g k)) (fun k => (pairPsh hu hv hR (g k)).1)).toReal) *
      ∏ k, weightPolynomial j k (g k)

omit [BorelSpace M] in
/-- The actual scaled-sum endpoint polynomial has degree at most the number
of slots, including the empty tuple. -/
theorem natDegree_potentialSumEndpointMassPolynomial_le
    (θ σ : ClosedRealOneOneForm n M) (u v R : M → EReal)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hR : IsThetaPshPotential σ.val R) (j : Fin (n + 1)) :
    (potentialSumEndpointMassPolynomial θ σ u v R hu hv hR j).natDegree ≤ n := by
  classical
  unfold potentialSumEndpointMassPolynomial
  apply natDegree_sum_le_of_forall_le
  intro g _
  apply (natDegree_C_mul_le _ _).trans
  calc
    _ ≤ ∑ k : Fin n, (weightPolynomial j k (g k)).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _k : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro k _
      cases g k with
      | none => simp only [weightPolynomial]; split_ifs <;> simp
      | some b => cases b <;> simp only [weightPolynomial] <;> split_ifs <;> simp
    _ = n := by simp

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
private theorem scaledSumPsh {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    {a : ℝ} (ha : 0 ≤ a) :
    IsThetaPshPotential (a • θ + σ).val (fun x => (a : EReal) * u x + v x) := by
  classical
  by_cases hzero : a = 0
  · simpa [hzero] using hv
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else σ
  let f : Bool → M → EReal := fun b => if b then u else v
  let w : Bool → ℝ := fun b => if b then a else 1
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have hw (b : Bool) : 0 < w b := by
    cases b
    · exact zero_lt_one
    · exact hapos
  have h := isThetaPshPotential_sumPot (T := Finset.univ) Finset.univ_nonempty hw hf
  have hQ : sumPot Finset.univ w f = fun x => (a : EReal) * u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, w, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, w, Bool.false_eq_true,
    ↓reduceIte, one_smul] using h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
private theorem sumTuplePsh {θ σ : ClosedRealOneOneForm n M} {u v R : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hR : IsThetaPshPotential σ.val R) (j : Fin (n + 1)) {a : ℝ} (ha : 0 ≤ a)
    (k : Fin n) :
    IsThetaPshPotential (if k.val < j.val then a • θ + σ else σ).val
      (if k.val < j.val then (fun x => (a : EReal) * u x + v x) else R) := by
  by_cases hk : k.val < j.val
  · simpa only [hk, ↓reduceIte] using scaledSumPsh hu hv ha
  · simpa only [hk, ↓reduceIte] using hR

/-- Every nonnegative evaluation is the real value of the actual mixed
mass with first `j` genuine scaled-sum slots, including coefficient zero. -/
theorem globalMixedMass_potential_sum_toReal_eq_eval
    (omega : KahlerBackground n M) {θ σ : ClosedRealOneOneForm n M}
    {u v R : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential σ.val v) (hR : IsThetaPshPotential σ.val R)
    (j : Fin (n + 1)) {a : ℝ} (ha : 0 ≤ a) :
    (globalMixedMass (fun k : Fin n => if k.val < j.val then a • θ + σ else σ)
      (fun k : Fin n => if k.val < j.val then (fun x => (a : EReal) * u x + v x) else R)
      (fun k => (sumTuplePsh hu hv hR j ha k).1)).toReal =
        (potentialSumEndpointMassPolynomial θ σ u v R hu hv hR j).eval a := by
  classical
  let c : Fin n → Option Bool → ℝ := fun k o => (weightPolynomial j k o).eval a
  have hc (k : Fin n) (o : Option Bool) : 0 ≤ c k o := by
    cases o with
    | none => dsimp [c, weightPolynomial]; split_ifs <;> simp
    | some b => cases b <;> dsimp [c, weightPolynomial] <;> split_ifs <;> simp [ha]
  have hF : (fun k => sumForm Finset.univ (c k) (pairForm θ σ)) =
      fun k : Fin n => if k.val < j.val then a • θ + σ else σ := by
    funext k
    by_cases hk : k.val < j.val <;>
      simp [sumForm, Fintype.sum_option, c, weightPolynomial, pairForm, hk]
  have hQ : (fun k => sumPot Finset.univ (c k) (pairPot u v R)) =
      fun k : Fin n => if k.val < j.val then (fun x => (a : EReal) * u x + v x) else R := by
    funext k x
    by_cases hk : k.val < j.val <;>
      simp [sumPot, Fintype.sum_option, c, weightPolynomial, pairPot, hk]
  have h := globalMixedMass_sumPot_expand_toReal omega hc (pairPsh hu hv hR)
  unfold globalMixedMass at h
  rw [globalMixedMeasure_congr hF hQ _ (fun k => (sumTuplePsh hu hv hR j ha k).1)] at h
  simpa only [potentialSumEndpointMassPolynomial, eval_finsetSum, eval_mul, eval_C,
    eval_prod, c, globalMixedMass, mul_comm] using h

/-- The constant term is exactly the finite real value of the original
endpoint mixed mass of `v` relative to `R`, with no positivity assumption. -/
theorem eval_zero_potentialSumEndpointMassPolynomial
    (omega : KahlerBackground n M) {θ σ : ClosedRealOneOneForm n M}
    {u v R : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential σ.val v) (hR : IsThetaPshPotential σ.val R)
    (j : Fin (n + 1)) :
    (potentialSumEndpointMassPolynomial θ σ u v R hu hv hR j).eval 0 =
      (endpointMixedMass σ R v hR hv j).toReal := by
  have h := globalMixedMass_potential_sum_toReal_eq_eval omega hu hv hR j (a := 0) le_rfl
  have hF : (fun k : Fin n => if k.val < j.val then (0 : ℝ) • θ + σ else σ) =
      fun _ : Fin n => σ := by
    funext k
    simp
  have hQ : (fun k : Fin n => if k.val < j.val then
      (fun x => ((0 : ℝ) : EReal) * u x + v x) else R) =
      endpointMixedPotential j v R := by
    funext k x
    simp [endpointMixedPotential]
  unfold globalMixedMass at h
  rw [globalMixedMeasure_congr hF hQ _
    (endpointMixedPotential_thetaPlurisubharmonic σ j v R hv hR)] at h
  exact h.symm

end
end SGPT.Foundations.Analysis.Pending.ActualPotentialSumMassPolynomial

import SGPT.Foundations.Analysis.Pending.IncreasingDiagonalContinuity
import SGPT.Foundations.Analysis.Pending.MixedProductIntegralPolarization

set_option autoImplicit false

/-!
# Increasing mixed products with independent backgrounds

The pointwise genuine-limit sequence case of Xia, Corollary 2.4.1.
Positive subset sums converge without a sign restriction, since genuine
PSH limits have no positive infinity. Actual diagonal weak continuity and
actual finite mixed polarization produce the independent-slot result.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingMixedContinuity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass
open GlobalMultilinearExpansion
open MixedMassProductCalculus MixedSummandCapacityDomination MixedProductIntegralPolarization
open IncreasingDiagonalWeakConvergence IncreasingDiagonalContinuity

noncomputable section

/-- Finite sums whose summands have no positive infinity also have no positive infinity. -/
theorem finsetSum_ne_top {iota : Type*} (S : Finset iota) {v : iota → EReal}
    (hv : ∀ i, v i ≠ ⊤) : (∑ i ∈ S, v i) ≠ ⊤ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.add_ne_top (hv i) ih

/-- Finite sums preserve filter limits when no limiting summand is positive infinity. -/
theorem tendsto_finsetSum_ereal_of_ne_top {iota J : Type*} (F : Filter J)
    (S : Finset iota) {f : iota → J → EReal} {v : iota → EReal}
    (hlim : ∀ i, Tendsto (f i) F (𝓝 (v i))) (hv : ∀ i, v i ≠ ⊤) :
    Tendsto (fun j => ∑ i ∈ S, f i j) F (𝓝 (∑ i ∈ S, v i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact tendsto_const_nhds
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (EReal.continuousAt_add (p := (v i, ∑ k ∈ S, v k))
      (Or.inl (hv i)) (Or.inr (finsetSum_ne_top S hv))).tendsto.comp
        ((hlim i).prodMk_nhds ih)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual positive subset diagonal integrals converge for independent backgrounds. -/
theorem tendsto_integral_diagonal_subsetSum (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (theta i).val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i)) {v : Fin n → M → EReal}
    (hv : ∀ i, IsThetaPshPotential (theta i).val (v i))
    (hlim : ∀ i x, Tendsto (fun j => u j i x) atTop (𝓝 (v i x)))
    (S : Finset (Fin n)) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂diagonalPotentialMeasure
      (sumForm S (fun _ => 1) theta) (sumPot S (fun _ => 1) (u j))
        (isThetaPshPotential_subsetSum (hu j) S)) atTop
      (𝓝 (∫ x, chi x ∂diagonalPotentialMeasure
        (sumForm S (fun _ => 1) theta) (sumPot S (fun _ => 1) v)
          (isThetaPshPotential_subsetSum hv S))) := by
  have hmonoS : Monotone fun j => sumPot S (fun _ => 1) (u j) :=
    fun i j hij => sumPot_mono (fun _ => one_pos) (fun k => hmono k hij)
  have hlimS : ∀ x, Tendsto (fun j => sumPot S (fun _ => 1) (u j) x) atTop
      (𝓝 (sumPot S (fun _ => 1) v x)) := by
    intro x
    simpa only [sumPot, EReal.coe_one, one_mul] using
      tendsto_finsetSum_ereal_of_ne_top atTop S (fun i => hlim i x)
        (fun i => (hv i).1.quasiPlurisubharmonic.ne_top x)
  have hvs := isThetaPshPotential_subsetSum hv S
  have heq := uscRegularization_iSup_eq_of_monotone_tendsto hmonoS
    hvs.1.quasiPlurisubharmonic.upperSemicontinuous hlimS
  have hU : IsThetaPshPotential (sumForm S (fun _ => 1) theta).val
      (uscRegularization (⨆ j, sumPot S (fun _ => 1) (u j))) := heq ▸ hvs
  have h := tendsto_integral_diagonal_of_monotone omega
    (fun j => isThetaPshPotential_subsetSum (hu j) S) hmonoS hU chi
  simpa only [heq] using h

/-- Actual independent mixed continuous-test convergence follows from finite polarization. -/
theorem tendsto_integral_mixed_of_monotone (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (theta i).val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i)) {v : Fin n → M → EReal}
    (hv : ∀ i, IsThetaPshPotential (theta i).val (v i))
    (hlim : ∀ i x, Tendsto (fun j => u j i x) atTop (𝓝 (v i x))) (chi : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, chi x ∂globalMixedMeasure theta (u j)
      (fun i => (hu j i).1)) atTop
      (𝓝 (∫ x, chi x ∂globalMixedMeasure theta v (fun i => (hv i).1))) := by
  classical
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Finset (Fin n))) fun S _ =>
    (tendsto_const_nhds (x := (-1 : ℝ) ^ (n - S.card))).mul
      (tendsto_integral_diagonal_subsetSum omega hu hmono hv hlim S chi)
  have hj := fun j => integral_mixed_eq_signed_diagonal_subsetSum omega (hu j) chi
  have hvtest := integral_mixed_eq_signed_diagonal_subsetSum omega hv chi
  have hfaclim : Tendsto (fun j => (n.factorial : ℝ) *
      ∫ x, chi x ∂globalMixedMeasure theta (u j) (fun i => (hu j i).1)) atTop
      (𝓝 ((n.factorial : ℝ) *
        ∫ x, chi x ∂globalMixedMeasure theta v (fun i => (hv i).1))) := by
    simpa only [hj, hvtest] using hsum
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simpa only [inv_mul_cancel_left₀ hfac] using
    (tendsto_const_nhds (x := (n.factorial : ℝ)⁻¹)).mul hfaclim

/-- The actual independent mixed product with its produced finite-mass proof. -/
def finiteMixedMeasure (omega : KahlerBackground n M)
    (theta : Fin n → ClosedRealOneOneForm n M) (u : Fin n → M → EReal)
    (hu : ∀ i, IsThetaPshPotential (theta i).val (u i)) : FiniteMeasure M :=
  ⟨globalMixedMeasure theta u (fun i => (hu i).1),
    globalMixedMeasure_isFiniteMeasure omega (fun i => (hu i).1)⟩

/-- Actual native weak convergence with independent backgrounds and genuine pointwise limits. -/
theorem weakTendsto_mixed_of_monotone (omega : KahlerBackground n M)
    {theta : Fin n → ClosedRealOneOneForm n M} {u : ℕ → Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (theta i).val (u j i))
    (hmono : ∀ i, Monotone (fun j => u j i)) {v : Fin n → M → EReal}
    (hv : ∀ i, IsThetaPshPotential (theta i).val (v i))
    (hlim : ∀ i x, Tendsto (fun j => u j i x) atTop (𝓝 (v i x))) :
    Tendsto (fun j => finiteMixedMeasure omega theta (u j) (hu j)) atTop
      (𝓝 (finiteMixedMeasure omega theta v hv)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro chi
  exact tendsto_integral_mixed_of_monotone omega hu hmono hv hlim chi

end

end SGPT.Foundations.Analysis.Pending.IncreasingMixedContinuity

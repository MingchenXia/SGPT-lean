import SGPT.Foundations.Analysis.Pending.ActualMultiplierFiniteGapAddition
import SGPT.Foundations.Analysis.Pending.RationalAnalyticAddition
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularTwoPotentialMaximum

set_option autoImplicit false

/-! # Actual full quasi-equisingular addition in independent backgrounds -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularAddition

open FirstPass FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation
  MixedSummandCapacityDomination GlobalMultilinearExpansion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem genuineAdd {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then θ else σ
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := isThetaPshPotential_sumPot (T := Finset.univ)
    (w := fun _ : Bool => (1 : ℝ)) Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [sumPot, Fintype.sum_bool, f, Bool.false_eq_true,
      ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [sumForm, Fintype.sum_bool, α, Bool.false_eq_true,
    ↓reduceIte, one_smul] using h

/-- The two original full predicates supply exactly the one finite level
pair needed for every strict sum clause. -/
theorem eventually_multiplierIdealIncluded_add
    {omega : KahlerBackground n M} {θ σ : ClosedRealOneOneForm n M}
    {u v : M → EReal} {ε δ : ℕ → ℝ} {U V : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε U)
    (hv : IsQuasiEquisingularApproximation omega σ v δ V)
    {c q : ℝ} (hc : 0 < c) (hcq : c < q) :
    ∀ᶠ j in atTop, MultiplierIdealIncluded (n := n)
      (fun x => U j x + V j x) q (fun x => u x + v x) c := by
  obtain ⟨m, hm, p, hp, hpm, hgap⟩ :=
    ActualMultiplierFiniteGapWeightBound.exists_exponent_parameters hc hcq
  filter_upwards [hu.eventually_multiplierIdealIncluded hp hpm,
    hv.eventually_multiplierIdealIncluded hp hpm] with j hjU hjV
  exact ActualMultiplierFiniteGapAddition.multiplierIdealIncluded_add_of_finite_levels
    (hu.term j) (hv.term j) hu.target hv.target hc (hc.trans hcq) hp hm hgap hjU hjV

/-- The literal sum sequence and error sum satisfy the entire genuine
quasi-equisingular predicate in the sum of independent backgrounds. -/
theorem isQuasiEquisingularApproximation_add
    {omega : KahlerBackground n M} {θ σ : ClosedRealOneOneForm n M}
    {u v : M → EReal} {ε δ : ℕ → ℝ} {U V : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε U)
    (hv : IsQuasiEquisingularApproximation omega σ v δ V) :
    IsQuasiEquisingularApproximation omega (θ + σ) (fun x => u x + v x)
      (fun j => ε j + δ j) (fun j x => U j x + V j x) := by
  have herror : NonnegativeDecreasesToZero (fun j => ε j + δ j) := by
    refine ⟨fun j => add_nonneg (hu.error_nonneg j) (hv.error_nonneg j),
      fun i j hij => add_le_add (hu.error_antitone hij) (hv.error_antitone hij), ?_⟩
    simpa only [add_zero] using hu.error_tendsto.add hv.error_tendsto
  refine ⟨genuineAdd hu.target hv.target, herror, ?_, ?_, ?_, ?_⟩
  · intro j
    have hform : (θ + ε j • omega.form) + (σ + δ j • omega.form) =
        θ + σ + (ε j + δ j) • omega.form := by module
    simpa only [hform] using genuineAdd (hu.term j) (hv.term j)
  · intro j e z hz
    exact RationalAnalyticAddition.hasAnalyticSingularityTypeAt_add
      (hu.term_hasAnalyticSingularityType j e z hz)
      (hv.term_hasAnalyticSingularityType j e z hz)
  · refine ⟨fun x i j hij => add_le_add (hu.term_antitone x hij) (hv.term_antitone x hij),
      fun x => ?_⟩
    exact (EReal.continuousAt_add
      (Or.inl (hu.target.1.quasiPlurisubharmonic.ne_top x))
      (Or.inr (hv.target.1.quasiPlurisubharmonic.ne_top x))).tendsto.comp
        ((hu.term_tendsto x).prodMk_nhds (hv.term_tendsto x))
  · intro c q hc hcq
    exact eventually_multiplierIdealIncluded_add hu hv hc hcq

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularAddition

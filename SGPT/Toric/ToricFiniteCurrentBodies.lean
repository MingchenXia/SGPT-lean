import SGPT.Toric.MetricFiniteSums
import SGPT.Toric.ToricIVolumeNewtonBody
import SGPT.Convex.FiniteConvexMinkowskiBodies
import SGPT.Okounkov.ThetaPotentialCurrentCombinations

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending NaturalThetaPshGeometricCurrent GlobalMultilinearExpansion
open scoped Topology ContDiff BigOperators Pointwise ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

private theorem coe_real_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ S, f i : ℝ) : EReal) = ∑ i ∈ S, (f i : EReal) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp only [Finset.sum_insert ha, EReal.coe_add, ih]

/-- The actual metric/reference-potential sum yields the actual original
body sum. The body identity is an OUTPUT of finite convex geometry. -/
theorem newtonBody_finite_sum_metric
    (D : Fin n → ToricDivisor γ hs) (h : ∀ i, BigToricMetric (D i))
    (u : Fin n → PolytopeToricVariety γ hs → EReal)
    (hu : ∀ i, u i ∈ (h i).PSHTor) (S : Finset (Fin n))
    (H : BigToricMetric (∑ i ∈ S, D i))
    (hpot : ∀ x, H.potential x = ∑ i ∈ S, (h i).potential x) :
    H.newtonBody (fun p => ∑ i ∈ S, u i p) =
      sourceMinkowskiSubsetSum (fun i => (h i).newtonBody (u i)) S := by
  let F : Fin n → RealConvexFunction (EuclideanSpace ℝ (Fin n)) :=
    fun i => ⟨(h i).realProfile (u i), ((h i).realProfile_mem (hu i)).1.1⟩
  have hbody (i : Fin n) : finiteConvexGradientBody (F i) =
      (h i).newtonBody (u i) := by
    unfold finiteConvexGradientBody BigToricMetric.newtonBody
    rw [((h i).realProfile_mem (hu i)).2]
  have hcompact (i : Fin n) : IsCompact (finiteConvexGradientBody (F i)) := by
    rw [hbody]
    exact ((h i).newtonBody_properties
      ((h i).nonempty_toricDivisorPolytope_of_mem (hu i)) (hu i)).2.1
  have hprofile : H.profile (fun p => ∑ i ∈ S, u i p) =
      fun x => ((finiteConvexSubsetSum F S).val x : EReal) := by
    rw [BigToricMetric.profile_finite_sum D h S H hpot u]
    funext x
    calc
      (∑ i ∈ S, (h i).profile (u i) x) = ∑ i ∈ S, ((F i).val x : EReal) :=
        Finset.sum_congr rfl (fun i _ => congrFun ((h i).realProfile_mem (hu i)).2 x)
      _ = ((finiteConvexSubsetSum F S).val x : EReal) :=
        (coe_real_finset_sum S (fun i => (F i).val x)).symm
  calc
    H.newtonBody (fun p => ∑ i ∈ S, u i p) =
        finiteConvexGradientBody (finiteConvexSubsetSum F S) := by
      unfold BigToricMetric.newtonBody finiteConvexGradientBody
      rw [hprofile]
    _ = sourceMinkowskiSubsetSum (fun i => finiteConvexGradientBody (F i)) S :=
      finiteConvexGradientBody_subsetSum F hcompact S
    _ = sourceMinkowskiSubsetSum (fun i => (h i).newtonBody (u i)) S := by
      congr 1
      funext i
      exact hbody i

section PositiveDimension

variable {m : ℕ} {γ : K → Fin (m + 1) → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "X" => PolytopeToricVariety γ hs

/-- Actual finite sums of the original toric currents manufacture a genuine
sum-divisor metric, actual global potential, SAME full-current reading and
the source single-I-volume/Minkowski-body identity. The empty sum is included.
No geometric body identity, current representation or mixed-volume conclusion
is an incoming certificate. -/
theorem exists_finite_sum_toric_current_and_body
    (D : Fin (m + 1) → ToricDivisor γ hs) (h : ∀ i, BigToricMetric (D i))
    (u : Fin (m + 1) → X → EReal) (hu : ∀ i, u i ∈ (h i).PSHTor)
    (S : Finset (Fin (m + 1))) :
    ∃ (H : BigToricMetric (∑ i ∈ S, D i))
      (hU : IsThetaPshPotential H.form.val (fun p => ∑ i ∈ S, u i p)),
      thetaPotentialCurrent H.form.val (fun p => ∑ i ∈ S, u i p) hU =
        ∑ i ∈ S, thetaPotentialCurrent (h i).form.val (u i)
          ((isThetaPSH_iff_nativeThetaPotential (h i).atlasForm (u i)).mp (hu i).1) ∧
      (fun p => ∑ i ∈ S, u i p) ∈ H.PSHTor ∧
      sourceIVolume H.atlasForm (fun p => ∑ i ∈ S, u i p)
        ((isThetaPSH_iff_nativeThetaPotential H.atlasForm _).mpr hU) =
          ((m + 1).factorial : ENNReal) *
            volume (sourceMinkowskiSubsetSum (fun i => (h i).newtonBody (u i)) S) := by
  classical
  obtain ⟨H, hform, hpot⟩ := BigToricMetric.exists_finite_sum_metric D h S
  let c : Fin (m + 1) → ℝ := fun i => if i ∈ S then 1 else 0
  have hc (i : Fin (m + 1)) : 0 ≤ c i := by
    dsimp only [c]
    split_ifs <;> norm_num
  have hnative (i : Fin (m + 1)) : IsThetaPshPotential (h i).form.val (u i) :=
    (isThetaPSH_iff_nativeThetaPotential (h i).atlasForm (u i)).mp (hu i).1
  obtain ⟨hU, hcurrent⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_finite_combination
    (c := c) hc hnative
  have hF : sumForm Finset.univ c (fun i => (h i).form) = H.form := by
    simpa [sumForm, c, Finset.sum_filter] using hform.symm
  have hP : sumPot Finset.univ c u = fun p => ∑ i ∈ S, u i p := by
    funext p
    simp [sumPot, c, apply_ite]
  have hU' : IsThetaPshPotential H.form.val (fun p => ∑ i ∈ S, u i p) := by
    simpa only [hF, hP] using hU
  have hcurrent' : thetaPotentialCurrent H.form.val (fun p => ∑ i ∈ S, u i p) hU' =
      ∑ i, c i • thetaPotentialCurrent (h i).form.val (u i) (hnative i) := by
    simpa only [hF, hP] using hcurrent
  have htor : (fun p => ∑ i ∈ S, u i p) ∈ H.PSHTor := by
    refine ⟨(isThetaPSH_iff_nativeThetaPotential H.atlasForm _).mpr hU', ?_⟩
    intro a ha p
    exact Finset.sum_congr rfl (fun i _ => (hu i).2 a ha p)
  refine ⟨H, hU', ?_, htor, ?_⟩
  · simpa [c, Finset.sum_filter] using hcurrent'
  · rw [H.sourceIVolume_eq_factorial_volume_newtonBody htor,
      newtonBody_finite_sum_metric D h u hu S H hpot]

end PositiveDimension
end SGPT.Toric

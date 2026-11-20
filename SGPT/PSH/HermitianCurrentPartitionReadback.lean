import SGPT.PSH.HermitianBidimensionOneOverlap
import SGPT.Foundations.Analysis.Pending.ChartWeightedPatchCurrent
import SGPT.Foundations.Analysis.Pending.RelativeSupportWeightedCompactTesting
import SGPT.Foundations.Analysis.Pending.NaturalSubdomainCurrentPullback

/-!
# Original local readers of the partitioned Hermitian mixed current

Actual bidimension-one covariance identifies every supported transported
summand. The manufactured partition then cancels on all original compact
full tests. Bounded Borel multiplication retains the same original reader.
This is current descent, before any scalar trace or integration-by-parts
estimate is used.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
  LocalCurrentPullback LocalCurrentPullbackDdc
  ChartPartitionRelativeSupports ChartWeightedPatchCurrent WholeChartPotentialPatchTransition
  RelativeSupportWeightedCompactTesting NaturalSubdomainCurrentPullback
  BidimensionOneFullTestFunctional BorelChartWeightedPatchCurrent BorelChartZeroExtension
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

omit [IsComplexManifold (m + 1) M] in
/-- The coordinate-domain inclusion, with the native open-domain type. -/
theorem CoordinatePatch.domainInChart (P : CoordinatePatch (m + 1) M) :
    P.domain ≤ chartTarget P.chart := fun _ hz => P.domain_le_target hz

private theorem pullback_congr_current {n r : ℕ} {A B : Opens (ComplexModel n)}
    {τ ι : ComplexModel n → ComplexModel n} (h : BedfordTaylor.IsBiholomorphicPair A B τ ι)
    {S T : LocalProductCurrent n B r} (hS : IsPositive S) (hT : IsPositive T)
    (heq : S = T) : pullback h hS = pullback h hT := by
  subst T
  rfl

/-- An original compact test reads the actual weighted transport of the
original Hermitian mixed current, with its cutoff produced internally. -/
theorem exists_patch_weighted_test (P Q : BackgroundPatch omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hsupp : tsupport χ ⊆ Q.geometry.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (φ : 𝓓(P.geometry.domain, ℝ)) :
    ∃ ψ : 𝓓(P.geometry.domain, ℝ),
      (∀ x, ψ x = φ x * chartWeight P.geometry.chart χ x) ∧
      ∀ γ : formSpan (m + 1) 1,
        chartWeightedPullback P.geometry.chart Q.geometry.zeroPotentialPatch
          (Q.bidimensionOneCurrent_isPositive u hu hb) χ hχ hsupp hnonneg γ
          (extTest P.geometry.domainInChart φ) = P.bidimensionOneCurrent u γ ψ := by
  let TQ := Q.bidimensionOneCurrent u
  let hQ : IsPositive TQ := Q.bidimensionOneCurrent_isPositive u hu hb
  let QQ := Q.geometry.zeroPotentialPatch
  let hg := WholeChartPotentialPatchTransition.isBiholomorphicPair P.geometry.chart QQ
  let hR := isPositive_restrict hQ hg.2.1
  have hA0A : P.geometry.overlapDomain Q.geometry ≤ chartOverlapDomain P.geometry.chart QQ :=
    fun _ hz => ⟨P.geometry.domainInChart hz.1, hz.2⟩
  have hB0B : Q.geometry.overlapDomain P.geometry ≤ patchOverlapDomain P.geometry.chart QQ :=
    fun _ hz => ⟨hz.1, hz.2.1⟩
  have hdouble : restrict hB0B (restrict hg.2.1 TQ) =
      restrict (Q.geometry.overlapDomain_le P.geometry) TQ := by
    ext γ η
    simp only [LocalBedfordTaylorLocality.restrict_apply]
    apply congrArg (TQ γ)
    apply TestFunction.ext
    intro x
    exact (extTest_apply hg.2.1 (extTest hB0B η) x).trans
      ((extTest_apply hB0B η x).trans
        (extTest_apply (Q.geometry.overlapDomain_le P.geometry) η x).symm)
  have hsmaller : restrict hA0A (pullback hg.2.2 hR) =
      restrict (P.geometry.overlapDomain_le Q.geometry) (P.bidimensionOneCurrent u) := by
    calc
      _ = pullback (P.geometry.isBiholomorphicPair Q.geometry)
          (isPositive_restrict hR hB0B) :=
        (pullback_on_subdomains hg.2.2 (P.geometry.isBiholomorphicPair Q.geometry)
          hA0A hB0B hR).symm
      _ = pullback (P.geometry.isBiholomorphicPair Q.geometry)
          (isPositive_restrict hQ (Q.geometry.overlapDomain_le P.geometry)) :=
        pullback_congr_current _ _ _ hdouble
      _ = _ := P.bidimensionOneCurrent_overlap Q u hu hb
  let hw := chartWeight_relativeSupport P.geometry.chart χ hχ QQ.source hsupp hnonneg
  have hχc : ContDiffOn ℝ ∞ (chartWeight P.geometry.chart χ) (chartTarget P.geometry.chart) :=
    (hχ P.geometry.chart).congr (fun z hz => indicator_of_mem hz _)
  obtain ⟨η, hη, hread⟩ := exists_weighted_test hg.2.2 hR hg.1
    (chartWeight P.geometry.chart χ) hχc hw.2.2.2 (extTest P.geometry.domainInChart φ)
  have hfunc : (η : ComplexModel (m + 1) → ℝ) =
      fun x => φ x * chartWeight P.geometry.chart χ x := by
    funext x
    exact (hη x).trans (congrArg (fun a : ℝ => a * chartWeight P.geometry.chart χ x)
      (extTest_apply P.geometry.domainInChart φ x))
  let η' : 𝓓(P.geometry.overlapDomain Q.geometry, ℝ) :=
    { toFun := η
      contDiff' := η.contDiff
      hasCompactSupport' := η.hasCompactSupport
      tsupport_subset' := fun x hx => by
        rw [hfunc] at hx
        have hP := φ.tsupport_subset (tsupport_mul_subset_left hx)
        exact ⟨hP, (hw.2.2.2
          ⟨tsupport_mul_subset_right hx, P.geometry.domainInChart hP⟩).2⟩ }
  have hext : extTest hA0A η' = η := by
    ext x
    rw [extTest_apply]
    rfl
  let ψ := extTest (P.geometry.overlapDomain_le Q.geometry) η'
  refine ⟨ψ, ?_, ?_⟩
  · intro x
    change extTest (P.geometry.overlapDomain_le Q.geometry) η' x = _
    rw [extTest_apply]
    exact congrFun hfunc x
  · intro γ
    change RelativeSupportWeightedCurrentPullback.weightedExtendedPullback hg.2.2 hR
      hg.1 (chartWeight P.geometry.chart χ) hw.1 hw.2.2.2 γ
        (extTest P.geometry.domainInChart φ) = _
    calc
      _ = pullback hg.2.2 hR γ η := hread γ
      _ = restrict hA0A (pullback hg.2.2 hR) γ η' := by
        rw [LocalBedfordTaylorLocality.restrict_apply, hext]
      _ = restrict (P.geometry.overlapDomain_le Q.geometry)
          (P.bidimensionOneCurrent u) γ η' := by rw [hsmaller]
      _ = P.bidimensionOneCurrent u γ ψ := rfl

namespace MixedCurrentPartition

/-- The supported finite partition recovers the SAME original local
bidimension-one Hermitian current on each genuine correction patch. -/
theorem unweighted_chartCurrent_restrict (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (P : BackgroundPatch omega) :
    restrict P.geometry.domainInChart
      (∑ j, chartWeightedPullback P.geometry.chart (D.patch j).geometry.zeroPotentialPatch
        ((D.patch j).bidimensionOneCurrent_isPositive u hu hb)
        (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j)) =
      P.bidimensionOneCurrent u := by
  classical
  ext γ φ
  choose ψ hψ hread using fun j => exists_patch_weighted_test P (D.patch j) u hu hb
    (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j) φ
  have hpsum : ∑ j, ψ j = φ := by
    ext x
    simp only [_root_.sum_apply]
    calc
      ∑ j, ψ j x = ∑ j, φ x * chartWeight P.geometry.chart (D.weight j) x :=
        Finset.sum_congr rfl fun j _ => hψ j x
      _ = φ x := by
        by_cases hx : x ∈ P.geometry.domain
        · have htarget : x ∈ P.geometry.chart.val.target := P.geometry.domain_le_target hx
          simp only [chartWeight, indicator_of_mem htarget]
          rw [← Finset.mul_sum, D.sum_one, mul_one]
        · have hzero := testFunction_eq_zero_of_notMem φ hx
          simp only [hzero, zero_mul, Finset.sum_const_zero]
  simp only [LocalBedfordTaylorLocality.restrict_apply, LinearMap.sum_apply, _root_.sum_apply]
  calc
    _ = ∑ j, P.bidimensionOneCurrent u γ (ψ j) :=
      Finset.sum_congr rfl fun j _ => hread j γ
    _ = P.bidimensionOneCurrent u γ (∑ j, ψ j) :=
      (map_sum (P.bidimensionOneCurrent u γ) ψ Finset.univ).symm
    _ = P.bidimensionOneCurrent u γ φ := by rw [hpsum]

end MixedCurrentPartition
end SGPT.PSH.HermitianGlobalProducts

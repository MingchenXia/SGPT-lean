import SGPT.Okounkov.EffectiveDivisorMetricGeneric
import SGPT.Okounkov.EffectiveDivisorDimensionZero
import SGPT.Okounkov.FlattenedDivisorMetric
import SGPT.Toric.GlobalTropicalMixedEnergy
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.MeteredDivisorWeightBounds

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open GlobalMultilinearExpansion
open scoped Topology BigOperators ENNReal

section Cartier

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual Cartier ideals internally manufacture metrics and one genuine global
pole function, including the empty family and complex dimension zero. -/
theorem exists_qpsh_pole_union_of_effective_divisors
    (D : Fin N → EffectiveDivisor n M) :
    ∃ (E : Fin N → MeteredEffectiveQDivisor n M) (ψ : M → EReal),
      (∀ j, (E j).support = (D j).support) ∧
      (∀ j, DivisorMetric.IsDivisorMetric (D j) (E j)) ∧
      (∀ x, ψ x = ∑ j, (E j).weight x) ∧
      IsGlobalQuasiPshPotential (n := n) ψ ∧
      {x | ψ x = ⊥} = ⋃ j, (D j).support ∧
      (n = 0 → {x | ψ x = ⊥} = ∅) := by
  classical
  choose E hsupport hmetric using fun j => DivisorMetric.exists_divisorMetric (D j)
  let ψ : M → EReal := fun x => ∑ j, (E j).weight x
  have htheta j := SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric
    (D j) (E j) (hmetric j)
  have hqpsh : IsGlobalQuasiPshPotential (n := n) ψ := by
    by_cases hN : N = 0
    · subst N
      simpa [ψ] using isGlobalQuasiPshPotential_const (n := n) (M := M) 0
    · let j₀ : Fin N := ⟨0, Nat.pos_of_ne_zero hN⟩
      have hT : (Finset.univ : Finset (Fin N)).Nonempty := ⟨j₀, Finset.mem_univ j₀⟩
      have hs := MixedSummandCapacityDomination.isThetaPshPotential_sumPot hT
        (w := fun _ : Fin N => (1 : ℝ)) (fun _ => zero_lt_one)
        (alpha := fun j => (E j).curvature) htheta
      have heq : sumPot Finset.univ (fun _ : Fin N => (1 : ℝ))
          (fun j => (E j).weight) = ψ := by
        funext x
        simp [GlobalMultilinearExpansion.sumPot, ψ]
      exact heq ▸ hs.quasiPshPotential
  have hpoles : {x | ψ x = ⊥} = ⋃ j, (D j).support := by
    ext x
    change ψ x = ⊥ ↔ x ∈ ⋃ j, (D j).support
    constructor
    · intro hx
      by_contra hout
      have hfinite j : (((E j).weight x).toReal : EReal) = (E j).weight x := by
        apply EReal.coe_toReal ((htheta j).quasiPshPotential.1.ne_top x)
        intro hbot
        apply hout
        apply Set.mem_iUnion.mpr
        refine ⟨j, ?_⟩
        rw [← hsupport j]
        exact hbot
      have hsum : ψ x = ((∑ j, ((E j).weight x).toReal : ℝ) : EReal) := by
        calc
          ψ x = ∑ j, ((((E j).weight x).toReal : ℝ) : EReal) := by
            apply Finset.sum_congr rfl
            intro j _
            exact (hfinite j).symm
          _ = ((∑ j, ((E j).weight x).toReal : ℝ) : EReal) :=
            (MeteredDivisorWeightBounds.coe_finsetSum Finset.univ
              (fun j => ((E j).weight x).toReal)).symm
      rw [hsum] at hx
      exact EReal.coe_ne_bot _ hx
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      have hbot : (E j).weight x = ⊥ := by
        rw [← hsupport j] at hj
        exact hj
      exact MeteredDivisorWeightBounds.sum_eq_bot_of_eq_bot (Finset.mem_univ j) hbot
  refine ⟨E, ψ, hsupport, hmetric, fun _ => rfl, hqpsh, hpoles, ?_⟩
  intro hn
  subst n
  rw [hpoles]
  simp only [SGPT.Okounkov.effectiveDivisor_support_eq_empty_of_dimension_zero,
    Set.iUnion_empty]

end Cartier

section SmoothBoundary

variable {m N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M]

/-- Original smooth closed codimension-one carriers manufacture the actual
Cartier ideals, metrics and independent boundary pole function. -/
theorem exists_boundary_pole_function_of_smooth_hypersurfaces
    (W : Fin N → Set M) (hW : ∀ j, IsClosedConnectedSubmanifold (m + 1) (W j) m) :
    ∃ (D : Fin N → EffectiveDivisor (m + 1) M)
      (E : Fin N → MeteredEffectiveQDivisor (m + 1) M) (ψ : M → EReal),
      (∀ j, (D j).ideal = vanishingIdeal (n := m + 1) (W j)) ∧
      (∀ j, (D j).support = W j) ∧
      (∀ j, (E j).support = W j) ∧
      (∀ j, DivisorMetric.IsDivisorMetric (D j) (E j)) ∧
      (∀ x, ψ x = ∑ j, (E j).weight x) ∧
      IsGlobalQuasiPshPotential (n := m + 1) ψ ∧
      {x | ψ x = ⊥} = ⋃ j, W j := by
  classical
  have hdiv j := SGPT.Okounkov.exists_normalized_smooth_divisor_metric_normal_forms (hW j)
  choose D hideal E₀ hsupp₀ hmetric₀ hnormal using hdiv
  have hsupp j : (D j).support = W j := by
    calc
      (D j).support = (E₀ j).support :=
        (StepFourNoComponentContainsW.support_eq_of_isDivisorMetric (hmetric₀ j)).symm
      _ = W j := hsupp₀ j
  obtain ⟨E, ψ, hED, hmetric, hsum, hqpsh, hpoles, _⟩ :=
    exists_qpsh_pole_union_of_effective_divisors D
  refine ⟨D, E, ψ, hideal, hsupp, fun j => (hED j).trans (hsupp j),
    hmetric, hsum, hqpsh, ?_⟩
  rw [hpoles]
  congr 1
  funext j
  exact hsupp j

end SmoothBoundary

section WholeMixedMeasure

open SGPT.Convex

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : Fin n → ClosedRealOneOneForm n M} {U : Fin n → M → EReal}
  {ρ : Fin n → ComplexModel n → ℝ}

/-- Geometric boundary coverage produces the independent quasi-PSH pole
geometry, boundary nullity and the whole original mixed tropical measure. -/
theorem globalMixedMeasure_eq_tropical_chart_of_effective_divisor_boundary
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (U i)) (e : ComplexChart n M)
    (hD : (tropicalSmoothDomain n : Set (ComplexModel n)) ⊆ e.val.target)
    (hρ : ∀ i, IsSmoothLocalPotential (θ i).val e (tropicalSmoothDomain n) (ρ i))
    (F : Fin n → RealConvexFunction (EuclideanSpace ℝ (Fin n)))
    (heq : ∀ i, EqOn (fun z => chartFunction (U i) e z + (ρ i z : EReal))
      (fun z => ((F i).val (tropicalization z) : EReal)) (tropicalSmoothDomain n))
    (D : Fin N → EffectiveDivisor n M)
    (hcover : {x | x ∈ e.val.source ∧ e.val x ∈ tropicalSmoothDomain n}ᶜ ⊆
      ⋃ j, (D j).support) :
    let P := mixedTropicalPotentialPatch e hD hρ F heq
    (P.source : Set M) = {x | x ∈ e.val.source ∧ e.val x ∈ tropicalSmoothDomain n} ∧
      GlobalNonPluripolar.globalMixedMeasure θ U hu (P.source : Set M)ᶜ = 0 ∧
      GlobalNonPluripolar.globalMixedMeasure θ U hu =
        P.pushMeasure (tropicalCanonicalMixedBTMeasure F) := by
  classical
  let P := mixedTropicalPotentialPatch e hD hρ F heq
  obtain ⟨_E, ψ, _hsupp, _hmetric, _hsum, hψ, hpoles, _hzero⟩ :=
    exists_qpsh_pole_union_of_effective_divisors D
  have hsource : (P.source : Set M) =
      {x | x ∈ e.val.source ∧ e.val x ∈ tropicalSmoothDomain n} := rfl
  have hpole : (P.source : Set M)ᶜ ⊆ {x | ψ x = ⊥} := by
    rw [hpoles, hsource]
    exact hcover
  have hnull : GlobalNonPluripolar.globalMixedMeasure θ U hu (P.source : Set M)ᶜ = 0 :=
    le_antisymm ((measure_mono hpole).trans_eq
      (GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_quasiPsh hu hψ)) bot_le
  exact ⟨hsource, hnull,
    globalMixedMeasure_eq_mixedTropical_chart_pushMeasure hu e hD hρ F heq hψ hpole⟩

end WholeMixedMeasure

end SGPT.Toric

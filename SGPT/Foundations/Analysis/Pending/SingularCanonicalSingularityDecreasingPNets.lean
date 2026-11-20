import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityPositiveCauchyFilters
import SGPT.Foundations.Analysis.Pending.ActualMixedMassGlobalPMonotone
import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

/-! # Genuine Cauchyness and limits of decreasing P-type nets

SGPT PDF0231--0232 Corollary 6.2.7 decreasing P-type net clause. Actual
independent endpoint masses are monotone and finite; their genuine real
average converges. Exact ordered distance and an actual directed common
upper bound internally prove Cauchyness, without comparing arbitrary
original indices. The original fixed-background order consumer then
produces a genuine model limit using the proved positive Cauchy theorem.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingPNets

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  RelativeEnergy MixedMass ThetaPshL1Topology SingularMinimalCanonicalRay
  SingularGlobalPOrder SingularGlobalPEnvelopeBridge ActualMixedMassGlobalPMonotone
  SingularCanonicalSingularityDistance SingularCanonicalOrderedMixedMassDistance
  SingularCanonicalSingularityPositiveCauchyFilters

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual decreasing global P-types produce genuine native Cauchyness
through finite original endpoint masses; original masses may all vanish. -/
theorem cauchy_map_of_antitone_sourcePOrder (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val)
    (horder : ∀ i j, i ≤ j → SourcePOrder (n := n) (ui j).val (ui i).val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Cauchy (map ui atTop) := by
  classical
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let V := thetaPshSupremum θ.val
  have hV : IsThetaPshPotential θ.val V :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  let T : I → Fin (n + 1) → Fin n → M → EReal := fun i k =>
    endpointMixedPotential k (ui i).val V
  have hT (i : I) (k : Fin (n + 1)) (s : Fin n) :
      IsThetaPshPotential θ.val (T i k s) := by
    dsimp only [T, endpointMixedPotential]
    split_ifs with hs
    · exact (ui i).property
    · exact hV
  let μ : I → Fin (n + 1) → ℝ := fun i k =>
    (endpointMixedMass θ V (ui i).val hV (ui i).property k).toReal
  have hμanti (k : Fin (n + 1)) : Antitone (fun i => μ i k) := by
    intro i j hij
    have hrel (s : Fin n) : SourcePOrder (n := n) (T j k s) (T i k s) := by
      dsimp only [T, endpointMixedPotential]
      split_ifs with hs
      · exact horder i j hij
      · exact sourcePOrder_refl_of_isThetaPshPotential omega hV
    have hm := globalMixedMass_mono_of_sourcePOrder omega (hT j k) (hT i k) hrel
    change endpointMixedMass θ V (ui j).val hV (ui j).property k ≤
      endpointMixedMass θ V (ui i).val hV (ui i).property k at hm
    exact ENNReal.toReal_mono (globalMixedMass_lt_top omega (fun s => (hT i k s).1)).ne hm
  let a : I → ℝ := fun i => (∑ k : Fin (n + 1), μ i k) / (n + 1 : ℝ)
  have ha0 (i : I) : 0 ≤ a i := by
    dsimp only [a, μ]
    positivity
  have haanti : Antitone a := by
    intro i j hij
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun k _ => hμanti k hij)
      (by positivity : (0 : ℝ) ≤ n + 1)
  have hbounded : BddBelow (range a) := ⟨0, by rintro _ ⟨i, rfl⟩; exact ha0 i⟩
  let l : ℝ := ⨅ i, a i
  have halim : Tendsto a atTop (𝓝 l) := tendsto_atTop_ciInf haanti hbounded
  have hdist (i j : I) (hij : i ≤ j) : dist (ui i) (ui j) = a i - a j := by
    rw [dist_comm (ui i) (ui j), dist_eq_singularityDistance_toReal omega θ hbig,
      singularityDistance_eq_mixedMass_sub_of_sourcePOrder omega θ hbig
        (ui j).property (ui i).property (horder i j hij), EReal.toReal_coe]
    change (∑ k : Fin (n + 1), (μ i k - μ j k)) / (n + 1 : ℝ) = a i - a j
    rw [Finset.sum_sub_distrib, sub_div]
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  have hev : ∀ᶠ i in atTop, a i < l + ε / 2 :=
    (tendsto_order.mp halim).2 (l + ε / 2) (by linarith)
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp hev
  refine ⟨ui '' Ici i₀, image_mem_map (eventually_ge_atTop i₀), ?_⟩
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hlk : l ≤ a k := ciInf_le hbounded k
  calc
    dist (ui i) (ui j) ≤ dist (ui i) (ui k) + dist (ui k) (ui j) := dist_triangle _ _ _
    _ = (a i - a k) + (a j - a k) := by rw [hdist i k hik, dist_comm (ui k) (ui j), hdist j k hjk]
    _ < ε := by linarith [hi₀ i hi, hi₀ j hj]

/-- The original fixed-background decreasing P-type contract internally
produces Cauchyness and a true positive model limit along the whole directed net. -/
theorem exists_model_limit_of_antitone_pOrderWith_of_uniform_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val)
    (horder : ∀ i j, i ≤ j → POrderWith θ (ui j).val (ui i).val)
    {δ : ℝ} (hδ : 0 < δ) (hstage : ∀ i, ENNReal.ofReal δ ≤
      DiagonalMass.diagonalPotentialMass θ (ui i).val (ui i).property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    ∃ U : ThetaPshL1 θ.val, IsModelPotential θ U.val ∧
      ENNReal.ofReal δ ≤ DiagonalMass.diagonalPotentialMass θ U.val U.property ∧
      Tendsto ui atTop (𝓝 U) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hsource (i j : I) (hij : i ≤ j) : SourcePOrder (n := n) (ui j).val (ui i).val :=
    sourcePOrder_of_pOrderWith omega θ (ui j).property (ui i).property (horder i j hij)
  exact exists_model_limit_of_cauchy_map omega θ hbig atTop ui hδ hstage
    (cauchy_map_of_antitone_sourcePOrder omega θ hbig ui hsource)

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingPNets

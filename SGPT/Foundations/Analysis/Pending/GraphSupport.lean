import SGPT.Foundations.Analysis.Pending.GraphTangentialReduction
import SGPT.Foundations.Analysis.Pending.DiagonalSupport

set_option autoImplicit false

/-!
# The support theorem on the graph of a holomorphic map

Let `V`, `X` be compact complex manifolds of dimension `n = q + 1`, `V` connected, `f : V → X`
holomorphic, `Γ_f = {(v, x) | f v = x}` its graph and `[Γ_f] = (id, f)_*[V]` the current of
integration over it (`graphCurrent`, for a Kähler form `w` on `V`).  For a closed positive current
`Θ` of bidimension `(n, n)` on `V × X`:

* if `Θ` is carried by `Γ_f`, then `Θ = c [Γ_f]` with `c ≥ 0` (`eq_smul_graphCurrent`);
* in general `𝟙_{Γ_f} Θ = c [Γ_f]` with `c ≥ 0` and `Θ - c [Γ_f] = 𝟙_{V × X \ Γ_f} Θ` is positive
  (`exists_restrictCurrent_graph_eq_smul`) -- TN-CLASSICAL's exact target for the graph route of
  the `(P)` step of Boucksom 4.8 (earlier discussion the statement under discussion; `demailly-cadg:III.2.10`, `III.2.13`,
  `III.2.14` for the smooth connected submanifold `Γ_f`).  `f = id` is
  `DiagonalSupport.exists_restrictCurrent_diagonal_eq_smul`.

*Proof.*  `μ = p₁_* Θ` is closed positive of top bidimension on `V` (`IsClosedCurrent.pushforward`),
hence `μ = c [V]` (`ClosedTopCurrents.eq_smul_integrationCurrent_of_isClosedCurrent`, `V` connected).
By the tangential reduction on the graph (`GraphTangentialReduction.apply_pullback_graphProjMap_eq`,
`Φ = (id, f) ∘ p₁`), `Θ φ = Θ(p₁^*(id, f)^*φ) = μ((id, f)^*φ) = c [V]((id, f)^*φ) = c [Γ_f] φ`.  For
a general `Θ`, `𝟙_{Γ_f} Θ` is closed by Skoda--El Mir for the graph
(`SkodaElMirHolomorphic.isClosedCurrent_restrictCurrent_graph`) and carried by `Γ_f`.

Step G6 of the graph support plan.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.GraphSupport

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  StronglyPositiveForms ProductTestForms PositiveProductCurrents ClosedProductCurrents
  CurrentTraceMeasure CurrentRestriction TopDegreeDensity ProductComplexManifold
  DiagonalFibreIntegration ClosedTopCurrents IntegrationCurrent GraphTangentialChart
  GraphTangentialReduction
open scoped ProductComplexManifold

variable {q : ℕ} {V X : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] [CompactSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X] [IsComplexManifold (q + 1) X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X] {f : V → X}

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- **The current of integration over the graph** `[Γ_f] = (id, f)_*[V]` (TN-CLASSICAL's definition,
I-0831 C-0032). -/
def graphCurrent (w : KahlerBackground (q + 1) V)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f) :
    ProductCurrent ((q + 1) + (q + 1)) (V × X) (q + 1) :=
  pushforward (contMDiff_prodMk contMDiff_id hf) (integrationCurrent w)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem graphCurrent_apply (w : KahlerBackground (q + 1) V)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)
    (φ : testSpace ((q + 1) + (q + 1)) (V × X) (q + 1)) :
    graphCurrent w hf φ =
      integrationCurrent w (pullbackTestLM (contMDiff_prodMk contMDiff_id hf) (q + 1) φ) :=
  rfl

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The graph current is positive. -/
theorem isPositive_graphCurrent (w : KahlerBackground (q + 1) V)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f) :
    IsPositive (graphCurrent w hf) :=
  (isPositive_integrationCurrent w).pushforward (contMDiff_prodMk contMDiff_id hf)

variable (hf : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ f)

/-- **The support theorem on the graph**: a closed positive current of bidimension `(n, n)` on
`V × X` carried by the graph of `f` is a nonnegative multiple of the current of integration over
the graph. -/
theorem eq_smul_graphCurrent [ConnectedSpace V] (w : KahlerBackground (q + 1) V)
    (w' : KahlerBackground ((q + 1) + (q + 1)) (V × X))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (V × X) (q + 1)} (hΘ : IsPositive Θ)
    (hΘc : IsClosedCurrent Θ) (hcar : traceMeasure w' Θ hΘ {p : V × X | f p.1 = p.2}ᶜ = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ Θ = c • graphCurrent w hf := by
  set μ := PositiveProductCurrents.pushforward contMDiff_fst Θ with hμ
  have hμp : IsPositive μ := hΘ.pushforward contMDiff_fst
  have hμc : IsClosedCurrent μ :=
    DiagonalSupport.IsClosedCurrent.pushforward contMDiff_fst hΘ hΘc
  obtain ⟨c, hc0, hμeq⟩ := eq_smul_integrationCurrent_of_isClosedCurrent w hμp hμc
  refine ⟨c, hc0, LinearMap.ext fun φ => ?_⟩
  rw [← apply_pullback_graphProjMap_eq hf w' hΘ hΘc hcar φ, LinearMap.smul_apply,
    graphCurrent_apply, ← LinearMap.smul_apply, ← hμeq, hμ, pushforward_apply]
  exact hΘ.apply_eq_of_coeff_eqOn fun e z hz =>
    pullback_comp_geometricallyEq (contMDiff_prodMk contMDiff_id hf) contMDiff_fst _ e hz

/-- **The graph part of a closed positive current** (TN-CLASSICAL's target, I-0831 C-0032): for
every closed positive current `Θ` of bidimension `(n, n)` on `V × X` there is `c ≥ 0` with
`𝟙_{Γ_f} Θ = c [Γ_f]`, and then `Θ - c [Γ_f] = 𝟙_{V × X \ Γ_f} Θ` is positive. -/
theorem exists_restrictCurrent_graph_eq_smul [ConnectedSpace V] (w : KahlerBackground (q + 1) V)
    (w' : KahlerBackground ((q + 1) + (q + 1)) (V × X))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (V × X) (q + 1)} (hΘ : IsPositive Θ)
    (hΘc : IsClosedCurrent Θ) :
    ∃ c : ℝ, 0 ≤ c ∧ restrictCurrent w' Θ hΘ {p | f p.1 = p.2} = c • graphCurrent w hf ∧
      IsPositive (Θ - c • graphCurrent w hf) := by
  have hΓm : MeasurableSet {p : V × X | f p.1 = p.2} := (isClosed_graph hf).measurableSet
  have hRp := isPositive_restrictCurrent w' Θ hΘ {p : V × X | f p.1 = p.2}
  have hRc := (SkodaElMirHolomorphic.isClosedCurrent_restrictCurrent_graph hf w' hΘ hΘc).1
  have hcar : traceMeasure w' (restrictCurrent w' Θ hΘ {p : V × X | f p.1 = p.2}) hRp
      {p : V × X | f p.1 = p.2}ᶜ = 0 := by
    rw [traceMeasure_restrictCurrent w' Θ hΘ hΓm, Measure.restrict_apply hΓm.compl,
      compl_inter_self, measure_empty]
  obtain ⟨c, hc0, hceq⟩ := eq_smul_graphCurrent hf w w' hRp hRc hcar
  refine ⟨c, hc0, hceq, ?_⟩
  have hsplit := restrictCurrent_add_compl w' Θ hΘ hΓm
  have : Θ - c • graphCurrent w hf = restrictCurrent w' Θ hΘ {p : V × X | f p.1 = p.2}ᶜ := by
    calc Θ - c • graphCurrent w hf =
        (restrictCurrent w' Θ hΘ {p : V × X | f p.1 = p.2} +
          restrictCurrent w' Θ hΘ {p : V × X | f p.1 = p.2}ᶜ) -
          restrictCurrent w' Θ hΘ {p : V × X | f p.1 = p.2} := by rw [hsplit, hceq]
      _ = _ := add_sub_cancel_left _ _
  rw [this]
  exact isPositive_restrictCurrent w' Θ hΘ _

end SGPT.Foundations.Analysis.Pending.GraphSupport

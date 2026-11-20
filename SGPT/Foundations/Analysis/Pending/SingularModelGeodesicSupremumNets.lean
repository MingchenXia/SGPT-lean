import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicSupremumProducer

set_option autoImplicit false

/-!
# Actual increasing Perron nets converge to their produced slice suprema

Xia SGPT PDF0174 Proposition 4.3.4 uses increasing-energy net continuity
from PDF0128--0129. Actual endpoint order makes the actual Perron slices
increasing. Their finite-energy regularized supremum is produced from
the natural endpoint data, and genuine directed Darvas continuity gives
both actual defining energy limits. No affinity, path-limit certificate,
or countable cofinality assumption is used. Geodesic identification is
kept separate.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicSupremumNets

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelGeodesicSupremumProducer

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Actual monotone endpoint nets produce Darvas, real, and defining extended-energy limits at each actual slice supremum. -/
theorem tendsto_at_regularized_geodesic_supremum
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {ui₀ ui₁ : I → M → EReal}
    (hui₀ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₀ i) hφ)
    (hui₁ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₁ i) hφ)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hreg₀ : uscRegularization (⨆ i, ui₀ i) = u₀)
    (hreg₁ : uscRegularization (⨆ i, ui₁ i) = u₁)
    (hm₀ : ∀ x, Monotone fun i => ui₀ i x)
    (hm₁ : ∀ x, Monotone fun i => ui₁ i x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun i => relativeD1 θ φ hφ
      (finiteGeodesic θ.val (ui₀ i) (ui₁ i) t)
      (uscRegularization (⨆ j, finiteGeodesic θ.val (ui₀ j) (ui₁ j) t)))
      atTop (𝓝 0) ∧
    Tendsto (fun i => (energy θ φ hφ
      (finiteGeodesic θ.val (ui₀ i) (ui₁ i) t)).toReal) atTop
      (𝓝 (energy θ φ hφ
        (uscRegularization (⨆ j, finiteGeodesic θ.val (ui₀ j) (ui₁ j) t))).toReal) ∧
    Tendsto (fun i => energy θ φ hφ
      (finiteGeodesic θ.val (ui₀ i) (ui₁ i) t)) atTop
      (𝓝 (energy θ φ hφ
        (uscRegularization (⨆ j, finiteGeodesic θ.val (ui₀ j) (ui₁ j) t)))) := by
  have hG (i : I) := relativeFiniteEnergyPreceq_finiteGeodesic omega (hui₀ i) (hui₁ i) ht
  have hH := (subgeodesic_and_finite_energy_of_regularized_endpoint_suprema
    omega hui₀ hui₁ hu₀ hu₁ hreg₀ hreg₁).2 t ht |>.1
  have hm : ∀ x, Monotone fun i => finiteGeodesic θ.val (ui₀ i) (ui₁ i) t x :=
    fun x i j hij => finiteGeodesic_mono (fun y => hm₀ y hij) (fun y => hm₁ y hij) t x
  have hd := SingularModelDarvasEnergyContinuity.relativeD1_tendsto_zero_of_directed_monotone_regularized
    omega hG hH hm rfl
  exact ⟨hd,
    SingularModelDarvasEnergyContinuity.toReal_energy_tendsto_of_relativeD1_tendsto_zero omega hG hH hd,
    SingularModelDarvasEnergyContinuity.energy_tendsto_of_relativeD1_tendsto_zero omega hG hH hd⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicSupremumNets

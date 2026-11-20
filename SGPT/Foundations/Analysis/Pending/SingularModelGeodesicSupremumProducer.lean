import SGPT.Foundations.Analysis.Pending.SubgeodesicPerronStability
import SGPT.Foundations.Analysis.Pending.SingularModelBoundedSupremumEnergyClosure

set_option autoImplicit false

/-!
# Actual finite-energy regularized suprema of Perron geodesics

Xia SGPT PDF0174 Proposition 4.3.4 first forms the regularized supremum
of the actual geodesics. Genuine endpoint regularized suprema produce
the common real family bound internally. Actual arbitrary-family
subgeodesic stability and finite-energy supremum closure then produce
the genuine subgeodesic, its actual E1 slices, and its Perron upper bound.
This independent arbitrary-family precursor uses no energy affinity and
does not assert equality with the endpoint-limit geodesic.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicSupremumProducer

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Actual endpoint suprema produce a genuine subgeodesic supremum with actual finite-energy slices. -/
theorem subgeodesic_and_finite_energy_of_regularized_endpoint_suprema
    {I : Type*} [Nonempty I] (omega : KahlerBackground n M)
    {ui₀ ui₁ : I → M → EReal}
    (hui₀ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₀ i) hφ)
    (hui₁ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₁ i) hφ)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hreg₀ : uscRegularization (⨆ i, ui₀ i) = u₀)
    (hreg₁ : uscRegularization (⨆ i, ui₁ i) = u₁) :
    IsSubgeodesicFrom θ.val
      (fun t => uscRegularization (⨆ i, finiteGeodesic θ.val (ui₀ i) (ui₁ i) t))
      u₀ u₁ ∧
    ∀ t ∈ Ioo (0 : ℝ) 1,
      RelativeFiniteEnergyPreceq θ φ
        (uscRegularization (⨆ i, finiteGeodesic θ.val (ui₀ i) (ui₁ i) t)) hφ ∧
      uscRegularization (⨆ i, finiteGeodesic θ.val (ui₀ i) (ui₁ i) t) ≤
        finiteGeodesic θ.val u₀ u₁ t := by
  have hi₀ (i : I) : ui₀ i ≤ u₀ := by
    rw [← hreg₀]
    exact (le_iSup ui₀ i).trans (le_uscRegularization _)
  have hi₁ (i : I) : ui₁ i ≤ u₁ := by
    rw [← hreg₁]
    exact (le_iSup ui₁ i).trans (le_uscRegularization _)
  obtain ⟨A, hA⟩ := exists_le_coe_of_isThetaPshPotential hu₀.1.plurisubharmonic
  obtain ⟨B, hB⟩ := exists_le_coe_of_isThetaPshPotential hu₁.1.plurisubharmonic
  have hC₀ : ∀ i x, ui₀ i x ≤ ((max A B : ℝ) : EReal) := fun i x =>
    (hi₀ i x).trans ((hA x).trans (EReal.coe_le_coe_iff.mpr (le_max_left A B)))
  have hC₁ : ∀ i x, ui₁ i x ≤ ((max A B : ℝ) : EReal) := fun i x =>
    (hi₁ i x).trans ((hB x).trans (EReal.coe_le_coe_iff.mpr (le_max_right A B)))
  have hsub (i : I) :=
    finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega (hui₀ i).1 (hui₁ i).1
  have hraw := SubgeodesicPerronStability.isSubgeodesicFrom_uscRegularization_iSup
    omega θ hsub hC₀ hC₁
  have hreg₀' : uscRegularization (fun x => ⨆ i, ui₀ i x) = u₀ := by
    have heq : (fun x => ⨆ i, ui₀ i x) = ⨆ i, ui₀ i := by
      funext x
      simp only [iSup_apply]
    rw [heq]
    exact hreg₀
  have hreg₁' : uscRegularization (fun x => ⨆ i, ui₁ i x) = u₁ := by
    have heq : (fun x => ⨆ i, ui₁ i x) = ⨆ i, ui₁ i := by
      funext x
      simp only [iSup_apply]
    rw [heq]
    exact hreg₁
  have hH : IsSubgeodesicFrom θ.val
      (fun t => uscRegularization (⨆ i, finiteGeodesic θ.val (ui₀ i) (ui₁ i) t))
      u₀ u₁ := by
    have hcurve : (fun t => uscRegularization
        (fun x => ⨆ i, finiteGeodesic θ.val (ui₀ i) (ui₁ i) t x)) =
        (fun t => uscRegularization (⨆ i, finiteGeodesic θ.val (ui₀ i) (ui₁ i) t)) := by
      funext t
      congr 1
      funext x
      simp only [iSup_apply]
    rw [hreg₀', hreg₁', hcurve] at hraw
    exact hraw
  refine ⟨hH, fun t ht => ⟨?_, subgeodesic_slice_le_finiteGeodesic hH t⟩⟩
  exact SingularModelBoundedSupremumEnergyClosure.relativeFiniteEnergyPreceq_uscRegularization_iSup
    omega (fun i => relativeFiniteEnergyPreceq_finiteGeodesic omega (hui₀ i) (hui₁ i) ht)
    (fun i x => SubgeodesicSupremumSlices.uniform_upper_bound_of_endpoint_bounds
      hsub hC₀ hC₁ i t ht x)

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicSupremumProducer

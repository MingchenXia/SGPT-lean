import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicClosedRestriction

set_option autoImplicit false

/-!
# Actual rooftop comparison for singular full-mass Perron geodesics

Xia SGPT PDF0174 Proposition 4.3.5 uses the Perron curve of endpoint
rooftops below the rooftop of the two time slices. Actual full-mass
rooftop closure and actual Perron monotonicity produce this comparison
throughout the endpoint-completed interval. This independent extension
requires no finite energy, bounded reference, same-type condition or
energy-affinity premise.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRooftopComparison

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ v₀ v₁ : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Actual endpoint-rooftop Perron curves lie below actual slice rooftops on the completed interval. -/
theorem closedGeodesic_rooftop_endpoints_le (omega : KahlerBackground n M)
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ)
    (hv₀ : RelativeFullMassPreceq θ φ v₀ hφ)
    (hv₁ : RelativeFullMassPreceq θ φ v₁ hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    closedSubgeodesicSlice
      (finiteGeodesic θ.val (rooftop θ u₀ v₀) (rooftop θ u₁ v₁))
      (rooftop θ u₀ v₀) (rooftop θ u₁ v₁) t ≤
    rooftop θ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t)
      (closedSubgeodesicSlice (finiteGeodesic θ.val v₀ v₁) v₀ v₁ t) := by
  by_cases ht0 : t = 0
  · simp only [ht0, closedSubgeodesicSlice_zero, le_refl]
  by_cases ht1 : t = 1
  · simp only [ht1, closedSubgeodesicSlice_one, le_refl]
  have hti : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  rw [closedSubgeodesicSlice_eq_curve hti, closedSubgeodesicSlice_eq_curve hti,
    closedSubgeodesicSlice_eq_curve hti]
  have hR₀ := relativeFullMassPreceq_rooftop omega hu₀ hv₀
  have hR₁ := relativeFullMassPreceq_rooftop omega hu₁ hv₁
  have hH := relativeFullMassPreceq_finiteGeodesic omega hR₀ hR₁ hti
  have hU := relativeFullMassPreceq_finiteGeodesic omega hu₀ hu₁ hti
  have hV := relativeFullMassPreceq_finiteGeodesic omega hv₀ hv₁ hti
  apply (le_rooftop_iff hU.plurisubharmonic hV.plurisubharmonic
    hH.plurisubharmonic).2
  constructor
  · exact finiteGeodesic_mono
      (rooftop_le_left hu₀.plurisubharmonic hv₀.plurisubharmonic)
      (rooftop_le_left hu₁.plurisubharmonic hv₁.plurisubharmonic) t
  · exact finiteGeodesic_mono
      (rooftop_le_right hu₀.plurisubharmonic hv₀.plurisubharmonic)
      (rooftop_le_right hu₁.plurisubharmonic hv₁.plurisubharmonic) t

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRooftopComparison

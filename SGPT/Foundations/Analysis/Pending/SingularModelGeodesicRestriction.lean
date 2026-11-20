import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
import SGPT.Foundations.Analysis.Pending.SubgeodesicGluing

set_option autoImplicit false

/-!
# Actual full-mass Perron curves restrict to their own Perron subsegments

Xia SGPT PDF0155--0156's closed-interval restriction. Actual full
singularity-order full-mass endpoints produce a genuine Perron subgeodesic
and actual full-mass closed slices. Actual affine restriction gives one
Perron comparison; actual dominating subgeodesic gluing and actual
competitor maximality give the reverse. There is no finite-energy,
same-type, bounded-reference, strip certificate or energy-affinity input.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRestriction

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

private theorem relativeFullMassPreceq_closedSlice (omega : KahlerBackground n M)
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ) (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    RelativeFullMassPreceq θ φ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) hφ := by
  by_cases ht0 : t = 0
  · simpa only [ht0, closedSubgeodesicSlice_zero] using hu₀
  by_cases ht1 : t = 1
  · simpa only [ht1, closedSubgeodesicSlice_one] using hu₁
  have hti : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  simpa only [closedSubgeodesicSlice_eq_curve hti] using
    relativeFullMassPreceq_finiteGeodesic omega hu₀ hu₁ hti

/-- Actual subgeodesic restriction and genuine dominating gluing identify every full-mass Perron subsegment. -/
theorem finiteGeodesic_closed_interval_restriction_eq (omega : KahlerBackground n M)
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ) (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ)
    {a b t : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (ht : t ∈ Ioo a b) :
    finiteGeodesic θ.val
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ a)
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ b)
      ((t - a) / (b - a)) = finiteGeodesic θ.val u₀ u₁ t := by
  classical
  have hU := finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hu₀ hu₁
  have hA := relativeFullMassPreceq_closedSlice omega hu₀ hu₁ ⟨ha, hab.le.trans hb⟩
  have hB := relativeFullMassPreceq_closedSlice omega hu₀ hu₁ ⟨ha.trans hab.le, hb⟩
  have hV := finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hA hB
  have hR := hU.closedAffineReparametrized ha hb hab
  have hinv (q : ℝ) : affineTimeReparam a b ((q - a) / (b - a)) = q := by
    unfold affineTimeReparam
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hdom : ∀ q ∈ Ioo a b, finiteGeodesic θ.val u₀ u₁ q ≤
      finiteGeodesic θ.val
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ a)
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ b)
        ((q - a) / (b - a)) := by
    intro q _
    have h := subgeodesic_slice_le_finiteGeodesic hR ((q - a) / (b - a))
    simpa only [affineReparametrizedCurve, hinv q] using h
  have hglue := SubgeodesicGluing.isSubgeodesicFrom_replacementCurve
    hU ha hb hab hV hdom
  refine le_antisymm ?_ (hdom t ht)
  simpa only [SubgeodesicGluing.replacementCurve, if_pos ht] using
    subgeodesic_slice_le_finiteGeodesic hglue t

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRestriction

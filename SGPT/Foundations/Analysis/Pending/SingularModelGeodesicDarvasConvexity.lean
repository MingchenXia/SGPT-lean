import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRooftopComparison
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicGeneralNativeContinuity
import SGPT.Foundations.Analysis.Pending.SingularGeodesicGeneralEnergyAffinity

set_option autoImplicit false

/-!
# Actual Darvas convexity along arbitrary singular-model geodesics

Xia SGPT PDF0174 Proposition 4.3.5. Actual finite-energy slice membership
and actual Perron restriction are produced on the complete closed interval.
Actual endpoint-rooftop Perron comparison and the independently proved
general energy affinity produce the defining distance chord and convexity,
without an affinity premise or bounded-model restriction.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicDarvasConvexity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelGeodesicRestriction
  SingularModelGeodesicNativeContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ v₀ v₁ : M → EReal}
  {hφ : IsModelPotential θ φ}

private theorem finiteEnergy_completedSlice (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    RelativeFiniteEnergyPreceq θ φ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) hφ :=
  (finiteEnergyGeodesicSegment omega ⟨u₀, hu₀⟩ ⟨u₁, hu₁⟩ ⟨t, ht⟩).property

private theorem completedSlice_restriction (omega : KahlerBackground n M)
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ)
    {a b s : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    closedSubgeodesicSlice
      (finiteGeodesic θ.val
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ a)
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ b))
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ a)
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ b) s =
    closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁
      (a + s * (b - a)) := by
  by_cases hs0 : s = 0
  · simp only [hs0, closedSubgeodesicSlice_zero, zero_mul, add_zero]
  by_cases hs1 : s = 1
  · simp only [hs1, closedSubgeodesicSlice_one, one_mul, add_sub_cancel]
  have hsi : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩
  have hti : a + s * (b - a) ∈ Ioo a b := by
    constructor
    · linarith [mul_pos hsi.1 (sub_pos.mpr hab)]
    · nlinarith [mul_pos (sub_pos.mpr hsi.2) (sub_pos.mpr hab)]
  have ht01 : a + s * (b - a) ∈ Ioo (0 : ℝ) 1 :=
    ⟨ha.trans_lt hti.1, hti.2.trans_le hb⟩
  rw [closedSubgeodesicSlice_eq_curve hsi, closedSubgeodesicSlice_eq_curve ht01]
  have hr := finiteGeodesic_closed_interval_restriction_eq omega hu₀ hu₁ ha hb hab hti
  have hid : (a + s * (b - a) - a) / (b - a) = s := by
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  simpa only [hid] using hr

/-- Genuine endpoint-rooftop comparison and genuine general energy affinity produce the actual closed-segment distance chord. -/
theorem relativeD1_closedGeodesics_le_endpoint_chord (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hv₀ : RelativeFiniteEnergyPreceq θ φ v₀ hφ)
    (hv₁ : RelativeFiniteEnergyPreceq θ φ v₁ hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t)
      (closedSubgeodesicSlice (finiteGeodesic θ.val v₀ v₁) v₀ v₁ t) ≤
    (1 - t) * relativeD1 θ φ hφ u₀ v₀ + t * relativeD1 θ φ hφ u₁ v₁ := by
  have hR₀ := relativeFiniteEnergyPreceq_rooftop omega hu₀ hv₀
  have hR₁ := relativeFiniteEnergyPreceq_rooftop omega hu₁ hv₁
  have hU := finiteEnergy_completedSlice omega hu₀ hu₁ ht
  have hV := finiteEnergy_completedSlice omega hv₀ hv₁ ht
  have hH := finiteEnergy_completedSlice omega hR₀ hR₁ ht
  have hR := relativeFiniteEnergyPreceq_rooftop omega hU hV
  have hle := SingularModelGeodesicRooftopComparison.closedGeodesic_rooftop_endpoints_le
    omega hu₀.1 hu₁.1 hv₀.1 hv₁.1 ht
  have hmono := SingularModelFiniteRealEnergy.toReal_energy_mono omega hH hR hle
  have hEH := SingularGeodesicGeneralEnergyAffinity.toReal_energy_closedSubgeodesicSlice_eq_chord
    omega hR₀ hR₁ ht
  have hEU := SingularGeodesicGeneralEnergyAffinity.toReal_energy_closedSubgeodesicSlice_eq_chord
    omega hu₀ hu₁ ht
  have hEV := SingularGeodesicGeneralEnergyAffinity.toReal_energy_closedSubgeodesicSlice_eq_chord
    omega hv₀ hv₁ ht
  rw [hEH] at hmono
  simp only [relativeD1]
  rw [hEU, hEV]
  nlinarith

private theorem relativeD1_closedGeodesics_three_point (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hv₀ : RelativeFiniteEnergyPreceq θ φ v₀ hφ)
    (hv₁ : RelativeFiniteEnergyPreceq θ φ v₁ hφ)
    {a b s : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ (a + s * (b - a)))
      (closedSubgeodesicSlice (finiteGeodesic θ.val v₀ v₁) v₀ v₁ (a + s * (b - a))) ≤
    (1 - s) * relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ a)
      (closedSubgeodesicSlice (finiteGeodesic θ.val v₀ v₁) v₀ v₁ a) +
    s * relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ b)
      (closedSubgeodesicSlice (finiteGeodesic θ.val v₀ v₁) v₀ v₁ b) := by
  have ha01 : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.le.trans hb⟩
  have hb01 : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab.le, hb⟩
  have h := relativeD1_closedGeodesics_le_endpoint_chord omega
    (finiteEnergy_completedSlice omega hu₀ hu₁ ha01)
    (finiteEnergy_completedSlice omega hu₀ hu₁ hb01)
    (finiteEnergy_completedSlice omega hv₀ hv₁ ha01)
    (finiteEnergy_completedSlice omega hv₀ hv₁ hb01) hs
  rw [completedSlice_restriction omega hu₀.1 hu₁.1 ha hb hab hs,
    completedSlice_restriction omega hv₀.1 hv₁.1 ha hb hab hs] at h
  exact h

/-- True Perron restriction and the true defining distance chord give convexity on the complete closed segment for arbitrary singular models and full E1 endpoints. -/
theorem convexOn_relativeD1_closedGeodesics (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hv₀ : RelativeFiniteEnergyPreceq θ φ v₀ hφ)
    (hv₁ : RelativeFiniteEnergyPreceq θ φ v₁ hφ) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t)
      (closedSubgeodesicSlice (finiteGeodesic θ.val v₀ v₁) v₀ v₁ t)) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h := relativeD1_closedGeodesics_three_point omega hu₀ hu₁ hv₀ hv₁ hx.1 hy.2 hxy
      (s := q) ⟨hq, by linarith⟩
    rw [show x + q * (y - x) = p * x + q * y by linear_combination (-x) * hpq,
      show 1 - q = p by linarith] at h
    exact h
  · subst hxy
    rw [← add_mul, hpq, one_mul, ← add_mul, hpq, one_mul]
  · have h := relativeD1_closedGeodesics_three_point omega hu₀ hu₁ hv₀ hv₁ hy.1 hx.2 hxy
      (s := p) ⟨hp, by linarith⟩
    rw [show y + p * (x - y) = p * x + q * y by linear_combination (-y) * hpq,
      show 1 - p = q by linarith] at h
    linarith

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicDarvasConvexity

import SGPT.PSH.SourceRelativeGeodesics
import SGPT.Foundations.Analysis.Pending.SingularGeodesicGeneralEnergyAffinity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

omit [BorelSpace M] [ConnectedSpace M] in
/-- The SAME original closed curve equals its actual assigned Perron trace
under the literal original affine reparametrization, including a=b and both
endpoints. No condition on an off-interval curve value is imposed. -/
theorem SourceGeodesicClosedInterval.eq_sourcePerronClosedSlice_reparam
    {omega : KahlerBackground n M} {a b s : ℝ} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ a b curve) (hs : s ∈ Icc (0 : ℝ) 1) :
    curve (s * b + (1 - s) * a) = sourcePerronClosedSlice omega θ (curve a) (curve b) s := by
  by_cases h0 : s = 0
  · simp only [h0, zero_mul, sub_zero, one_mul, zero_add,
      sourcePerronClosedSlice, closedSubgeodesicSlice_zero]
  by_cases h1 : s = 1
  · simp only [h1, one_mul, sub_self, zero_mul, add_zero,
      sourcePerronClosedSlice, closedSubgeodesicSlice_one]
  have hsi : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm h0), lt_of_le_of_ne hs.2 h1⟩
  rw [sourcePerronClosedSlice, closedSubgeodesicSlice_eq_curve hsi]
  exact h.2.2.2.2.2 s hsi

/-- Genuine original endpoint E1 memberships manufacture EVERY actual
closed Perron E1 slice, preserving the two original assigned endpoints. -/
theorem sourceRelativeFiniteEnergy_sourcePerronClosedSlice (omega : KahlerBackground n M)
    {u₀ u₁ : M → EReal} (h₀ : SourceRelativeFiniteEnergy θ φ u₀ hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ u₁ hφ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    SourceRelativeFiniteEnergy θ φ (sourcePerronClosedSlice omega θ u₀ u₁ s) hφ := by
  by_cases h0 : s = 0
  · simpa only [h0, sourcePerronClosedSlice, closedSubgeodesicSlice_zero] using h₀
  by_cases h1 : s = 1
  · simpa only [h1, sourcePerronClosedSlice, closedSubgeodesicSlice_one] using h₁
  have hsi : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm h0), lt_of_le_of_ne hs.2 h1⟩
  simpa only [sourcePerronClosedSlice, closedSubgeodesicSlice_eq_curve hsi] using
    sourceRelativeFiniteEnergy_sourcePerron omega h₀ h₁ hsi

/-- The actual original finite real model energy has its exact chord on the
ENTIRE canonical closed segment, for arbitrary original singular model. -/
theorem sourcePerronClosedSlice_toReal_energy_chord (omega : KahlerBackground n M)
    {u₀ u₁ : M → EReal} (h₀ : SourceRelativeFiniteEnergy θ φ u₀ hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ u₁ hφ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (sourceRelativeEnergy θ φ (sourcePerronClosedSlice omega θ u₀ u₁ s) hφ).toReal =
      (1 - s) * (sourceRelativeEnergy θ φ u₀ hφ).toReal +
        s * (sourceRelativeEnergy θ φ u₁ hφ).toReal := by
  simp only [sourcePerronClosedSlice_eq_native, sourceRelativeEnergy_eq_native]
  exact SingularGeodesicGeneralEnergyAffinity.toReal_energy_closedSubgeodesicSlice_eq_chord omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp h₀)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp h₁) hs

/-- The identical true EReal energies have the actual closed-segment chord;
genuine E1 excludes BOTH infinities before realification in the producer. -/
theorem sourcePerronClosedSlice_energy_chord (omega : KahlerBackground n M)
    {u₀ u₁ : M → EReal} (h₀ : SourceRelativeFiniteEnergy θ φ u₀ hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ u₁ hφ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    sourceRelativeEnergy θ φ (sourcePerronClosedSlice omega θ u₀ u₁ s) hφ =
      ((1 - s : ℝ) : EReal) * sourceRelativeEnergy θ φ u₀ hφ +
        (s : EReal) * sourceRelativeEnergy θ φ u₁ hφ := by
  simp only [sourcePerronClosedSlice_eq_native, sourceRelativeEnergy_eq_native]
  exact SingularGeodesicGeneralEnergyAffinity.energy_closedSubgeodesicSlice_eq_chord omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp h₀)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp h₁) hs

/-- EVERY original closed geodesic, including a=b, has the genuine finite
real endpoint-energy chord under the literal source reparametrization. -/
theorem sourceGeodesic_toReal_energy_chord_reparam {omega : KahlerBackground n M}
    {a b s : ℝ} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ a b curve)
    (h₀ : SourceRelativeFiniteEnergy θ φ (curve a) hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ (curve b) hφ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (sourceRelativeEnergy θ φ (curve (s * b + (1 - s) * a)) hφ).toReal =
      (1 - s) * (sourceRelativeEnergy θ φ (curve a) hφ).toReal +
        s * (sourceRelativeEnergy θ φ (curve b) hφ).toReal := by
  rw [h.eq_sourcePerronClosedSlice_reparam hs]
  exact sourcePerronClosedSlice_toReal_energy_chord omega h₀ h₁ hs

/-- The identical original EReal energy chord for EVERY actual original
closed geodesic, with both endpoint zero-weight cases and a=b retained. -/
theorem sourceGeodesic_energy_chord_reparam {omega : KahlerBackground n M}
    {a b s : ℝ} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ a b curve)
    (h₀ : SourceRelativeFiniteEnergy θ φ (curve a) hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ (curve b) hφ) (hs : s ∈ Icc (0 : ℝ) 1) :
    sourceRelativeEnergy θ φ (curve (s * b + (1 - s) * a)) hφ =
      ((1 - s : ℝ) : EReal) * sourceRelativeEnergy θ φ (curve a) hφ +
        (s : EReal) * sourceRelativeEnergy θ φ (curve b) hφ := by
  rw [h.eq_sourcePerronClosedSlice_reparam hs]
  exact sourcePerronClosedSlice_energy_chord omega h₀ h₁ hs

/-- Actual original endpoint E1 classes manufacture EVERY original closed
geodesic slice class, on arbitrary [a,b] including the degenerate interval. -/
theorem sourceRelativeFiniteEnergy_sourceGeodesic_on {omega : KahlerBackground n M}
    {a b t : ℝ} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ a b curve)
    (h₀ : SourceRelativeFiniteEnergy θ φ (curve a) hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ (curve b) hφ) (ht : t ∈ Icc a b) :
    SourceRelativeFiniteEnergy θ φ (curve t) hφ := by
  rcases eq_or_lt_of_le h.1 with heq | hab
  · have hta : t = a := by rw [← heq] at ht; exact le_antisymm ht.2 ht.1
    simpa only [hta] using h₀
  let s := (t - a) / (b - a)
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hab.le), ?_⟩
    exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])
  have heq : s * b + (1 - s) * a = t := by
    dsimp only [s]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hc := h.eq_sourcePerronClosedSlice_reparam hs
  rw [heq] at hc
  rw [hc]
  exact sourceRelativeFiniteEnergy_sourcePerronClosedSlice omega h₀ h₁ hs

/-- WHOLE original prop:energylinear: the original defining finite real
energy is an actual affine function on EVERY original closed geodesic
interval. Arbitrary singular model and the closed a=b case remain literal. -/
theorem sourceGeodesic_energy_affine {omega : KahlerBackground n M}
    {a b : ℝ} {curve : ℝ → M → EReal}
    (h : SourceGeodesicClosedInterval omega θ a b curve)
    (h₀ : SourceRelativeFiniteEnergy θ φ (curve a) hφ)
    (h₁ : SourceRelativeFiniteEnergy θ φ (curve b) hφ) :
    ∃ c₀ c₁ : ℝ, ∀ t ∈ Icc a b,
      (sourceRelativeEnergy θ φ (curve t) hφ).toReal = c₀ + c₁ * t := by
  rcases eq_or_lt_of_le h.1 with heq | hab
  · refine ⟨(sourceRelativeEnergy θ φ (curve a) hφ).toReal, 0, ?_⟩
    intro t ht
    have hta : t = a := by rw [← heq] at ht; exact le_antisymm ht.2 ht.1
    simp only [hta, zero_mul, add_zero]
  let m := ((sourceRelativeEnergy θ φ (curve b) hφ).toReal -
    (sourceRelativeEnergy θ φ (curve a) hφ).toReal) / (b - a)
  refine ⟨(sourceRelativeEnergy θ φ (curve a) hφ).toReal - m * a, m, ?_⟩
  intro t ht
  let s := (t - a) / (b - a)
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hab.le), ?_⟩
    exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])
  have heq : s * b + (1 - s) * a = t := by
    dsimp only [s]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hc := sourceGeodesic_toReal_energy_chord_reparam h h₀ h₁ hs
  rw [heq] at hc
  rw [hc]
  dsimp only [s, m]
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

end SGPT.PSH.VariableComplexAtlas

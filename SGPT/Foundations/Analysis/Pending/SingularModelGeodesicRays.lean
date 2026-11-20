import SGPT.Foundations.Analysis.Pending.SingularGeodesicGeneralEnergyAffinity
import SGPT.Foundations.Analysis.Pending.RelativePreceqRays
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricSpace

set_option autoImplicit false

/-! # Actual native finite-energy rays over arbitrary singular models -/

open Set
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRays

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularModelDarvasMetricSpace

noncomputable section

/-- The actual nonnegative interpolation time of two nonnegative real times. -/
def rayTime (a b : ℝ≥0) (s : Icc (0 : ℝ) 1) : ℝ≥0 :=
  ⟨(1 - s.val) * a + s.val * b,
    add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) a.property)
      (mul_nonneg s.property.1 b.property)⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Genuine E1 slices and actual closed Perron restriction are the entire ray contract; energy and metric identities are outputs of later producers. -/
structure ModelFiniteEnergyGeodesicRay (θ : ClosedRealOneOneForm n M)
    (φ : M → EReal) (hφ : IsModelPotential θ φ) where
  toFun : ℝ≥0 → ModelFiniteEnergyPotential θ φ hφ
  segment_eq : ∀ a b : ℝ≥0, a < b → ∀ s : Icc (0 : ℝ) 1,
    (toFun (rayTime a b s)).val =
      closedSubgeodesicSlice (finiteGeodesic θ.val (toFun a).val (toFun b).val)
        (toFun a).val (toFun b).val s.val

namespace ModelFiniteEnergyGeodesicRay

/-- The actual reader extends the nonnegative-time native ray by its initial slice at negative times. -/
def rawCurve (L : ModelFiniteEnergyGeodesicRay θ φ hφ) (t : ℝ) : M → EReal :=
  (L.toFun ⟨max t 0, le_max_right t 0⟩).val

omit [BorelSpace M] in
/-- The actual nonnegative-time reader is precisely the genuine typed ray slice. -/
theorem rawCurve_coe (L : ModelFiniteEnergyGeodesicRay θ φ hφ) (t : ℝ≥0) :
    L.rawCurve t = (L.toFun t).val := by
  have heq : (⟨max (t : ℝ) 0, le_max_right (t : ℝ) 0⟩ : ℝ≥0) = t :=
    Subtype.ext (max_eq_left t.property)
  exact congrArg (fun r : ℝ≥0 => (L.toFun r).val) heq

omit [BorelSpace M] in
/-- Every real-time reader value is an actual member of the genuine full singularity-order E1 class. -/
theorem finiteEnergy_rawCurve (L : ModelFiniteEnergyGeodesicRay θ φ hφ) (t : ℝ) :
    RelativeFiniteEnergyPreceq θ φ (L.rawCurve t) hφ :=
  (L.toFun ⟨max t 0, le_max_right t 0⟩).property

omit [BorelSpace M] in
/-- The genuine native geometry yields the exact actual closed Perron identity for the real-time reader. -/
theorem rawCurve_segment_eq (L : ModelFiniteEnergyGeodesicRay θ φ hφ)
    (a b : ℝ≥0) (hab : a < b) (s : Icc (0 : ℝ) 1) :
    L.rawCurve ((1 - s.val) * a + s.val * b) =
      closedSubgeodesicSlice (finiteGeodesic θ.val (L.rawCurve a) (L.rawCurve b))
        (L.rawCurve a) (L.rawCurve b) s.val := by
  change L.rawCurve (rayTime a b s : ℝ) = _
  rw [L.rawCurve_coe, L.rawCurve_coe a, L.rawCurve_coe b]
  exact L.segment_eq a b hab s

private theorem rayTime_zero (a b : ℝ≥0) (s : Icc (0 : ℝ) 1) (h0 : s.val = 0) :
    rayTime a b s = a := by
  apply Subtype.ext
  change (1 - s.val) * (a : ℝ) + s.val * (b : ℝ) = (a : ℝ)
  rw [h0]
  ring

private theorem rayTime_one (a b : ℝ≥0) (s : Icc (0 : ℝ) 1) (h1 : s.val = 1) :
    rayTime a b s = b := by
  apply Subtype.ext
  change (1 - s.val) * (a : ℝ) + s.val * (b : ℝ) = (b : ℝ)
  rw [h1]
  ring

/-- Genuine source ray restriction and genuine initial E1 membership construct the actual native ray, without energy or distance assumptions. -/
def ofFiniteEnergyPreceqRay {ℓ : ℝ → M → EReal}
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (h0 : RelativeFiniteEnergyPreceq θ φ (ℓ 0) hφ) :
    ModelFiniteEnergyGeodesicRay θ φ hφ := by
  have hf (t : ℝ) (ht : 0 ≤ t) : RelativeFiniteEnergyPreceq θ φ (ℓ t) hφ := by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]
      exact h0
    · exact hℓ.2 t h
  refine ⟨fun t => ⟨ℓ t, hf t t.property⟩, ?_⟩
  intro a b hab s
  change ℓ (rayTime a b s : ℝ) =
    closedSubgeodesicSlice (finiteGeodesic θ.val (ℓ a) (ℓ b)) (ℓ a) (ℓ b) s.val
  by_cases hs0 : s.val = 0
  · rw [rayTime_zero a b s hs0, hs0, closedSubgeodesicSlice_zero]
  by_cases hs1 : s.val = 1
  · rw [rayTime_one a b s hs1, hs1, closedSubgeodesicSlice_one]
  have hs : s.val ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0), lt_of_le_of_ne s.property.2 hs1⟩
  have htime : (rayTime a b s : ℝ) = (a : ℝ) + s.val * ((b : ℝ) - a) := by
    change (1 - s.val) * (a : ℝ) + s.val * (b : ℝ) = _
    ring
  rw [htime, closedSubgeodesicSlice_eq_curve hs]
  exact hℓ.1.2 a b a.property hab s.val hs

/-- A genuine source ray from the model internally produces initial E1 membership by actual finite-type inclusion, with no bounded reference hypothesis. -/
def ofFiniteEnergyRayFromModel (omega : KahlerBackground n M)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ) :
    ModelFiniteEnergyGeodesicRay θ φ hφ := by
  have hfinite : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have h0 : RelativeFiniteEnergyPreceq θ φ (ℓ 0) hφ := by
    simpa only [hℓ.2] using hfinite
  exact ofFiniteEnergyPreceqRay hℓ.1 h0

end ModelFiniteEnergyGeodesicRay

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRays

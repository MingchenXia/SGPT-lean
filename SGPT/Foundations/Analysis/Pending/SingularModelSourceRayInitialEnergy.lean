import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicFullMassTruncation
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRays

set_option autoImplicit false

/-!
# Initial finite energy in the actual original positive-time ray domain

Xia SGPT PDF0159 and PDF0174--0175. Actual full-mass canonical Perron
energy limits recover the extended chord and force initial finite energy
from the source's genuine positive-time E1 slices. The original initial
point is arbitrary; boundedness, model origin, initial E1, affinity and
reader-identification certificates are not assumptions.
-/

open Set Filter
open scoped Topology NNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelSourceRayInitialEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays SingularModelGeodesicRays
  SingularModelGeodesicFullMassTruncation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ : ℝ → M → EReal}

/-- The actual full-mass source ray has its true defining extended energy chord on each closed finite interval, allowing negative infinity. -/
theorem energy_ray_preceq (omega : KahlerBackground n M)
    (hℓ : IsRelativeGeodesicRayPreceq θ φ hφ ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    energy θ φ hφ (ℓ (a + s * (b - a))) =
      ((1 - s : ℝ) : EReal) * energy θ φ hφ (ℓ a) +
        (s : EReal) * energy θ φ hφ (ℓ b) := by
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0
    simp only [zero_mul, add_zero, sub_zero, EReal.coe_one, one_mul, EReal.coe_zero, zero_mul]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · subst h1
    simp only [one_mul, add_sub_cancel, sub_self, EReal.coe_zero, zero_mul, EReal.coe_one, zero_add]
  rw [hℓ.2 a b ha hab s ⟨h0, h1⟩]
  exact energy_finiteGeodesic_eq_chord_of_fullMass omega
    (hℓ.1 a ha) (hℓ.1 b (ha.trans hab.le)) ⟨h0, h1⟩

/-- Actual finite positive-time source slices produce actual finite energy of the arbitrary initial slice over any singular model. -/
theorem relativeFiniteEnergyPreceq_ray_zero (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) :
    RelativeFiniteEnergyPreceq θ φ (ℓ 0) hφ := by
  have hm : ℓ (1 / 2) = finiteGeodesic θ.val (ℓ 0) (ℓ 1) (1 / 2) := by
    simpa only [sub_zero, mul_one, zero_add] using
      hℓ.1.2 0 1 le_rfl zero_lt_one (1 / 2) ⟨by norm_num, by norm_num⟩
  apply relativeFiniteEnergyPreceq_left_of_midpoint omega (hℓ.1.1 0 le_rfl)
    (hℓ.2 1 zero_lt_one)
  rw [← hm]
  exact hℓ.2 (1 / 2) (by norm_num)

/-- The same actual initial-energy producer applies to the original normalized source ray predicate, retaining genuine normalized full mass. -/
theorem relativeFiniteEnergy_ray_zero (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) :
    RelativeFiniteEnergy θ φ (ℓ 0) hφ :=
  ⟨hℓ.1.1 0 le_rfl,
    (relativeFiniteEnergyPreceq_ray_zero omega (isFiniteEnergyRayPreceq_of_isFiniteEnergyRay hℓ)).2⟩

/-- The entire genuine source positive-time E1 domain internally supplies initial E1 and produces an actual native ray; no initial class certificate is supplied by the caller. -/
def nativeRay (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) : ModelFiniteEnergyGeodesicRay θ φ hφ :=
  ModelFiniteEnergyGeodesicRay.ofFiniteEnergyPreceqRay hℓ
    (relativeFiniteEnergyPreceq_ray_zero omega hℓ)

/-- The actual reader of the genuinely produced native ray agrees with the given source at every nonnegative time, including its arbitrary initial slice. -/
theorem nativeRay_reader_eq (omega : KahlerBackground n M)
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    (nativeRay omega hℓ).rawCurve t = ℓ t := by
  change ℓ (max t 0) = ℓ t
  rw [max_eq_left ht]

end

end SGPT.Foundations.Analysis.Pending.SingularModelSourceRayInitialEnergy

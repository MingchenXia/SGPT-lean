import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity
import SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

set_option autoImplicit false

/-! # Actual continuous-test algebra of locally bounded mixed products

Independent integral consumers of genuine Bedford--Taylor additivity and
homogeneity. Only compact test support, never total domain mass, is used.
The all-slot scaling statement includes dimension zero.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualLocalMixedIntegralSlots

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  BedfordTaylor MixedMongeAmpere LocalBedfordTaylorCalculus

noncomputable section

variable {n : ℕ} {Q : Opens (ComplexModel n)}

private theorem integrable_test {u : Fin n → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedMixedPshOn Q u) {h : ComplexModel n → ℝ}
    (hc : Continuous h) (hk : HasCompactSupport h) (ht : tsupport h ⊆ Q) :
    Integrable h (canonicalMixedBedfordTaylorMeasure Q u hu) := by
  exact integrable_of_bounded_of_support (isClosed_tsupport h).measurableSet
    (canonicalMixedBedfordTaylorMeasure_finiteOnCompacts hu hk ht)
    hc.stronglyMeasurable
    (exists_bound_of_continuous_of_hasCompactSupport hc hk).choose_spec.2
    (fun z hz => image_eq_zero_of_notMem_tsupport hz)

private theorem locallyBounded_positive_mul {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Q u) {c : ℝ} (hc : 0 < c) :
    IsLocallyBoundedPshOn Q (fun z => c * u z) := by
  refine ⟨plurisubharmonicOn_coe_const_mul hu.1 hc, fun z hz => ?_⟩
  obtain ⟨V, hzV, hVQ, B, hB⟩ := hu.2 z hz
  refine ⟨V, hzV, hVQ, c * B, fun w hw => ?_⟩
  rw [abs_mul, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hB w hw) hc.le

/-- Natural locally bounded PSH inputs produce the actual slot-sum integral
identity for every continuous compact test. -/
theorem integral_slot_add {u : Fin n → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedMixedPshOn Q u) (k : Fin n)
    {a b : ComplexModel n → ℝ} (ha : IsLocallyBoundedPshOn Q a)
    (hb : IsLocallyBoundedPshOn Q b) :
    ∃ (hA : IsLocallyBoundedMixedPshOn Q (Function.update u k a))
      (hB : IsLocallyBoundedMixedPshOn Q (Function.update u k b))
      (hS : IsLocallyBoundedMixedPshOn Q (Function.update u k (fun z => a z + b z))),
      ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h → tsupport h ⊆ Q →
        (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q
          (Function.update u k (fun z => a z + b z)) hS) =
        (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (Function.update u k a) hA) +
          ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (Function.update u k b) hB := by
  classical
  have hupdate (f : ComplexModel n → ℝ) (hf : IsLocallyBoundedPshOn Q f) :
      IsLocallyBoundedMixedPshOn Q (Function.update u k f) := by
    intro i
    by_cases hi : i = k
    · subst hi
      simpa using hf
    · simpa [Function.update_of_ne hi] using hu i
  let hA := hupdate a ha
  let hB := hupdate b hb
  let hS := hupdate (fun z => a z + b z) (isLocallyBoundedPshOn_add ha hb)
  have hlimit (v : Fin n → ComplexModel n → ℝ) (hv : IsLocallyBoundedMixedPshOn Q v) :
      IsBTLimit Q v (canonicalMixedBedfordTaylorMeasure Q v hv) :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec Q v hv)
  have hμ := (hlimit _ hS).add_slot k (hlimit _ hA) (hlimit _ hB)
  refine ⟨hA, hB, hS, fun h hc hk ht => ?_⟩
  rw [hμ, integral_add_measure (integrable_test hA hc hk ht) (integrable_test hB hc hk ht)]

/-- Genuine common positive scaling produces its actual canonical measure and
integral identity, including the empty tuple. -/
theorem integral_positive_scale {u : Fin n → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedMixedPshOn Q u) {c : ℝ} (hc : 0 < c) :
    ∃ hC : IsLocallyBoundedMixedPshOn Q (fun i z => c * u i z),
      ∀ h : ComplexModel n → ℝ,
        (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (fun i z => c * u i z) hC) =
          c ^ n * ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q u hu := by
  let hC : IsLocallyBoundedMixedPshOn Q (fun i z => c * u i z) :=
    fun i => locallyBounded_positive_mul (hu i) hc
  have hlim : IsBTLimit Q u (canonicalMixedBedfordTaylorMeasure Q u hu) :=
    IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec Q u hu)
  have hscaled : canonicalMixedBedfordTaylorMeasure Q (fun i z => c * u i z) hC =
      (ENNReal.ofReal c ^ n) • canonicalMixedBedfordTaylorMeasure Q u hu :=
    (IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (canonicalMixedBedfordTaylorMeasure_spec Q (fun i z => c * u i z) hC)).unique
        (hlim.const_mul_all hc.le)
  refine ⟨hC, fun h => ?_⟩
  rw [hscaled, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc.le,
    smul_eq_mul]

end
end SGPT.Foundations.Analysis.Pending.ActualLocalMixedIntegralSlots

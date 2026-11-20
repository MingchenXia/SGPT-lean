import SGPT.Okounkov.TranscendentalWNVolumeGlobalMain
import SGPT.Okounkov.TranscendentalWNLegendreReduction

/-!
# Measurability in `λ` and the unconditional first volume formula (package WN-VF2)

Blueprint nodes `tok-wn-vf2:measurable`, `tok-wn-vf2:gluing`, `tok-wn-vf:global-legendre-ma`,
`tok-wn:formula-volume`.

* `legendreMAMeasurable`: `LegendreMAMeasurableStatement N`.  On the open "good set" `O ⊇ Ω \ A`
  where the `û_λ` are locally uniformly bounded, the a.e.-measurability of
  `λ ↦ ⟨(dd^c û_λ)^N⟩(E ∩ O)` is part of the local identity
  (`legendreIdentityOn_good`, the bounded case of WN21 Theorem 3.3); and `E \ O ⊆ A ∪ Ωᶜ` is not
  charged.
* `globalLegendreMA`: WN21 Theorem 3.5 (`GlobalLegendreMAStatement N`, `0 < N`), from WN-LEG's
  `partialLegendreMALocalStatement` (WN21 Theorem 3.3).
* `deformationVolume`, `deformationVolumeDifference`: **`tok-wn:formula-volume`**,
  unconditionally: `vol(β) = (n + 1)((b - c) vol(ξ) + ∫₀^c vol(ξ_t) dt)` and
  `vol(β) - vol(β - {X₀}) = (n + 1) vol(ξ)`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

/-- **Measurable dependence on `λ`** (`tok-wn-vf2:measurable`). -/
theorem legendreMAMeasurable {N : ℕ} : LegendreMAMeasurableStatement N := by
  intro Ω u a b A h hû E hE
  rcases h.le.eq_or_lt with hab | hab
  · subst hab
    rw [Icc_self, Measure.restrict_eq_zero.mpr Real.volume_singleton]
    exact aemeasurable_zero_measure
  have hu : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens Ω) :=
    h.plurisubharmonicOn_productModelFunction
  have hO := isOpen_goodSet Ω u a b
  have hΩA := diff_subset_goodSet h hab
  have hid := legendreIdentityOn_good h hab hu hû
  have h1 := (hid (E ∩ goodSet Ω u a b) (hE.inter hO.measurableSet) inter_subset_right).1
  refine h1.congr (Eventually.of_forall fun lam => ?_)
  have hpp := MongeAmpere.truncationLimitMeasure_doesNotChargePluripolarOn (hû lam) A
    h.pluripolar
  have hsub : E \ goodSet Ω u a b ⊆ (A ∩ Ω) ∪ (Ω : Set (ComplexModel N))ᶜ := by
    intro z hz
    by_cases hzΩ : z ∈ (Ω : Set (ComplexModel N))
    · refine Or.inl ⟨?_, hzΩ⟩
      by_contra hnA
      exact hz.2 (hΩA ⟨hzΩ, hnA⟩)
    · exact Or.inr hzΩ
  have h0 := measure_mono_null hsub (measure_union_null hpp
    (MongeAmpere.truncationLimitMeasure_compl (hû lam)))
  simp only
  rw [← measure_inter_add_sdiff E hO.measurableSet, h0, add_zero]

/-- **`tok-wn-vf:global-legendre-ma`** (WN21 Theorem 3.5), unconditionally. -/
theorem globalLegendreMA {N : ℕ} (hN : 0 < N) : GlobalLegendreMAStatement.{u} N :=
  globalLegendreMA_of_local_of_measurable hN partialLegendreMALocalStatement legendreMAMeasurable

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn:formula-volume`** (WN21 Theorem 1.6 (1)):
`vol(β) = (n + 1)((b - c) vol(ξ) + ∫₀^c vol(ξ_t) dt)`. -/
theorem deformationVolume : DeformationVolumeStatement F :=
  deformationVolume_of_local F partialLegendreMALocalStatement legendreMAMeasurable

/-- **`tok-wn:formula-volume`, second half** (WN21 Corollary 4.7):
`vol(β) - vol(β - {X₀}) = (n + 1) vol(ξ)` for `b > c + 1`. -/
theorem deformationVolumeDifference : DeformationVolumeDifferenceStatement F :=
  deformationVolumeDifference_of_volume F (deformationVolume F)

end SGPT.Okounkov.TranscendentalWN

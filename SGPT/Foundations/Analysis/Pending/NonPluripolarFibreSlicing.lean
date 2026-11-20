import SGPT.Foundations.Analysis.Pending.BedfordTaylorGauge
import SGPT.Foundations.Analysis.Pending.BedfordTaylorPositiveFibreSlicing
import SGPT.Foundations.Analysis.Pending.IncreasingMeasureIntegrals
import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
import SGPT.Foundations.Analysis.PlurisubharmonicPullback

set_option autoImplicit false

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarFibreSlicing

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  FirstPass.MixedNonPluripolar BedfordTaylor BedfordTaylorFibreSlicing
  FiniteGeodesicMaximality MixedDensityRankOneSlot

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel (n + 1))}
  {u : Fin (n + 1) → ComplexModel (n + 1) → EReal}

/-- The actual first n extended-real potentials on a genuine fibre. -/
def fibrePotentials (u : Fin (n + 1) → ComplexModel (n + 1) → EReal) (τ : ℂ) :
    Fin n → ComplexModel n → EReal := fun i y => u i.castSucc (fibreMap n τ y)

/-- Genuine PSH fibre membership is produced by actual complex affine pullback. -/
theorem plurisubharmonicOn_fibrePotentials
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (τ : ℂ) (i : Fin n) :
    PlurisubharmonicOn (fibrePotentials u τ i) (fibreOpens Ω τ) := by
  let L : ComplexModel n →L[ℂ] ComplexModel (n + 1) :=
    (stripModelEquiv n).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℂ (ComplexModel n) ℂ)
  let b := fibreMap n τ 0
  have ha (y : ComplexModel n) : fibreMap n τ y = b + L y := by
    change (stripModelEquiv n).symm (y, τ) =
      (stripModelEquiv n).symm (0, τ) + (stripModelEquiv n).symm (y, 0)
    rw [← map_add]
    congr 1
    simp
  have h := (hu i.castSucc).comp_affine L b
  change PlurisubharmonicOn (fun y => u i.castSucc (fibreMap n τ y))
    ((fun y => fibreMap n τ y) ⁻¹' (Ω : Set (ComplexModel (n + 1))))
  simpa only [← ha] using h

private theorem truncation_last
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal)) (k : ℕ) :
    mixedTruncationReal u k (Fin.last n) = lastNormSq n := by
  funext q
  simp only [mixedTruncationReal, truncationReal, truncation, hlast]
  rw [max_eq_left]
  · exact EReal.toReal_coe _
  · apply EReal.coe_le_coe_iff.mpr
    exact (neg_nonpos.mpr (Nat.cast_nonneg k)).trans (by unfold lastNormSq; positivity)

private theorem fibre_commonStrictLocus
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    (τ : ℂ) (k : ℕ) :
    fibreMap n τ ⁻¹' commonStrictLocus Ω u (k + 1) =
      commonStrictLocus (fibreOpens Ω τ) (fibrePotentials u τ) (k + 1) := by
  ext y
  simp only [mem_preimage, commonStrictLocus, mem_ofPred_eq, mem_fibreOpens]
  constructor
  · intro h
    exact ⟨h.1, fun i => h.2 i.castSucc⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => h.2 j) i
    rw [hlast]
    apply EReal.coe_lt_coe_iff.mpr
    have hneg : -(↑(k + 1) : ℝ) < 0 := neg_neg_of_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ k))
    exact hneg.trans_le (by unfold lastNormSq; positivity)

/-- Actual positive truncation slicing, with fibre PSH membership and
all base measurability produced internally. -/
theorem lintegral_indicator_truncation_eq_fibre
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {χ : ComplexModel (n + 1) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {E : Set (ComplexModel (n + 1))} (hE : MeasurableSet E)
    (k : ℕ) :
    AEMeasurable (fun τ : ℂ => ∫⁻ y,
      E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y)
        ∂MixedNonPluripolar.mixedTruncationMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
          (plurisubharmonicOn_fibrePotentials hu τ) (k + 1)) ∧
    (∫⁻ q, E.indicator (fun z => ENNReal.ofReal (χ z)) q
      ∂MixedNonPluripolar.mixedTruncationMeasure Ω u hu (k + 1)) =
      (∫⁻ τ : ℂ, ∫⁻ y,
        E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y)
          ∂MixedNonPluripolar.mixedTruncationMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
            (plurisubharmonicOn_fibrePotentials hu τ) (k + 1)) /
          ENNReal.ofReal Real.pi := by
  classical
  let S := commonStrictLocus Ω u (k + 1)
  let ν := MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω
    (mixedTruncationReal u (k + 1)) (mixedTruncationReal_isLocallyBounded hu (k + 1))
  let μ := fun τ => MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure (fibreOpens Ω τ)
    (mixedTruncationReal (fibrePotentials u τ) (k + 1))
      (mixedTruncationReal_isLocallyBounded (plurisubharmonicOn_fibrePotentials hu τ) (k + 1))
  have hS : MeasurableSet S := measurableSet_commonStrictLocus hu (k + 1)
  have hν : IsBTLimit Ω (mixedTruncationReal u (k + 1)) ν :=
    BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec Ω _
        (mixedTruncationReal_isLocallyBounded hu (k + 1)))
  have hμ (τ : ℂ) : IsBTLimit (fibreOpens Ω τ)
      (fibreTuple (mixedTruncationReal u (k + 1)) τ) (μ τ) :=
    BedfordTaylor.IsLocalMixedBedfordTaylorMeasure.isBTLimit
      (MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_spec (fibreOpens Ω τ) _
        (mixedTruncationReal_isLocallyBounded (plurisubharmonicOn_fibrePotentials hu τ)
          (k + 1)))
  have hs := BedfordTaylorPositiveFibreSlicing.lintegral_indicator_isBTLimit_eq_fibre
    (truncation_last hlast (k + 1)) hν hμ hχ hχc hχΩ hχ0 (hS.inter hE)
  have hj : (∫⁻ q, E.indicator (fun z => ENNReal.ofReal (χ z)) q
      ∂MixedNonPluripolar.mixedTruncationMeasure Ω u hu (k + 1)) =
      ∫⁻ q, (S ∩ E).indicator (fun z => ENNReal.ofReal (χ z)) q ∂ν := by
    change (∫⁻ q, E.indicator (fun z => ENNReal.ofReal (χ z)) q ∂ν.restrict S) = _
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro q
    by_cases hqS : q ∈ S <;> by_cases hqE : q ∈ E <;> simp [hqS, hqE]
  have hf (τ : ℂ) : (∫⁻ y,
      E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y)
        ∂MixedNonPluripolar.mixedTruncationMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
          (plurisubharmonicOn_fibrePotentials hu τ) (k + 1)) =
      ∫⁻ y, (S ∩ E).indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y) ∂μ τ := by
    change (∫⁻ y, E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y)
      ∂(μ τ).restrict (commonStrictLocus (fibreOpens Ω τ) (fibrePotentials u τ) (k + 1))) = _
    rw [← lintegral_indicator (measurableSet_commonStrictLocus
      (plurisubharmonicOn_fibrePotentials hu τ) (k + 1))]
    apply lintegral_congr
    intro y
    have hmem : y ∈ commonStrictLocus (fibreOpens Ω τ) (fibrePotentials u τ) (k + 1) ↔
        fibreMap n τ y ∈ S := by
      rw [← fibre_commonStrictLocus hlast τ k]
      rfl
    by_cases hy : fibreMap n τ y ∈ S <;>
      by_cases he : fibreMap n τ y ∈ E <;> simp [hmem, hy, he]
  refine ⟨?_, ?_⟩
  · simpa only [hf] using hs.1
  · rw [hj]
    simpa only [hf] using hs.2

private theorem lintegral_npLimit_eq_iSup_shift
    {m : ℕ} {V : Opens (ComplexModel m)}
    {v : Fin m → ComplexModel m → EReal}
    (hv : ∀ i, PlurisubharmonicOn (v i) V) {f : ComplexModel m → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ z, f z ∂MixedNonPluripolar.mixedTruncationLimitMeasure V v hv) =
      ⨆ k, ∫⁻ z, f z ∂MixedNonPluripolar.mixedTruncationMeasure V v hv (k + 1) := by
  let μ := MixedNonPluripolar.mixedTruncationMeasure V v hv
  have hμ : Monotone μ := MixedNonPluripolar.mixedTruncationMeasure_mono hv
  change (∫⁻ z, f z ∂FirstPass.IncreasingMeasures.increasingLimit μ hμ) = _
  rw [← IncreasingMeasureIntegrals.increasingLimit_add μ hμ 1]
  exact IncreasingMeasureIntegrals.lintegral_increasingLimit (fun k => μ (k + 1))
    (fun _ _ hkl => hμ (Nat.add_le_add_right hkl 1)) hf

/-- Actual positive Borel NP slicing. The joint and every-fibre limit
measure are genuine increasing truncation limits; infinite mass is allowed. -/
theorem lintegral_indicator_npLimit_eq_fibre
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω)
    (hlast : u (Fin.last n) = fun q => (lastNormSq n q : EReal))
    {χ : ComplexModel (n + 1) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {E : Set (ComplexModel (n + 1))} (hE : MeasurableSet E) :
    AEMeasurable (fun τ : ℂ => ∫⁻ y,
      E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
          (plurisubharmonicOn_fibrePotentials hu τ)) ∧
    (∫⁻ q, E.indicator (fun z => ENNReal.ofReal (χ z)) q
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure Ω u hu) =
      (∫⁻ τ : ℂ, ∫⁻ y,
        E.indicator (fun q => ENNReal.ofReal (χ q)) (fibreMap n τ y)
          ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
            (plurisubharmonicOn_fibrePotentials hu τ)) /
          ENNReal.ofReal Real.pi := by
  let f := E.indicator (fun q => ENNReal.ofReal (χ q))
  let I := fun k τ => ∫⁻ y, f (fibreMap n τ y)
    ∂MixedNonPluripolar.mixedTruncationMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
      (plurisubharmonicOn_fibrePotentials hu τ) (k + 1)
  have hf : Measurable f :=
    (ENNReal.continuous_ofReal.measurable.comp hχ.measurable).indicator hE
  have hlevel (k : ℕ) :=
    lintegral_indicator_truncation_eq_fibre hu hlast hχ hχc hχΩ hχ0 hE k
  have hIae (k : ℕ) : AEMeasurable (I k) := (hlevel k).1
  have hImono (τ : ℂ) : Monotone (fun k => I k τ) := by
    intro k l hkl
    exact lintegral_mono'
      (MixedNonPluripolar.mixedTruncationMeasure_mono (plurisubharmonicOn_fibrePotentials hu τ)
        (Nat.add_le_add_right hkl 1)) le_rfl
  have hfibre (τ : ℂ) : (∫⁻ y, f (fibreMap n τ y)
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ)) = ⨆ k, I k τ :=
    lintegral_npLimit_eq_iSup_shift (plurisubharmonicOn_fibrePotentials hu τ)
      (hf.comp (continuous_fibreMap τ).measurable)
  refine ⟨?_, ?_⟩
  · change AEMeasurable (fun τ => ∫⁻ y, f (fibreMap n τ y)
      ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
        (plurisubharmonicOn_fibrePotentials hu τ))
    simpa only [hfibre] using AEMeasurable.iSup hIae
  · change (∫⁻ q, f q ∂MixedNonPluripolar.mixedTruncationLimitMeasure Ω u hu) =
      (∫⁻ τ : ℂ, ∫⁻ y, f (fibreMap n τ y)
        ∂MixedNonPluripolar.mixedTruncationLimitMeasure (fibreOpens Ω τ) (fibrePotentials u τ)
          (plurisubharmonicOn_fibrePotentials hu τ)) / ENNReal.ofReal Real.pi
    rw [lintegral_npLimit_eq_iSup_shift hu hf]
    have hjlevel (k : ℕ) : (∫⁻ q, f q
        ∂MixedNonPluripolar.mixedTruncationMeasure Ω u hu (k + 1)) =
        (∫⁻ τ : ℂ, I k τ) / ENNReal.ofReal Real.pi := (hlevel k).2
    simp_rw [hjlevel]
    rw [← ENNReal.iSup_div]
    rw [← lintegral_iSup' hIae (Eventually.of_forall hImono)]
    simp_rw [hfibre]

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarFibreSlicing

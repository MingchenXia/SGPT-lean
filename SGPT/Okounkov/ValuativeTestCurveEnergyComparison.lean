import SGPT.Okounkov.ValuativeTestCurve

/-!
# Energy comparison for the revised Okounkov test-curve theorem

Source: upstream SGPT de08f12f, `thm:Okountescurvex`, in positive dimension.
The base potential is I-model; the slices need not be I-model. The source
energy is bounded above by the energy of the actual Okounkov test curve,
so finite energy transfers. Equality for I-model slices remains the separate
existing theorem `okounkovTestCurve_energy_eq_of_iModel`.

The comparison retains the genuine extended-real deficit integrals. Their
values may be infinite; no real projection of an infinite deficit is used.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov.Valuative

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.PartialBody SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
  [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}

/-- Every actual slice's ordinary non-pluripolar mass is bounded by its
factorial-scaled partial-body volume. Finiteness precedes real readback. -/
theorem sourceMass_le_factorial_mul_volume_real
    (ω : KahlerBackground (m + 1) F.carrier) {u : F.carrier → EReal}
    (hu : (ofFixedModel (m + 1) F.carrier).IsThetaPSH θ u) :
    (sourcePotentialNonPluripolarMeasure θ u hu univ).toReal ≤
      ((m + 1).factorial : ℝ) * volume.real (TranscendentalMain.euclideanImage
        (generalPartialBody F (atlasClosedFormToNative θ) u)) := by
  let hun : IsThetaPshPotential (atlasClosedFormToNative θ).val u :=
    (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hm : sourcePotentialNonPluripolarMeasure θ u hu univ ≤
      iVolume (atlasClosedFormToNative θ)
        (LocalPotentials.closedRealOneOne_hasLocalPotentials (atlasClosedFormToNative θ)) u hun :=
    diagonalPotentialMass_le_iVolume ω hun
  have hr := ENNReal.toReal_mono (iVolume_ne_top ω hun) hm
  rw [measureReal_def, volume_euclideanImage,
    volume_generalPartialBody_of_borelSpace hun, ENNReal.toReal_div,
    ENNReal.toReal_natCast]
  have hf : ((m + 1).factorial : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.factorial_pos _).ne'
  refine hr.trans_eq ?_
  field_simp

/-- Revised `thm:Okountescurvex`: with I-model base, ordinary source energy
is at most the actual Okounkov test-curve energy. No slice I-model premise. -/
theorem sourceTestCurveEnergy_le_okounkovTestCurve_energy
    (ω : KahlerBackground (m + 1) F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hφI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val φ) :
    sourceTestCurveEnergy ω hφ Γ hΓ ≤ (okounkovTestCurve (F := F) hbig Γ).energy := by
  set K := okounkovTestCurve (F := F) hbig Γ with hK
  set c : ℝ := ((m + 1).factorial : ℝ) with hc
  have hvolt : ∀ t : ℝ, t < Γ.max →
      sourceTestCurveRealMassAt ω Γ t ≤
        c * volume.real ((K.bodyAt t : Set (EuclideanSpace ℝ (Fin (m + 1))))) := by
    intro t ht
    have hbody : K.bodyAt t = K.body ⟨t, ht⟩ := by
      rw [TestCurve.bodyAt, dif_pos (show t < K.max from ht)]
    rw [hbody, sourceTestCurveRealMassAt_of_lt ω Γ ht]
    exact sourceMass_le_factorial_mul_volume_real ω (Γ.thetaPSH _)
  have hvolΔ : c * volume.real ((partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit Γ) :
      Set (EuclideanSpace ℝ (Fin (m + 1))))) =
        (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal := by
    have hlim : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ
    rw [coe_partialConvexBody]
    have h := factorial_mul_volume_real_eq_of_isIModel (θ := θ) (F := F) hφ.thetaPSH hφI
    change c * volume.real (TranscendentalMain.euclideanImage (generalPartialBody F
      (atlasClosedFormToNative θ) (sourceTestCurveLimit Γ.toSourceTestCurvePredata))) = _
    rw [hlim]
    exact h
  rw [TestCurve.energy_eq_deficit, sourceTestCurveEnergy]
  apply EReal.sub_le_sub
  · apply le_of_eq
    congr 1
    change Γ.max * _ = c * Γ.max * _
    rw [← hvolΔ]
    ring
  · have hcE : ((((m + 1).factorial : ℕ)) : EReal) =
        ((((m + 1).factorial : ℕ) : ℝ≥0∞) : EReal) := by
      rw [← ENNReal.coe_natCast, EReal.coe_nnreal_eq_coe_real, NNReal.coe_natCast]
      rfl
    rw [hcE, ← EReal.coe_ennreal_mul,
      ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    have ht' : t < Γ.max := ht
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    change c * (_ - _) ≤ _
    rw [mul_sub, hvolΔ]
    linarith [hvolt t ht']

/-- The revised finite-energy implication assumes only an I-model base;
the actual source test-curve slices are arbitrary model slices. -/
theorem okounkovTestCurve_hasFiniteEnergy_of_base_iModel
    (ω : KahlerBackground (m + 1) F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hφI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val φ)
    (hE : Γ ∈ SourceFiniteEnergyTestCurves ω θ φ hφ) :
    (okounkovTestCurve (F := F) hbig Γ).HasFiniteEnergy := by
  obtain ⟨hΓ, hfinite⟩ := hE
  unfold TestCurve.HasFiniteEnergy
  exact hfinite.trans_le (sourceTestCurveEnergy_le_okounkovTestCurve_energy ω hbig hΓ hφI)

end SGPT.Okounkov.Valuative

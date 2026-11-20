import SGPT.Foundations.Analysis.Pending.NefOriginalCurrentCalibratedLimit
import SGPT.Foundations.Analysis.Pending.NefOriginalCurrentSharpACMass
import SGPT.Foundations.Analysis.Pending.OriginalCurrentACVolume

set_option autoImplicit false

/-! Full BP statements and ENTIRE proofs saved before Lean. Actual smooth
reference AC measure identification, internally produced nef CY equality and
ALL-original-current nef volume. No calibration/limit/desired measure input.
General pseff CY and volume semicontinuity are not asserted. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
namespace SGPT.Foundations.Analysis.Pending.NefOriginalCurrentCalabiYau
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  CanonicalCurrentFrame CurrentBottChernClass GlobalCurrentPotentials
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  PositiveCurrentACTopMeasure ActualAnalyticCurrentLocalDensity
  LocalProductCurrents SmoothMixedMeasureDensity GlobalNonPluripolar
  IntegrationCurrent NefMixedMass NefOriginalCurrentCalibratedLimit
  NefOriginalCurrentSharpACMass OriginalCurrentACVolume
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

omit [CompactSpace M] in
private theorem chart_measure_apply
    (T : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))) (hT : IsFullPositive T)
    (e : ComplexChart (m+1) M) (s : Set M) :
    chartACMeasure T hT e s =
      acTopMeasure (isPositive_chartSpanCurrent T hT e) (e.val.target ∩ e.val.symm ⁻¹' s) := by
  let j : e.val.target → M := fun z => ((e.val.toHomeomorphSourceTarget).symm z : M)
  have hj : MeasurableEmbedding j :=
    (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
      (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel (m+1)) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  change ((acTopMeasure (isPositive_chartSpanCurrent T hT e)).comap
    (Subtype.val : e.val.target → ComplexModel (m+1))).map j s = _
  rw [hj.map_apply,hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.property,hw⟩
  · rintro ⟨hz,hzs⟩
    exact ⟨⟨z,hz⟩,hzs,rfl⟩

/-- The SAME smooth original current's canonical AC measure is the actual
zero-potential smooth NP measure, for any original positivity proof. -/
theorem globalACtopMeasure_smoothClosedCurrent_eq
    (σ : ClosedRealOneOneForm (m+1) M) (hσ : σ.val.IsSemipositive)
    (hT : IsFullPositive (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) σ).val) :
    globalACtopMeasure
      (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) σ).val hT =
      globalMixedMeasure (fun _ : Fin (m+1) => σ) (fun _ _ => 0)
        (fun _ => (LocalPotentials.thetaPlurisubharmonic_zero_iff σ).mpr hσ) := by
  let T := (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) σ).val
  let h0 : ∀ _ : Fin (m+1), ThetaPlurisubharmonic σ.val (fun _ => 0) :=
    fun _ => (LocalPotentials.thetaPlurisubharmonic_zero_iff σ).mpr hσ
  let ν := globalMixedMeasure (fun _ : Fin (m+1) => σ) (fun _ _ => 0) h0
  apply (globalACtopMeasure_unique T hT ν ?_).symm
  intro e
  have hd : acTopMeasure (isPositive_chartSpanCurrent T hT e) =
      (volume.restrict e.val.target).withDensity (chartDensity (fun _ => σ) e) := by
    rw [acTopMeasure]
    change (volume.withDensity fun z => ENNReal.ofReal (actualTopPowerDensity
      (LocalCurrentDeterminant.acForm (isPositive_chartSpanCurrent T hT e) z))).restrict
        e.val.target = _
    rw [restrict_withDensity e.val.open_target.measurableSet]
    apply withDensity_congr_ae
    filter_upwards [ae_acForm_smoothClosedCurrent σ hσ hT e] with z hz
    rw [hz]
    simp only [chartDensity,actualMixedTopDensity_const]
  ext A hA
  let C := e.val.target ∩ e.val.symm ⁻¹' A
  have hC : MeasurableSet C :=
    measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
      e.val.continuousOn_symm hA
  have himage : e.val.symm '' e.val.target = e.val.source := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact e.val.map_target hz
    · intro hx
      exact ⟨e.val x,e.val.map_source hx,e.val.left_inv hx⟩
  have hpiece : A ∩ e.val.source = e.val.symm '' C := by
    change A ∩ e.val.source = e.val.symm '' (e.val.target ∩ e.val.symm ⁻¹' A)
    rw [image_inter_preimage,himage,inter_comm]
  rw [Measure.restrict_apply hA,hpiece]
  change globalMixedMeasure (fun _ : Fin (m+1) => σ) (fun _ _ => 0) h0
      (e.val.symm '' C) = _
  rw [globalMixedMeasure_image_eq_lintegral h0 e hC inter_subset_left,
    chart_measure_apply,hd,withDensity_apply' _ _,
    Measure.restrict_restrict_of_subset inter_subset_left]

private theorem reference_scaled_mass
    (ω : KahlerBackground (m+1) M) (I : ℝ) (hc : 0 ≤ I / (kahlerVolume ω).real univ)
    (hV : 0 < (kahlerVolume ω).real univ) :
    (ENNReal.ofReal (I / (kahlerVolume ω).real univ) • kahlerVolume ω) univ =
      ENNReal.ofReal I := by
  rw [Measure.smul_apply,smul_eq_mul,
    ← ENNReal.ofReal_toReal (measure_ne_top (kahlerVolume ω) univ),
    ← ENNReal.ofReal_mul hc]
  change ENNReal.ofReal (I / (kahlerVolume ω).real univ * (kahlerVolume ω).real univ) = _
  rw [div_mul_cancel₀ _ hV.ne']

/-- Nefness internally produces the SAME original closed positive current
with the entire calibrated AC measure equal to the genuine Kahler volume. -/
theorem exists_nef_original_current_calabi_yau [ConnectedSpace M]
    (ω : KahlerBackground (m+1) M) (θ : ClosedRealOneOneForm (m+1) M)
    (hnef : NefWithRespectTo ω θ) :
    0 ≤ slotIntegral ω (fun _ => θ) / (kahlerVolume ω).real univ ∧
    ∃ (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m))
      (hT : IsFullPositive T.val),
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T =
        RealBottChern.ofRepresentative θ ∧
      globalACtopMeasure T.val hT =
        ENNReal.ofReal (slotIntegral ω (fun _ => θ) / (kahlerVolume ω).real univ) •
          kahlerVolume ω := by
  obtain ⟨hc,T,hT,hclass,hmeasure⟩ := exists_nef_original_current_ac_lower_bound ω θ hnef
  have hreference : ∀ hR : IsFullPositive
      (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) ω.form).val,
      globalACtopMeasure
        (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) ω.form).val hR =
        kahlerVolume ω := by
    intro hR
    exact globalACtopMeasure_smoothClosedCurrent_eq ω.form ω.isSemipositive hR
  rw [hreference] at hmeasure
  have hV := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω
  have hmass := reference_scaled_mass ω (slotIntegral ω (fun _ => θ)) hc hV
  have hupper := original_ac_top_mass_le_intersection_of_nef ω θ hnef T hT hclass
  have heqmass : (ENNReal.ofReal (slotIntegral ω (fun _ => θ) / (kahlerVolume ω).real univ) •
      kahlerVolume ω) univ = globalACtopMeasure T.val hT univ :=
    le_antisymm (Measure.le_iff'.mp hmeasure univ) (hupper.trans_eq hmass.symm)
  let : IsFiniteMeasure (ENNReal.ofReal (slotIntegral ω (fun _ => θ) /
      (kahlerVolume ω).real univ) • kahlerVolume ω) := ⟨by
    rw [hmass]
    exact ENNReal.ofReal_lt_top⟩
  exact ⟨hc,T,hT,hclass,(Measure.eq_of_le_of_measure_univ_eq hmeasure heqmass).symm⟩

/-- The genuine ALL-original-current volume supremum of a nef class is its
actual smooth intersection; its maximizing current is produced internally. -/
theorem originalCurrentACVolume_nef_eq_intersection [ConnectedSpace M]
    (ω : KahlerBackground (m+1) M) (θ : ClosedRealOneOneForm (m+1) M)
    (hnef : NefWithRespectTo ω θ) :
    originalCurrentACVolume (RealBottChern.ofRepresentative θ) =
      ENNReal.ofReal (slotIntegral ω (fun _ => θ)) := by
  apply le_antisymm
  · exact iSup_le fun T => iSup_le fun hT => iSup_le fun hclass =>
      original_ac_top_mass_le_intersection_of_nef ω θ hnef T hT hclass
  · obtain ⟨hc,T,hT,hclass,hmeasure⟩ := exists_nef_original_current_calabi_yau ω θ hnef
    have hmass := reference_scaled_mass ω (slotIntegral ω (fun _ => θ)) hc
      (NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω)
    have hm : globalACtopMeasure T.val hT univ = ENNReal.ofReal (slotIntegral ω (fun _ => θ)) := by
      rw [hmeasure]
      exact hmass
    rw [← hm]
    exact ac_top_mass_le_volume T hT hclass

end SGPT.Foundations.Analysis.Pending.NefOriginalCurrentCalabiYau

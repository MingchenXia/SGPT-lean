import SGPT.PSH.SourceTestCurveSumIGood
import SGPT.PSH.SourceIModelTestCurveLimits
import SGPT.PSH.SourceTestCurveScalingProjection

/-! # Actual limits and symmetry of the original test-curve sum

The limit identity uses genuine increasing chart-AE recovery for the unchanged
original potentials. Background identifications are equalities of whole forms.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [BorelSpace M] [ConnectedSpace M] in
/-- Genuine increasing exhaustion commutes with the literal sum of the two
original spatial limits, retaining both negative-infinite pole loci. -/
theorem sourceTestCurve_exhaustingSum_regularized_eq
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    uscRegularization (⨆ j : ℕ, fun x ↦
      Γ.potential (sourceTestCurveExhaustingParameter Γ.toSourceTestCurvePredata j) x +
        Δ.potential (sourceTestCurveExhaustingParameter Δ.toSourceTestCurvePredata j) x) =
      fun x ↦ sourceTestCurveLimit Γ.toSourceTestCurvePredata x +
        sourceTestCurveLimit Δ.toSourceTestCurvePredata x := by
  let A : ℕ → M → EReal := fun j ↦
    Γ.potential (sourceTestCurveExhaustingParameter Γ.toSourceTestCurvePredata j)
  let B : ℕ → M → EReal := fun j ↦
    Δ.potential (sourceTestCurveExhaustingParameter Δ.toSourceTestCurvePredata j)
  let T := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  have hAm : Monotone A := Γ.toSourceTestCurvePredata.exhaustingPotential_monotone
  have hBm : Monotone B := Δ.toSourceTestCurvePredata.exhaustingPotential_monotone
  have hA (j : ℕ) : IsThetaPshPotential (atlasClosedFormToNative θ).val (A j) :=
    Γ.native_thetaPSH _
  have hB (j : ℕ) : IsThetaPshPotential (atlasClosedFormToNative σ).val (B j) :=
    Δ.native_thetaPSH _
  have hPA := (isThetaPSH_iff_nativeThetaPotential θ _).mp Γ.limit_thetaPSH
  have hPB := (isThetaPSH_iff_nativeThetaPotential σ _).mp Δ.limit_thetaPSH
  have heqA : uscRegularization (⨆ j, A j) =
      sourceTestCurveLimit Γ.toSourceTestCurvePredata :=
    Γ.toSourceTestCurvePredata.exhaustingPotential_regularized_eq
  have heqB : uscRegularization (⨆ j, B j) =
      sourceTestCurveLimit Δ.toSourceTestCurvePredata :=
    Δ.toSourceTestCurvePredata.exhaustingPotential_regularized_eq
  apply SingularModelIncreasingAERegularizedLimit.uscRegularization_iSup_eq_of_monotone_ae_chart_tendsto
    (fun j ↦ (isThetaPSH_iff_nativeThetaPotential T _).mp
      (sourceIndependentSum_thetaPSH (Γ.thetaPSH _) (Δ.thetaPSH _)))
    ((isThetaPSH_iff_nativeThetaPotential T _).mp
      (sourceIndependentSum_thetaPSH Γ.limit_thetaPSH Δ.limit_thetaPSH))
    (fun x j k hjk ↦ add_le_add (hAm hjk x) (hBm hjk x))
  intro e
  have hAEa := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
    hA hAm (heqA.symm ▸ hPA) e
  have hAEb := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
    hB hBm (heqB.symm ▸ hPB) e
  rw [heqA] at hAEa
  rw [heqB] at hAEb
  filter_upwards [hAEa, hAEb] with z ha hb
  have hla : Tendsto (fun j ↦ A j (e.val.symm z)) atTop
      (𝓝 (sourceTestCurveLimit Γ.toSourceTestCurvePredata (e.val.symm z))) := by
    change Tendsto (fun j ↦ chartFunction (A j) e z) atTop
      (𝓝 (chartFunction (sourceTestCurveLimit Γ.toSourceTestCurvePredata) e z))
    rw [← ha]
    exact tendsto_atTop_iSup (fun j k hjk ↦ hAm hjk (e.val.symm z))
  have hlb : Tendsto (fun j ↦ B j (e.val.symm z)) atTop
      (𝓝 (sourceTestCurveLimit Δ.toSourceTestCurvePredata (e.val.symm z))) := by
    change Tendsto (fun j ↦ chartFunction (B j) e z) atTop
      (𝓝 (chartFunction (sourceTestCurveLimit Δ.toSourceTestCurvePredata) e z))
    rw [← hb]
    exact tendsto_atTop_iSup (fun j k hjk ↦ hBm hjk (e.val.symm z))
  exact (EReal.continuousAt_add
    (Or.inl (hPA.1.quasiPlurisubharmonic.ne_top (e.val.symm z)))
    (Or.inr (hPB.1.quasiPlurisubharmonic.ne_top (e.val.symm z)))).tendsto.comp
      (hla.prodMk_nhds hlb)

/-- Exact original `eq:sumGammaGammap`, on the same actual two-background
ordinary envelope and genuine original negative-infinity limit functions. -/
theorem SourceTestCurve.sum_limit (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    sourceTestCurveLimit (SourceTestCurve.sum omega Γ Δ).toSourceTestCurvePredata =
      sourceSingularityEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
        (fun x ↦ sourceTestCurveLimit Γ.toSourceTestCurvePredata x +
          sourceTestCurveLimit Δ.toSourceTestCurvePredata x) := by
  let T := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  let S := SourceTestCurve.sum omega Γ Δ
  let U : M → EReal := fun x ↦ sourceTestCurveLimit Γ.toSourceTestCurvePredata x +
    sourceTestCurveLimit Δ.toSourceTestCurvePredata x
  have hU : (ofFixedModel n M).IsThetaPSH T U :=
    sourceIndependentSum_thetaPSH Γ.limit_thetaPSH Δ.limit_thetaPSH
  have hP : (ofFixedModel n M).IsThetaPSH T (sourceSingularityEnvelope T U) :=
    sourceOrdinaryEnvelope_genuine hU
  have hL := S.limit_thetaPSH
  have hupper : sourceTestCurveLimit S.toSourceTestCurvePredata ≤
      sourceSingularityEnvelope T U := by
    apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential T _).mp hP).1.quasiPlurisubharmonic.upperSemicontinuous
    intro x
    apply iSup_le
    intro r
    apply sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun y _ ↦ ?_) x
    apply iSup_le
    intro d
    exact add_le_add (Γ.toSourceTestCurvePredata.at_le_limit d y)
      (Δ.toSourceTestCurvePredata.at_le_limit (r.val - d) y)
  have hstage (j : ℕ) :
      (fun x ↦ Γ.potential (sourceTestCurveExhaustingParameter Γ.toSourceTestCurvePredata j) x +
        Δ.potential (sourceTestCurveExhaustingParameter Δ.toSourceTestCurvePredata j) x) ≤
      sourceTestCurveLimit S.toSourceTestCurvePredata := by
    let a := sourceTestCurveExhaustingParameter Γ.toSourceTestCurvePredata j
    let b := sourceTestCurveExhaustingParameter Δ.toSourceTestCurvePredata j
    let r : Iio S.max := ⟨a.val + b.val, by
      change a.val + b.val < Γ.max + Δ.max
      have ha : a.val < Γ.max := a.property
      have hb : b.val < Δ.max := b.property
      linarith⟩
    have hraw := sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata (show r.val ≤ Γ.max + Δ.max from r.property.le)
    have hown : sourceTestCurveRawSum Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata r.val ≤ S.potential r := by
      exact le_sourceSingularityEnvelope hraw
        (sourceTestCurveRawSum_le_zero Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r.val)
        (MoreSingularOn.of_le fun _ _ ↦ le_rfl)
    intro x
    have hsummand : Γ.potential a x + Δ.potential b x ≤
        sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r.val x := by
      have h := le_iSup (fun d : ℝ ↦ sourceTestCurveAt Γ.toSourceTestCurvePredata d x +
        sourceTestCurveAt Δ.toSourceTestCurvePredata (r.val - d) x) a.val
      have hab : r.val - a.val = b.val := by dsimp [r]; ring
      simpa only [sourceTestCurveRawSum, hab, sourceTestCurveAt_of_lt _ a.property,
        sourceTestCurveAt_of_lt _ b.property] using h
    exact (hsummand.trans (hown x)).trans
      ((le_iSup (fun q : Iio S.max ↦ S.potential q x) r).trans
        (le_uscRegularization (fun y ↦ ⨆ q : Iio S.max, S.potential q y) x))
  have hUL : U ≤ sourceTestCurveLimit S.toSourceTestCurvePredata := by
    rw [show U = uscRegularization (⨆ j : ℕ, fun x ↦
      Γ.potential (sourceTestCurveExhaustingParameter Γ.toSourceTestCurvePredata j) x +
        Δ.potential (sourceTestCurveExhaustingParameter Δ.toSourceTestCurvePredata j) x) from
      (sourceTestCurve_exhaustingSum_regularized_eq Γ Δ).symm]
    exact uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential T _).mp hL).1.quasiPlurisubharmonic.upperSemicontinuous
      (iSup_le hstage)
  exact le_antisymm hupper ((sourceOrdinaryEnvelope_mono
    (MoreSingularOn.of_le fun x _ ↦ hUL x)).trans_eq
      (S.limit_model omega).choose_spec.1.symm)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The two full atlas sum backgrounds agree, beyond their cohomology classes. -/
theorem sourceTestCurveSumBackground_comm
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ) =
      nativeClosedFormToAtlas (atlasClosedFormToNative σ + atlasClosedFormToNative θ) :=
  congrArg nativeClosedFormToAtlas (add_comm _ _)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The actual all-real raw convolution is symmetric even at cutoff values. -/
theorem sourceTestCurveRawSum_comm (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) (r : ℝ) :
    sourceTestCurveRawSum Γ Δ r = sourceTestCurveRawSum Δ Γ r := by
  funext x
  apply le_antisymm
  · apply iSup_le
    intro d
    have h := le_iSup (fun e : ℝ ↦ sourceTestCurveAt Δ e x + sourceTestCurveAt Γ (r-e) x) (r-d)
    simpa only [sourceTestCurveRawSum, sub_sub_cancel, add_comm] using h
  · apply iSup_le
    intro e
    have h := le_iSup (fun d : ℝ ↦ sourceTestCurveAt Γ d x + sourceTestCurveAt Δ (r-d) x) (r-e)
    simpa only [sourceTestCurveRawSum, sub_sub_cancel, add_comm] using h

/-- Commutativity of the actual original objects, with the exact whole-form
identification and unchanged cutoff and open-slice potentials. -/
theorem SourceTestCurve.sum_comm (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    (SourceTestCurve.sum omega Γ Δ).castBackground (sourceTestCurveSumBackground_comm θ σ) =
      SourceTestCurve.sum omega Δ Γ := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.castBackground_max, SourceTestCurve.sum_max, add_comm]
  · intro r hr hs
    have hrl : r < (SourceTestCurve.sum omega Γ Δ).max := by
      simpa only [SourceTestCurve.castBackground_max] using hr
    rw [SourceTestCurve.castBackground_potential _ _ r hrl hr,
      SourceTestCurve.sum_potential, SourceTestCurve.sum_potential]
    rw [sourceTestCurveRawSum_comm]
    exact congrArg (fun T ↦ sourceSingularityEnvelope T
      (sourceTestCurveRawSum Δ.toSourceTestCurvePredata Γ.toSourceTestCurvePredata r))
        (sourceTestCurveSumBackground_comm θ σ)

/-- Actual positive raw I-goodness in the unchanged sum background gives
genuine I-modelness of every original open ordinary-sum slice. -/
theorem SourceTestCurve.sum_isIModel (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (hΓ : SourceTestCurveIsIModel Γ) (hΔ : SourceTestCurveIsIModel Δ) :
    SourceTestCurveIsIModel (SourceTestCurve.sum omega Γ Δ) := by
  intro r
  let T := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  let u := sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r.val
  have hr : r.val < Γ.max + Δ.max := r.property
  have hu : (ofFixedModel n M).IsThetaPSH T u :=
    sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hr.le
  have hpos := sourceTestCurveRawSum_mass_positive omega Γ Δ hr
  have hgood := (sourceIGood_iff_native _).mp (sourceTestCurveRawSum_iGood omega Γ Δ hΓ hΔ hr)
  obtain ⟨B, huB, hgoodB⟩ := hgood
  have huT := (isThetaPSH_iff_nativeThetaPotential T u).mp hu
  have hgoodT := (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
    omega B (atlasClosedFormToNative T) huB huT hgoodB.positiveMass hpos).mp hgoodB
  have heq := ((sourceIGoodWith_iff_native T u hu).mpr hgoodT).envelope_eq
  change IEnvelope.IsIModelPotential (atlasClosedFormToNative T).val
    (sourceSingularityEnvelope T u)
  rw [heq]
  exact (sourceIModel_iff_native T _).mp (sourceIEnvelope_isIModel hu)

end SGPT.PSH.VariableComplexAtlas

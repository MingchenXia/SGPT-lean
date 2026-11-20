import SGPT.PSH.SourceTestCurveRegularizationConvergence
import SGPT.PSH.SourceTestCurveBoundedEnergy
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

/-- The SAME bounded regularization at the canonical positive parameters. -/
def sourceTestCurveRegularizationSequence (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (k : ℕ) : SourceTestCurve θ :=
  sourceTestCurveRegularization omega Γ hΓ hmax (sourceRegularizationParameter_pos k)

/-- Original based and bounded membership is produced, not assumed. -/
theorem sourceTestCurveRegularizationSequence_bounded (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (k : ℕ) :
    sourceTestCurveRegularizationSequence omega Γ hΓ hmax k ∈ SourceBoundedTestCurves θ φ hφ :=
  sourceTestCurveRegularization_bounded omega Γ hΓ hmax (sourceRegularizationParameter_pos k)

/-- Actual mass order in the SEQUENCE index at every original negative parameter. -/
theorem sourceTestCurveRegularizationSequence_realMass_antitone (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) {r : ℝ} (hr : r < 0) :
    Antitone (fun k => sourceTestCurveRealMassAt omega
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k) r) := by
  intro i j hij
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
  have hi : r < (G i).max := hr
  have hj : r < (G j).max := hr
  change sourceTestCurveRealMassAt omega (G j) r ≤ sourceTestCurveRealMassAt omega (G i) r
  rw [sourceTestCurveRealMassAt_of_lt omega (G i) hi,
    sourceTestCurveRealMassAt_of_lt omega (G j) hj]
  apply ENNReal.toReal_mono ((G i).mass_lt_top omega ⟨r, hi⟩).ne
  apply sourcePotentialNonPluripolarMass_mono omega
  apply MoreSingularOn.of_le
  intro x _
  change sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter j) r x ≤
    sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter i) r x
  exact sourceTestCurveRegularizationFamily_antitone_sequence Γ hΓ hr hij x

/-- Literal actual mass readers converge; the cutoff dummy is never used. -/
theorem sourceTestCurveRegularizationSequence_realMass_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) {r : ℝ} (hr : r < 0) :
    Tendsto (fun k => sourceTestCurveRealMassAt omega
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k) r) atTop
      (𝓝 (sourceTestCurveRealMassAt omega Γ r)) := by
  have hrΓ : r < Γ.max := by rwa [hmax]
  have h := sourceTestCurveRegularizationFamily_realMass_tendsto omega Γ hΓ hmax hr
  rw [sourceTestCurveRealMassAt_of_lt omega Γ hrΓ]
  simp only [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hrΓ] at h
  have hreader (k : ℕ) : sourceTestCurveRealMassAt omega
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k) r =
      (sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r)
        (sourceTestCurveRegularizationFamily_model omega Γ hΓ hmax
          (sourceRegularizationParameter_pos k) hr).thetaPSH univ).toReal := by
    rw [sourceTestCurveRealMassAt_of_lt omega _ (show r <
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).max from hr)]
    rfl
  simp_rw [hreader]
  exact h

private theorem actualDeficit_integrals (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) :
    let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
    let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
    let D := fun k => ∫⁻ r : ℝ in Iio (0 : ℝ),
      ENNReal.ofReal (V - sourceTestCurveRealMassAt omega (G k) r)
    Monotone D ∧ Tendsto D atTop (𝓝 (∫⁻ r : ℝ in Iio (0 : ℝ),
      ENNReal.ofReal (V - sourceTestCurveRealMassAt omega Γ r))) := by
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
  let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  let μ : Measure ℝ := volume.restrict (Iio (0 : ℝ))
  let f := fun k r => ENNReal.ofReal (V - sourceTestCurveRealMassAt omega (G k) r)
  have hf (k : ℕ) : AEMeasurable (f k) μ :=
    (ENNReal.continuous_ofReal.measurable.comp
      (measurable_const.sub (sourceTestCurveRealMassAt_measurable omega (G k)))).aemeasurable
  have hm : ∀ᵐ r ∂μ, Monotone (fun k => f k r) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with r hr
    intro i j hij
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left
      (sourceTestCurveRegularizationSequence_realMass_antitone omega Γ hΓ hmax hr hij) V)
  have ht : ∀ᵐ r ∂μ, Tendsto (fun k => f k r) atTop
      (𝓝 (ENNReal.ofReal (V - sourceTestCurveRealMassAt omega Γ r))) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with r hr
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.sub
      (sourceTestCurveRegularizationSequence_realMass_tendsto omega Γ hΓ hmax hr))
  exact ⟨fun _ _ hij => lintegral_mono_ae (hm.mono fun _ hr => hr hij),
    lintegral_tendsto_of_tendsto_of_monotone hf hm ht⟩

/-- Actual extended energies decrease along the canonical sequence. -/
theorem sourceTestCurveRegularizationSequence_energy_antitone (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) :
    Antitone (fun k => sourceTestCurveEnergy omega hφ
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k)
      (sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k).1) := by
  have hm := (actualDeficit_integrals omega Γ hΓ hmax).1
  intro i j hij
  simp only [sourceTestCurveEnergy,
    show (sourceTestCurveRegularizationSequence omega Γ hΓ hmax j).max = 0 from rfl,
    show (sourceTestCurveRegularizationSequence omega Γ hΓ hmax i).max = 0 from rfl,
    zero_mul, EReal.coe_zero, zero_sub]
  exact EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hm hij))

/-- Genuine infinite-interval MCT gives the SAME defining extended-energy
limit, including the original negative-infinite branch. -/
theorem sourceTestCurveRegularizationSequence_energy_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) :
    Tendsto (fun k => sourceTestCurveEnergy omega hφ
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k)
      (sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k).1) atTop
      (𝓝 (sourceTestCurveEnergy omega hφ Γ hΓ)) := by
  have ht := continuous_coe_ennreal_ereal.continuousAt.tendsto.comp
    (actualDeficit_integrals omega Γ hΓ hmax).2
  have hn := ht.neg
  simpa only [sourceTestCurveEnergy,
    show ∀ k, (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).max = 0 from fun _ => rfl,
    hmax, zero_mul, EReal.coe_zero, zero_sub, Function.comp_def] using hn

/-- Real readback is licensed by the ORIGINAL finite-energy class at the limit. -/
theorem sourceTestCurveRegularizationSequence_realEnergy_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (hE : Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ) :
    Tendsto (fun k => (sourceTestCurveEnergy omega hφ
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k)
      (sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k).1).toReal) atTop
      (𝓝 (sourceTestCurveEnergy omega hφ Γ hΓ).toReal) := by
  obtain ⟨hb, hbot, htop⟩ := sourceTestCurveEnergy_finite_of_mem omega hφ Γ hE
  exact (EReal.tendsto_toReal htop hbot).comp
    (sourceTestCurveRegularizationSequence_energy_tendsto omega Γ hΓ hmax)

/-- BOTH actual time-one energies are the SAME stagewise test-curve energy. -/
theorem sourceTestCurveRegularizationSequence_legendreOne_energy (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (k : ℕ) :
    let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax k
    let hb := sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre G.toSourceTestCurvePredata 1) hφ =
        sourceTestCurveEnergy omega hφ G hb.1 ∧
    sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay G.toSourceTestCurvePredata ⟨1, by norm_num⟩) hφ =
        sourceTestCurveEnergy omega hφ G hb.1 := by
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax k
  have hb := sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k
  exact ⟨by simpa only [EReal.coe_one, one_mul] using
      (G.boundedLegendre_energy_identity omega hb (show G.max = 0 from rfl) (by norm_num : (0 : ℝ) < 1)).1,
    by simpa only [EReal.coe_one, one_mul] using
      (G.boundedLegendre_assigned_energy_identity omega hb (show G.max = 0 from rfl) ⟨1, by norm_num⟩).2⟩

/-- The two actual approximating-ray energy sequences converge, even at bottom. -/
theorem sourceTestCurveRegularizationSequence_legendreOne_energy_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) :
    let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
    Tendsto (fun k => sourceRelativeEnergy θ φ
      (sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata 1) hφ) atTop
      (𝓝 (sourceTestCurveEnergy omega hφ Γ hΓ)) ∧
    Tendsto (fun k => sourceRelativeEnergy θ φ
      (sourceTestCurveLegendreRay (G k).toSourceTestCurvePredata ⟨1, by norm_num⟩) hφ) atTop
      (𝓝 (sourceTestCurveEnergy omega hφ Γ hΓ)) := by
  have ht := sourceTestCurveRegularizationSequence_energy_tendsto omega Γ hΓ hmax
  constructor
  · simpa only [(sourceTestCurveRegularizationSequence_legendreOne_energy omega Γ hΓ hmax _).1] using ht
  · simpa only [(sourceTestCurveRegularizationSequence_legendreOne_energy omega Γ hΓ hmax _).2] using ht

/-- Finite original energy licenses BOTH actual time-one real-energy readbacks. -/
theorem sourceTestCurveRegularizationSequence_legendreOne_realEnergy_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (hE : Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ) :
    let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
    Tendsto (fun k => (sourceRelativeEnergy θ φ
      (sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata 1) hφ).toReal) atTop
      (𝓝 (sourceTestCurveEnergy omega hφ Γ hΓ).toReal) ∧
    Tendsto (fun k => (sourceRelativeEnergy θ φ
      (sourceTestCurveLegendreRay (G k).toSourceTestCurvePredata ⟨1, by norm_num⟩) hφ).toReal) atTop
      (𝓝 (sourceTestCurveEnergy omega hφ Γ hΓ).toReal) := by
  have ht := sourceTestCurveRegularizationSequence_realEnergy_tendsto omega Γ hΓ hmax hE
  constructor
  · simpa only [(sourceTestCurveRegularizationSequence_legendreOne_energy omega Γ hΓ hmax _).1] using ht
  · simpa only [(sourceTestCurveRegularizationSequence_legendreOne_energy omega Γ hΓ hmax _).2] using ht

end SGPT.PSH.VariableComplexAtlas

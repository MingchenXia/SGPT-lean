import SGPT.PSH.SourceDarvasMetric
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalTopology
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMaximumBound

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped ENNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- The actual sum of the two original non-pluripolar diagonal measures. -/
def sourceIThetaMeasure (u v : SourceFiniteEnergyPotential θ φ hφ) : Measure M :=
  sourcePotentialNonPluripolarMeasure θ u.val u.property.1.choose +
    sourcePotentialNonPluripolarMeasure θ v.val v.property.1.choose

/-- WHOLE original def:Itheta on exactly its original E1 domain. The
nonnegative extended integral keeps the true extended absolute gap, with
common negative poles assigned zero and one-sided poles kept infinite. -/
def sourceITheta (u v : SourceFiniteEnergyPotential θ φ hφ) : ENNReal :=
  ∫⁻ x, canonicalERealAbsDiff (u.val x) (v.val x) ∂sourceIThetaMeasure u v

omit [ConnectedSpace M] [BorelSpace M] in
/-- The whole original integral has the identical native measure/integrand. -/
theorem sourceITheta_eq_native (u v : SourceFiniteEnergyPotential θ φ hφ) :
    sourceITheta u v = SingularModelFiniteEnergyDiagonalGap.diagonalGapIntegral
      (atlasClosedFormToNative θ) u.val v.val
      ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property.1.choose)
      ((isThetaPSH_iff_nativeThetaPotential θ v.val).mp v.property.1.choose) := rfl

omit [ConnectedSpace M] in
/-- BOTH actual potentials are genuinely finite almost everywhere for the
actual SUM measure. This precedes every ordinary real-difference readback. -/
theorem sourceITheta_ae_finite (u v : SourceFiniteEnergyPotential θ φ hφ) :
    ∀ᵐ x ∂sourceIThetaMeasure u v,
      u.val x ≠ ⊤ ∧ u.val x ≠ ⊥ ∧ v.val x ≠ ⊤ ∧ v.val x ≠ ⊥ := by
  have hu := (isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property.1.choose
  have hv := (isThetaPSH_iff_nativeThetaPotential θ v.val).mp v.property.1.choose
  have hpole (w : M → EReal) (hw : IsThetaPshPotential (atlasClosedFormToNative θ).val w) :
      ∀ᵐ x ∂sourceIThetaMeasure u v, w x ≠ ⊥ := by
    apply ae_iff.mpr
    have hz : sourceIThetaMeasure u v {x | w x = ⊥} = 0 := by
      change (DiagonalMass.diagonalPotentialMeasure (atlasClosedFormToNative θ) u.val hu +
        DiagonalMass.diagonalPotentialMeasure (atlasClosedFormToNative θ) v.val hv) {x | w x = ⊥} = 0
      simp only [Measure.add_apply, DiagonalMass.diagonalPotentialMeasure,
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
          (fun _ : Fin n ↦ hu.1) hw,
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
          (fun _ : Fin n ↦ hv.1) hw, add_zero]
    simpa only [not_not] using hz
  filter_upwards [hpole u.val hu, hpole v.val hv] with x hub hvb
  exact ⟨hu.1.quasiPlurisubharmonic.ne_top x, hub,
    hv.1.quasiPlurisubharmonic.ne_top x, hvb⟩

omit [ConnectedSpace M] in
/-- Actual arbitrary-pair E1 cross-measure integrability and genuine AE
finiteness produce integrability of the ordinary absolute real difference. -/
theorem sourceITheta_integrable_abs (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    Integrable (fun x ↦ |(u.val x).toReal - (v.val x).toReal|) (sourceIThetaMeasure u v) := by
  have hi : Integrable (fun x ↦ canonicalERealDiffToReal (u.val x) (v.val x))
      (sourceIThetaMeasure u v) :=
    SingularModelFiniteEnergyGapMax.integrable_canonicalDiff_diagonal_add omega
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)
  have heq : (fun x ↦ canonicalERealDiffToReal (u.val x) (v.val x)) =ᵐ[sourceIThetaMeasure u v]
      (fun x ↦ (u.val x).toReal - (v.val x).toReal) := by
    filter_upwards [sourceITheta_ae_finite u v] with x hx
    exact RelativeEnergyIntegrability.canonicalDiff_eq_sub_toReal hx.1 hx.2.2.1
      ⟨fun h ↦ (hx.2.1 h).elim, fun h ↦ (hx.2.2.2 h).elim⟩
  exact (hi.congr heq).abs

omit [ConnectedSpace M] in
/-- Actual pole-nullity and actual integrability identify the whole source
functional with the ordinary absolute integral of the original functions. -/
theorem sourceITheta_eq_integral_abs (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    sourceITheta u v = ENNReal.ofReal
      (∫ x, |(u.val x).toReal - (v.val x).toReal| ∂sourceIThetaMeasure u v) := by
  rw [ofReal_integral_eq_lintegral_ofReal (sourceITheta_integrable_abs omega u v)
    (Eventually.of_forall fun _ ↦ abs_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [sourceITheta_ae_finite u v] with x hx
  have hpole : u.val x = ⊥ ↔ v.val x = ⊥ :=
    ⟨fun h ↦ (hx.2.1 h).elim, fun h ↦ (hx.2.2.2 h).elim⟩
  rw [canonicalERealAbsDiff_eq_ofReal_abs_diff hx.1 hx.2.2.1 hpole,
    RelativeEnergyIntegrability.canonicalDiff_eq_sub_toReal hx.1 hx.2.2.1 hpole]

omit [ConnectedSpace M] in
/-- Genuine maximum closure, locality and actual ordered gap bounds exclude
positive infinity of the entire original absolute diagonal integral. -/
theorem sourceITheta_finite (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) : sourceITheta u v < ⊤ := by
  rw [sourceITheta_eq_native]
  exact SingularModelFiniteEnergyGapMax.diagonalGapIntegral_lt_top omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)

omit [ConnectedSpace M] in
/-- Genuine finiteness justifies the exact nonnegative extended readback. -/
theorem sourceITheta_finite_readback (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    ENNReal.ofReal (sourceITheta u v).toReal = sourceITheta u v :=
  ENNReal.ofReal_toReal (ne_of_lt (sourceITheta_finite omega u v))

omit [ConnectedSpace M] in
/-- Actual E1 upward/max closure manufactures the genuine source maximum. -/
def sourceFiniteEnergyMaximum (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) : SourceFiniteEnergyPotential θ φ hφ :=
  ⟨fun x ↦ max (u.val x) (v.val x), (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mpr
    (SingularModelFiniteEnergyGapMax.relativeFiniteEnergyPreceq_max omega
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
      ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property))⟩

omit [ConnectedSpace M] in
/-- WHOLE original lma:I_equal_Imaxsum, using genuine plurifine maximum
locality for the actual original measures and all infinite strata. -/
theorem sourceITheta_max_decomposition (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    sourceITheta u v = sourceITheta (sourceFiniteEnergyMaximum omega u v) u +
      sourceITheta (sourceFiniteEnergyMaximum omega u v) v := by
  simp only [sourceITheta_eq_native, sourceFiniteEnergyMaximum]
  exact SingularModelFiniteEnergyGapMax.diagonalGapIntegral_max_decomposition
    ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property.1.choose)
    ((isThetaPSH_iff_nativeThetaPotential θ v.val).mp v.property.1.choose)

/-- Exactly the original dimension constant, including dimension zero. -/
def sourceIThetaComparisonConstant (k : ℕ) : ℝ := 3 * 2 ^ (k + 2) * ((k : ℝ) + 1)

theorem sourceIThetaComparisonConstant_pos (k : ℕ) : 0 < sourceIThetaComparisonConstant k := by
  unfold sourceIThetaComparisonConstant
  positivity

/-- Actual two-sided extended-integral bounds; actual rooftop/contact and
midpoint measure inputs are produced by the genuine native proof. -/
theorem sourceITheta_darvas_bounds_ennreal (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    ENNReal.ofReal (sourceDarvasDistance θ φ hφ u v) ≤ sourceITheta u v ∧
    sourceITheta u v ≤ ENNReal.ofReal
      (sourceIThetaComparisonConstant n * sourceDarvasDistance θ φ hφ u v) := by
  simp only [sourceDarvasDistance_eq_native omega, sourceITheta_eq_native,
    sourceIThetaComparisonConstant]
  exact SingularModelDarvasDiagonalUpperComparison.ofReal_relativeD1_le_diagonalGapIntegral_le_mul
    omega ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)

/-- WHOLE original thm:I_d1_comp with EXACT source C_n, after genuine
absolute-integral finiteness. No bounded-reference or integrability input. -/
theorem sourceITheta_darvas_bounds (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    (sourceITheta u v).toReal / sourceIThetaComparisonConstant n ≤
        sourceDarvasDistance θ φ hφ u v ∧
      sourceDarvasDistance θ φ hφ u v ≤ (sourceITheta u v).toReal := by
  have hn := SingularModelDarvasDiagonalTopology.relativeD1_le_diagonalGapIntegral_toReal_le omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)
  have hs : sourceDarvasDistance θ φ hφ u v ≤ (sourceITheta u v).toReal ∧
      (sourceITheta u v).toReal ≤
        sourceIThetaComparisonConstant n * sourceDarvasDistance θ φ hφ u v := by
    simpa only [sourceDarvasDistance_eq_native omega, sourceITheta_eq_native,
      sourceIThetaComparisonConstant] using hn
  refine ⟨(div_le_iff₀ (sourceIThetaComparisonConstant_pos n)).mpr ?_, hs.1⟩
  simpa only [mul_comm] using hs.2

/-- WHOLE original cor:d1maxonearg, retaining the exact source constant
and manufactured genuine maximum on the entire original E1 class. -/
theorem sourceDarvasDistance_max_le (omega : KahlerBackground n M)
    (u v : SourceFiniteEnergyPotential θ φ hφ) :
    sourceDarvasDistance θ φ hφ (sourceFiniteEnergyMaximum omega u v) u ≤
      sourceIThetaComparisonConstant n * sourceDarvasDistance θ φ hφ u v := by
  simp only [sourceDarvasDistance_eq_native omega, sourceFiniteEnergyMaximum,
    sourceIThetaComparisonConstant]
  exact SingularModelDarvasMaximumBound.relativeD1_max_le_mul omega
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp u.property)
    ((sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mp v.property)

end SGPT.PSH.VariableComplexAtlas

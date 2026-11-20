import SGPT.Envelopes.SourceDominationPrinciple
import SGPT.PSH.SourceRayL1
import SGPT.Foundations.Analysis.Pending.PositiveMassCurrentBelow
import SGPT.Foundations.Analysis.Pending.NonBigPotentialMass

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending DiagonalMass ThetaPshConvexCombination

/-- The LITERAL original increasing sequence, with source index i=j+1.
No regularization or value at a pole is changed. -/
def sourceCurrentMinorant {M : Type*} (u s : M → EReal) (j : ℕ) : M → EReal :=
  convexComb (((j : ℝ) + 2)⁻¹) s u

/-- Both weights are genuinely positive at EVERY original sequence index. -/
theorem sourceCurrentMinorant_weights (j : ℕ) :
    0 < ((j : ℝ) + 2)⁻¹ ∧ ((j : ℝ) + 2)⁻¹ < 1 := by
  constructor
  · positivity
  · apply inv_lt_one_of_one_lt₀
    have h := Nat.cast_nonneg (α := ℝ) j
    linarith

/-- Genuine existing scalar inverse-affine limits give the actual coefficient limit. -/
theorem sourceCurrentMinorant_weight_tendsto :
    Tendsto (fun j : ℕ => ((j : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
  simpa only [Function.comp_def, one_mul] using
    (tendsto_mul_add_inv_atTop_nhds_zero 1 2 one_ne_zero).comp tendsto_natCast_atTop_atTop

/-- Exact source displayed coefficient formula after i=j+1. -/
theorem sourceCurrentMinorant_formula {M : Type*} (u s : M → EReal) (j : ℕ) :
    sourceCurrentMinorant u s j = convexComb (1 - ((j : ℝ) + 2)⁻¹) u s :=
  ConvexCombEnvelopeMass.convexComb_symm _ _ _

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u s : M → EReal}

/-- BOTH exact current dictionary directions: SAME actual original representative,
potential and positive lower form. This supplies an actual existing current object,
without a new target-shaped source-current predicate. -/
theorem sourceStrictCurrent_iff (ω : KahlerBackground n M) {δ : ℝ} (hδ : 0 < δ) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ - δ • ω.form)) s ↔
    ∃ T : KahlerCurrent (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
      T.representative = atlasClosedFormToNative θ ∧ T.potential = s ∧
        T.lowerBound.form = δ • ω.form := by
  constructor
  · intro hs
    have hsn := (isThetaPSH_iff_nativeThetaPotential _ s).mp hs
    rw [sourceNativeAtlasForm_roundTrip] at hsn
    exact ⟨AmbientConvexCurrent.kahlerCurrentOfSubSmul ω hδ hsn, rfl, rfl, rfl⟩
  · rintro ⟨T, hrep, hpot, hbound⟩
    apply (isThetaPSH_iff_nativeThetaPotential _ s).mpr
    rw [sourceNativeAtlasForm_roundTrip]
    have h := T.strictlyPsh
    rwa [hrep, hpot, hbound] at h

/-- Existing extended-real weight monotonicity handles EVERY original pole;
no real readback is used in the pointwise increasing assertion. -/
theorem sourceCurrentMinorant_mono
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hsu : s ≤ u) :
    Monotone (sourceCurrentMinorant u s) := by
  intro j k hjk
  have hjpos : 0 < (j : ℝ) + 2 := by positivity
  have hjkle : (j : ℝ) + 2 ≤ (k : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hjk 2
  have hε : ((k : ℝ) + 2)⁻¹ ≤ ((j : ℝ) + 2)⁻¹ :=
    inv_anti₀ hjpos hjkle
  exact DominationPrincipleBarrier.convexComb_antitone_of_le hsu
    (fun x => ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1.quasiPlurisubharmonic.ne_top x)
    (sourceCurrentMinorant_weights k).1 hε

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- BOTH genuine finite-AE inputs precede ALL ordinary real interpolation.
The result uses the ACTUAL original source omega^n, not a substituted measure. -/
theorem sourceCurrentMinorant_ae_tendsto (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hs : (ofFixedModel n M).IsThetaPSH θ s) :
    ∀ᵐ x ∂sourceKahlerVolume ω,
      Tendsto (fun j => sourceCurrentMinorant u s j x) atTop (𝓝 (u x)) := by
  rw [sourceKahlerVolume_eq_native]
  filter_upwards [sourceThetaPSH_ae_finite_kahlerVolume ω hu,
    sourceThetaPSH_ae_finite_kahlerVolume ω hs] with x hux hsx
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hreal : Tendsto
      (fun j : ℕ => ((j : ℝ) + 2)⁻¹ * (s x).toReal +
        (1 - ((j : ℝ) + 2)⁻¹) * (u x).toReal) atTop (𝓝 (u x).toReal) := by
    simpa only [zero_mul, sub_zero, one_mul, zero_add] using
      (sourceCurrentMinorant_weight_tendsto.mul_const (s x).toReal).add
        ((hOne.sub sourceCurrentMinorant_weight_tendsto).mul_const (u x).toReal)
  have hext := (continuous_coe_real_ereal.tendsto (u x).toReal).comp hreal
  simpa only [Function.comp_def, sourceCurrentMinorant, convexComb_apply,
    EReal.coe_mul, EReal.coe_add, EReal.coe_toReal hsx.1 hsx.2,
    EReal.coe_toReal hux.1 hux.2] using hext

variable [ConnectedSpace M]

/-- Positive mass produces bigness at the SAME representative. The actual
zero-dimensional constructor removes any n>0 restriction from the source. -/
theorem sourcePositiveMass_isBig (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact NonBigPotentialMass.isBigClass_of_dim_zero hn ω (atlasClosedFormToNative θ)
  · exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hn ω
      (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hpos

/-- WHOLE original prop:nppposimpbig: literal nonempty original positive-mass class. -/
theorem sourcePositiveMassClass_isBig (ω : KahlerBackground n M)
    (hne : ∃ u : M → EReal, ∃ hu : (ofFixedModel n M).IsThetaPSH θ u,
      0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) := by
  obtain ⟨u, hu, hpos⟩ := hne
  exact sourcePositiveMass_isBig ω hu hpos

/-- The existing WHOLE strict-lower-potential mother is used only AFTER
actual bigness is internally produced from the original positive mass. -/
theorem sourcePositiveMass_strictMinorant (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ s : M → EReal,
      (ofFixedModel n M).IsThetaPSH θ s ∧
      (ofFixedModel n M).IsThetaPSH
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ - δ • ω.form)) s ∧ s ≤ u := by
  obtain ⟨δ, hδ, s, hstrict, hsu⟩ := PositiveMassCurrentBelow.exists_strict_thetaPsh_potential_le
    ω (atlasClosedFormToNative θ) (sourcePositiveMass_isBig ω hu hpos)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hpos
  have hθ := LocalPotentials.isThetaPshPotential_add_of_semipositive hstrict
    (KahlerDomination.isSemipositive_smul ω.isSemipositive hδ.le)
  rw [sub_add_cancel] at hθ
  refine ⟨δ, hδ, s, (isThetaPSH_iff_nativeThetaPotential θ s).mpr hθ, ?_, hsu⟩
  apply (isThetaPSH_iff_nativeThetaPotential _ s).mpr
  simpa only [sourceNativeAtlasForm_roundTrip] using hstrict

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Existing convexity in BOTH form and potential produces the ACTUAL positive
shrinking margin, keeping the same original functions and background. -/
theorem sourceCurrentMinorant_strict (ω : KahlerBackground n M) {δ : ℝ}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hs : (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ - δ • ω.form)) s) (j : ℕ) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ -
        (((j : ℝ) + 2)⁻¹ * δ) • ω.form)) (sourceCurrentMinorant u s j) := by
  have hsn := (isThetaPSH_iff_nativeThetaPotential _ s).mp hs
  rw [sourceNativeAtlasForm_roundTrip] at hsn
  have hun : IsThetaPshPotential
      (atlasClosedFormToNative θ - (0 : ℝ) • ω.form).val u := by
    simpa only [zero_smul, sub_zero] using (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have h := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul ω
    (sourceCurrentMinorant_weights j).1 (sourceCurrentMinorant_weights j).2 hsn hun
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  simpa only [sourceNativeAtlasForm_roundTrip, mul_zero, add_zero, sourceCurrentMinorant] using h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The whole literal sequence consists of genuine original theta-PSH functions. -/
theorem sourceCurrentMinorant_genuine
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hs : (ofFixedModel n M).IsThetaPSH θ s) (j : ℕ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceCurrentMinorant u s j) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (isThetaPshPotential_convexComb ((isThetaPSH_iff_nativeThetaPotential θ s).mp hs)
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      (sourceCurrentMinorant_weights j).1 (sourceCurrentMinorant_weights j).2)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- EVERY sequence member has an ACTUAL existing Kähler-current object, with
exact original representative/potential and the manufactured positive margin. -/
theorem sourceCurrentMinorant_kahler (ω : KahlerBackground n M) {δ : ℝ} (hδ : 0 < δ)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hs : (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ - δ • ω.form)) s) (j : ℕ) :
    ∃ T : KahlerCurrent (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
      T.representative = atlasClosedFormToNative θ ∧
      T.potential = sourceCurrentMinorant u s j ∧
      T.lowerBound.form = (((j : ℝ) + 2)⁻¹ * δ) • ω.form :=
  (sourceStrictCurrent_iff ω (mul_pos (sourceCurrentMinorant_weights j).1 hδ)).mp
    (sourceCurrentMinorant_strict ω hu hs j)

/-- The original strict lower current and pointwise comparison are produced,
with the SAME source representative and SAME actual original potential. -/
theorem sourcePositiveMass_kahlerMinorant (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    ∃ s : M → EReal, (ofFixedModel n M).IsThetaPSH θ s ∧ s ≤ u ∧
      ∃ T : KahlerCurrent (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
        T.representative = atlasClosedFormToNative θ ∧ T.potential = s := by
  obtain ⟨δ, hδ, s, hs, hstrict, hsu⟩ := sourcePositiveMass_strictMinorant ω hu hpos
  obtain ⟨T, hrep, hpot, _⟩ := (sourceStrictCurrent_iff ω hδ).mp hstrict
  exact ⟨s, hs, hsu, T, hrep, hpot⟩

/-- WHOLE original lma:kahcurrentposmass: BOTH actual current/order clauses
AND its increasing-AE sequence conclusion. The original literal coefficient
formula and actual source omega^n are retained, including n=0 and unbounded poles. -/
theorem sourcePositiveMass_kahlerCurrent_and_increasingMinorants (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ s : M → EReal,
      (ofFixedModel n M).IsThetaPSH θ s ∧ s ≤ u ∧
      (∃ T : KahlerCurrent (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
        T.representative = atlasClosedFormToNative θ ∧ T.potential = s ∧
          T.lowerBound.form = δ • ω.form) ∧
      (∀ j, (ofFixedModel n M).IsThetaPSH θ (sourceCurrentMinorant u s j)) ∧
      Monotone (sourceCurrentMinorant u s) ∧
      (∀ j, ∃ T : KahlerCurrent (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
        T.representative = atlasClosedFormToNative θ ∧
        T.potential = sourceCurrentMinorant u s j ∧
        T.lowerBound.form = (((j : ℝ) + 2)⁻¹ * δ) • ω.form) ∧
      ∀ᵐ x ∂sourceKahlerVolume ω,
        Tendsto (fun j => sourceCurrentMinorant u s j x) atTop (𝓝 (u x)) := by
  obtain ⟨δ, hδ, s, hs, hstrict, hsu⟩ := sourcePositiveMass_strictMinorant ω hu hpos
  exact ⟨δ, hδ, s, hs, hsu, (sourceStrictCurrent_iff ω hδ).mp hstrict,
    sourceCurrentMinorant_genuine hu hs, sourceCurrentMinorant_mono hu hsu,
    sourceCurrentMinorant_kahler ω hδ hu hstrict, sourceCurrentMinorant_ae_tendsto ω hu hs⟩

end SGPT.PSH.VariableComplexAtlas

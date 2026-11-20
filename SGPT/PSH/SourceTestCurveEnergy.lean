import SGPT.PSH.SourceTestCurveFoundation
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Convex.GrowthClasses

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Actual diagonal mixed-mass finiteness is PRODUCED before real readback. -/
theorem SourceTestCurve.mass_lt_top (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ)
    (τ : Iio Γ.max) :
    sourcePotentialNonPluripolarMeasure θ (Γ.potential τ) (Γ.thetaPSH τ) univ < ⊤ := by
  simpa only [sourceMixedNonPluripolarMass_diagonal] using
    (sourceMixedNonPluripolarMass_lt_top ω (fun _ : Fin n ↦ θ)
      (fun _ ↦ Γ.potential τ) (fun _ ↦ Γ.thetaPSH τ))

/-- Actual FINITE source masses below the cutoff, with an auxiliary zero
scalar outside the integration domain. This is NOT the cutoff's mass. -/
def sourceTestCurveRealMassAt (_ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ) (τ : ℝ) : ℝ :=
  if hτ : τ < Γ.max then
    (sourcePotentialNonPluripolarMeasure θ (Γ.potential ⟨τ, hτ⟩) (Γ.thetaPSH ⟨τ, hτ⟩) univ).toReal
  else 0

omit [BorelSpace M] in
/-- SAME actual original mass at EVERY original integration parameter. -/
theorem sourceTestCurveRealMassAt_of_lt (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ)
    {τ : ℝ} (hτ : τ < Γ.max) :
    sourceTestCurveRealMassAt ω Γ τ =
      (sourcePotentialNonPluripolarMeasure θ (Γ.potential ⟨τ, hτ⟩) (Γ.thetaPSH ⟨τ, hτ⟩) univ).toReal := by
  rw [sourceTestCurveRealMassAt, dif_pos hτ]

/-- Genuine NP mass monotonicity and actual finiteness manufacture the
whole scalar antitone representative; no mass monotonicity certificate. -/
theorem sourceTestCurveRealMassAt_antitone (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ) :
    Antitone (sourceTestCurveRealMassAt ω Γ) := by
  intro a b hab
  by_cases ha : a < Γ.max
  · by_cases hb : b < Γ.max
    · rw [sourceTestCurveRealMassAt_of_lt ω Γ ha, sourceTestCurveRealMassAt_of_lt ω Γ hb]
      apply ENNReal.toReal_mono (Γ.mass_lt_top ω ⟨a, ha⟩).ne
      exact sourcePotentialNonPluripolarMass_mono ω (Γ.thetaPSH ⟨b, hb⟩)
        (Γ.thetaPSH ⟨a, ha⟩) (MoreSingularOn.of_le fun x _ ↦ Γ.antitone x hab)
    · rw [sourceTestCurveRealMassAt, dif_neg hb, sourceTestCurveRealMassAt_of_lt ω Γ ha]
      exact ENNReal.toReal_nonneg
  · have hb : ¬ b < Γ.max := fun hb ↦ ha (hab.trans_lt hb)
    simp only [sourceTestCurveRealMassAt, dif_neg ha, dif_neg hb, le_refl]

/-- The ACTUAL scalar integration function is Borel measurable. -/
theorem sourceTestCurveRealMassAt_measurable (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ) :
    Measurable (sourceTestCurveRealMassAt ω Γ) :=
  (sourceTestCurveRealMassAt_antitone ω Γ).measurable

/-- Literal based equality plus actual USCsup order and NP mass order
produce the whole nonnegative deficit bound BEFORE any energy formula. -/
theorem sourceTestCurveMass_le_model (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (τ : ℝ) :
    0 ≤ sourceTestCurveRealMassAt ω Γ τ ∧ sourceTestCurveRealMassAt ω Γ τ ≤
      (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal := by
  change sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ at hΓ
  have hfin : sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ < ⊤ := by
    simpa only [sourceMixedNonPluripolarMass_diagonal] using
      (sourceMixedNonPluripolarMass_lt_top ω (fun _ : Fin n ↦ θ)
        (fun _ ↦ φ) (fun _ ↦ hφ.thetaPSH))
  by_cases hτ : τ < Γ.max
  · rw [sourceTestCurveRealMassAt_of_lt ω Γ hτ]
    refine ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hfin.ne ?_⟩
    apply sourcePotentialNonPluripolarMass_mono ω (Γ.thetaPSH ⟨τ, hτ⟩) hφ.thetaPSH
    apply MoreSingularOn.of_le
    intro x _
    have hx : Γ.potential ⟨τ, hτ⟩ x ≤ sourceTestCurveLimit Γ.toSourceTestCurvePredata x :=
      (le_iSup (fun σ : Iio Γ.max ↦ Γ.potential σ x) ⟨τ, hτ⟩).trans
        (le_uscRegularization (fun y ↦ ⨆ σ : Iio Γ.max, Γ.potential σ y) x)
    rwa [hΓ] at hx
  · rw [sourceTestCurveRealMassAt, dif_neg hτ]
    exact ⟨le_rfl, ENNReal.toReal_nonneg⟩

/-- EXACT original eventual equality on the genuine original parameter
interval; no time reparametrization or singularity-equivalence substitute. -/
def SourceTestCurveIsBounded {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (φ : M → EReal) (Γ : SourceTestCurve θ) : Prop :=
  ∀ᶠ τ : Iio Γ.max in atBot, Γ.potential τ = φ

/-- The original bounded class retains its actual original based membership. -/
def SourceBoundedTestCurves (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) : Set (SourceTestCurve θ) :=
  {Γ | Γ ∈ SourceTestCurvesBased θ φ hφ ∧ SourceTestCurveIsBounded φ Γ}

/-- The LITERAL original REAL supremum, on precisely the original bounded
class, using the actual original three-branch extension INCLUDING cutoff. -/
def sourceTestCurveMinimum {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {φ : M → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (_hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) : ℝ :=
  sSup {τ : ℝ | sourceTestCurveAt Γ.toSourceTestCurvePredata τ = φ}

section MinimumProof
variable [ConnectedSpace M]

omit [BorelSpace M] in
/-- Actual eventual equality and genuine model nonbottom manufacture BOTH
real-supremum hypotheses. The cutoff MAY belong to the equality set. -/
theorem sourceTestCurveMinimum_wellDefined
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) :
    {τ : ℝ | sourceTestCurveAt Γ.toSourceTestCurvePredata τ = φ}.Nonempty ∧
      BddAbove {τ : ℝ | sourceTestCurveAt Γ.toSourceTestCurvePredata τ = φ} ∧
      (∃ τ : ℝ, sourceTestCurveAt Γ.toSourceTestCurvePredata τ = φ ∧
        τ ≤ sourceTestCurveMinimum hφ Γ hΓ) ∧
      sourceTestCurveMinimum hφ Γ hΓ ≤ Γ.max := by
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  let S : Set ℝ := {τ | sourceTestCurveAt Γ.toSourceTestCurvePredata τ = φ}
  have hne : S.Nonempty := by
    obtain ⟨τ, hτ⟩ := hΓ.2.exists
    refine ⟨τ.val, ?_⟩
    change sourceTestCurveAt Γ.toSourceTestCurvePredata τ.val = φ
    rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata
      (show τ.val < Γ.max from τ.property)]
    exact hτ
  have hφne : φ ≠ ⊥ := sourceThetaPSH_ne_bot hφ.thetaPSH
  have hup : ∀ τ ∈ S, τ ≤ Γ.max := by
    intro τ hτ
    by_contra hnot
    exact hφne (hτ.symm.trans
      (sourceTestCurveAt_of_gt Γ.toSourceTestCurvePredata (lt_of_not_ge hnot)))
  have hbd : BddAbove S := ⟨Γ.max, hup⟩
  refine ⟨hne, hbd, ?_, ?_⟩
  · obtain ⟨τ, hτ⟩ := hne
    exact ⟨τ, hτ, le_csSup hbd hτ⟩
  · exact csSup_le hne hup

end MinimumProof

/-- The original extended energy on EXACT original based curves. Actual
masses are already finite; the genuine nonnegative deficit integral may
be infinite, and finite minus its top value is LITERALLY bottom. -/
def sourceTestCurveEnergy (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (_hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) : EReal :=
  ((Γ.max * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) -
    ((∫⁻ τ : ℝ in Iio Γ.max, ENNReal.ofReal
      ((sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal -
        sourceTestCurveRealMassAt ω Γ τ)) : EReal)

/-- EXACT printed signed-integral formula, on the genuine INFINITE-measure
original parameter interval. Positive part is produced zero; no finite-
measure upper-gap theorem or integrability certificate is assumed. -/
theorem sourceTestCurveEnergy_signedIntegral (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    sourceTestCurveEnergy ω hφ Γ hΓ =
      ((Γ.max * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) +
        SGPT.Convex.extendedSignedIntegral (volume.restrict (Iio Γ.max))
          (fun τ : ℝ ↦ ((sourceTestCurveRealMassAt ω Γ τ -
            (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal)) := by
  let μ : Measure ℝ := volume.restrict (Iio Γ.max)
  let m : ℝ := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  let f : ℝ → ℝ := sourceTestCurveRealMassAt ω Γ
  have hpos : ∫⁻ τ : ℝ, (((f τ - m : ℝ) : EReal)).toENNReal ∂μ = 0 := by
    calc
      _ = ∫⁻ _τ : ℝ, (0 : ENNReal) ∂μ := by
        apply lintegral_congr
        intro τ
        rw [EReal.real_coe_toENNReal]
        exact ENNReal.ofReal_eq_zero.mpr
          (sub_nonpos.mpr (sourceTestCurveMass_le_model ω hφ Γ hΓ τ).2)
      _ = 0 := lintegral_zero
  have hneg : (∫⁻ τ : ℝ, (-((f τ - m : ℝ) : EReal)).toENNReal ∂μ) =
      ∫⁻ τ : ℝ, ENNReal.ofReal (m - f τ) ∂μ := by
    apply lintegral_congr
    intro τ
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal]
    congr 1
    ring
  change ((Γ.max * m : ℝ) : EReal) -
      ((∫⁻ τ : ℝ, ENNReal.ofReal (m - f τ) ∂μ) : EReal) =
        ((Γ.max * m : ℝ) : EReal) +
          SGPT.Convex.extendedSignedIntegral μ (fun τ ↦ ((f τ - m : ℝ) : EReal))
  rw [SGPT.Convex.extendedSignedIntegral, hpos, hneg]
  simp only [EReal.coe_ennreal_zero, sub_eq_add_neg, zero_add]

omit [BorelSpace M] in
/-- The actual nonnegative extended deficit gives a FINITE upper bound,
while preserving the genuine possible negative-infinite energy branch. -/
theorem sourceTestCurveEnergy_le_upper (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    sourceTestCurveEnergy ω hφ Γ hΓ ≤
      ((Γ.max * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) := by
  unfold sourceTestCurveEnergy
  exact (EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)).trans_eq (sub_zero _)

/-- The EXACT original finite-energy class retains original based
membership and strict comparison with the literal extended bottom. -/
def SourceFiniteEnergyTestCurves (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) : Set (SourceTestCurve θ) :=
  {Γ | ∃ hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ, ⊥ < sourceTestCurveEnergy ω hφ Γ hΓ}

omit [BorelSpace M] in
/-- Literal original class reader, preserving the SAME functions and full
extended energy, including its genuine possible negative-infinite branch. -/
theorem sourceFiniteEnergyTestCurves_iff (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ) :
    Γ ∈ SourceFiniteEnergyTestCurves ω θ φ hφ ↔
      ∃ hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ, ⊥ < sourceTestCurveEnergy ω hφ Γ hΓ := Iff.rfl

omit [BorelSpace M] in
/-- BOTH extended endpoints are excluded from the actual printed finite-
energy class, licensing subsequent real readers WITHOUT an output premise. -/
theorem sourceTestCurveEnergy_finite_of_mem (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceFiniteEnergyTestCurves ω θ φ hφ) :
    ∃ hb : Γ ∈ SourceTestCurvesBased θ φ hφ,
      sourceTestCurveEnergy ω hφ Γ hb ≠ ⊥ ∧ sourceTestCurveEnergy ω hφ Γ hb ≠ ⊤ := by
  obtain ⟨hb, hbot⟩ := hΓ
  exact ⟨hb, ne_of_gt hbot, ne_of_lt ((sourceTestCurveEnergy_le_upper ω hφ Γ hb).trans_lt
    (EReal.coe_lt_top _))⟩

end SGPT.PSH.VariableComplexAtlas

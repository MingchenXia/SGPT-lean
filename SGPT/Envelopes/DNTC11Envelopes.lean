import SGPT.Envelopes.DNTC11Main
import SGPT.Envelopes.DNTEnvelopes

/-!
# Monge–Ampère measures of envelopes: the Di Nezza–Trapani circle for `C^{1,1̄}` obstacles

Lane S53 (`claude-dnt-c11`).  Consequences of the contact formula for obstacles with bounded
complex Hessian (`diagonalPotentialMeasure_restrict_contact_eq`), on a compact connected complex
manifold `X` with a Kähler form `ω`; `θ_fⁿ` is `c11TopMeasure ω θ f`.  These extend lane S48's
smooth-obstacle statements (`SGPT.Envelopes.DNT`) to `C^{1,1̄} ∩ QPSH` obstacles.

* `sourcePotentialNonPluripolarMeasure_restrict_contact_eq` (book `thm:DNTcontact`, diagonal case,
  source-facing form).
* `diagonalPotentialMeasure_rooftopEnvelope_eq`, `sourceObstacleEnvelope_measure_eq`
  (book `cor:DNTenvelope1`): `θⁿ_{P_θ(f)} = 𝟙_{P_θ(f) = f} θ_fⁿ`.
* `sourceGeneralizedEnvelope_measure_eq` (book `prop:DNTenvelope2`, first assertion):
  `θⁿ_{P_θ[φ](f)} = 𝟙_{P_θ[φ](f) = f} θ_fⁿ`.
* `sourceObstacleEnvelope_contact_measure_eq`, `sourceGeneralizedEnvelope_contact_measure_eq`
  (book `prop:DNTenvelope3`).
* `roofEnvelope_measure_eq` (book `lma:DNTroof`, measure assertions).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.DNTC11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg
open SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.DNT

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! ### Envelopes of `C^{1,1̄}` obstacles (native) -/

/-- The non-pluripolar measure of the envelope `P_θ(f)` of a continuous obstacle is carried by the
contact set `{P_θ(f) = f}`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_carried [ConnectedSpace M]
    (w : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hfc : Continuous f)
    (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal))) :
    diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun x => (f x : EReal)) hP =
      (diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun x => (f x : EReal)) hP).restrict
        {x | rooftopEnvelope θ.val (fun y => (f y : EReal)) x = (f x : EReal)} := by
  set P := rooftopEnvelope θ.val fun x => (f x : EReal) with hPdef
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have hnb : P ≠ fun _ => ⊥ := by
    intro h
    obtain ⟨y, -, hy⟩ := hP.2 x₀ univ isOpen_univ (mem_univ x₀)
    exact hy (congrFun h y)
  have hnt : P ≠ fun _ => ⊤ := by
    intro h
    exact hP.1.quasiPlurisubharmonic.ne_top x₀ (congrFun h x₀)
  have hqc : ActualExtendedObstacleQuasiContinuity.QuasiContinuousERealFor
      (ThetaCapacity.thetaCapacity w.form (fun _ => 0)) fun x => (f x : EReal) := by
    intro η hη
    refine ⟨∅, isOpen_empty, ?_, ?_⟩
    · rw [ThetaCapacity.thetaCapacity_empty]
      exact hη
    · exact (continuous_coe_real_ereal.comp hfc).continuousOn
  obtain ⟨hP', -, hneq⟩ :=
    ActualQuasiContinuousEnvelopeContact.exists_genuine_envelope_and_contact w θ hqc hnb hnt
  refine (Measure.restrict_eq_self_of_ae_mem ?_).symm
  rw [ae_iff]
  exact hneq

/-- **`cor:DNTenvelope1` for obstacles with bounded complex Hessian**:
`⟨(θ + ddᶜP_θ(f))ⁿ⟩ = 𝟙_{P_θ(f) = f} θ_fⁿ`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_eq [ConnectedSpace M] (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal))) :
    diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun x => (f x : EReal)) hP =
      (c11TopMeasure w θ f).restrict
        {x | rooftopEnvelope θ.val (fun y => (f y : EReal)) x = (f x : EReal)} := by
  rw [diagonalPotentialMeasure_rooftopEnvelope_carried w θ hf.1 hP]
  exact diagonalPotentialMeasure_restrict_contact_eq w θ hP hf
    (rooftopEnvelope_le_of_isThetaPshPotential hf.1 hP)

/-! ### Source-facing statements -/

/-- **The Di Nezza–Trapani contact formula**, source-facing form (book `thm:DNTcontact` for
`θᵢ = θ`, `φᵢ = u`, `fᵢ = f` with bounded complex Hessian). -/
theorem sourcePotentialNonPluripolarMeasure_restrict_contact_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    (hle : ∀ x, u x ≤ (f x : EReal)) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (c11TopMeasure w (atlasClosedFormToNative θ) f).restrict {x | u x = (f x : EReal)} :=
  diagonalPotentialMeasure_restrict_contact_eq w (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hf hle

/-- **`cor:DNTenvelope1` for obstacles with bounded complex Hessian**, source-facing form: if
`PSH(X, θ) ≠ ∅`, the source envelope `P = P_θ(f)` is `θ`-psh and `θⁿ_P = 𝟙_{P = f} θ_fⁿ`. -/
theorem sourceObstacleEnvelope_measure_eq [ConnectedSpace M] (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hne : ∃ φ : M → EReal, (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) :
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP =
        (c11TopMeasure w (atlasClosedFormToNative θ) f).restrict
          {x | sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x = (f x : EReal)} := by
  obtain ⟨φ, hφ⟩ := hne
  have heq := sourceObstacleEnvelope_eq_native θ (fun x => (f x : EReal))
  have hP' := isThetaPshPotential_rooftopEnvelope_of_continuous w (atlasClosedFormToNative θ) hf.1
    ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
  have hP : (ofFixedModel n M).IsThetaPSH θ
      (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) := by
    rw [isThetaPSH_iff_nativeThetaPotential, heq]
    exact hP'
  refine ⟨hP, ?_⟩
  calc sourcePotentialNonPluripolarMeasure θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP
      = diagonalPotentialMeasure (atlasClosedFormToNative θ)
          (rooftopEnvelope (atlasClosedFormToNative θ).val fun x => (f x : EReal)) hP' :=
        MaxMassDecomposition.diagonalPotentialMeasure_congr _ hP' heq
    _ = _ := diagonalPotentialMeasure_rooftopEnvelope_eq w _ hf hP'
    _ = _ := by rw [heq]

variable [ConnectedSpace M]

/-- **`prop:DNTenvelope2`, first assertion, for obstacles with bounded complex Hessian**: for
`φ ∈ PSH(X, θ)` and `f ≥ φ` with bounded complex Hessian, the generalized envelope
`η = P_θ[φ](f)` (`def:Pthetavarphif`) is `θ`-psh and `θⁿ_η = 𝟙_{η = f} θ_fⁿ`. -/
theorem sourceGeneralizedEnvelope_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)) hη =
        (c11TopMeasure w (atlasClosedFormToNative θ) f).restrict
          {x | sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x = (f x : EReal)} := by
  have hfc : Continuous f := hf.1
  obtain ⟨hη, -, hηP, hηf⟩ := sourceGeneralizedEnvelope_genuine w θ hφ hfc hle
  obtain ⟨hP, hφP, hPf⟩ := sourceObstacleEnvelope_genuine_of_le w θ hφ hfc hle
  obtain ⟨hP', hPmeas⟩ := sourceObstacleEnvelope_measure_eq w θ ⟨φ, hφ⟩ hf
  set Pf := sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal) with hPfdef
  set η := sourceRelativeEnvelope θ φ fun x => (f x : EReal) with hηdef
  have hηeq : η = sourceRelativeEnvelope θ φ Pf :=
    sourceGeneralizedEnvelope_eq_obstacleEnvelope φ hfc hP
  have hne : sourceRelativeEnvelope θ φ Pf ≠ ⊥ := by
    rw [← hηeq]
    intro h
    obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
    obtain ⟨y, -, hy⟩ := ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).2 x₀ univ isOpen_univ
      (mem_univ x₀)
    exact hy (congrFun h y)
  have hC : MeasurableSet {x | Pf x = (f x : EReal)} :=
    (isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ Pf).mp hP).1 hfc
      hPf).measurableSet
  refine ⟨hη, le_antisymm ?_ ?_⟩
  · refine Measure.le_iff.mpr fun A hA => ?_
    have h1 := sourceRelativeEnvelope_measure_le_apply w hφ hP hne A
    have hset : {x | sourceRelativeEnvelope θ φ Pf x = Pf x} = {x | η x = Pf x} := by rw [hηeq]
    rw [hset] at h1
    rw [sourcePotentialNonPluripolarMeasure_congr hη
      (sourceRelativeEnvelope_genuine_of_ne_bot hP hne) hηeq]
    calc sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ Pf)
          (sourceRelativeEnvelope_genuine_of_ne_bot hP hne) A
        ≤ sourcePotentialNonPluripolarMeasure θ Pf hP (A ∩ {x | η x = Pf x}) := h1
      _ = (c11TopMeasure w (atlasClosedFormToNative θ) f)
            ((A ∩ {x | η x = Pf x}) ∩ {x | Pf x = (f x : EReal)}) := by
          rw [hPmeas, Measure.restrict_apply' hC]
      _ ≤ (c11TopMeasure w (atlasClosedFormToNative θ) f)
            (A ∩ {x | η x = (f x : EReal)}) := by
          refine measure_mono fun x hx => ⟨hx.1.1, ?_⟩
          exact (hx.1.2 : η x = Pf x).trans hx.2
      _ = _ := (Measure.restrict_apply hA).symm
  · rw [← sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hη hf hηf]
    exact Measure.restrict_le_self

/-- **`prop:DNTenvelope3`, first equality, for obstacles with bounded complex Hessian**: for
`φ ∈ PSH(X, θ)` and `f ≥ φ` with bounded complex Hessian, with `P = P_θ(f)`,
`𝟙_{φ = P} θⁿ_P = 𝟙_{φ = P} θⁿ_φ`. -/
theorem sourceObstacleEnvelope_contact_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP).restrict
          {x | φ x = sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x} := by
  have hfc : Continuous f := hf.1
  obtain ⟨hP, hφP, hPf⟩ := sourceObstacleEnvelope_genuine_of_le w θ hφ hfc hle
  obtain ⟨hP', hPmeas⟩ := sourceObstacleEnvelope_measure_eq w θ ⟨φ, hφ⟩ hf
  set Pf := sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal) with hPfdef
  have hC : MeasurableSet {x | Pf x = (f x : EReal)} :=
    (isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ Pf).mp hP).1 hfc
      hPf).measurableSet
  have hD : MeasurableSet {x | φ x = (f x : EReal)} :=
    (isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1 hfc
      hle).measurableSet
  have hdnt := sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hφ hf hle
  refine ⟨hP, le_antisymm ?_ (sourcePotentialNonPluripolarMeasure_contact w hφ hP hφP)⟩
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  calc sourcePotentialNonPluripolarMeasure θ Pf hP (A ∩ {x | φ x = Pf x})
      = (c11TopMeasure w (atlasClosedFormToNative θ) f)
          ((A ∩ {x | φ x = Pf x}) ∩ {x | Pf x = (f x : EReal)}) := by
        rw [hPmeas, Measure.restrict_apply' hC]
    _ ≤ (c11TopMeasure w (atlasClosedFormToNative θ) f)
          ((A ∩ {x | φ x = Pf x}) ∩ {x | φ x = (f x : EReal)}) :=
        measure_mono fun x hx => ⟨hx.1, (hx.1.2 : φ x = Pf x).trans hx.2⟩
    _ = sourcePotentialNonPluripolarMeasure θ φ hφ
          ((A ∩ {x | φ x = Pf x}) ∩ {x | φ x = (f x : EReal)}) := by
        rw [← Measure.restrict_apply' hD, ← hdnt, Measure.restrict_apply' hD]
    _ ≤ sourcePotentialNonPluripolarMeasure θ φ hφ (A ∩ {x | φ x = Pf x}) :=
        measure_mono inter_subset_left

/-- **`prop:DNTenvelope3`, second equality, for obstacles with bounded complex Hessian**: for
`φ ∈ PSH(X, θ)` and `f ≥ φ` with bounded complex Hessian, with `η = P_θ[φ](f)`,
`𝟙_{φ = η} θⁿ_η = 𝟙_{φ = η} θⁿ_φ`. -/
theorem sourceGeneralizedEnvelope_contact_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal))
          hη).restrict {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} := by
  have hfc : Continuous f := hf.1
  obtain ⟨-, hφη, -, hηf⟩ := sourceGeneralizedEnvelope_genuine w θ hφ hfc hle
  obtain ⟨hη, hηmeas⟩ := sourceGeneralizedEnvelope_measure_eq w θ hφ hf hle
  set η := sourceRelativeEnvelope θ φ fun x => (f x : EReal) with hηdef
  have hC : MeasurableSet {x | η x = (f x : EReal)} :=
    (isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).1 hfc
      hηf).measurableSet
  have hD : MeasurableSet {x | φ x = (f x : EReal)} :=
    (isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1 hfc
      hle).measurableSet
  have hdnt := sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hφ hf hle
  refine ⟨hη, le_antisymm ?_ (sourcePotentialNonPluripolarMeasure_contact w hφ hη hφη)⟩
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  calc sourcePotentialNonPluripolarMeasure θ η hη (A ∩ {x | φ x = η x})
      = (c11TopMeasure w (atlasClosedFormToNative θ) f)
          ((A ∩ {x | φ x = η x}) ∩ {x | η x = (f x : EReal)}) := by
        rw [hηmeas, Measure.restrict_apply' hC]
    _ ≤ (c11TopMeasure w (atlasClosedFormToNative θ) f)
          ((A ∩ {x | φ x = η x}) ∩ {x | φ x = (f x : EReal)}) :=
        measure_mono fun x hx => ⟨hx.1, (hx.1.2 : φ x = η x).trans hx.2⟩
    _ = sourcePotentialNonPluripolarMeasure θ φ hφ
          ((A ∩ {x | φ x = η x}) ∩ {x | φ x = (f x : EReal)}) := by
        rw [← Measure.restrict_apply' hD, ← hdnt, Measure.restrict_apply' hD]
    _ ≤ sourcePotentialNonPluripolarMeasure θ φ hφ (A ∩ {x | φ x = η x}) :=
        measure_mono inter_subset_left

/-! ### `lma:DNTroof` for obstacles with bounded complex Hessian -/

/-- **`lma:DNTroof`, measure assertions, for obstacles with bounded complex Hessian.**  Let `ω` be
a Kähler form, `f₁, f₂` continuous with bounded complex Hessian, `P = P_ω(min{f₁, f₂})`,
`Cᵢ = {P = fᵢ}`, `C = C₁ ∩ C₂ = {P = f₁ = f₂}`.  Then `P ∈ PSH(X, ω)`, and

* `𝟙_C ω_{f₁}ⁿ = 𝟙_C ω_{f₂}ⁿ`;
* `ωⁿ_P + 𝟙_C ω_{fⱼ}ⁿ = 𝟙_{C₁} ω_{f₁}ⁿ + 𝟙_{C₂} ω_{f₂}ⁿ` for `j = 1, 2` (the book's
  `eq:DNTroof_Pomega` with the subtracted finite measure moved to the left);
* `ωⁿ_P ≥ 𝟙_{Cⱼ} ω_{fⱼ}ⁿ`. -/
theorem roofEnvelope_measure_eq (w : KahlerBackground n M) {f₁ f₂ : M → ℝ}
    (hf₁ : HasBoundedComplexHessian (n := n) f₁) (hf₂ : HasBoundedComplexHessian (n := n) f₂) :
    ∃ hP : IsThetaPshPotential w.form.val (roofEnvelope w f₁ f₂),
      (c11TopMeasure w w.form f₁).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧ roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (c11TopMeasure w w.form f₂).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧ roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ∧
      (diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP +
          (c11TopMeasure w w.form f₁).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (c11TopMeasure w w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (c11TopMeasure w w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP +
          (c11TopMeasure w w.form f₂).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (c11TopMeasure w w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (c11TopMeasure w w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (c11TopMeasure w w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} ≤
        diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP ∧
      (c11TopMeasure w w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ≤
        diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP := by
  have hc₁ : Continuous f₁ := hf₁.1
  have hc₂ : Continuous f₂ := hf₂.1
  obtain ⟨hP, hle₁, hle₂⟩ := roofEnvelope_genuine w hc₁ hc₂
  set P := roofEnvelope w f₁ f₂ with hPdef
  set μ := diagonalPotentialMeasure w.form P hP with hμ
  set ν₁ := c11TopMeasure w w.form f₁ with hν₁
  set ν₂ := c11TopMeasure w w.form f₂ with hν₂
  set C₁ : Set M := {x | P x = (f₁ x : EReal)} with hC₁
  set C₂ : Set M := {x | P x = (f₂ x : EReal)} with hC₂
  have hC₂m : MeasurableSet C₂ := (isClosed_contact_of_continuous hP.1 hc₂ hle₂).measurableSet
  have hC : {x | P x = (f₁ x : EReal) ∧ P x = (f₂ x : EReal)} = C₁ ∩ C₂ := rfl
  have h₁ : μ.restrict C₁ = ν₁.restrict C₁ :=
    diagonalPotentialMeasure_restrict_contact_eq w w.form hP hf₁ hle₁
  have h₂ : μ.restrict C₂ = ν₂.restrict C₂ :=
    diagonalPotentialMeasure_restrict_contact_eq w w.form hP hf₂ hle₂
  have hcar : μ.restrict (C₁ ∪ C₂) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      exact roofEnvelope_measure_carried w hc₁ hc₂ hP)
  have hCν₁ : ν₁.restrict (C₁ ∩ C₂) = μ.restrict (C₁ ∩ C₂) := by
    rw [← Measure.restrict_restrict_of_subset inter_subset_left, ← h₁,
      Measure.restrict_restrict_of_subset inter_subset_left]
  have hCν₂ : ν₂.restrict (C₁ ∩ C₂) = μ.restrict (C₁ ∩ C₂) := by
    rw [← Measure.restrict_restrict_of_subset inter_subset_right, ← h₂,
      Measure.restrict_restrict_of_subset inter_subset_right]
  refine ⟨hP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC, hCν₁, hCν₂]
  · rw [hC, hCν₁, ← h₁, ← h₂, ← Measure.restrict_union_add_inter C₁ hC₂m, hcar]
  · rw [hC, hCν₂, ← h₁, ← h₂, ← Measure.restrict_union_add_inter C₁ hC₂m, hcar]
  · rw [← h₁]
    exact Measure.restrict_le_self
  · rw [← h₂]
    exact Measure.restrict_le_self

end SGPT.Envelopes.DNTC11

import SGPT.Envelopes.LapClass3Contact
import SGPT.Envelopes.DNTC11Envelopes

/-!
# Monge–Ampère measures of envelopes of obstacles in `C^{1,1̄}(X)` (all dimensions)

Lane CZ-LP (`claude-cz-lp`, node `czlp:envelopes`).  Consequences of the contact formula
`LapClass3.diagonalPotentialMeasure_restrict_contact_eq` for obstacles in the book's class
`C^{1,1̄}(X)` (continuous, bounded `ω`-Laplacian), with `θ_fⁿ = lapTopMeasure θ f`, on a compact
connected complex manifold `X` of dimension `n = m + 1` with a Kähler form `ω`.  The proofs are the
book's, as in the bounded-Hessian versions (`DNTC11Envelopes`).

* `diagonalPotentialMeasure_rooftopEnvelope_eq`, `sourceObstacleEnvelope_measure_eq`
  (`cor:DNTenvelope1`): `θⁿ_{P_θ(f)} = 𝟙_{P_θ(f) = f} θ_fⁿ`.
* `sourceGeneralizedEnvelope_measure_eq` (`prop:DNTenvelope2`, first assertion):
  `θⁿ_{P_θ[φ](f)} = 𝟙_{P_θ[φ](f) = f} θ_fⁿ`.
* `sourceObstacleEnvelope_contact_measure_eq`, `sourceGeneralizedEnvelope_contact_measure_eq`
  (`prop:DNTenvelope3`).
* `roofEnvelope_measure_eq` (`lma:DNTroof`, measure assertions):
  `𝟙_C ω_{f₁}ⁿ = 𝟙_C ω_{f₂}ⁿ`, `ωⁿ_P + 𝟙_C ω_{fⱼ}ⁿ = 𝟙_{C₁} ω_{f₁}ⁿ + 𝟙_{C₂} ω_{f₂}ⁿ` and
  `ωⁿ_P ≥ 𝟙_{Cⱼ} ω_{fⱼ}ⁿ`, `P = P_ω(min{f₁, f₂})`, `Cᵢ = {P = fᵢ}`, `C = C₁ ∩ C₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg
open SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.DNT SGPT.Envelopes.LapClass

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [ConnectedSpace Y]

/-- **`cor:DNTenvelope1` for `f ∈ C^{1,1̄}(X)`** (native form):
`⟨(θ + ddᶜP_θ(f))ⁿ⟩ = 𝟙_{P_θ(f) = f} θ_fⁿ`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_eq (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f)
    (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal))) :
    diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun x => (f x : EReal)) hP =
      (lapTopMeasure θ f).restrict
        {x | rooftopEnvelope θ.val (fun y => (f y : EReal)) x = (f x : EReal)} := by
  rw [DNTC11.diagonalPotentialMeasure_rooftopEnvelope_carried w θ hf.1 hP]
  exact diagonalPotentialMeasure_restrict_contact_eq w θ hP hf
    (rooftopEnvelope_le_of_isThetaPshPotential hf.1 hP)

/-- **`cor:DNTenvelope1` for `f ∈ C^{1,1̄}(X)`**, source-facing form: if `PSH(X, θ) ≠ ∅`, the source
envelope `P = P_θ(f)` is `θ`-psh and `θⁿ_P = 𝟙_{P = f} θ_fⁿ`. -/
theorem sourceObstacleEnvelope_measure_eq (w : KahlerBackground (m + 1) Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y))
    (hne : ∃ φ : Y → EReal, (ofFixedModel (m + 1) Y).IsThetaPSH θ φ) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    ∃ hP : (ofFixedModel (m + 1) Y).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP =
        (lapTopMeasure (atlasClosedFormToNative θ) f).restrict
          {x | sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x = (f x : EReal)} := by
  obtain ⟨φ, hφ⟩ := hne
  have heq := sourceObstacleEnvelope_eq_native θ (fun x => (f x : EReal))
  have hP' := isThetaPshPotential_rooftopEnvelope_of_continuous w (atlasClosedFormToNative θ) hf.1
    ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
  have hP : (ofFixedModel (m + 1) Y).IsThetaPSH θ
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

/-- **`prop:DNTenvelope2`, first assertion, for `f ∈ C^{1,1̄}(X)`**: for `φ ∈ PSH(X, θ)` and
`f ≥ φ`, the generalized envelope `η = P_θ[φ](f)` (`def:Pthetavarphif`) is `θ`-psh and
`θⁿ_η = 𝟙_{η = f} θ_fⁿ`. -/
theorem sourceGeneralizedEnvelope_measure_eq (w : KahlerBackground (m + 1) Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y))
    {φ : Y → EReal} (hφ : (ofFixedModel (m + 1) Y).IsThetaPSH θ φ) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel (m + 1) Y).IsThetaPSH θ
        (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)) hη =
        (lapTopMeasure (atlasClosedFormToNative θ) f).restrict
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
    obtain ⟨x₀⟩ := (inferInstance : Nonempty Y)
    obtain ⟨y, -, hy⟩ := ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).2 x₀ univ isOpen_univ
      (mem_univ x₀)
    exact hy (congrFun h y)
  have hC : MeasurableSet {x | Pf x = (f x : EReal)} :=
    (DNTC11.isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ Pf).mp hP).1 hfc
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
      _ = (lapTopMeasure (atlasClosedFormToNative θ) f)
            ((A ∩ {x | η x = Pf x}) ∩ {x | Pf x = (f x : EReal)}) := by
          rw [hPmeas, Measure.restrict_apply' hC]
      _ ≤ (lapTopMeasure (atlasClosedFormToNative θ) f)
            (A ∩ {x | η x = (f x : EReal)}) := by
          refine measure_mono fun x hx => ⟨hx.1.1, ?_⟩
          exact (hx.1.2 : η x = Pf x).trans hx.2
      _ = _ := (Measure.restrict_apply hA).symm
  · rw [← sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hη hf hηf]
    exact Measure.restrict_le_self

/-- **`prop:DNTenvelope3`, first equality, for `f ∈ C^{1,1̄}(X)`**: with `P = P_θ(f)`,
`𝟙_{φ = P} θⁿ_P = 𝟙_{φ = P} θⁿ_φ`. -/
theorem sourceObstacleEnvelope_contact_measure_eq (w : KahlerBackground (m + 1) Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y))
    {φ : Y → EReal} (hφ : (ofFixedModel (m + 1) Y).IsThetaPSH θ φ) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hP : (ofFixedModel (m + 1) Y).IsThetaPSH θ
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
    (DNTC11.isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ Pf).mp hP).1 hfc
      hPf).measurableSet
  have hD : MeasurableSet {x | φ x = (f x : EReal)} :=
    (DNTC11.isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1 hfc
      hle).measurableSet
  have hdnt := sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hφ hf hle
  refine ⟨hP, le_antisymm ?_ (sourcePotentialNonPluripolarMeasure_contact w hφ hP hφP)⟩
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  calc sourcePotentialNonPluripolarMeasure θ Pf hP (A ∩ {x | φ x = Pf x})
      = (lapTopMeasure (atlasClosedFormToNative θ) f)
          ((A ∩ {x | φ x = Pf x}) ∩ {x | Pf x = (f x : EReal)}) := by
        rw [hPmeas, Measure.restrict_apply' hC]
    _ ≤ (lapTopMeasure (atlasClosedFormToNative θ) f)
          ((A ∩ {x | φ x = Pf x}) ∩ {x | φ x = (f x : EReal)}) :=
        measure_mono fun x hx => ⟨hx.1, (hx.1.2 : φ x = Pf x).trans hx.2⟩
    _ = sourcePotentialNonPluripolarMeasure θ φ hφ
          ((A ∩ {x | φ x = Pf x}) ∩ {x | φ x = (f x : EReal)}) := by
        rw [← Measure.restrict_apply' hD, ← hdnt, Measure.restrict_apply' hD]
    _ ≤ sourcePotentialNonPluripolarMeasure θ φ hφ (A ∩ {x | φ x = Pf x}) :=
        measure_mono inter_subset_left

/-- **`prop:DNTenvelope3`, second equality, for `f ∈ C^{1,1̄}(X)`**: with `η = P_θ[φ](f)`,
`𝟙_{φ = η} θⁿ_η = 𝟙_{φ = η} θⁿ_φ`. -/
theorem sourceGeneralizedEnvelope_contact_measure_eq (w : KahlerBackground (m + 1) Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y))
    {φ : Y → EReal} (hφ : (ofFixedModel (m + 1) Y).IsThetaPSH θ φ) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel (m + 1) Y).IsThetaPSH θ
        (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal))
          hη).restrict {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} := by
  have hfc : Continuous f := hf.1
  obtain ⟨-, hφη, -, hηf⟩ := sourceGeneralizedEnvelope_genuine w θ hφ hfc hle
  obtain ⟨hη, hηmeas⟩ := sourceGeneralizedEnvelope_measure_eq w θ hφ hf hle
  set η := sourceRelativeEnvelope θ φ fun x => (f x : EReal) with hηdef
  have hC : MeasurableSet {x | η x = (f x : EReal)} :=
    (DNTC11.isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).1 hfc
      hηf).measurableSet
  have hD : MeasurableSet {x | φ x = (f x : EReal)} :=
    (DNTC11.isClosed_contact_of_continuous ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1 hfc
      hle).measurableSet
  have hdnt := sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hφ hf hle
  refine ⟨hη, le_antisymm ?_ (sourcePotentialNonPluripolarMeasure_contact w hφ hη hφη)⟩
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  calc sourcePotentialNonPluripolarMeasure θ η hη (A ∩ {x | φ x = η x})
      = (lapTopMeasure (atlasClosedFormToNative θ) f)
          ((A ∩ {x | φ x = η x}) ∩ {x | η x = (f x : EReal)}) := by
        rw [hηmeas, Measure.restrict_apply' hC]
    _ ≤ (lapTopMeasure (atlasClosedFormToNative θ) f)
          ((A ∩ {x | φ x = η x}) ∩ {x | φ x = (f x : EReal)}) :=
        measure_mono fun x hx => ⟨hx.1, (hx.1.2 : φ x = η x).trans hx.2⟩
    _ = sourcePotentialNonPluripolarMeasure θ φ hφ
          ((A ∩ {x | φ x = η x}) ∩ {x | φ x = (f x : EReal)}) := by
        rw [← Measure.restrict_apply' hD, ← hdnt, Measure.restrict_apply' hD]
    _ ≤ sourcePotentialNonPluripolarMeasure θ φ hφ (A ∩ {x | φ x = η x}) :=
        measure_mono inter_subset_left

/-- **`lma:DNTroof`, measure assertions, for `f₁, f₂ ∈ C^{1,1̄}(X)`** (every dimension).  Let `ω` be
the Kähler form, `P = P_ω(min{f₁, f₂})`, `Cᵢ = {P = fᵢ}`, `C = C₁ ∩ C₂`, `ω_{fᵢ}ⁿ =
lapTopMeasure ω fᵢ`.  Then `P ∈ PSH(X, ω)`, `𝟙_C ω_{f₁}ⁿ = 𝟙_C ω_{f₂}ⁿ`,
`ωⁿ_P + 𝟙_C ω_{fⱼ}ⁿ = 𝟙_{C₁} ω_{f₁}ⁿ + 𝟙_{C₂} ω_{f₂}ⁿ` for `j = 1, 2` (`eq:DNTroof_Pomega` with the
subtracted finite measure moved to the left), and `ωⁿ_P ≥ 𝟙_{Cⱼ} ω_{fⱼ}ⁿ`. -/
theorem roofEnvelope_measure_eq (w : KahlerBackground (m + 1) Y) {f₁ f₂ : Y → ℝ}
    (hf₁ : HasBoundedMetricLaplacian w f₁) (hf₂ : HasBoundedMetricLaplacian w f₂) :
    ∃ hP : IsThetaPshPotential w.form.val (roofEnvelope w f₁ f₂),
      (lapTopMeasure w.form f₁).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧ roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (lapTopMeasure w.form f₂).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧ roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ∧
      (diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP +
          (lapTopMeasure w.form f₁).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (lapTopMeasure w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (lapTopMeasure w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP +
          (lapTopMeasure w.form f₂).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (lapTopMeasure w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (lapTopMeasure w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (lapTopMeasure w.form f₁).restrict {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} ≤
        diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP ∧
      (lapTopMeasure w.form f₂).restrict {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ≤
        diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP := by
  have hc₁ : Continuous f₁ := hf₁.1
  have hc₂ : Continuous f₂ := hf₂.1
  obtain ⟨hP, hle₁, hle₂⟩ := roofEnvelope_genuine w hc₁ hc₂
  set P := roofEnvelope w f₁ f₂ with hPdef
  set μ := diagonalPotentialMeasure w.form P hP with hμ
  set ν₁ := lapTopMeasure w.form f₁ with hν₁
  set ν₂ := lapTopMeasure w.form f₂ with hν₂
  set C₁ : Set Y := {x | P x = (f₁ x : EReal)} with hC₁
  set C₂ : Set Y := {x | P x = (f₂ x : EReal)} with hC₂
  have hC₂m : MeasurableSet C₂ :=
    (DNTC11.isClosed_contact_of_continuous hP.1 hc₂ hle₂).measurableSet
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

end SGPT.Envelopes.LapClass3

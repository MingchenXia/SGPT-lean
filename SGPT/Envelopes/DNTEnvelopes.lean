import SGPT.Okounkov.TranscendentalWNRegDNTEnvelope
import SGPT.Envelopes.SourceRooftopContactMeasures
import SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousEnvelopeContact

/-!
# Monge–Ampère measures of envelopes: the Di Nezza–Trapani circle for smooth obstacles

Consequences of the Di Nezza–Trapani contact formula for smooth obstacles
(`TranscendentalWNReg.sourcePotentialNonPluripolarMeasure_restrict_contact_eq`, lane WN-REG2), on a
compact connected complex manifold `X` with a Kähler form `ω`, `θ` a (source) closed real
`(1,1)`-form, `φ ∈ PSH(X, θ)` and a smooth `f ≥ φ`.  `θ_f = θ + ddᶜf`, and `θ_fⁿ` is the measure
`positiveTopMeasure ω θ_f` (density `max(θ_fⁿ/ωⁿ, 0)`), which on the contact sets below is the
genuine signed measure of the smooth form (`TranscendentalWN.topRatio_nonneg_of_contact`).

* `sourceGeneralizedEnvelope_eq_obstacleEnvelope`: `P_θ[φ](f) = P_θ[φ](P_θ(f))` (the first line of
  the book's proof of `prop:DNTenvelope2`), for continuous `f`.
* `sourceGeneralizedEnvelope_measure_eq` (source `prop:DNTenvelope2`, first assertion, smooth `f`):
  `θⁿ_{P_θ[φ](f)} = 𝟙_{P_θ[φ](f) = f} θ_fⁿ`.
* `sourceObstacleEnvelope_contact_measure_eq`, `sourceGeneralizedEnvelope_contact_measure_eq`
  (source `prop:DNTenvelope3`, smooth `f`): `𝟙_{φ = P_θ(f)} θⁿ_{P_θ(f)} = 𝟙_{φ = P_θ(f)} θⁿ_φ` and
  `𝟙_{φ = P_θ[φ](f)} θⁿ_{P_θ[φ](f)} = 𝟙_{φ = P_θ[φ](f)} θⁿ_φ`.
* `roofEnvelope_measure_eq` (source `lma:DNTroof`, measure assertions, smooth `f₁, f₂`): for
  `P = P_ω(min{f₁, f₂})`, `𝟙_{P = f₁ = f₂} ω_{f₁}ⁿ = 𝟙_{P = f₁ = f₂} ω_{f₂}ⁿ` and
  `ωⁿ_P + 𝟙_{P = f₁ = f₂} ω_{fⱼ}ⁿ = 𝟙_{P = f₁} ω_{f₁}ⁿ + 𝟙_{P = f₂} ω_{f₂}ⁿ` (the book's
  `eq:DNTroof_Pomega`, with the subtracted term moved to the left), and `ωⁿ_P ≥ 𝟙_{P = fⱼ} ω_{fⱼ}ⁿ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.DNT

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Elementary envelope comparisons -/

section Envelopes

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A competitor lies below the generalized envelope `P_θ[u](f)`. -/
theorem le_sourceRelativeEnvelope {u f a : M → EReal} (ha : (ofFixedModel n M).IsThetaPSH θ a)
    (haf : SourceQuasiEverywhere (n := n) (fun x => a x ≤ f x)) (hau : SGPT.PSH.SingularityLE a u)
    (x : M) : a x ≤ sourceRelativeEnvelope θ u f x :=
  (le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ u f => b.1 x) ⟨a, ha, haf, hau⟩).trans
    (le_uscRegularization (fun y => ⨆ b : sourceRelativeEnvelopeCompetitors θ u f, b.1 y) x)

/-- `φ ≤ P_θ[φ](f)` when `φ ∈ PSH(X, θ)` and `φ ≤ f`. -/
theorem self_le_sourceRelativeEnvelope {φ f : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hle : φ ≤ f) : φ ≤ sourceRelativeEnvelope θ φ f := fun x =>
  le_sourceRelativeEnvelope hφ (sourceQuasiEverywhere_of_forall hle)
    (SGPT.PSH.singularityLE_refl φ) x

/-- A generalized envelope with a genuine `θ`-psh obstacle `v` lies below `v`. -/
theorem sourceRelativeEnvelope_le_of_isThetaPSH {u v : M → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH θ v) : sourceRelativeEnvelope θ u v ≤ v :=
  uscRegularization_le hv.upperSemicontinuous fun x =>
    iSup_le fun a => ((sourceRelativeEnvelopeCompetitors_iff hv).mp a.2).2.1 x

/-- The obstacle envelope `P_θ(f)` of a continuous `f` lies below `f` once it is `θ`-psh. -/
theorem sourceObstacleEnvelope_le [CompactSpace M] [ConnectedSpace M] {f : M → ℝ} (hf : Continuous f)
    (hP : (ofFixedModel n M).IsThetaPSH θ
      (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal))) (x : M) :
    sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x ≤ (f x : EReal) := by
  have heq := sourceObstacleEnvelope_eq_native θ (fun x => (f x : EReal))
  have hPn := (isThetaPSH_iff_nativeThetaPotential θ _).mp hP
  rw [heq] at hPn ⊢
  exact rooftopEnvelope_le_of_isThetaPshPotential hf hPn x

/-- **`P_θ[φ](f) = P_θ[φ](P_θ(f))`** for a continuous obstacle `f` whose envelope `P_θ(f)` is
`θ`-psh (the first line of the book's proof of `prop:DNTenvelope2`). -/
theorem sourceGeneralizedEnvelope_eq_obstacleEnvelope [CompactSpace M] [ConnectedSpace M] (u : M → EReal)
    {f : M → ℝ} (hf : Continuous f)
    (hP : (ofFixedModel n M).IsThetaPSH θ
      (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal))) :
    sourceRelativeEnvelope θ u (fun x => (f x : EReal)) =
      sourceRelativeEnvelope θ u (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro a
    refine le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ u
      (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) => b.1 x)
      ⟨a.1, a.2.1, sourceQuasiEverywhere_of_forall fun y => ?_, a.2.2.2⟩
    exact le_sourceRelativeEnvelope a.2.1 a.2.2.1 (sourceObstacle_topReference a.1) y
  · apply iSup_le
    intro a
    have ha := (sourceRelativeEnvelopeCompetitors_iff hP).mp a.2
    exact le_iSup (fun b : sourceRelativeEnvelopeCompetitors θ u (fun x => (f x : EReal)) => b.1 x)
      ⟨a.1, a.2.1, sourceQuasiEverywhere_of_forall fun y => (ha.2.1 y).trans
        (sourceObstacleEnvelope_le hf hP y), a.2.2.2⟩

end Envelopes

/-! ### `prop:DNTenvelope2` and `prop:DNTenvelope3` for smooth obstacles -/

section Source

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- The source non-pluripolar measure depends only on the potential. -/
theorem sourcePotentialNonPluripolarMeasure_congr {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (h : u = v) :
    sourcePotentialNonPluripolarMeasure θ u hu = sourcePotentialNonPluripolarMeasure θ v hv := by
  subst h
  rfl

variable [ConnectedSpace M]

/-- The obstacle envelope `P_θ(f)` of a continuous `f ≥ φ`, `φ ∈ PSH(X, θ)`: it is `θ`-psh and
`φ ≤ P_θ(f) ≤ f`. -/
theorem sourceObstacleEnvelope_genuine_of_le (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ} (hf : Continuous f)
    (hle : ∀ x, φ x ≤ (f x : EReal)) :
    (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) ∧
      φ ≤ sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal)) ∧
      ∀ x, sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x ≤ (f x : EReal) := by
  have heq := sourceObstacleEnvelope_eq_native θ (fun x => (f x : EReal))
  have hPn := isThetaPshPotential_rooftopEnvelope_of_continuous w (atlasClosedFormToNative θ) hf
    ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
  have hP : (ofFixedModel n M).IsThetaPSH θ
      (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) := by
    rw [isThetaPSH_iff_nativeThetaPotential, heq]
    exact hPn
  exact ⟨hP, fun x => le_sourceRelativeEnvelope hφ (sourceQuasiEverywhere_of_forall hle)
    (sourceObstacle_topReference φ) x, sourceObstacleEnvelope_le hf hP⟩

/-- The generalized envelope `P_θ[φ](f)` of a continuous `f ≥ φ`, `φ ∈ PSH(X, θ)`: it is `θ`-psh
and `φ ≤ P_θ[φ](f) ≤ P_θ(f) ≤ f`. -/
theorem sourceGeneralizedEnvelope_genuine (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ} (hf : Continuous f)
    (hle : ∀ x, φ x ≤ (f x : EReal)) :
    (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)) ∧
      φ ≤ sourceRelativeEnvelope θ φ (fun x => (f x : EReal)) ∧
      sourceRelativeEnvelope θ φ (fun x => (f x : EReal)) ≤
        sourceRelativeEnvelope θ (fun _ => ⊤) (fun x => (f x : EReal)) ∧
      ∀ x, sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x ≤ (f x : EReal) := by
  obtain ⟨hP, hφP, hPf⟩ := sourceObstacleEnvelope_genuine_of_le w θ hφ hf hle
  rw [sourceGeneralizedEnvelope_eq_obstacleEnvelope φ hf hP]
  have hφη := self_le_sourceRelativeEnvelope hφ hφP
  have hne : sourceRelativeEnvelope θ φ
      (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) ≠ ⊥ := by
    intro h
    obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
    obtain ⟨y, -, hy⟩ := ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).2 x₀ univ isOpen_univ
      (mem_univ x₀)
    exact hy (le_bot_iff.mp ((hφη y).trans_eq (congrFun h y)))
  have hηP := sourceRelativeEnvelope_le_of_isThetaPSH (u := φ) hP
  exact ⟨sourceRelativeEnvelope_genuine_of_ne_bot hP hne, hφη, hηP,
    fun x => (hηP x).trans (hPf x)⟩

/-- **`prop:DNTenvelope2`, first assertion, for smooth obstacles**: for `φ ∈ PSH(X, θ)` and a
smooth `f ≥ φ`, the generalized envelope `η = P_θ[φ](f)` (`def:Pthetavarphif`) is `θ`-psh and
`θⁿ_η = 𝟙_{η = f} θ_fⁿ`. -/
theorem sourceGeneralizedEnvelope_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : ChartSmooth (n := n) f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)) hη =
        (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf)).restrict
          {x | sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x = (f x : EReal)} := by
  have hfc : Continuous f := ProductTestForms.ChartSmooth.continuous hf
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
    (TranscendentalWN.isClosed_contact ((isThetaPSH_iff_nativeThetaPotential θ Pf).mp hP).1 hf
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
      _ = (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf))
            ((A ∩ {x | η x = Pf x}) ∩ {x | Pf x = (f x : EReal)}) := by
          rw [hPmeas, Measure.restrict_apply' hC]
      _ ≤ (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf))
            (A ∩ {x | η x = (f x : EReal)}) := by
          refine measure_mono fun x hx => ⟨hx.1.1, ?_⟩
          exact (hx.1.2 : η x = Pf x).trans hx.2
      _ = _ := (Measure.restrict_apply hA).symm
  · rw [← sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hη hf hηf]
    exact Measure.restrict_le_self

/-- **`prop:DNTenvelope3`, first equality, for smooth obstacles**: for `φ ∈ PSH(X, θ)` and a
smooth `f ≥ φ`, with `P = P_θ(f)`, `𝟙_{φ = P} θⁿ_P = 𝟙_{φ = P} θⁿ_φ`. -/
theorem sourceObstacleEnvelope_contact_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : ChartSmooth (n := n) f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP).restrict
          {x | φ x = sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x} := by
  have hfc : Continuous f := ProductTestForms.ChartSmooth.continuous hf
  obtain ⟨hP, hφP, hPf⟩ := sourceObstacleEnvelope_genuine_of_le w θ hφ hfc hle
  obtain ⟨hP', hPmeas⟩ := sourceObstacleEnvelope_measure_eq w θ ⟨φ, hφ⟩ hf
  set Pf := sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal) with hPfdef
  have hC : MeasurableSet {x | Pf x = (f x : EReal)} :=
    (TranscendentalWN.isClosed_contact ((isThetaPSH_iff_nativeThetaPotential θ Pf).mp hP).1 hf
      hPf).measurableSet
  have hD : MeasurableSet {x | φ x = (f x : EReal)} :=
    (TranscendentalWN.isClosed_contact ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1 hf
      hle).measurableSet
  have hdnt := sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hφ hf hle
  refine ⟨hP, le_antisymm ?_ (sourcePotentialNonPluripolarMeasure_contact w hφ hP hφP)⟩
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  calc sourcePotentialNonPluripolarMeasure θ Pf hP (A ∩ {x | φ x = Pf x})
      = (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf))
          ((A ∩ {x | φ x = Pf x}) ∩ {x | Pf x = (f x : EReal)}) := by
        rw [hPmeas, Measure.restrict_apply' hC]
    _ ≤ (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf))
          ((A ∩ {x | φ x = Pf x}) ∩ {x | φ x = (f x : EReal)}) :=
        measure_mono fun x hx => ⟨hx.1, (hx.1.2 : φ x = Pf x).trans hx.2⟩
    _ = sourcePotentialNonPluripolarMeasure θ φ hφ
          ((A ∩ {x | φ x = Pf x}) ∩ {x | φ x = (f x : EReal)}) := by
        rw [← Measure.restrict_apply' hD, ← hdnt, Measure.restrict_apply' hD]
    _ ≤ sourcePotentialNonPluripolarMeasure θ φ hφ (A ∩ {x | φ x = Pf x}) :=
        measure_mono inter_subset_left

/-- **`prop:DNTenvelope3`, second equality, for smooth obstacles**: for `φ ∈ PSH(X, θ)` and a
smooth `f ≥ φ`, with `η = P_θ[φ](f)`, `𝟙_{φ = η} θⁿ_η = 𝟙_{φ = η} θⁿ_φ`. -/
theorem sourceGeneralizedEnvelope_contact_measure_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : ChartSmooth (n := n) f) (hle : ∀ x, φ x ≤ (f x : EReal)) :
    ∃ hη : (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal)),
      (sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ fun x => (f x : EReal))
          hη).restrict {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} =
        (sourcePotentialNonPluripolarMeasure θ φ hφ).restrict
          {x | φ x = sourceRelativeEnvelope θ φ (fun y => (f y : EReal)) x} := by
  have hfc : Continuous f := ProductTestForms.ChartSmooth.continuous hf
  obtain ⟨-, hφη, -, hηf⟩ := sourceGeneralizedEnvelope_genuine w θ hφ hfc hle
  obtain ⟨hη, hηmeas⟩ := sourceGeneralizedEnvelope_measure_eq w θ hφ hf hle
  set η := sourceRelativeEnvelope θ φ fun x => (f x : EReal) with hηdef
  have hC : MeasurableSet {x | η x = (f x : EReal)} :=
    (TranscendentalWN.isClosed_contact ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).1 hf
      hηf).measurableSet
  have hD : MeasurableSet {x | φ x = (f x : EReal)} :=
    (TranscendentalWN.isClosed_contact ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1 hf
      hle).measurableSet
  have hdnt := sourcePotentialNonPluripolarMeasure_restrict_contact_eq w θ hφ hf hle
  refine ⟨hη, le_antisymm ?_ (sourcePotentialNonPluripolarMeasure_contact w hφ hη hφη)⟩
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  calc sourcePotentialNonPluripolarMeasure θ η hη (A ∩ {x | φ x = η x})
      = (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf))
          ((A ∩ {x | φ x = η x}) ∩ {x | η x = (f x : EReal)}) := by
        rw [hηmeas, Measure.restrict_apply' hC]
    _ ≤ (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf))
          ((A ∩ {x | φ x = η x}) ∩ {x | φ x = (f x : EReal)}) :=
        measure_mono fun x hx => ⟨hx.1, (hx.1.2 : φ x = η x).trans hx.2⟩
    _ = sourcePotentialNonPluripolarMeasure θ φ hφ
          ((A ∩ {x | φ x = η x}) ∩ {x | φ x = (f x : EReal)}) := by
        rw [← Measure.restrict_apply' hD, ← hdnt, Measure.restrict_apply' hD]
    _ ≤ sourcePotentialNonPluripolarMeasure θ φ hφ (A ∩ {x | φ x = η x}) :=
        measure_mono inter_subset_left

end Source

/-! ### `lma:DNTroof` for smooth obstacles -/

section Roof

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The rooftop envelope `P_ω(min{f₁, f₂})` of two real functions, for a Kähler form `ω`. -/
def roofEnvelope (w : KahlerBackground n M) (f₁ f₂ : M → ℝ) : M → EReal :=
  rooftopEnvelope w.form.val fun x => ((min (f₁ x) (f₂ x) : ℝ) : EReal)

/-- `P_ω(min{f₁, f₂})` is `ω`-psh and lies below `f₁` and `f₂`, for continuous `fᵢ`. -/
theorem roofEnvelope_genuine (w : KahlerBackground n M) {f₁ f₂ : M → ℝ} (hf₁ : Continuous f₁)
    (hf₂ : Continuous f₂) :
    IsThetaPshPotential w.form.val (roofEnvelope w f₁ f₂) ∧
      (∀ x, roofEnvelope w f₁ f₂ x ≤ (f₁ x : EReal)) ∧
      ∀ x, roofEnvelope w f₁ f₂ x ≤ (f₂ x : EReal) := by
  have hg : Continuous fun x => min (f₁ x) (f₂ x) := hf₁.min hf₂
  have h0 : IsThetaPshPotential w.form.val (fun _ => 0) :=
    (LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive
  have hP := isThetaPshPotential_rooftopEnvelope_of_continuous w w.form hg h0
  have hle := rooftopEnvelope_le_of_isThetaPshPotential hg hP
  refine ⟨hP, fun x => (hle x).trans ?_, fun x => (hle x).trans ?_⟩
  · exact EReal.coe_le_coe_iff.mpr (min_le_left _ _)
  · exact EReal.coe_le_coe_iff.mpr (min_le_right _ _)

/-- The non-pluripolar measure of `P_ω(min{f₁, f₂})` is carried by `{P = f₁} ∪ {P = f₂}`
(concentration on the contact set of the continuous obstacle `min{f₁, f₂}`). -/
theorem roofEnvelope_measure_carried (w : KahlerBackground n M) {f₁ f₂ : M → ℝ}
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hP : IsThetaPshPotential w.form.val (roofEnvelope w f₁ f₂)) :
    diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP
      ({x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} ∪
        {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)})ᶜ = 0 := by
  have hg : Continuous fun x => min (f₁ x) (f₂ x) := hf₁.min hf₂
  set P := roofEnvelope w f₁ f₂ with hPdef
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have hnb : rooftopEnvelope w.form.val (fun x => ((min (f₁ x) (f₂ x) : ℝ) : EReal)) ≠
      fun _ => ⊥ := by
    intro h
    obtain ⟨y, -, hy⟩ := hP.2 x₀ univ isOpen_univ (mem_univ x₀)
    exact hy (congrFun h y)
  have hnt : rooftopEnvelope w.form.val (fun x => ((min (f₁ x) (f₂ x) : ℝ) : EReal)) ≠
      fun _ => ⊤ := by
    intro h
    exact hP.1.quasiPlurisubharmonic.ne_top x₀ (congrFun h x₀)
  have hqc : ActualExtendedObstacleQuasiContinuity.QuasiContinuousERealFor
      (ThetaCapacity.thetaCapacity w.form (fun _ => 0))
      fun x => ((min (f₁ x) (f₂ x) : ℝ) : EReal) := by
    intro η hη
    refine ⟨∅, isOpen_empty, ?_, ?_⟩
    · rw [ThetaCapacity.thetaCapacity_empty]
      exact hη
    · exact (continuous_coe_real_ereal.comp hg).continuousOn
  obtain ⟨hP', -, hneq⟩ :=
    ActualQuasiContinuousEnvelopeContact.exists_genuine_envelope_and_contact w w.form hqc hnb hnt
  refine measure_mono_null (fun x hx => ?_) hneq
  intro hPx
  apply hx
  rcases min_choice (f₁ x) (f₂ x) with h | h
  · left
    change P x = (f₁ x : EReal)
    rw [← h]
    exact hPx
  · right
    change P x = (f₂ x : EReal)
    rw [← h]
    exact hPx

/-- **`lma:DNTroof`, measure assertions, for smooth obstacles.**  Let `ω` be a Kähler form,
`f₁, f₂` smooth, `P = P_ω(min{f₁, f₂})`, `Cᵢ = {P = fᵢ}`, `C = C₁ ∩ C₂ = {P = f₁ = f₂}`.  Then
`P ∈ PSH(X, ω)`, and

* `𝟙_C ω_{f₁}ⁿ = 𝟙_C ω_{f₂}ⁿ`;
* `ωⁿ_P + 𝟙_C ω_{fⱼ}ⁿ = 𝟙_{C₁} ω_{f₁}ⁿ + 𝟙_{C₂} ω_{f₂}ⁿ` for `j = 1` and `j = 2` (the book's
  `eq:DNTroof_Pomega`, `ωⁿ_P = 𝟙_{C₁} ω_{f₁}ⁿ + 𝟙_{C₂} ω_{f₂}ⁿ - 𝟙_C ω_{fⱼ}ⁿ`, with the subtracted
  finite measure moved to the left);
* `ωⁿ_P ≥ 𝟙_{Cⱼ} ω_{fⱼ}ⁿ`. -/
theorem roofEnvelope_measure_eq (w : KahlerBackground n M) {f₁ f₂ : M → ℝ}
    (hf₁ : ChartSmooth (n := n) f₁) (hf₂ : ChartSmooth (n := n) f₂) :
    ∃ hP : IsThetaPshPotential w.form.val (roofEnvelope w f₁ f₂),
      (positiveTopMeasure w (w.form + ddcClosedForm f₁ hf₁)).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧ roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (positiveTopMeasure w (w.form + ddcClosedForm f₂ hf₂)).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧ roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ∧
      (diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP +
          (positiveTopMeasure w (w.form + ddcClosedForm f₁ hf₁)).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (positiveTopMeasure w (w.form + ddcClosedForm f₁ hf₁)).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (positiveTopMeasure w (w.form + ddcClosedForm f₂ hf₂)).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP +
          (positiveTopMeasure w (w.form + ddcClosedForm f₂ hf₂)).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal) ∧
              roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} =
        (positiveTopMeasure w (w.form + ddcClosedForm f₁ hf₁)).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} +
          (positiveTopMeasure w (w.form + ddcClosedForm f₂ hf₂)).restrict
            {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)}) ∧
      (positiveTopMeasure w (w.form + ddcClosedForm f₁ hf₁)).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₁ x : EReal)} ≤
        diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP ∧
      (positiveTopMeasure w (w.form + ddcClosedForm f₂ hf₂)).restrict
          {x | roofEnvelope w f₁ f₂ x = (f₂ x : EReal)} ≤
        diagonalPotentialMeasure w.form (roofEnvelope w f₁ f₂) hP := by
  have hc₁ : Continuous f₁ := ProductTestForms.ChartSmooth.continuous hf₁
  have hc₂ : Continuous f₂ := ProductTestForms.ChartSmooth.continuous hf₂
  obtain ⟨hP, hle₁, hle₂⟩ := roofEnvelope_genuine w hc₁ hc₂
  set P := roofEnvelope w f₁ f₂ with hPdef
  set μ := diagonalPotentialMeasure w.form P hP with hμ
  set ν₁ := positiveTopMeasure w (w.form + ddcClosedForm f₁ hf₁) with hν₁
  set ν₂ := positiveTopMeasure w (w.form + ddcClosedForm f₂ hf₂) with hν₂
  set C₁ : Set M := {x | P x = (f₁ x : EReal)} with hC₁
  set C₂ : Set M := {x | P x = (f₂ x : EReal)} with hC₂
  have hC₁m : MeasurableSet C₁ := (TranscendentalWN.isClosed_contact hP.1 hf₁ hle₁).measurableSet
  have hC₂m : MeasurableSet C₂ := (TranscendentalWN.isClosed_contact hP.1 hf₂ hle₂).measurableSet
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

end Roof

end SGPT.Envelopes.DNT

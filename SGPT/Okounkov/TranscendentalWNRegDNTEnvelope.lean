import SGPT.Okounkov.TranscendentalWNRegContact
import SGPT.Foundations.Analysis.Pending.ActualNoncollapsedObstacleEnvelope
import SGPT.Envelopes.SourceEnvelopeContactSupport

/-!
# Monge–Ampère measures of envelopes of smooth obstacles (package WN-REG)

Package WN-REG (`claude-tok-wn-reg`, nodes `tok-wn-reg:dnt-envelope`, `tok-wn-reg:dnt-source`):
consequences of the Di Nezza–Trapani contact formula for smooth obstacles
(`diagonalPotentialMeasure_restrict_contact_eq`).

* `isThetaPshPotential_rooftopEnvelope_of_continuous`: if `PSH(M, θ) ≠ ∅` and `f` is continuous, the
  envelope `P_θ(f)` is a genuine `θ`-psh function.
* `diagonalPotentialMeasure_rooftopEnvelope_eq` (the book's `cor:DNTenvelope1` for smooth `f`):
  `⟨(θ + ddᶜP_θ(f))ⁿ⟩ = 𝟙_{P_θ(f) = f} (θ + ddᶜf)ⁿ`; `diagonalPotentialMeasure_rooftopEnvelope_zero_eq`:
  its case `f = 0`, `⟨(θ + ddᶜV_θ)ⁿ⟩ = 𝟙_{V_θ = 0} θⁿ` with `V_θ = P_θ(0)`.
* `sourcePotentialNonPluripolarMeasure_restrict_contact_eq`, `sourceObstacleEnvelope_measure_eq`,
  `sourceObstacleEnvelope_zero_measure_eq`: the same statements for the source-facing objects
  (`AtlasClosedRealOneOneForm`, `IsThetaPSH`, `sourcePotentialNonPluripolarMeasure`, the source
  obstacle envelope `sourceRelativeEnvelope θ ⊤ f` of `def:Pthetaf`).

The measure `(θ + ddᶜf)ⁿ` is `positiveTopMeasure ω (θ + ddᶜf)` (density `max((θ + ddᶜf)ⁿ/ωⁿ, 0)`
against `ωⁿ`), which on the contact set is the genuine top power of the smooth form
(`TranscendentalWN.topRatio_nonneg_of_contact`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Okounkov.TranscendentalWNReg

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

section Native

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- **The envelope of a continuous obstacle is genuinely `θ`-psh** as soon as `PSH(M, θ) ≠ ∅`. -/
theorem isThetaPshPotential_rooftopEnvelope_of_continuous (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : Continuous f) {φ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal)) := by
  obtain ⟨xmin, -, hxmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  refine ActualNoncollapsedObstacleEnvelope.isThetaPshPotential_of_ne_infinities w θ ?_ ?_
  · intro h
    obtain ⟨M₀, hM₀⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hφ
    set φ' : M → EReal := fun x => φ x + ((f xmin - M₀ : ℝ) : EReal) with hφ'
    have hφ'psh : IsThetaPshPotential θ.val φ' := hφ.add_const _
    have hφ'le : ∀ x, φ' x ≤ (f x : EReal) := by
      intro x
      calc φ' x ≤ (M₀ : EReal) + ((f xmin - M₀ : ℝ) : EReal) := add_le_add (hM₀ x) le_rfl
        _ = (f xmin : EReal) := by rw [← EReal.coe_add]; congr 1; ring
        _ ≤ (f x : EReal) := EReal.coe_le_coe_iff.mpr (hxmin (mem_univ x))
    have hle := le_rooftopEnvelope hφ'psh (quasiEverywhere_of_forall hφ'le)
    obtain ⟨y, -, hy⟩ := hφ.2 xmin univ isOpen_univ (mem_univ xmin)
    have hyb : φ' y = ⊥ := le_bot_iff.mp ((hle y).trans_eq (congrFun h y))
    exact hy (EReal.add_eq_bot_iff.mp hyb |>.resolve_right (EReal.coe_ne_bot _))
  · intro h
    have hle : rooftopEnvelope θ.val (fun x => (f x : EReal)) ≤ fun _ => (f xmax : EReal) :=
      (rooftopEnvelope_le_iff upperSemicontinuous_const).mpr fun u hu hq x =>
        ContinuousObstacleEnvelopeContact.rooftopCompetitors_le_const
          (fun y => hxmax (mem_univ y)) ⟨hu, hq⟩ x
    have := hle xmin
    rw [congrFun h xmin] at this
    exact EReal.coe_ne_top _ (top_le_iff.mp this)

omit [MeasurableSpace M] [BorelSpace M] in
/-- The envelope of a continuous obstacle lies below the obstacle everywhere. -/
theorem rooftopEnvelope_le_of_isThetaPshPotential {θ : ClosedRealOneOneForm n M} {f : M → ℝ}
    (hf : Continuous f) (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal)))
    (x : M) : rooftopEnvelope θ.val (fun y => (f y : EReal)) x ≤ (f x : EReal) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have hnb : rooftopEnvelope θ.val (fun y => (f y : EReal)) ≠ fun _ => ⊥ := by
    intro h
    obtain ⟨y, -, hy⟩ := hP.2 x₀ univ isOpen_univ (mem_univ x₀)
    exact hy (congrFun h y)
  have hne : (rooftopCompetitors θ.val fun y => (f y : EReal)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    exact hnb (rooftopEnvelope_of_empty hemp)
  exact ContinuousObstacleEnvelopeContact.rooftopEnvelope_le_of_continuous hf hne hP.1 x

/-- **The Monge–Ampère measure of the envelope of a smooth obstacle** (the book's
`cor:DNTenvelope1` for smooth `f`): `⟨(θ + ddᶜP_θ(f))ⁿ⟩ = 𝟙_{P_θ(f) = f} (θ + ddᶜf)ⁿ`. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_eq (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal))) :
    diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun x => (f x : EReal)) hP =
      (positiveTopMeasure w (θ + ddcClosedForm f hf)).restrict
        {x | rooftopEnvelope θ.val (fun y => (f y : EReal)) x = (f x : EReal)} := by
  refine le_antisymm (TranscendentalWN.diagonalPotentialMeasure_rooftopEnvelope_le_contact w θ hf hP)
    ?_
  exact positiveTopMeasure_restrict_contact_le w θ hP hf
    (rooftopEnvelope_le_of_isThetaPshPotential (ProductTestForms.ChartSmooth.continuous hf) hP)

/-- **`cor:DNTenvelope1` for smooth obstacles**: if `PSH(M, θ) ≠ ∅` and `f` is smooth, then `P_θ(f)`
is `θ`-psh and `⟨(θ + ddᶜP_θ(f))ⁿ⟩ = 𝟙_{P_θ(f) = f} (θ + ddᶜf)ⁿ`. -/
theorem exists_diagonalPotentialMeasure_rooftopEnvelope_eq (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hne : ∃ φ : M → EReal, IsThetaPshPotential θ.val φ)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) :
    ∃ hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun x => (f x : EReal)),
      diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun x => (f x : EReal)) hP =
        (positiveTopMeasure w (θ + ddcClosedForm f hf)).restrict
          {x | rooftopEnvelope θ.val (fun y => (f y : EReal)) x = (f x : EReal)} := by
  obtain ⟨φ, hφ⟩ := hne
  have hP := isThetaPshPotential_rooftopEnvelope_of_continuous w θ
    (ProductTestForms.ChartSmooth.continuous hf) hφ
  exact ⟨hP, diagonalPotentialMeasure_rooftopEnvelope_eq w θ hf hP⟩

/-- **The "in particular" of `cor:DNTenvelope1`**: with `V_θ = P_θ(0)`,
`⟨(θ + ddᶜV_θ)ⁿ⟩ = 𝟙_{V_θ = 0} θⁿ` (if `PSH(M, θ) ≠ ∅`). -/
theorem exists_diagonalPotentialMeasure_rooftopEnvelope_zero_eq (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hne : ∃ φ : M → EReal, IsThetaPshPotential θ.val φ) :
    ∃ hV : IsThetaPshPotential θ.val (rooftopEnvelope θ.val fun _ => 0),
      diagonalPotentialMeasure θ (rooftopEnvelope θ.val fun _ => 0) hV =
        (positiveTopMeasure w θ).restrict {x | rooftopEnvelope θ.val (fun _ => 0) x = 0} := by
  obtain ⟨hP, h⟩ := exists_diagonalPotentialMeasure_rooftopEnvelope_eq w θ hne
    (ProductTestForms.chartSmooth_const (n := n) (M := M) 0)
  simp only [add_ddcClosedForm_const, EReal.coe_zero] at h hP
  exact ⟨hP, h⟩

end Native

/-! ### Source-facing statements -/

section Source

open SGPT.PSH.VariableComplexAtlas

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The Di Nezza–Trapani contact formula for smooth obstacles**, source-facing form (the book's
`thm:DNTcontact` for `θᵢ = θ`, `φᵢ = u`, `fᵢ = f` smooth). -/
theorem sourcePotentialNonPluripolarMeasure_restrict_contact_eq (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (hle : ∀ x, u x ≤ (f x : EReal)) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf)).restrict
        {x | u x = (f x : EReal)} :=
  diagonalPotentialMeasure_restrict_contact_eq w (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hf hle

/-- **`cor:DNTenvelope1` for smooth obstacles**, source-facing form: if `PSH(X, θ) ≠ ∅` and `f` is
smooth, the source envelope `P = P_θ(f)` is `θ`-psh and `θⁿ_P = 𝟙_{P = f} (θ + ddᶜf)ⁿ`. -/
theorem sourceObstacleEnvelope_measure_eq [ConnectedSpace M] (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hne : ∃ φ : M → EReal, (ofFixedModel n M).IsThetaPSH θ φ) {f : M → ℝ}
    (hf : ChartSmooth (n := n) f) :
    ∃ hP : (ofFixedModel n M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP =
        (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f hf)).restrict
          {x | sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x = (f x : EReal)} := by
  obtain ⟨φ, hφ⟩ := hne
  have heq := sourceObstacleEnvelope_eq_native θ (fun x => (f x : EReal))
  obtain ⟨hP', h⟩ := exists_diagonalPotentialMeasure_rooftopEnvelope_eq w
    (atlasClosedFormToNative θ) ⟨φ, (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ⟩ hf
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
    _ = _ := h
    _ = _ := by rw [heq]

/-- **The "in particular" of `cor:DNTenvelope1`**, source-facing form: with
`V_θ = P_θ(0) = sourceRelativeEnvelope θ ⊤ 0`, `θⁿ_{V_θ} = 𝟙_{V_θ = 0} θⁿ`. -/
theorem sourceObstacleEnvelope_zero_measure_eq [ConnectedSpace M] (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hne : ∃ φ : M → EReal, (ofFixedModel n M).IsThetaPSH θ φ) :
    ∃ hV : (ofFixedModel n M).IsThetaPSH θ (sourceRelativeEnvelope θ (fun _ => ⊤) fun _ => 0),
      sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ (fun _ => ⊤) fun _ => 0) hV =
        (positiveTopMeasure w (atlasClosedFormToNative θ)).restrict
          {x | sourceRelativeEnvelope θ (fun _ => ⊤) (fun _ => 0) x = 0} := by
  obtain ⟨hP, h⟩ := sourceObstacleEnvelope_measure_eq w θ hne
    (ProductTestForms.chartSmooth_const (n := n) (M := M) 0)
  simp only [add_ddcClosedForm_const, EReal.coe_zero] at h hP
  exact ⟨hP, h⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- On the contact set of a potential `u ≤ 0`, the density of `θⁿ` is nonnegative: there the measure
`positiveTopMeasure ω θ` is the genuine (signed) measure `θⁿ` of the smooth form. -/
theorem topRatio_nonneg_of_le_zero_of_eq_zero (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hle : u ≤ 0) {x : M} (hx : u x = 0) :
    0 ≤ IntegrationCurrent.topRatio w.form.val
      (ProductTestForms.formPow (atlasClosedFormToNative θ).val n) x := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have h := TranscendentalWN.topRatio_nonneg_of_contact w (atlasClosedFormToNative θ) hn.1
    (ProductTestForms.chartSmooth_const (n := n) (M := M) 0)
    (fun y => by rw [EReal.coe_zero]; exact hle y) (by rw [EReal.coe_zero]; exact hx)
  rwa [add_ddcClosedForm_const] at h

/-- **`cor:DNTenvelope1`, "in particular"**, with the book's `V_θ = sup{φ ∈ PSH(X,θ) : φ ≤ 0}`
(`sourceMinimalEnvelope`): if `PSH(X,θ) ≠ ∅`, then `θⁿ_{V_θ} = 𝟙_{V_θ = 0} θⁿ`. -/
theorem sourceMinimalEnvelope_measure_eq [ConnectedSpace M] (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
        (sourceMinimalEnvelope_thetaPSH_of_mem hu) =
      (positiveTopMeasure w (atlasClosedFormToNative θ)).restrict
        {x | sourceMinimalEnvelope θ x = 0} := by
  set V := sourceMinimalEnvelope θ with hVdef
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hu
  have hVn := (isThetaPSH_iff_nativeThetaPotential θ V).mp hV
  have hV0 : ∀ x, V x ≤ ((0 : ℝ) : EReal) := fun x => by
    rw [EReal.coe_zero]; exact sourceMinimalEnvelope_le_zero θ x
  have hE : {x | V x = ((0 : ℝ) : EReal)} = {x | V x = 0} := by
    ext x; simp only [EReal.coe_zero]
  have hc := ProductTestForms.chartSmooth_const (n := n) (M := M) 0
  refine le_antisymm ?_ ?_
  · have hcarried : sourcePotentialNonPluripolarMeasure θ V hV =
        (sourcePotentialNonPluripolarMeasure θ V hV).restrict {x | V x = 0} := by
      refine (Measure.restrict_eq_self_of_ae_mem ?_).symm
      rw [ae_iff]
      have hset : {x | ¬ (x ∈ {x | V x = 0})} = {x | V x < 0} := by
        ext x
        simp only [mem_ofPred_eq]
        exact ⟨fun h => lt_of_le_of_ne (sourceMinimalEnvelope_le_zero θ x) h, fun h => h.ne⟩
      rw [hset]
      exact sourceMinimalEnvelope_measure_negative_null w hV
    rw [hcarried]
    have h := TranscendentalWN.diagonalPotentialMeasure_restrict_contact_le w
      (atlasClosedFormToNative θ) hVn hc hV0
    rw [hE, ← positiveTopMeasure_eq_topFormMeasure, add_ddcClosedForm_const] at h
    exact h
  · have h := positiveTopMeasure_restrict_contact_le w (atlasClosedFormToNative θ) hVn hc hV0
    rw [hE, add_ddcClosedForm_const] at h
    exact h

/-- **`prop:DNTenvelope2`, "in particular"** (and hence the book's `thm:Pvarphisupport` with
equality): for `φ ∈ PSH(X,θ)`, `θⁿ_{P_θ[φ]} = 𝟙_{P_θ[φ] = 0} θⁿ`. -/
theorem sourceSingularityEnvelope_measure_eq [ConnectedSpace M] (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ (sourceSingularityEnvelope θ u)
        (sourceOrdinaryEnvelope_genuine hu) =
      (positiveTopMeasure w (atlasClosedFormToNative θ)).restrict
        {x | sourceSingularityEnvelope θ u x = 0} := by
  set P := sourceSingularityEnvelope θ u with hPdef
  have hP := sourceOrdinaryEnvelope_genuine hu
  have hPn := (isThetaPSH_iff_nativeThetaPotential θ P).mp hP
  have hP0 : ∀ x, P x ≤ ((0 : ℝ) : EReal) := fun x => by
    rw [EReal.coe_zero]; exact sourceSingularityEnvelope_le_zero θ u x
  have hE : {x | P x = ((0 : ℝ) : EReal)} = {x | P x = 0} := by
    ext x; simp only [EReal.coe_zero]
  have hc := ProductTestForms.chartSmooth_const (n := n) (M := M) 0
  refine le_antisymm ?_ ?_
  · calc sourcePotentialNonPluripolarMeasure θ P hP
        ≤ (sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
            (sourceMinimalEnvelope_thetaPSH_of_mem hu)).restrict {x | P x = 0} :=
          sourceSingularityEnvelope_measure_le_minimal w hu
      _ = ((positiveTopMeasure w (atlasClosedFormToNative θ)).restrict
            {x | sourceMinimalEnvelope θ x = 0}).restrict {x | P x = 0} := by
          rw [sourceMinimalEnvelope_measure_eq w θ hu]
      _ ≤ (positiveTopMeasure w (atlasClosedFormToNative θ)).restrict {x | P x = 0} :=
          Measure.restrict_mono subset_rfl Measure.restrict_le_self
  · have h := positiveTopMeasure_restrict_contact_le w (atlasClosedFormToNative θ) hPn hc hP0
    rw [hE, add_ddcClosedForm_const] at h
    exact h

/-- **The book's `thm:Pvarphisupport`**: `θⁿ_{P_θ[φ]} ≤ 𝟙_{P_θ[φ] = 0} θⁿ`. -/
theorem sourceSingularityEnvelope_measure_le [ConnectedSpace M] (w : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ (sourceSingularityEnvelope θ u)
        (sourceOrdinaryEnvelope_genuine hu) ≤
      (positiveTopMeasure w (atlasClosedFormToNative θ)).restrict
        {x | sourceSingularityEnvelope θ u x = 0} :=
  (sourceSingularityEnvelope_measure_eq w θ hu).le

end Source

end SGPT.Okounkov.TranscendentalWNReg

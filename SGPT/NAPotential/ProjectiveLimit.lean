import SGPT.NAPotential.TransitionOperations

/-! # `PSH^NA(X, θ)` as a projective limit of the spaces `PSH^NA(X, θ + ω)`

Source `prop:NApotential:L222` and (the Kähler-indexed form of) `prop:PSHNAreform1` of
`chapter_NApotential.tex`.  The maps `P_{θ+ω}[•]_𝓘 : PSH^NA(X, θ) → PSH^NA(X, θ + ω)` of
`def:PSHNAtrangeneral`, `ω ∈ Kah(X)`, induce a bijection
`PSH^NA(X, θ) ≃ lim_{ω ∈ Kah(X)} PSH^NA(X, θ + ω)`, the transition maps of the limit being the
maps `P_{θ+ω}[•]_𝓘 : PSH^NA(X, θ + ω') → PSH^NA(X, θ + ω)` for `ω ≥ ω'`.

Everything is reduced to the intrinsic order: background changes preserve the intrinsic type
(`SourceNAPotential.backgroundChange_POrder_equivalent`), and two metrics in the same background
which are mutually comparable coincide (`SourceNAPOrder.antisymm`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {α β θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The map `P_β[•]_𝓘 : PSH^NA(X, α) → PSH^NA(X, β)` for `β - α` semipositive: the existing
background change by `β - α`, read in the background `β`. -/
def SourceNAPotential.transition
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Ξ : SourceNAPotential α) : SourceNAPotential β :=
  (Ξ.backgroundChange (sourceNATransitionForm α β)
    (sourceNATransitionForm_semipositive hαβ)).castBackground (sourceNATransitionForm_add α β)

/-- Transitions preserve the intrinsic type. -/
theorem SourceNAPotential.transition_POrder_equivalent (omega : KahlerBackground n M)
    (hαβ : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (Ξ : SourceNAPotential α) :
    SourceNAPOrder Ξ (Ξ.transition hαβ) ∧ SourceNAPOrder (Ξ.transition hαβ) Ξ := by
  have h1 := Ξ.backgroundChange_POrder_equivalent omega (sourceNATransitionForm α β)
    (sourceNATransitionForm_semipositive hαβ)
  have h2 := (Ξ.backgroundChange (sourceNATransitionForm α β)
    (sourceNATransitionForm_semipositive hαβ)).castBackground_POrder_equivalent omega
      (sourceNATransitionForm_add α β)
  exact ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

/-- The Kähler form `ω`, as an atlas form. -/
def sourceNAKahlerAtlasForm (κ : SourceKahlerForm n M) :
    AtlasClosedRealOneOneForm (ofFixedModel n M) :=
  nativeClosedFormToAtlas (sourceKahlerFormRepresentative κ).form

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
theorem sourceNAKahlerAtlasForm_semipositive (κ : SourceKahlerForm n M) :
    (atlasClosedFormToNative (sourceNAKahlerAtlasForm κ)).val.IsSemipositive := by
  simpa only [sourceNAKahlerAtlasForm, sourceNativeAtlasForm_roundTrip] using
    (sourceKahlerFormRepresentative κ).isSemipositive

/-- Source `def:PSHNAtrangeneral` at a Kähler index: `P_{θ+ω}[Γ]_𝓘 ∈ PSH^NA(X, θ + ω)`;
the background `θ + ω` is literally `sourceNAComponentBackground θ ω`. -/
def SourceNAPotential.kahlerProjection (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n M) :
    SourceNAPotential (sourceNAComponentBackground θ κ) :=
  Γ.backgroundChange (sourceNAKahlerAtlasForm κ) (sourceNAKahlerAtlasForm_semipositive κ)

/-- The target of `prop:NApotential:L222`: compatible families
`(Ξ^ω)_{ω ∈ Kah(X)}` with `Ξ^ω ∈ PSH^NA(X, θ + ω)` and `P_{θ+ω'}[Ξ^ω]_𝓘 = Ξ^{ω'}` whenever
`ω ≤ ω'` as forms (i.e. `ω' ⪯ ω` in the book's order on `Kah(X)`). -/
structure SourceNAProjectiveLimit (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) where
  family : ∀ κ : SourceKahlerForm n M, SourceNAPotential (sourceNAComponentBackground θ κ)
  compatible : ∀ (κ ζ : SourceKahlerForm n M) (h : sourceKahlerFormLE κ ζ),
    (family κ).transition (sourceNAComponentBackground_difference θ h) = family ζ

@[ext] theorem SourceNAProjectiveLimit.ext {P Q : SourceNAProjectiveLimit θ}
    (h : ∀ κ : SourceKahlerForm n M, P.family κ = Q.family κ) : P = Q := by
  cases P with
  | mk p hp =>
    cases Q with
    | mk q hq =>
      have hpq : p = q := funext h
      subst hpq
      rfl

/-- The map of `prop:NApotential:L222`. -/
def SourceNAPotential.toProjectiveLimit (Γ : SourceNAPotential θ) : SourceNAProjectiveLimit θ where
  family κ := Γ.kahlerProjection κ
  compatible κ ζ h := by
    let omega := sourceKahlerFormRepresentative ζ
    have hκ := Γ.backgroundChange_POrder_equivalent omega (sourceNAKahlerAtlasForm κ)
      (sourceNAKahlerAtlasForm_semipositive κ)
    have hζ := Γ.backgroundChange_POrder_equivalent omega (sourceNAKahlerAtlasForm ζ)
      (sourceNAKahlerAtlasForm_semipositive ζ)
    have ht := (Γ.kahlerProjection κ).transition_POrder_equivalent omega
      (sourceNAComponentBackground_difference θ h)
    exact SourceNAPOrder.antisymm (ht.2.trans (hκ.2.trans hζ.1)) (hζ.2.trans (hκ.1.trans ht.1))

theorem SourceNAPotential.toProjectiveLimit_family (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) : Γ.toProjectiveLimit.family κ = Γ.kahlerProjection κ := rfl

/-- All members of a compatible family have the same intrinsic type. -/
theorem SourceNAProjectiveLimit.family_POrder_equivalent (P : SourceNAProjectiveLimit θ)
    (κ ζ : SourceKahlerForm n M) :
    SourceNAPOrder (P.family κ) (P.family ζ) ∧ SourceNAPOrder (P.family ζ) (P.family κ) := by
  let μ := sourceKahlerFormCommonUpper κ ζ
  let omega := sourceKahlerFormRepresentative μ
  have hκ := (P.family κ).transition_POrder_equivalent omega
    (sourceNAComponentBackground_difference θ (sourceKahlerFormLE_commonUpper_left κ ζ))
  have hζ := (P.family ζ).transition_POrder_equivalent omega
    (sourceNAComponentBackground_difference θ (sourceKahlerFormLE_commonUpper_right κ ζ))
  rw [P.compatible κ μ (sourceKahlerFormLE_commonUpper_left κ ζ)] at hκ
  rw [P.compatible ζ μ (sourceKahlerFormLE_commonUpper_right κ ζ)] at hζ
  exact ⟨hκ.1.trans hζ.2, hζ.1.trans hκ.2⟩

/-- The index `ω / 2`. -/
def sourceNAHalfKahlerForm (κ : SourceKahlerForm n M) : SourceKahlerForm n M :=
  sourceKahlerFormOfBackground (sourceNAHalfKahlerBackground (sourceKahlerFormRepresentative κ))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- `(θ + ω/2) + ω/2` and `θ + ω` have the same coefficients on every chart target. -/
theorem sourceNAHalfHalfBackground_semipositive (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (κ : SourceKahlerForm n M) :
    (atlasClosedFormToNative (sourceNAComponentBackground θ κ) -
      atlasClosedFormToNative (sourceNAComponentBackground
        (sourceNAComponentBackground θ (sourceNAHalfKahlerForm κ))
        (sourceNAHalfKahlerForm κ))).val.IsSemipositive := by
  intro e z hz v
  have h := sourceKahlerFormRepresentative_geometricallyEq
    (sourceNAHalfKahlerBackground (sourceKahlerFormRepresentative κ)) e hz
  change (sourceKahlerFormRepresentative (sourceNAHalfKahlerForm κ)).form.val.coeff e z =
    (sourceNAHalfKahlerBackground (sourceKahlerFormRepresentative κ)).form.val.coeff e z at h
  simp only [sourceNAComponentBackground_native, sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, h, sourceNAHalfKahlerBackground, KahlerBackground.smul_form,
    ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring_nf
  exact le_rfl

/-- The preimage component at `ω`: the component at `ω/2` of `Ξ^{ω/2}`, read in `θ + ω`
(the book's `Γ^{θ+ω} = Γ^{ω/2, ω/2}`). -/
def SourceNAProjectiveLimit.preimageComponent (P : SourceNAProjectiveLimit θ)
    (κ : SourceKahlerForm n M) : SourcePositiveIModelTestCurve (sourceNAComponentBackground θ κ) :=
  sourceIModelTestCurveTransition (sourceKahlerFormRepresentative κ)
    (sourceNAHalfHalfBackground_semipositive θ κ)
    ((P.family (sourceNAHalfKahlerForm κ)).component (sourceNAHalfKahlerForm κ))

/-- Every preimage component has the intrinsic type of every component of every member. -/
theorem SourceNAProjectiveLimit.preimageComponent_POrder_equivalent
    (P : SourceNAProjectiveLimit θ) (κ ζ ν : SourceKahlerForm n M) :
    SourceTestCurvePOrder (P.preimageComponent κ).val ((P.family ζ).component ν).val ∧
      SourceTestCurvePOrder ((P.family ζ).component ν).val (P.preimageComponent κ).val := by
  let omega := sourceKahlerFormRepresentative κ
  let κ₂ := sourceNAHalfKahlerForm κ
  have ht := sourceIModelTestCurveTransition_POrder_equivalent omega
    (sourceNAHalfHalfBackground_semipositive θ κ) ((P.family κ₂).component κ₂)
  have hf := P.family_POrder_equivalent κ₂ ζ
  have hc := (P.family κ₂).component_POrder_equivalent κ₂ ν
  have h1 := (sourceNAPOrder_iff_component (P.family κ₂) (P.family ζ) ν).mp hf.1
  have h2 := (sourceNAPOrder_iff_component (P.family ζ) (P.family κ₂) ν).mp hf.2
  exact ⟨SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega ht.2 hc.1) h1,
    SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega h2 hc.2) ht.1⟩

/-- The preimage of a compatible family. -/
def SourceNAProjectiveLimit.preimage (P : SourceNAProjectiveLimit θ) : SourceNAPotential θ where
  component κ := P.preimageComponent κ
  compatible κ ζ h := by
    let omega := sourceKahlerFormRepresentative ζ
    have ht := sourceIModelTestCurveTransition_POrder_equivalent omega
      (sourceNAComponentBackground_difference θ h) (P.preimageComponent κ)
    have hκ := P.preimageComponent_POrder_equivalent κ κ κ
    have hζ := P.preimageComponent_POrder_equivalent ζ κ κ
    apply Subtype.ext
    exact SourceTestCurvePOrder.antisymm omega
      (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega ht.2 hκ.1) hζ.2)
      (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hζ.1 hκ.2) ht.1)

/-- The preimage maps to the given family. -/
theorem SourceNAProjectiveLimit.toProjectiveLimit_preimage (P : SourceNAProjectiveLimit θ) :
    P.preimage.toProjectiveLimit = P := by
  apply SourceNAProjectiveLimit.ext
  intro κ
  let omega := sourceKahlerFormRepresentative κ
  have hb := P.preimage.backgroundChange_POrder_equivalent omega (sourceNAKahlerAtlasForm κ)
    (sourceNAKahlerAtlasForm_semipositive κ)
  have h1 : SourceNAPOrder P.preimage (P.family κ) :=
    ⟨κ, (P.preimageComponent_POrder_equivalent κ κ κ).1⟩
  have h2 : SourceNAPOrder (P.family κ) P.preimage :=
    ⟨κ, (P.preimageComponent_POrder_equivalent κ κ κ).2⟩
  exact SourceNAPOrder.antisymm (hb.2.trans h1) (h2.trans hb.1)

/-- The map of `prop:NApotential:L222` is injective. -/
theorem SourceNAPotential.toProjectiveLimit_injective (omega : KahlerBackground n M) :
    Function.Injective (SourceNAPotential.toProjectiveLimit (θ := θ)) := by
  intro Γ Δ h
  let κ := sourceKahlerFormOfBackground omega
  have he : Γ.kahlerProjection κ = Δ.kahlerProjection κ :=
    congrArg (fun P : SourceNAProjectiveLimit θ => P.family κ) h
  have hΓ := Γ.backgroundChange_POrder_equivalent omega (sourceNAKahlerAtlasForm κ)
    (sourceNAKahlerAtlasForm_semipositive κ)
  have hΔ := Δ.backgroundChange_POrder_equivalent omega (sourceNAKahlerAtlasForm κ)
    (sourceNAKahlerAtlasForm_semipositive κ)
  change SourceNAPOrder Γ (Γ.kahlerProjection κ) ∧ SourceNAPOrder (Γ.kahlerProjection κ) Γ at hΓ
  change SourceNAPOrder Δ (Δ.kahlerProjection κ) ∧ SourceNAPOrder (Δ.kahlerProjection κ) Δ at hΔ
  rw [he] at hΓ
  exact SourceNAPOrder.antisymm (hΓ.1.trans hΔ.2) (hΔ.1.trans hΓ.2)

/-- Source `prop:NApotential:L222`: the maps `P_{θ+ω}[•]_𝓘` induce a bijection
`PSH^NA(X, θ) ≃ lim_{ω ∈ Kah(X)} PSH^NA(X, θ + ω)`. -/
theorem SourceNAPotential.toProjectiveLimit_bijective (omega : KahlerBackground n M) :
    Function.Bijective (SourceNAPotential.toProjectiveLimit (θ := θ)) :=
  ⟨SourceNAPotential.toProjectiveLimit_injective omega,
    fun P => ⟨P.preimage, P.toProjectiveLimit_preimage⟩⟩

/-- The bijection of `prop:NApotential:L222` as an equivalence. -/
def sourceNAProjectiveLimitEquiv (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    SourceNAPotential θ ≃ SourceNAProjectiveLimit θ :=
  Equiv.ofBijective _ (SourceNAPotential.toProjectiveLimit_bijective omega)

/-! ### The positive-part projective limit (`prop:PSHNAreform1`, Kähler index) -/

/-- The tautological bijection of `prop:PSHNAreform1` between `PSH^NA(X, θ)` and
`lim_ω PSH^NA(X, θ + ω)_{>0}`: an element is the same thing as its compatible family of
positive `𝓘`-model components (`def:NApotential:L24`). -/
def sourceNAPotentialEquivCompatibleComponents (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    SourceNAPotential θ ≃
      {c : ∀ κ : SourceKahlerForm n M, SourcePositiveIModelTestCurve (sourceNAComponentBackground θ κ) //
        ∀ (κ ζ : SourceKahlerForm n M) (h : sourceKahlerFormLE κ ζ),
          sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ζ)
            (sourceNAComponentBackground_difference θ h) (c κ) = c ζ} where
  toFun Γ := ⟨Γ.component, Γ.compatible⟩
  invFun c := ⟨c.val, c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Under `prop:NAposNAemb`, every component of `Γ`, viewed in `PSH^NA(X, θ + ω)`, is
`P_{θ+ω}[Γ]_𝓘`. -/
theorem SourceNAPotential.kahlerProjection_eq_embedding (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) :
    Γ.kahlerProjection κ = sourcePositiveTestCurveToNA (Γ.component κ) := by
  let omega := sourceKahlerFormRepresentative κ
  have hb := Γ.backgroundChange_POrder_equivalent omega (sourceNAKahlerAtlasForm κ)
    (sourceNAKahlerAtlasForm_semipositive κ)
  have hG := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent (Γ.component κ) omega
  have hΓ := Γ.realizedComponent_component_POrder_equivalent omega κ
  have h1 : SourceNAPOrder (sourcePositiveTestCurveToNA (Γ.component κ)) Γ :=
    (sourceNAPOrder_iff_realizedComponents _ Γ omega omega).mpr
      (SourceTestCurvePOrder.trans omega hG.1 hΓ.2)
  have h2 : SourceNAPOrder Γ (sourcePositiveTestCurveToNA (Γ.component κ)) :=
    (sourceNAPOrder_iff_realizedComponents Γ _ omega omega).mpr
      (SourceTestCurvePOrder.trans omega hΓ.1 hG.2)
  exact SourceNAPOrder.antisymm (hb.2.trans h2) (h1.trans hb.1)

/-- The map `lim_ω PSH^NA(X, θ + ω)_{>0} → lim_ω PSH^NA(X, θ + ω)` induced by the injections
of `prop:NAposNAemb`. -/
def SourceNAPotential.toEmbeddedProjectiveLimit (Γ : SourceNAPotential θ) :
    SourceNAProjectiveLimit θ where
  family κ := sourcePositiveTestCurveToNA (Γ.component κ)
  compatible κ ζ h := by
    rw [← Γ.kahlerProjection_eq_embedding, ← Γ.kahlerProjection_eq_embedding]
    exact Γ.toProjectiveLimit.compatible κ ζ h

/-- The composite of the two maps of `prop:PSHNAreform1` is the map of
`prop:NApotential:L222`. -/
theorem SourceNAPotential.toEmbeddedProjectiveLimit_eq (Γ : SourceNAPotential θ) :
    Γ.toEmbeddedProjectiveLimit = Γ.toProjectiveLimit := by
  apply SourceNAProjectiveLimit.ext
  intro κ
  exact (Γ.kahlerProjection_eq_embedding κ).symm

/-- Source `prop:PSHNAreform1` for `ω` running over `Kah(X)`: the map
`lim_ω PSH^NA(X, θ + ω)_{>0} → lim_ω PSH^NA(X, θ + ω)` induced by `prop:NAposNAemb` is a
bijection (the first map being the tautological bijection
`sourceNAPotentialEquivCompatibleComponents`). -/
theorem SourceNAPotential.toEmbeddedProjectiveLimit_bijective (omega : KahlerBackground n M) :
    Function.Bijective (SourceNAPotential.toEmbeddedProjectiveLimit (θ := θ)) := by
  have h : (SourceNAPotential.toEmbeddedProjectiveLimit (θ := θ)) =
      SourceNAPotential.toProjectiveLimit :=
    funext SourceNAPotential.toEmbeddedProjectiveLimit_eq
  rw [h]
  exact SourceNAPotential.toProjectiveLimit_bijective omega

end SGPT.PSH.VariableComplexAtlas

import SGPT.NAPotential.TransitionOperations
import SGPT.PSH.SourceIModelTestCurveRepresentativeChange

/-! # Independence of the representative of the cohomology class

Source `rmk:NApotential:L47` of `chapter_NApotential.tex`: for `θ'` representing `{θ}` there is a
canonical bijection `PSH^NA(X, θ) ≃ PSH^NA(X, θ')` (componentwise the bijection of
`prop:Imodeltestcurveindeptheta`), these bijections satisfy the cocycle condition, and the
projective limit `PSH^NA(X, {θ}) = lim_θ PSH^NA(X, θ)` over the representatives is canonically
in bijection with each `PSH^NA(X, θ)`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ η ξ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Cohomologous forms give cohomologous components. -/
theorem sourceNAComponentBackground_class
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (κ : SourceKahlerForm n M) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative (sourceNAComponentBackground θ κ)) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative (sourceNAComponentBackground η κ)) := by
  rw [sourceNAComponentBackground_native, sourceNAComponentBackground_native,
    RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_add, hc]

/-- A test curve and its image under the change of representative have the same intrinsic
type. -/
theorem SourceTestCurve.changeRepresentative_POrder_equivalent (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (G : SourceTestCurve θ) :
    SourceTestCurvePOrder G (G.changeRepresentative omega hc) ∧
      SourceTestCurvePOrder (G.changeRepresentative omega hc) G := by
  obtain ⟨g, hg, hθη⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hc
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  have hbound : ∀ x, |g x| ≤ B := fun x => by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x)
  have hslice (r : ℝ) (hr : r < G.max) :
      SGPT.PSH.SingularityEquiv (G.potential ⟨r, hr⟩)
        ((G.changeRepresentative omega hc).potential ⟨r, hr⟩) := by
    have hs := (sourceOrdinaryEnvelope_changeRepresentative hg hθη (G.thetaPSH ⟨r, hr⟩)).2
    rw [G.fixedPoint ⟨r, hr⟩] at hs
    have hshift : SGPT.PSH.SingularityEquiv (G.potential ⟨r, hr⟩)
        (fun x => G.potential ⟨r, hr⟩ x - (g x : EReal)) := by
      refine ⟨⟨B, fun x _ => ?_⟩, ⟨B, fun x _ => ?_⟩⟩
      · have h := add_le_add (le_refl (G.potential ⟨r, hr⟩ x - (g x : EReal)))
          (EReal.coe_le_coe_iff.mpr (abs_le.mp (hbound x)).2)
        simpa only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
          neg_add_cancel, EReal.coe_zero, add_zero] using h
      · change G.potential ⟨r, hr⟩ x + -(g x : EReal) ≤ G.potential ⟨r, hr⟩ x + (B : EReal)
        apply add_le_add le_rfl
        rw [← EReal.coe_neg]
        exact EReal.coe_le_coe_iff.mpr (by linarith [(abs_le.mp (hbound x)).1])
    have henv : sourceSingularityEnvelope η (G.potential ⟨r, hr⟩) =
        sourceSingularityEnvelope η (fun x => G.potential ⟨r, hr⟩ x - (g x : EReal)) :=
      le_antisymm (sourceOrdinaryEnvelope_mono hshift.1) (sourceOrdinaryEnvelope_mono hshift.2)
    change SGPT.PSH.SingularityEquiv (G.potential ⟨r, hr⟩)
      (sourceSingularityEnvelope η (G.potential ⟨r, hr⟩))
    rw [henv]
    exact hs
  have hq (r : ℝ) (hr : r < G.max) : IsGlobalQuasiPshPotential (n := n) (G.potential ⟨r, hr⟩) :=
    ⟨(G.native_thetaPSH ⟨r, hr⟩).1.quasiPlurisubharmonic, (G.native_thetaPSH ⟨r, hr⟩).2⟩
  have hq' (r : ℝ) (hr : r < (G.changeRepresentative omega hc).max) :
      IsGlobalQuasiPshPotential (n := n) ((G.changeRepresentative omega hc).potential ⟨r, hr⟩) :=
    ⟨((G.changeRepresentative omega hc).native_thetaPSH ⟨r, hr⟩).1.quasiPlurisubharmonic,
      ((G.changeRepresentative omega hc).native_thetaPSH ⟨r, hr⟩).2⟩
  refine ⟨⟨le_rfl, fun r hr => ?_⟩, ⟨le_rfl, fun r hr => ?_⟩⟩
  · exact GlobalPComparison.sourcePOrder_of_moreSingular omega (hq r hr) (hq' r hr)
      (hslice r hr).1
  · exact GlobalPComparison.sourcePOrder_of_moreSingular omega (hq' r hr) (hq r hr)
      (hslice r hr).2

/-- The componentwise change of representative of a non-Archimedean metric. -/
def SourceNAPotential.changeRepresentative
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceNAPotential θ) :
    SourceNAPotential η where
  component κ := sourceIModelTestCurveRepresentativeEquiv (sourceKahlerFormRepresentative κ)
    (sourceNAComponentBackground_class hc κ) (Γ.component κ)
  compatible κ ζ h := by
    let omega := sourceKahlerFormRepresentative ζ
    have hκ := ((Γ.component κ).val.changeRepresentative_POrder_equivalent
      (sourceKahlerFormRepresentative κ) (sourceNAComponentBackground_class hc κ))
    have hζ := ((Γ.component ζ).val.changeRepresentative_POrder_equivalent
      (sourceKahlerFormRepresentative ζ) (sourceNAComponentBackground_class hc ζ))
    have hΓ := Γ.component_POrder_equivalent κ ζ
    have ht := sourceIModelTestCurveTransition_POrder_equivalent omega
      (sourceNAComponentBackground_difference η h)
      (sourceIModelTestCurveRepresentativeEquiv (sourceKahlerFormRepresentative κ)
        (sourceNAComponentBackground_class hc κ) (Γ.component κ))
    apply Subtype.ext
    exact SourceTestCurvePOrder.antisymm omega
      (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega
        (SourceTestCurvePOrder.trans omega ht.2 hκ.2) hΓ.1) hζ.1)
      (SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega
        (SourceTestCurvePOrder.trans omega hζ.2 hΓ.2) hκ.1) ht.1)

theorem SourceNAPotential.changeRepresentative_component
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) :
    ((Γ.changeRepresentative hc).component κ).val =
      (Γ.component κ).val.changeRepresentative (sourceKahlerFormRepresentative κ)
        (sourceNAComponentBackground_class hc κ) := rfl

/-- Cocycle condition. -/
theorem SourceNAPotential.changeRepresentative_trans
    (hθη : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (hηξ : RealBottChern.ofRepresentative (atlasClosedFormToNative η) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative ξ)) (Γ : SourceNAPotential θ) :
    (Γ.changeRepresentative hθη).changeRepresentative hηξ =
      Γ.changeRepresentative (hθη.trans hηξ) := by
  apply SourceNAPotential.ext
  intro κ
  exact congrArg (fun e => e (Γ.component κ))
    (sourceIModelTestCurveRepresentativeEquiv_trans (sourceKahlerFormRepresentative κ)
      (sourceNAComponentBackground_class hθη κ) (sourceNAComponentBackground_class hηξ κ))

/-- The identity case of the change of representative. -/
theorem SourceNAPotential.changeRepresentative_self
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ)) (Γ : SourceNAPotential θ) :
    Γ.changeRepresentative hc = Γ := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  exact (Γ.component κ).val.changeRepresentative_self (sourceKahlerFormRepresentative κ)

/-- Source `rmk:NApotential:L47`: the canonical bijection
`PSH^NA(X, θ) ≃ PSH^NA(X, θ')` for `θ'` cohomologous to `θ`. -/
def sourceNARepresentativeEquiv
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) :
    SourceNAPotential θ ≃ SourceNAPotential η where
  toFun := SourceNAPotential.changeRepresentative hc
  invFun := SourceNAPotential.changeRepresentative hc.symm
  left_inv Γ := by
    rw [SourceNAPotential.changeRepresentative_trans, SourceNAPotential.changeRepresentative_self]
  right_inv Γ := by
    rw [SourceNAPotential.changeRepresentative_trans, SourceNAPotential.changeRepresentative_self]

/-- `PSH^NA(X, {θ}) = lim_θ PSH^NA(X, θ)`: compatible families indexed by all representatives
`θ'` of the class of `θ`. -/
structure SourceNAClassPotential (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) where
  family : ∀ (θ' : AtlasClosedRealOneOneForm (ofFixedModel n M)),
    RealBottChern.ofRepresentative (atlasClosedFormToNative θ') =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ) → SourceNAPotential θ'
  compatible : ∀ (θ' θ'' : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (h' : RealBottChern.ofRepresentative (atlasClosedFormToNative θ') =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ))
    (h'' : RealBottChern.ofRepresentative (atlasClosedFormToNative θ'') =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ)),
    (family θ' h').changeRepresentative (h'.trans h''.symm) = family θ'' h''

theorem SourceNAClassPotential.ext {P Q : SourceNAClassPotential θ}
    (h : ∀ θ' h', P.family θ' h' = Q.family θ' h') : P = Q := by
  cases P with
  | mk f hf =>
    cases Q with
    | mk g hg =>
      have hfg : f = g := funext fun θ' => funext fun h' => h θ' h'
      subst hfg
      rfl

/-- The projective limit over the representatives is in bijection with `PSH^NA(X, θ)`; hence
it does not depend on the representative. -/
def sourceNAClassPotentialEquiv (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    SourceNAClassPotential θ ≃ SourceNAPotential θ where
  toFun P := P.family θ rfl
  invFun Γ := ⟨fun θ' h' => Γ.changeRepresentative h'.symm, fun θ' θ'' h' h'' => by
    rw [SourceNAPotential.changeRepresentative_trans]⟩
  left_inv P := SourceNAClassPotential.ext fun θ' h' => P.compatible θ θ' rfl h'
  right_inv Γ := SourceNAPotential.changeRepresentative_self rfl Γ

end SGPT.PSH.VariableComplexAtlas

import SGPT.NAPotential.ModificationEquiv
import SGPT.NAPotential.DecreasingInfimum
import SGPT.PSH.SourceNATranslation
import SGPT.PSH.SourceTestCurveGeneralLaws
import SGPT.PSH.SourceNAPositiveScaling
import SGPT.PSH.SourceNASum

/-! # The operations on `PSH^NA` are invariant under pullback to a modification

Source `prop:NApotential:L655` (`chapter_NApotential.tex`): for a proper bimeromorphic morphism
`π : Y → X` from a compact Kähler manifold `Y`, *all definitions in this section are invariant
under pullback to `Y`*.  The pullback `π^* : PSH^NA(X, θ) ≃ PSH^NA(Y, π^*θ)` is the bijection of
`cor:PSHNAbimero` (`WholeClosureNA.sourceNAPullback`, with inverse `sourceNADescent`).  This file
proves its compatibility with the order, the cutoff `Γ_max` and the operations of `sec:opnA`
that are characterized by the order or defined slicewise:

* the order of `def:NApotential:L274` (already `sourceNAPOrder_pullback_iff`);
* `sourceNAPotentialCutoff_pullback`: `(π^*Γ)_max = Γ_max`;
* `sourceNAPullback_join` (`def:PSHNAlor`), `sourceNAPullback_uscSup`
  (`def:NApotential:L413`), `sourceNAPullback_decreasingInf` (`def:NApotential:L525`) and
  `sourceNAPullback_translate` (`def:NApotential:L341`): `π^*` commutes with maxima, usc suprema,
  decreasing infima and translations;
* `sourceNAPullback_positiveScale_POrder_equivalent`, `sourceNAPullback_positiveScale`
  (`def:NApotential:L572`): `π^*(cΓ) = c π^*Γ`, after the identification
  `π^*(cθ) = c π^*θ` of the backgrounds (`nativeHolomorphicPullback_scaledBackground`).

* `sourceNAPullback_sum_POrder_equivalent`, `sourceNAPullback_sum` (`def:sumNAmetrics`):
  `π^*(Γ + Δ) = π^*Γ + π^*Δ`, after the identification `π^*(θ + σ) = π^*θ + π^*σ`.

The volumes (`def:NApotential:L102`) and the trace operator (`def:NApotential:L623`, the case
treated in the book's proof) are not covered here.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.PSH.VariableComplexAtlas.WholeClosureNA

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {π : Y → X}

/-- The pullback to a modification preserves `Γ_max`. -/
theorem sourceNAPotentialCutoff_pullback (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) :
    sourceNAPotentialCutoff omegaY (sourceNAPullback omegaX hπ Γ) =
      sourceNAPotentialCutoff omegaX Γ := by
  change (sourceNAPullbackComponent omegaX hπ Γ (sourceKahlerFormOfBackground omegaY)).val.max = _
  unfold sourceNAPullbackComponent
  rw [sourceIModelTestCurveTransition_max]
  exact Γ.realizedComponent_max_eq_cutoff omegaX _

/-- The pullback commutes with the maximum `Γ ∨ Δ` of `def:PSHNAlor`. -/
theorem sourceNAPullback_join (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) (Γ Δ : SourceNAPotential θ) :
    sourceNAPullback omegaX hπ (Γ.join Δ) =
      (sourceNAPullback omegaX hπ Γ).join (sourceNAPullback omegaX hπ Δ) := by
  have hiff := sourceNAPOrder_pullback_iff (θ := θ) (σ := θ) omegaX omegaY hπ
  let J := (sourceNAPullback omegaX hπ Γ).join (sourceNAPullback omegaX hπ Δ)
  let Ξ := sourceNADescent omegaX omegaY hπ J
  have hΞ : sourceNAPullback omegaX hπ Ξ = J := sourceNAPullback_descent omegaX omegaY hπ J
  apply SourceNAPOrder.antisymm
  · have hle : SourceNAPOrder (Γ.join Δ) Ξ := by
      apply SourceNAPotential.join_le
      · apply (hiff Γ Ξ).mpr
        rw [hΞ]
        exact (sourceNAPullback omegaX hπ Γ).le_join_left _ omegaY
      · apply (hiff Δ Ξ).mpr
        rw [hΞ]
        exact (sourceNAPullback omegaX hπ Γ).le_join_right _ omegaY
    have h := (hiff _ _).mp hle
    rwa [hΞ] at h
  · exact SourceNAPotential.join_le ((hiff _ _).mp (Γ.le_join_left Δ omegaX))
      ((hiff _ _).mp (Γ.le_join_right Δ omegaX))

/-- The cutoffs of a family stay bounded above after pullback. -/
theorem sourceNAPullback_bddAbove {I : Type*} (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omegaX (Γ i))) :
    BddAbove (range fun i =>
      sourceNAPotentialCutoff omegaY (sourceNAPullback omegaX hπ (Γ i))) := by
  simp_rw [sourceNAPotentialCutoff_pullback omegaX omegaY hπ]
  exact hb

/-- The cutoffs of a family stay bounded below after pullback. -/
theorem sourceNAPullback_bddBelow {I : Type*} (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    (Γ : I → SourceNAPotential θ)
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (Γ i))) :
    BddBelow (range fun i =>
      sourceNAPotentialCutoff omegaY (sourceNAPullback omegaX hπ (Γ i))) := by
  simp_rw [sourceNAPotentialCutoff_pullback omegaX omegaY hπ]
  exact hb

/-- The pullback commutes with the usc supremum of `def:NApotential:L413`. -/
theorem sourceNAPullback_uscSup {I : Type*} [Nonempty I] (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omegaX (Γ i))) :
    sourceNAPullback omegaX hπ (SourceNAPotential.uscSup omegaX Γ hb) =
      SourceNAPotential.uscSup omegaY (fun i => sourceNAPullback omegaX hπ (Γ i))
        (sourceNAPullback_bddAbove omegaX omegaY hπ Γ hb) := by
  have hiff := sourceNAPOrder_pullback_iff (θ := θ) (σ := θ) omegaX omegaY hπ
  let S := SourceNAPotential.uscSup omegaY (fun i => sourceNAPullback omegaX hπ (Γ i))
    (sourceNAPullback_bddAbove omegaX omegaY hπ Γ hb)
  let Ξ := sourceNADescent omegaX omegaY hπ S
  have hΞ : sourceNAPullback omegaX hπ Ξ = S := sourceNAPullback_descent omegaX omegaY hπ S
  apply SourceNAPOrder.antisymm
  · have hle : SourceNAPOrder (SourceNAPotential.uscSup omegaX Γ hb) Ξ := by
      apply SourceNAPotential.uscSup_le omegaX Γ hb Ξ
      intro i
      apply (hiff (Γ i) Ξ).mpr
      rw [hΞ]
      exact SourceNAPotential.le_uscSup omegaY (fun i => sourceNAPullback omegaX hπ (Γ i))
        (sourceNAPullback_bddAbove omegaX omegaY hπ Γ hb) i
    have h := (hiff _ _).mp hle
    rwa [hΞ] at h
  · apply SourceNAPotential.uscSup_le omegaY _ _ _
    intro i
    exact (hiff _ _).mp (SourceNAPotential.le_uscSup omegaX Γ hb i)

/-- The pullback commutes with the decreasing infimum of `def:NApotential:L525`. -/
theorem sourceNAPullback_decreasingInf {I : Type*} [Nonempty I] [Preorder I] [IsDirectedOrder I]
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omegaX (Γ i))) :
    sourceNAPullback omegaX hπ (SourceNAPotential.decreasingInf omegaX Γ ha hb) =
      SourceNAPotential.decreasingInf omegaY (fun i => sourceNAPullback omegaX hπ (Γ i))
        (fun i j hij => (sourceNAPOrder_pullback_iff omegaX omegaY hπ _ _).mp (ha i j hij))
        (sourceNAPullback_bddBelow omegaX omegaY hπ Γ hb) := by
  have hiff := sourceNAPOrder_pullback_iff (θ := θ) (σ := θ) omegaX omegaY hπ
  let ha' : ∀ i j, i ≤ j →
      SourceNAPOrder (sourceNAPullback omegaX hπ (Γ j)) (sourceNAPullback omegaX hπ (Γ i)) :=
    fun i j hij => (hiff _ _).mp (ha i j hij)
  let D := SourceNAPotential.decreasingInf omegaY (fun i => sourceNAPullback omegaX hπ (Γ i)) ha'
    (sourceNAPullback_bddBelow omegaX omegaY hπ Γ hb)
  let Ξ := sourceNADescent omegaX omegaY hπ D
  have hΞ : sourceNAPullback omegaX hπ Ξ = D := sourceNAPullback_descent omegaX omegaY hπ D
  apply SourceNAPOrder.antisymm
  · exact SourceNAPotential.le_decreasingInf omegaY _ ha' _ _
      fun i => (hiff _ _).mp (SourceNAPotential.decreasingInf_le omegaX Γ ha hb i)
  · have hle : SourceNAPOrder Ξ (SourceNAPotential.decreasingInf omegaX Γ ha hb) := by
      apply SourceNAPotential.le_decreasingInf omegaX Γ ha hb Ξ
      intro i
      apply (hiff Ξ (Γ i)).mpr
      rw [hΞ]
      exact SourceNAPotential.decreasingInf_le omegaY _ ha' _ i
    have h := (hiff _ _).mp hle
    rwa [hΞ] at h

omit [ConnectedSpace Y] in
/-- Pullback of test curves commutes with translation. -/
theorem modificationPullback_translate_curve (hπ : IsAnalyticModification (n := n) π)
    (G : SourceTestCurve θ) (C : ℝ) :
    (G.translate C).modificationPullback hπ = (G.modificationPullback hπ).translate C := by
  apply SourceTestCurve.ext_of_max_potential
  · rfl
  · intro r hr hs
    rfl

/-- The pullback commutes with the translation `Γ + C` of `def:NApotential:L341`. -/
theorem sourceNAPullback_translate (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) (C : ℝ) :
    sourceNAPullback omegaX hπ (Γ.translate C) = (sourceNAPullback omegaX hπ Γ).translate C := by
  let κ := sourceKahlerFormOfBackground omegaY
  have hA := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ (Γ.translate C) κ omegaX
  have hB := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ Γ κ omegaX
  have hR : ((Γ.translate C).realizedComponent omegaX).val.modificationPullback hπ =
      (((Γ.realizedComponent omegaX).val.modificationPullback hπ).translate C) := by
    rw [SourceNAPotential.translate_realizedComponent]
    exact modificationPullback_translate_curve hπ _ C
  rw [hR] at hA
  have hB1 := hB.1.translate C
  have hB2 := hB.2.translate C
  apply SourceNAPOrder.antisymm
  · exact ⟨κ, SourceTestCurvePOrder.trans omegaY hA.1 hB2⟩
  · exact ⟨κ, SourceTestCurvePOrder.trans omegaY hB1 hA.2⟩

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] in
/-- The pullback of `c θ` is `c π^*θ`. -/
theorem nativeHolomorphicPullback_scaledBackground (hπ : IsAnalyticModification (n := n) π)
    (c : ℝ) :
    (sourceNAScaledBackground θ c).nativeHolomorphicPullback hπ.1 =
      sourceNAScaledBackground (θ.nativeHolomorphicPullback hπ.1) c := by
  unfold sourceNAScaledBackground AtlasClosedRealOneOneForm.nativeHolomorphicPullback
  rw [sourceNativeAtlasForm_roundTrip, sourceNativeAtlasForm_roundTrip]
  congr 1

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Two test curves with the same cutoff and literally the same slices have the same
intrinsic type. -/
theorem sourceTestCurvePOrder_of_eq_slices (omegaY : KahlerBackground n Y)
    {α β : AtlasClosedRealOneOneForm (ofFixedModel n Y)} {G : SourceTestCurve α}
    {H : SourceTestCurve β} (hmax : G.max = H.max)
    (hpot : ∀ (r : ℝ) (hr : r < G.max) (hs : r < H.max),
      G.potential ⟨r, hr⟩ = H.potential ⟨r, hs⟩) :
    SourceTestCurvePOrder G H := by
  refine ⟨hmax.le, fun r hr => ?_⟩
  rw [hpot r hr (hr.trans_le hmax.le)]
  exact SingularGlobalPOrder.sourcePOrder_refl_of_isThetaPshPotential omegaY
    (H.native_thetaPSH ⟨r, hr.trans_le hmax.le⟩)

/-- Pullback of test curves commutes with positive rescaling, up to the identification of the
backgrounds: both curves have the same slices `y ↦ c Γ_{τ/c}(π y)`. -/
theorem modificationPullback_positiveScale_POrder_equivalent (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) (G : SourceTestCurve θ) {c : ℝ} (hc : 0 < c) :
    SourceTestCurvePOrder ((G.positiveScale hc).modificationPullback hπ)
        ((G.modificationPullback hπ).positiveScale hc) ∧
      SourceTestCurvePOrder ((G.modificationPullback hπ).positiveScale hc)
        ((G.positiveScale hc).modificationPullback hπ) :=
  ⟨sourceTestCurvePOrder_of_eq_slices omegaY rfl fun _ _ _ => rfl,
    sourceTestCurvePOrder_of_eq_slices omegaY rfl fun _ _ _ => rfl⟩

/-- The pullback commutes with the positive rescaling `Γ ↦ cΓ` of `def:NApotential:L572`, in
the intrinsic sense: `π^*(cΓ)` and `c π^*Γ` lie below each other. -/
theorem sourceNAPullback_positiveScale_POrder_equivalent (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) :
    SourceNAPOrder (sourceNAPullback omegaX hπ (Γ.positiveScale hc))
        ((sourceNAPullback omegaX hπ Γ).positiveScale hc) ∧
      SourceNAPOrder ((sourceNAPullback omegaX hπ Γ).positiveScale hc)
        (sourceNAPullback omegaX hπ (Γ.positiveScale hc)) := by
  let κY := sourceKahlerFormOfBackground omegaY
  let D := sourceNADividedKahlerBackground hc omegaX
  -- the left side: `π^*(cΓ)`
  have hL1 := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ (Γ.positiveScale hc)
    κY omegaX
  have hL2 := (Γ.positiveScale hc).realizedComponent_component_POrder_equivalent omegaX
    (sourceKahlerFormOfBackground omegaX)
  have hL3 := Γ.positiveScaleComponent_POrder_equivalent_reader hc
    (sourceKahlerFormOfBackground omegaX) omegaX
  have hL23a := SourceTestCurvePOrder.trans omegaX hL2.1 hL3.1
  have hL23b := SourceTestCurvePOrder.trans omegaX hL3.2 hL2.2
  have hL4a := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hL23a
  have hL4b := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hL23b
  have hL5 := modificationPullback_positiveScale_POrder_equivalent omegaY hπ
    (Γ.realizedComponent D).val hc
  -- the right side: `c π^*Γ`
  let P := sourceNAPullback omegaX hπ Γ
  let DY := sourceNADividedKahlerBackground hc omegaY
  have hR1 := P.positiveScaleComponent_POrder_equivalent_reader hc κY omegaY
  have hR2 := P.realizedComponent_component_POrder_equivalent DY
    (sourceKahlerFormOfBackground DY)
  have hR3 := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ Γ
    (sourceKahlerFormOfBackground DY) D
  have hR23a := SourceTestCurvePOrder.trans omegaY hR2.1 hR3.1
  have hR23b := SourceTestCurvePOrder.trans omegaY hR3.2 hR2.2
  have hR4a := hR23a.positiveScale hc
  have hR4b := hR23b.positiveScale hc
  refine ⟨⟨κY, ?_⟩, ⟨κY, ?_⟩⟩
  · change SourceTestCurvePOrder (sourceNAPullbackComponent omegaX hπ (Γ.positiveScale hc) κY).val
      (P.positiveScaleComponent hc κY).val
    exact SourceTestCurvePOrder.trans omegaY hL1.1 (SourceTestCurvePOrder.trans omegaY hL4a
      (SourceTestCurvePOrder.trans omegaY hL5.1 (SourceTestCurvePOrder.trans omegaY hR4b hR1.2)))
  · change SourceTestCurvePOrder (P.positiveScaleComponent hc κY).val
      (sourceNAPullbackComponent omegaX hπ (Γ.positiveScale hc) κY).val
    exact SourceTestCurvePOrder.trans omegaY hR1.1 (SourceTestCurvePOrder.trans omegaY hR4a
      (SourceTestCurvePOrder.trans omegaY hL5.2 (SourceTestCurvePOrder.trans omegaY hL4b hL1.2)))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Intrinsically equivalent metrics in equal backgrounds are equal after transport. -/
theorem eq_cast_of_POrder_equivalent {α β : AtlasClosedRealOneOneForm (ofFixedModel n Y)}
    (h : α = β) {A : SourceNAPotential α} {B : SourceNAPotential β}
    (h1 : SourceNAPOrder A B) (h2 : SourceNAPOrder B A) : h ▸ A = B := by
  subst h
  exact SourceNAPOrder.antisymm h1 h2

/-- The pullback commutes with the positive rescaling of `def:NApotential:L572`:
`π^*(cΓ) = c π^*Γ` under the identification `π^*(cθ) = c π^*θ`. -/
theorem sourceNAPullback_positiveScale (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c) :
    nativeHolomorphicPullback_scaledBackground (θ := θ) hπ c ▸
        sourceNAPullback omegaX hπ (Γ.positiveScale hc) =
      (sourceNAPullback omegaX hπ Γ).positiveScale hc := by
  have h := sourceNAPullback_positiveScale_POrder_equivalent omegaX omegaY hπ Γ hc
  exact eq_cast_of_POrder_equivalent (nativeHolomorphicPullback_scaledBackground (θ := θ) hπ c)
    h.1 h.2

/-! ### Sums -/

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y] in
/-- The pullback of `θ + σ` is `π^*θ + π^*σ`. -/
theorem nativeHolomorphicPullback_add (hπ : IsAnalyticModification (n := n) π)
    (σ : AtlasClosedRealOneOneForm (ofFixedModel n X)) :
    (θ.add σ).nativeHolomorphicPullback hπ.1 =
      (θ.nativeHolomorphicPullback hπ.1).add (σ.nativeHolomorphicPullback hπ.1) := by
  apply Function.LeftInverse.injective (fun T => sourceAtlasNativeForm_roundTrip T)
  simp only [AtlasClosedRealOneOneForm.nativeHolomorphicPullback, sourceNativeClosedForm_add,
    sourceNativeAtlasForm_roundTrip]
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace Y] [ConnectedSpace Y] in
/-- Evaluating a pulled-back curve at any parameter (including the cutoff and beyond) is
evaluating the original curve at the image point. -/
theorem sourceTestCurveAt_modificationPullback (hπ : IsAnalyticModification (n := n) π)
    (G : SourceTestCurvePredata θ) (τ : ℝ) :
    sourceTestCurveAt (G.modificationPullback hπ) τ = sourceTestCurveAt G τ ∘ π := by
  funext y
  change (if hτ : τ < G.max then (G.modificationPullback hπ).potential ⟨τ, hτ⟩
      else if τ = G.max then sourceTestCurveCutoff (G.modificationPullback hπ) else ⊥) y =
    (if hτ : τ < G.max then G.potential ⟨τ, hτ⟩
      else if τ = G.max then sourceTestCurveCutoff G else ⊥) (π y)
  split_ifs <;> rfl

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace Y] [ConnectedSpace Y] in
/-- The raw sum of pulled-back curves is the pullback of the raw sum. -/
theorem sourceTestCurveRawSum_modificationPullback (hπ : IsAnalyticModification (n := n) π)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (G : SourceTestCurvePredata θ) (H : SourceTestCurvePredata σ) (τ : ℝ) :
    sourceTestCurveRawSum (G.modificationPullback hπ) (H.modificationPullback hπ) τ =
      sourceTestCurveRawSum G H τ ∘ π := by
  funext y
  unfold sourceTestCurveRawSum
  simp only [sourceTestCurveAt_modificationPullback, Function.comp_apply]

/-- Pullback of test curves commutes with their sum, up to the identification of the
backgrounds: corresponding slices are `P`-equivalent. -/
theorem modificationPullback_sum_POrder_equivalent (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (G : SourceTestCurve θ) (H : SourceTestCurve σ) :
    SourceTestCurvePOrder ((SourceTestCurve.sum omegaX G H).modificationPullback hπ)
        (SourceTestCurve.sum omegaY (G.modificationPullback hπ) (H.modificationPullback hπ)) ∧
      SourceTestCurvePOrder
        (SourceTestCurve.sum omegaY (G.modificationPullback hπ) (H.modificationPullback hπ))
        ((SourceTestCurve.sum omegaX G H).modificationPullback hπ) := by
  have hs (r : ℝ) (hr : r < G.max + H.max) :
      SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := n)
        (((SourceTestCurve.sum omegaX G H).modificationPullback hπ).potential ⟨r, hr⟩)
        ((SourceTestCurve.sum omegaY (G.modificationPullback hπ)
          (H.modificationPullback hπ)).potential ⟨r, hr⟩) := by
    have hX := SourceTestCurve.sum_slice_raw_PEquivalent omegaX G H r hr
    have hY := SourceTestCurve.sum_slice_raw_PEquivalent omegaY (G.modificationPullback hπ)
      (H.modificationPullback hπ) r hr
    rw [show sourceTestCurveRawSum (G.modificationPullback hπ).toSourceTestCurvePredata
        (H.modificationPullback hπ).toSourceTestCurvePredata r =
        sourceTestCurveRawSum G.toSourceTestCurvePredata H.toSourceTestCurvePredata r ∘ π from
      sourceTestCurveRawSum_modificationPullback hπ G.toSourceTestCurvePredata
        H.toSourceTestCurvePredata r] at hY
    have hq1 : (ofFixedModel n X).IsQPSH ((SourceTestCurve.sum omegaX G H).potential ⟨r, hr⟩) :=
      ⟨_, (SourceTestCurve.sum omegaX G H).thetaPSH ⟨r, hr⟩⟩
    have hq2 : (ofFixedModel n X).IsQPSH
        (sourceTestCurveRawSum G.toSourceTestCurvePredata H.toSourceTestCurvePredata r) :=
      ⟨_, sourceTestCurveRawSum_thetaPSH G.toSourceTestCurvePredata H.toSourceTestCurvePredata
        hr.le⟩
    have hp1 := (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff omegaX omegaY
      hπ hq1 hq2).mp hX.1
    have hp2 := (SGPT.PSH.ModificationOrders.sourcePOrder_modification_pullback_iff omegaX omegaY
      hπ hq2 hq1).mp hX.2
    exact ⟨SGPT.PSH.GlobalPComparison.sourcePOrder_trans omegaY hp1 hY.2,
      SGPT.PSH.GlobalPComparison.sourcePOrder_trans omegaY hY.1 hp2⟩
  exact ⟨⟨le_rfl, fun r hr => (hs r hr).1⟩, ⟨le_rfl, fun r hr => (hs r hr).2⟩⟩

/-- The pullback commutes with the sum of `def:sumNAmetrics`, in the intrinsic sense:
`π^*(Γ + Δ)` and `π^*Γ + π^*Δ` lie below each other. -/
theorem sourceNAPullback_sum_POrder_equivalent (omegaX : KahlerBackground n X)
    (omegaY : KahlerBackground n Y) (hπ : IsAnalyticModification (n := n) π)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    SourceNAPOrder (sourceNAPullback omegaX hπ (Γ.sum Δ))
        ((sourceNAPullback omegaX hπ Γ).sum (sourceNAPullback omegaX hπ Δ)) ∧
      SourceNAPOrder ((sourceNAPullback omegaX hπ Γ).sum (sourceNAPullback omegaX hπ Δ))
        (sourceNAPullback omegaX hπ (Γ.sum Δ)) := by
  let κY := sourceKahlerFormOfBackground omegaY
  let κX := sourceKahlerFormOfBackground omegaX
  let P := sourceNAPullback omegaX hπ Γ
  let Q := sourceNAPullback omegaX hπ Δ
  -- left side
  have hL1 := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ (Γ.sum Δ) κY omegaX
  have hL2 := (Γ.sum Δ).realizedComponent_component_POrder_equivalent omegaX κX
  have hL3 := Γ.sumComponent_POrder_equivalent_sum Δ κX omegaX omegaX
  have hL23a := SourceTestCurvePOrder.trans omegaX hL2.1 hL3.1
  have hL23b := SourceTestCurvePOrder.trans omegaX hL3.2 hL2.2
  have hL4a := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hL23a
  have hL4b := (curvePOrder_modificationPullback_iff omegaX omegaY hπ _ _).mp hL23b
  have hL5 := modificationPullback_sum_POrder_equivalent omegaX omegaY hπ
    (Γ.realizedComponent omegaX).val (Δ.realizedComponent omegaX).val
  -- right side
  have hR1 := P.sumComponent_POrder_equivalent_sum Q κY omegaY omegaY
  have hP1 := P.realizedComponent_component_POrder_equivalent omegaY κY
  have hP2 := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ Γ κY omegaX
  have hQ1 := Q.realizedComponent_component_POrder_equivalent omegaY κY
  have hQ2 := sourceNAPullbackComponent_POrder_equivalent_reader omegaX hπ Δ κY omegaX
  have hR2 := SourceTestCurve.sum_POrder_equivalent omegaY omegaY
    (P.realizedComponent omegaY).val (Q.realizedComponent omegaY).val
    ((Γ.realizedComponent omegaX).val.modificationPullback hπ)
    ((Δ.realizedComponent omegaX).val.modificationPullback hπ)
    (SourceTestCurvePOrder.trans omegaY hP1.1 hP2.1)
    (SourceTestCurvePOrder.trans omegaY hP2.2 hP1.2)
    (SourceTestCurvePOrder.trans omegaY hQ1.1 hQ2.1)
    (SourceTestCurvePOrder.trans omegaY hQ2.2 hQ1.2)
  refine ⟨⟨κY, ?_⟩, ⟨κY, ?_⟩⟩
  · change SourceTestCurvePOrder (sourceNAPullbackComponent omegaX hπ (Γ.sum Δ) κY).val
      (P.sumComponent Q κY).val
    exact SourceTestCurvePOrder.trans omegaY hL1.1 (SourceTestCurvePOrder.trans omegaY hL4a
      (SourceTestCurvePOrder.trans omegaY hL5.1 (SourceTestCurvePOrder.trans omegaY hR2.2
        hR1.2)))
  · change SourceTestCurvePOrder (P.sumComponent Q κY).val
      (sourceNAPullbackComponent omegaX hπ (Γ.sum Δ) κY).val
    exact SourceTestCurvePOrder.trans omegaY hR1.1 (SourceTestCurvePOrder.trans omegaY hR2.1
      (SourceTestCurvePOrder.trans omegaY hL5.2 (SourceTestCurvePOrder.trans omegaY hL4b
        hL1.2)))

/-- The pullback commutes with the sum of `def:sumNAmetrics`: `π^*(Γ + Δ) = π^*Γ + π^*Δ` under
the identification `π^*(θ + σ) = π^*θ + π^*σ`. -/
theorem sourceNAPullback_sum (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (hπ : IsAnalyticModification (n := n) π) {σ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    nativeHolomorphicPullback_add (θ := θ) hπ σ ▸ sourceNAPullback omegaX hπ (Γ.sum Δ) =
      (sourceNAPullback omegaX hπ Γ).sum (sourceNAPullback omegaX hπ Δ) := by
  have h := sourceNAPullback_sum_POrder_equivalent omegaX omegaY hπ Γ Δ
  exact eq_cast_of_POrder_equivalent (nativeHolomorphicPullback_add (θ := θ) hπ σ) h.1 h.2

end SGPT.PSH.VariableComplexAtlas.WholeClosureNA

end

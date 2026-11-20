import SGPT.NAPotential.RepresentativeChange
import SGPT.NAPotential.DecreasingInfimum
import SGPT.PSH.SourceNATranslation
import SGPT.PSH.SourceNAPositiveScaling

/-! # The constructions on `PSH^NA(X, θ)` do not depend on the representative `θ`

Source `rmk:NApotential:L47` (`chapter_NApotential.tex`), closing sentence: *the constructions
below are independent of the choice of `θ` within its cohomology class*.  The canonical bijection
`PSH^NA(X, θ) ≃ PSH^NA(X, θ')` of the remark is `SourceNAPotential.changeRepresentative`
(componentwise `prop:Imodeltestcurveindeptheta`).  This file shows that it is compatible with
the constructions of `sec:opnA`:

* `SourceNAPotential.changeRepresentative_POrder_equivalent`: `Γ` and its image have the same
  intrinsic type; hence `sourceNAPOrder_changeRepresentative_iff`: the bijection preserves and
  reflects the order of `def:NApotential:L274` (even between different classes);
* `sourceNAPotentialCutoff_changeRepresentative`: it preserves `Γ_max`;
* `SourceNAPotential.changeRepresentative_join` (`def:PSHNAlor`),
  `SourceNAPotential.changeRepresentative_uscSup` (`def:NApotential:L413`),
  `SourceNAPotential.changeRepresentative_decreasingInf` (`def:NApotential:L525`),
  `SourceNAPotential.changeRepresentative_translate` (`def:NApotential:L341`): it commutes with
  maxima, usc suprema, decreasing infima and translations;
* `SourceNAPotential.changeRepresentative_sum` (`def:sumNAmetrics`),
  `SourceNAPotential.changeRepresentative_positiveScale` (`def:NApotential:L572`): it commutes
  with sums (changing both summands' representatives) and positive rescalings;
* `sourceNAVolume_changeRepresentative` (`def:NApotential:L102`): it preserves the volume.

The trace operator (`def:NApotential:L623`) and the Duistermaat–Heckman measures are not
treated here.
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
  {θ η σ σ' : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- `Γ` and its image under the change of representative have the same intrinsic type:
each lies below the other in the order of `def:NApotential:L274`. -/
theorem SourceNAPotential.changeRepresentative_POrder_equivalent
    (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceNAPotential θ) :
    SourceNAPOrder Γ (Γ.changeRepresentative hc) ∧
      SourceNAPOrder (Γ.changeRepresentative hc) Γ := by
  let κ := sourceKahlerFormOfBackground omega
  have h := (Γ.component κ).val.changeRepresentative_POrder_equivalent
    (sourceKahlerFormRepresentative κ) (sourceNAComponentBackground_class hc κ)
  refine ⟨⟨κ, ?_⟩, ⟨κ, ?_⟩⟩
  · rw [SourceNAPotential.changeRepresentative_component]
    exact h.1
  · rw [SourceNAPotential.changeRepresentative_component]
    exact h.2

/-- The change of representative preserves and reflects the order of `def:NApotential:L274`,
also between metrics in different classes. -/
theorem sourceNAPOrder_changeRepresentative_iff (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (hc' : RealBottChern.ofRepresentative (atlasClosedFormToNative σ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative σ'))
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    SourceNAPOrder Γ Δ ↔
      SourceNAPOrder (Γ.changeRepresentative hc) (Δ.changeRepresentative hc') := by
  have hΓ := Γ.changeRepresentative_POrder_equivalent omega hc
  have hΔ := Δ.changeRepresentative_POrder_equivalent omega hc'
  constructor
  · exact fun h => (hΓ.2.trans h).trans hΔ.1
  · exact fun h => (hΓ.1.trans h).trans hΔ.2

/-- The change of representative preserves `Γ_max`. -/
theorem sourceNAPotentialCutoff_changeRepresentative (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceNAPotential θ) :
    sourceNAPotentialCutoff omega (Γ.changeRepresentative hc) = sourceNAPotentialCutoff omega Γ :=
  rfl

/-- The change of representative commutes with the maximum `Γ ∨ Δ` of `def:PSHNAlor`. -/
theorem SourceNAPotential.changeRepresentative_join (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ Δ : SourceNAPotential θ) :
    (Γ.join Δ).changeRepresentative hc =
      (Γ.changeRepresentative hc).join (Δ.changeRepresentative hc) := by
  let J := (Γ.changeRepresentative hc).join (Δ.changeRepresentative hc)
  have hJ := J.changeRepresentative_POrder_equivalent omega hc.symm
  have hJΓ := Γ.changeRepresentative_POrder_equivalent omega hc
  have hJΔ := Δ.changeRepresentative_POrder_equivalent omega hc
  have hJJ := (Γ.join Δ).changeRepresentative_POrder_equivalent omega hc
  apply SourceNAPOrder.antisymm
  · have hle : SourceNAPOrder (Γ.join Δ) (J.changeRepresentative hc.symm) :=
      SourceNAPotential.join_le
        ((hJΓ.1.trans ((Γ.changeRepresentative hc).le_join_left _ omega)).trans hJ.1)
        ((hJΔ.1.trans ((Γ.changeRepresentative hc).le_join_right _ omega)).trans hJ.1)
    exact (hJJ.2.trans hle).trans hJ.2
  · exact SourceNAPotential.join_le
      ((hJΓ.2.trans (Γ.le_join_left Δ omega)).trans hJJ.1)
      ((hJΔ.2.trans (Γ.le_join_right Δ omega)).trans hJJ.1)

/-- The change of representative commutes with the usc supremum of `def:NApotential:L413`. -/
theorem SourceNAPotential.changeRepresentative_uscSup {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) :
    (SourceNAPotential.uscSup omega Γ hb).changeRepresentative hc =
      SourceNAPotential.uscSup omega (fun i => (Γ i).changeRepresentative hc) hb := by
  let S := SourceNAPotential.uscSup omega (fun i => (Γ i).changeRepresentative hc) hb
  have hS := (SourceNAPotential.uscSup omega Γ hb).changeRepresentative_POrder_equivalent omega hc
  have hΓ (i : I) := (Γ i).changeRepresentative_POrder_equivalent omega hc
  apply SourceNAPOrder.antisymm
  · refine hS.2.trans (SourceNAPotential.uscSup_le omega Γ hb S fun i => ?_)
    exact (hΓ i).1.trans (SourceNAPotential.le_uscSup omega
      (fun i => (Γ i).changeRepresentative hc) hb i)
  · refine SourceNAPotential.uscSup_le omega (fun i => (Γ i).changeRepresentative hc) hb _
      fun i => ?_
    exact ((hΓ i).2.trans (SourceNAPotential.le_uscSup omega Γ hb i)).trans hS.1

/-- The change of representative commutes with the decreasing infimum of
`def:NApotential:L525`. -/
theorem SourceNAPotential.changeRepresentative_decreasingInf {I : Type*} [Nonempty I]
    [Preorder I] [IsDirectedOrder I] (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i))) :
    (SourceNAPotential.decreasingInf omega Γ ha hb).changeRepresentative hc =
      SourceNAPotential.decreasingInf omega (fun i => (Γ i).changeRepresentative hc)
        (fun i j hij => (sourceNAPOrder_changeRepresentative_iff omega hc hc _ _).mp (ha i j hij))
        hb := by
  let ha' : ∀ i j, i ≤ j →
      SourceNAPOrder ((Γ j).changeRepresentative hc) ((Γ i).changeRepresentative hc) :=
    fun i j hij => (sourceNAPOrder_changeRepresentative_iff omega hc hc _ _).mp (ha i j hij)
  let D := SourceNAPotential.decreasingInf omega (fun i => (Γ i).changeRepresentative hc) ha' hb
  have hD := (SourceNAPotential.decreasingInf omega Γ ha hb).changeRepresentative_POrder_equivalent
    omega hc
  have hΓ (i : I) := (Γ i).changeRepresentative_POrder_equivalent omega hc
  apply SourceNAPOrder.antisymm
  · refine SourceNAPotential.le_decreasingInf omega _ ha' hb _ fun i => ?_
    exact (hD.2.trans (SourceNAPotential.decreasingInf_le omega Γ ha hb i)).trans (hΓ i).1
  · refine (SourceNAPotential.le_decreasingInf omega Γ ha hb D fun i => ?_).trans hD.1
    exact (SourceNAPotential.decreasingInf_le omega _ ha' hb i).trans (hΓ i).2

/-- The change of representative commutes with the translation `Γ + C` of
`def:NApotential:L341`. -/
theorem SourceNAPotential.changeRepresentative_translate
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceNAPotential θ) (C : ℝ) :
    (Γ.translate C).changeRepresentative hc = (Γ.changeRepresentative hc).translate C := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · rfl
  · intro r hr hs
    rfl

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem singularityEquiv_sub_bounded (u : M → EReal) (g : M → ℝ)
    (B : ℝ) (hB : ∀ x, |g x| ≤ B) :
    SGPT.PSH.SingularityEquiv u (fun x ↦ u x - (g x : EReal)) := by
  refine ⟨⟨B, fun x _ ↦ ?_⟩, ⟨B, fun x _ ↦ ?_⟩⟩
  · have h := add_le_add (le_refl (u x - (g x : EReal)))
      (EReal.coe_le_coe_iff.mpr (abs_le.mp (hB x)).2)
    simpa only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
      neg_add_cancel, EReal.coe_zero, add_zero] using h
  · change u x + -(g x : EReal) ≤ u x + (B : EReal)
    apply add_le_add le_rfl
    rw [← EReal.coe_neg]
    exact EReal.coe_le_coe_iff.mpr (by linarith [(abs_le.mp (hB x)).1])

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- For a `θ`-model potential `φ` and a cohomologous `η`, the envelope `P_η[φ]` has the
singularity type of `φ`. -/
theorem singularityEquiv_sourceSingularityEnvelope_of_cohomologous
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hfix : sourceSingularityEnvelope θ φ = φ) :
    SGPT.PSH.SingularityEquiv φ (sourceSingularityEnvelope η φ) := by
  obtain ⟨g, hg, hθη⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hc
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  have hbound : ∀ x, |g x| ≤ B := fun x => by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x)
  have hs := (sourceOrdinaryEnvelope_changeRepresentative hg hθη hφ).2
  rw [hfix] at hs
  have hshift := singularityEquiv_sub_bounded φ g B hbound
  have henv : sourceSingularityEnvelope η φ =
      sourceSingularityEnvelope η (fun x => φ x - (g x : EReal)) :=
    le_antisymm (sourceOrdinaryEnvelope_mono hshift.1) (sourceOrdinaryEnvelope_mono hshift.2)
  rw [henv]
  exact hs

/-- The change of representative of a test curve preserves the mass of its limit
`Γ_{-∞}`. -/
theorem SourceTestCurve.changeRepresentative_limit_mass (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (G : SourceTestCurve θ) :
    sourcePotentialNonPluripolarMeasure η
        (sourceTestCurveLimit (G.changeRepresentative omega hc).toSourceTestCurvePredata)
        (G.changeRepresentative omega hc).limit_thetaPSH univ =
      sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit G.toSourceTestCurvePredata)
        G.limit_thetaPSH univ := by
  have hφ := G.limit_model omega
  have hφ' := (G.changeRepresentative omega hc).limit_model omega
  have hequiv : SGPT.PSH.SingularityEquiv (sourceTestCurveLimit G.toSourceTestCurvePredata)
      (sourceTestCurveLimit (G.changeRepresentative omega hc).toSourceTestCurvePredata) := by
    rw [G.changeRepresentative_limit omega hc]
    exact singularityEquiv_sourceSingularityEnvelope_of_cohomologous hc G.limit_thetaPSH
      hφ.choose_spec.1.symm
  exact sourceTestCurveRepresentative_base_mass hφ hφ' hequiv omega hc

/-- The change of representative preserves every component mass. -/
theorem sourceNAComponentMass_changeRepresentative
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) :
    sourceNAComponentMass (Γ.changeRepresentative hc) κ = sourceNAComponentMass Γ κ :=
  (Γ.component κ).val.changeRepresentative_limit_mass (sourceKahlerFormRepresentative κ)
    (sourceNAComponentBackground_class hc κ)

/-- The change of representative preserves the volume `vol Γ` of `def:NApotential:L102`. -/
theorem sourceNAVolume_changeRepresentative
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (Γ : SourceNAPotential θ) :
    sourceNAVolume (Γ.changeRepresentative hc) = sourceNAVolume Γ := by
  unfold sourceNAVolume
  simp_rw [sourceNAComponentMass_changeRepresentative hc Γ]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Cohomologous summands give cohomologous sums. -/
theorem sourceNASumBackground_class
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (hc' : RealBottChern.ofRepresentative (atlasClosedFormToNative σ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative σ')) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative (θ.add σ)) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative (η.add σ')) := by
  rw [sourceNativeClosedForm_add, sourceNativeClosedForm_add, RealBottChern.ofRepresentative_add,
    RealBottChern.ofRepresentative_add, hc, hc']

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Cohomologous forms stay cohomologous after a rescaling. -/
theorem sourceNAScaledBackground_class
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η)) (c : ℝ) :
    RealBottChern.ofRepresentative (atlasClosedFormToNative (sourceNAScaledBackground θ c)) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative (sourceNAScaledBackground η c)) := by
  simp only [sourceNAScaledBackground, sourceNativeAtlasForm_roundTrip,
    RealBottChern.ofRepresentative_smul, hc]

/-- The sum of `def:sumNAmetrics` respects intrinsic equivalence of both summands, also across
different backgrounds. -/
theorem SourceNAPotential.sum_POrder_equivalent_of_equivalent (omega : KahlerBackground n M)
    {θ' τ τ' : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {Γ : SourceNAPotential θ} {Γ' : SourceNAPotential θ'} {Δ : SourceNAPotential τ}
    {Δ' : SourceNAPotential τ'}
    (hΓ : SourceNAPOrder Γ Γ') (hΓ' : SourceNAPOrder Γ' Γ)
    (hΔ : SourceNAPOrder Δ Δ') (hΔ' : SourceNAPOrder Δ' Δ) :
    SourceNAPOrder (Γ.sum Δ) (Γ'.sum Δ') ∧ SourceNAPOrder (Γ'.sum Δ') (Γ.sum Δ) := by
  let κ := sourceKahlerFormOfBackground omega
  have hs1 := Γ.sumComponent_POrder_equivalent_sum Δ κ omega omega
  have hs2 := Γ'.sumComponent_POrder_equivalent_sum Δ' κ omega omega
  have hsum := SourceTestCurve.sum_POrder_equivalent omega omega
    (Γ.realizedComponent omega).val (Δ.realizedComponent omega).val
    (Γ'.realizedComponent omega).val (Δ'.realizedComponent omega).val
    ((sourceNAPOrder_iff_realizedComponents Γ Γ' omega omega).mp hΓ)
    ((sourceNAPOrder_iff_realizedComponents Γ' Γ omega omega).mp hΓ')
    ((sourceNAPOrder_iff_realizedComponents Δ Δ' omega omega).mp hΔ)
    ((sourceNAPOrder_iff_realizedComponents Δ' Δ omega omega).mp hΔ')
  exact ⟨⟨κ, SourceTestCurvePOrder.trans omega hs1.1 (SourceTestCurvePOrder.trans omega hsum.1
      hs2.2)⟩,
    ⟨κ, SourceTestCurvePOrder.trans omega hs2.1 (SourceTestCurvePOrder.trans omega hsum.2
      hs1.2)⟩⟩

/-- The change of representative commutes with the sum of `def:sumNAmetrics`: changing the
representatives of both summands changes the representative of the sum. -/
theorem SourceNAPotential.changeRepresentative_sum (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (hc' : RealBottChern.ofRepresentative (atlasClosedFormToNative σ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative σ'))
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    (Γ.sum Δ).changeRepresentative (sourceNASumBackground_class hc hc') =
      (Γ.changeRepresentative hc).sum (Δ.changeRepresentative hc') := by
  have h1 := (Γ.sum Δ).changeRepresentative_POrder_equivalent omega
    (sourceNASumBackground_class hc hc')
  have hΓ := Γ.changeRepresentative_POrder_equivalent omega hc
  have hΔ := Δ.changeRepresentative_POrder_equivalent omega hc'
  have h2 := SourceNAPotential.sum_POrder_equivalent_of_equivalent omega hΓ.1 hΓ.2 hΔ.1 hΔ.2
  exact SourceNAPOrder.antisymm (h1.2.trans h2.1) (h2.2.trans h1.1)

/-- The change of representative commutes with the positive rescaling of
`def:NApotential:L572`. -/
theorem SourceNAPotential.changeRepresentative_positiveScale (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourceNAPotential θ) {c : ℝ} (hc0 : 0 < c) :
    (Γ.positiveScale hc0).changeRepresentative (sourceNAScaledBackground_class hc c) =
      (Γ.changeRepresentative hc).positiveScale hc0 := by
  have h1 := (Γ.positiveScale hc0).changeRepresentative_POrder_equivalent omega
    (sourceNAScaledBackground_class hc c)
  have hΓ := Γ.changeRepresentative_POrder_equivalent omega hc
  exact SourceNAPOrder.antisymm (h1.2.trans (hΓ.1.positiveScale hc0))
    ((hΓ.2.positiveScale hc0).trans h1.1)

end SGPT.PSH.VariableComplexAtlas

end

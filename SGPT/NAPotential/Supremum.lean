import SGPT.NAPotential.Join
import SGPT.PSH.SourceTestCurveChoquet

/-! # The usc supremum of a family of non-Archimedean metrics

Source `def:NApotential:L413`, `prop:NAsupproj`, `prop:NAChoquet`, `prop:supGammiotherprop2`
and the supremum clause of `prop:resclacompat2` of `chapter_NApotential.tex`.

For a non-empty family `(Γ^i)_{i ∈ I}` in `PSH^NA(X, θ)` with `sup_i Γ^i_max < ∞`
(`eq:supPSHNAmaxfinite`), the component of `uscsup_i Γ^i` at a Kähler form `ω` is the
test-curve usc supremum `uscsup_i Γ^{i,θ+ω}` (`def:testcurvsupsgeneral`).  Compatibility is
proved from `lma:testcursupcompatible`.
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
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A non-Archimedean metric is determined by any single one of its components
(the injectivity argument of `prop:NAposNAemb`). -/
theorem SourceNAPotential.eq_of_component_eq {Γ Δ : SourceNAPotential θ}
    (κ : SourceKahlerForm n M) (h : Γ.component κ = Δ.component κ) : Γ = Δ :=
  SourceNAPOrder.antisymm
    ⟨κ, by rw [h]; exact SourceTestCurvePOrder.refl (sourceKahlerFormRepresentative κ) _⟩
    ⟨κ, by rw [h]; exact SourceTestCurvePOrder.refl (sourceKahlerFormRepresentative κ) _⟩

section Supremum

variable {I : Type*} [Nonempty I]

omit [Nonempty I] in
/-- The bound `eq:supPSHNAmaxfinite` read at any component. -/
theorem sourceNAFamily_component_bddAbove (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (κ : SourceKahlerForm n M) :
    BddAbove (range fun i => ((Γ i).component κ).val.max) := by
  have h : (fun i => ((Γ i).component κ).val.max) = fun i => sourceNAPotentialCutoff omega (Γ i) :=
    funext fun i => (sourceNAPotentialCutoff_eq_component omega (Γ i) κ).symm
  rw [h]
  exact hb

omit [Nonempty I] in
/-- The bound `eq:supPSHNAmaxfinite` read at any literal background `θ + ω`. -/
theorem sourceNAFamily_realized_bddAbove (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (omega' : KahlerBackground n M) :
    BddAbove (range fun i => ((Γ i).realizedComponent omega').val.max) := by
  have h : (fun i => ((Γ i).realizedComponent omega').val.max) =
      fun i => sourceNAPotentialCutoff omega (Γ i) :=
    funext fun i => (Γ i).realizedComponent_max_eq_cutoff omega omega'
  rw [h]
  exact hb

/-- Source `def:NApotential:L413`: the usc supremum `uscsup_{i ∈ I} Γ^i` of a non-empty family
satisfying `eq:supPSHNAmaxfinite`.  Its component at every geometric Kähler index is the
test-curve usc supremum of the components. -/
def SourceNAPotential.uscSup (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) : SourceNAPotential θ where
  component κ := SourcePositiveIModelTestCurve.generalSup (sourceKahlerFormRepresentative κ)
    (fun i => (Γ i).component κ) (sourceNAFamily_component_bddAbove omega Γ hb κ)
  compatible κ ζ h := by
    rw [SourcePositiveIModelTestCurve.generalSup_ambient_independent
      (sourceKahlerFormRepresentative κ) (sourceKahlerFormRepresentative ζ)]
    exact sourceIModelTestCurveTransition_generalSup _ _ _ _ _
      (fun i => (Γ i).compatible κ ζ h) _

/-- The defining component formula of `def:NApotential:L413`. -/
theorem SourceNAPotential.uscSup_component (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (κ : SourceKahlerForm n M) :
    (SourceNAPotential.uscSup omega Γ hb).component κ =
      SourcePositiveIModelTestCurve.generalSup (sourceKahlerFormRepresentative κ)
        (fun i => (Γ i).component κ) (sourceNAFamily_component_bddAbove omega Γ hb κ) := rfl

/-- `uscsup_i Γ^i` is the unique element with the components of `def:NApotential:L413`. -/
theorem SourceNAPotential.uscSup_unique (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (E : SourceNAPotential θ)
    (h : ∀ κ : SourceKahlerForm n M, E.component κ =
      SourcePositiveIModelTestCurve.generalSup (sourceKahlerFormRepresentative κ)
        (fun i => (Γ i).component κ) (sourceNAFamily_component_bddAbove omega Γ hb κ)) :
    E = SourceNAPotential.uscSup omega Γ hb :=
  SourceNAPotential.ext h

/-- The formula of `def:NApotential:L413` in every literal background `θ + ω`. -/
theorem SourceNAPotential.uscSup_realizedComponent (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (omega' : KahlerBackground n M) :
    (SourceNAPotential.uscSup omega Γ hb).realizedComponent omega' =
      SourcePositiveIModelTestCurve.generalSup omega' (fun i => (Γ i).realizedComponent omega')
        (sourceNAFamily_realized_bddAbove omega Γ hb omega') := by
  dsimp only [SourceNAPotential.realizedComponent, sourceIModelTestCurvePresentationEquiv,
    Equiv.coe_fn_mk]
  rw [SourceNAPotential.uscSup_component,
    SourcePositiveIModelTestCurve.generalSup_ambient_independent
      (sourceKahlerFormRepresentative (sourceKahlerFormOfBackground omega')) omega']
  exact sourceIModelTestCurveTransition_generalSup _ _ _ _ _ (fun i => rfl) _

/-- The cutoff of `uscsup_i Γ^i` is `sup_i Γ^i_max`. -/
theorem sourceNAPotentialCutoff_uscSup (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) :
    sourceNAPotentialCutoff omega (SourceNAPotential.uscSup omega Γ hb) =
      sSup (range fun i => sourceNAPotentialCutoff omega (Γ i)) := by
  exact SourceTestCurve.generalSup_max
    (sourceKahlerFormRepresentative (sourceKahlerFormOfBackground omega))
    (fun i => ((Γ i).component (sourceKahlerFormOfBackground omega)).val)
    (sourceNAFamily_component_bddAbove omega Γ hb _)

/-- Every member of the family lies below its usc supremum. -/
theorem SourceNAPotential.le_uscSup (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) (i : I) :
    SourceNAPOrder (Γ i) (SourceNAPotential.uscSup omega Γ hb) :=
  let κ := sourceKahlerFormOfBackground omega
  ⟨κ, SourceTestCurve.le_generalSup (sourceKahlerFormRepresentative κ)
    (fun i => ((Γ i).component κ).val) (sourceNAFamily_component_bddAbove omega Γ hb κ) i⟩

/-- The usc supremum is the least upper bound, even against a metric in another background. -/
theorem SourceNAPotential.uscSup_le (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (Ξ : SourceNAPotential σ) (h : ∀ i, SourceNAPOrder (Γ i) Ξ) :
    SourceNAPOrder (SourceNAPotential.uscSup omega Γ hb) Ξ := by
  let κ := sourceKahlerFormOfBackground omega
  exact ⟨κ, SourceTestCurve.generalSup_le_cross_background (sourceKahlerFormRepresentative κ)
    (fun i => ((Γ i).component κ).val) (sourceNAFamily_component_bddAbove omega Γ hb κ)
    (Ξ.component κ).val (fun i => (sourceNAPOrder_iff_component (Γ i) Ξ κ).mp (h i))⟩

/-- The usc supremum extends the maximum of `def:PSHNAlor`. -/
theorem SourceNAPotential.uscSup_bool (omega : KahlerBackground n M) (Γ : Bool → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) :
    SourceNAPotential.uscSup omega Γ hb = (Γ false).join (Γ true) := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  exact SourceTestCurve.generalSup_bool (sourceKahlerFormRepresentative κ)
    (fun b => ((Γ b).component κ).val) (sourceNAFamily_component_bddAbove omega Γ hb κ)

omit [Nonempty I] in
/-- The cutoff bound for the image of a bounded family of positive curves. -/
theorem sourcePositiveTestCurveToNA_family_bddAbove (omega : KahlerBackground n M)
    (G : I → SourcePositiveIModelTestCurve θ) (hb : BddAbove (range fun i => (G i).val.max)) :
    BddAbove (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (G i))) := by
  simpa only [sourcePositiveTestCurveToNA_cutoff] using hb

/-- The usc supremum extends `def:testcurvsupsgeneral` under the embedding of `prop:NAposNAemb`. -/
theorem sourcePositiveTestCurveToNA_generalSup (omega : KahlerBackground n M)
    (G : I → SourcePositiveIModelTestCurve θ) (hb : BddAbove (range fun i => (G i).val.max)) :
    sourcePositiveTestCurveToNA (SourcePositiveIModelTestCurve.generalSup omega G hb) =
      SourceNAPotential.uscSup omega (fun i => sourcePositiveTestCurveToNA (G i))
        (sourcePositiveTestCurveToNA_family_bddAbove omega G hb) := by
  apply SourceNAPotential.ext
  intro κ
  change sourceIModelTestCurveTransition (sourceKahlerFormRepresentative κ)
      (sourceNAComponentBackground_positive θ κ)
      (SourcePositiveIModelTestCurve.generalSup omega G hb) = _
  rw [SourcePositiveIModelTestCurve.generalSup_ambient_independent omega
    (sourceKahlerFormRepresentative κ)]
  exact sourceIModelTestCurveTransition_generalSup _ _ _ _ _ (fun i => rfl) _

omit [Nonempty I] in
/-- The cutoff bound survives a background change. -/
theorem sourceNAFamily_backgroundChange_bddAbove (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    BddAbove (range fun i => sourceNAPotentialCutoff omega ((Γ i).backgroundChange η hη)) := by
  simpa only [sourceNAPotentialCutoff_backgroundChange] using hb

/-- Source `prop:NAsupproj`: for every closed semipositive `(1,1)`-form `η`,
`P_{θ+η}[uscsup_i Γ^i]_𝓘 = uscsup_i P_{θ+η}[Γ^i]_𝓘`. -/
theorem SourceNAPotential.uscSup_backgroundChange (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    (SourceNAPotential.uscSup omega Γ hb).backgroundChange η hη =
      SourceNAPotential.uscSup omega (fun i => (Γ i).backgroundChange η hη)
        (sourceNAFamily_backgroundChange_bddAbove omega Γ hb η hη) := by
  apply SourceNAPotential.ext
  intro κ
  rw [SourceNAPotential.backgroundChange_component, SourceNAPotential.uscSup_component]
  unfold SourceNAPotential.reindexedComponent
  rw [SourceNAPotential.uscSup_realizedComponent,
    SourcePositiveIModelTestCurve.castBackground_generalSup,
    SourcePositiveIModelTestCurve.generalSup_ambient_independent
      (sourceNAAugmentedKahlerBackground η hη (sourceKahlerFormRepresentative κ))
      (sourceKahlerFormRepresentative κ)]
  rfl

omit [Nonempty I] in
/-- The cutoff bound inherited by a subfamily. -/
theorem sourceNAFamily_restrict_bddAbove (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) (J : Set I) :
    BddAbove (range fun j : J => sourceNAPotentialCutoff omega (Γ j.val)) := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, by rintro _ ⟨j, rfl⟩; exact hC (mem_range_self j.val)⟩

/-- Source `prop:NAChoquet`, the non-Archimedean Choquet lemma: some non-empty countable
subfamily has the same usc supremum. -/
theorem SourceNAPotential.uscSup_choquet (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) :
    ∃ (J : Set I) (hJ : J.Nonempty), J.Countable ∧
      (letI : Nonempty J := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
       SourceNAPotential.uscSup omega (fun j : J => Γ j.val)
         (sourceNAFamily_restrict_bddAbove omega Γ hb J)) =
        SourceNAPotential.uscSup omega Γ hb := by
  let κ := sourceKahlerFormOfBackground omega
  obtain ⟨J, hJ, hc, heq⟩ := source_test_curve_choquet_whole (sourceKahlerFormRepresentative κ)
    (fun i => ((Γ i).component κ).val) (sourceNAFamily_component_bddAbove omega Γ hb κ)
  refine ⟨J, hJ, hc, ?_⟩
  let : Nonempty J := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  apply SourceNAPotential.eq_of_component_eq κ
  apply Subtype.ext
  exact heq

omit [Nonempty I] in
/-- The cutoff bound survives translation. -/
theorem sourceNAFamily_translate_bddAbove (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) (C : ℝ) :
    BddAbove (range fun i => sourceNAPotentialCutoff omega ((Γ i).translate C)) := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B + C, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi := hB (mem_range_self i)
  simp only [sourceNAPotentialCutoff_translate]
  linarith

/-- Source `prop:supGammiotherprop2`, first clause: `uscsup_i (Γ^i + C) = uscsup_i Γ^i + C`. -/
theorem SourceNAPotential.uscSup_translate (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) (C : ℝ) :
    SourceNAPotential.uscSup omega (fun i => (Γ i).translate C)
        (sourceNAFamily_translate_bddAbove omega Γ hb C) =
      (SourceNAPotential.uscSup omega Γ hb).translate C := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  exact SourceTestCurve.generalSup_translate (sourceKahlerFormRepresentative κ)
    (fun i => ((Γ i).component κ).val) (sourceNAFamily_component_bddAbove omega Γ hb κ) C

/-- Source `prop:supGammiotherprop2`, second clause: if `Γ^i ≤ Γ'^i` for all `i`, with `Γ'^i` in
another background `θ'`, then `uscsup_i Γ^i ≤ uscsup_i Γ'^i`. -/
theorem SourceNAPotential.uscSup_mono (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (Δ : I → SourceNAPotential σ)
    (hbΓ : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (hbΔ : BddAbove (range fun i => sourceNAPotentialCutoff omega (Δ i)))
    (h : ∀ i, SourceNAPOrder (Γ i) (Δ i)) :
    SourceNAPOrder (SourceNAPotential.uscSup omega Γ hbΓ) (SourceNAPotential.uscSup omega Δ hbΔ) :=
  SourceNAPotential.uscSup_le omega Γ hbΓ _ fun i =>
    (h i).trans (SourceNAPotential.le_uscSup omega Δ hbΔ i)

omit [Nonempty I] in
/-- The cutoff bound survives positive rescaling. -/
theorem sourceNAFamily_positiveScale_bddAbove (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) {c : ℝ} (hc : 0 < c) :
    BddAbove (range fun i => sourceNAPotentialCutoff omega ((Γ i).positiveScale hc)) := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨c * B, ?_⟩
  rintro _ ⟨i, rfl⟩
  simp only [sourceNAPotentialCutoff_positiveScale]
  exact mul_le_mul_of_nonneg_left (hB (mem_range_self i)) hc.le

/-- Source `prop:resclacompat2`, supremum clause:
`λ (uscsup_i Γ^i) = uscsup_i (λ Γ^i)`. -/
theorem SourceNAPotential.uscSup_positiveScale (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i))) {c : ℝ} (hc : 0 < c) :
    (SourceNAPotential.uscSup omega Γ hb).positiveScale hc =
      SourceNAPotential.uscSup omega (fun i => (Γ i).positiveScale hc)
        (sourceNAFamily_positiveScale_bddAbove omega Γ hb hc) := by
  apply SourceNAPotential.ext
  intro κ
  change ((((SourceNAPotential.uscSup omega Γ hb).realizedComponent
      (sourceNADividedKahlerBackground hc (sourceKahlerFormRepresentative κ))).positiveScale
      (sourceKahlerFormRepresentative κ) hc).castBackground
      (sourceNAPositiveScaleComponentBackground_eq θ hc κ)) = _
  rw [SourceNAPotential.uscSup_realizedComponent,
    SourcePositiveIModelTestCurve.generalSup_positiveScale]
  exact (SourcePositiveIModelTestCurve.castBackground_generalSup _ _ _ _).trans
    (SourcePositiveIModelTestCurve.generalSup_ambient_independent _ _ _ _)

end Supremum

end SGPT.PSH.VariableComplexAtlas

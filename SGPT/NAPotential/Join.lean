import SGPT.NAPotential.TransitionOperations

/-! # The maximum `Γ ∨ Γ'` of two non-Archimedean metrics

Source `def:PSHNAlor`, `prop:NApotential:L394` and `prop:NApotential:L404` of
`chapter_NApotential.tex`.  For `Γ, Γ' ∈ PSH^NA(X, θ)` the component of `Γ ∨ Γ'` at every
Kähler form `ω` is the test-curve join `Γ^{θ+ω} ∨ Γ'^{θ+ω}` (`def:testcurlor`).  The inverse
system compatibility of these components is proved from the commutation of the transitions
`P_{θ+ω}[•]_𝓘` with joins (`lma:testcurlorPthetapomega`), not assumed.
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

/-- Source `def:PSHNAlor`: the maximum `Γ ∨ Γ'` of two non-Archimedean metrics.  Its component
at every geometric Kähler index is the join of the two components. -/
def SourceNAPotential.join (Γ Δ : SourceNAPotential θ) : SourceNAPotential θ where
  component κ := (Γ.component κ).join (sourceKahlerFormRepresentative κ) (Δ.component κ)
  compatible κ ζ h := by
    rw [SourcePositiveIModelTestCurve.join_ambient_independent (sourceKahlerFormRepresentative κ)
      (sourceKahlerFormRepresentative ζ), sourceIModelTestCurveTransition_join,
      Γ.compatible κ ζ h, Δ.compatible κ ζ h]

/-- The defining component formula of `def:PSHNAlor`. -/
theorem SourceNAPotential.join_component (Γ Δ : SourceNAPotential θ) (κ : SourceKahlerForm n M) :
    (Γ.join Δ).component κ =
      (Γ.component κ).join (sourceKahlerFormRepresentative κ) (Δ.component κ) := rfl

/-- `Γ ∨ Γ'` is the unique element of `PSH^NA(X, θ)` with the components of `def:PSHNAlor`. -/
theorem SourceNAPotential.join_unique (Γ Δ E : SourceNAPotential θ)
    (h : ∀ κ : SourceKahlerForm n M,
      E.component κ = (Γ.component κ).join (sourceKahlerFormRepresentative κ) (Δ.component κ)) :
    E = Γ.join Δ :=
  SourceNAPotential.ext h

/-- The formula of `def:PSHNAlor` in every literal background `θ + ω`:
`(Γ ∨ Γ')^{θ+ω} = Γ^{θ+ω} ∨ Γ'^{θ+ω}`. -/
theorem SourceNAPotential.join_realizedComponent (Γ Δ : SourceNAPotential θ)
    (omega : KahlerBackground n M) :
    (Γ.join Δ).realizedComponent omega =
      (Γ.realizedComponent omega).join omega (Δ.realizedComponent omega) := by
  dsimp only [SourceNAPotential.realizedComponent, sourceIModelTestCurvePresentationEquiv,
    Equiv.coe_fn_mk]
  rw [SourceNAPotential.join_component,
    SourcePositiveIModelTestCurve.join_ambient_independent
      (sourceKahlerFormRepresentative (sourceKahlerFormOfBackground omega)) omega,
    sourceIModelTestCurveTransition_join]

/-- The cutoff of `Γ ∨ Γ'` is `max(Γ_max, Γ'_max)`. -/
theorem sourceNAPotentialCutoff_join (omega : KahlerBackground n M) (Γ Δ : SourceNAPotential θ) :
    sourceNAPotentialCutoff omega (Γ.join Δ) =
      max (sourceNAPotentialCutoff omega Γ) (sourceNAPotentialCutoff omega Δ) :=
  rfl

/-- The definition extends the join of positive `𝓘`-model test curves (`def:testcurlor`)
under the embedding of `prop:NAposNAemb`. -/
theorem sourcePositiveTestCurveToNA_join (omega : KahlerBackground n M)
    (G H : SourcePositiveIModelTestCurve θ) :
    sourcePositiveTestCurveToNA (G.join omega H) =
      (sourcePositiveTestCurveToNA G).join (sourcePositiveTestCurveToNA H) := by
  apply SourceNAPotential.ext
  intro κ
  change sourceIModelTestCurveTransition (sourceKahlerFormRepresentative κ)
      (sourceNAComponentBackground_positive θ κ) (G.join omega H) =
    (sourceIModelTestCurveTransition (sourceKahlerFormRepresentative κ)
      (sourceNAComponentBackground_positive θ κ) G).join (sourceKahlerFormRepresentative κ)
      (sourceIModelTestCurveTransition (sourceKahlerFormRepresentative κ)
        (sourceNAComponentBackground_positive θ κ) H)
  rw [SourcePositiveIModelTestCurve.join_ambient_independent omega
    (sourceKahlerFormRepresentative κ), sourceIModelTestCurveTransition_join]

/-- Source `prop:NApotential:L394`: for every closed semipositive `(1,1)`-form `η`,
`P_{θ+η}[Γ ∨ Γ']_𝓘 = P_{θ+η}[Γ]_𝓘 ∨ P_{θ+η}[Γ']_𝓘`. -/
theorem SourceNAPotential.join_backgroundChange (Γ Δ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    (Γ.join Δ).backgroundChange η hη = (Γ.backgroundChange η hη).join (Δ.backgroundChange η hη) := by
  apply SourceNAPotential.ext
  intro κ
  rw [SourceNAPotential.backgroundChange_component, SourceNAPotential.join_component,
    SourceNAPotential.backgroundChange_component, SourceNAPotential.backgroundChange_component]
  unfold SourceNAPotential.reindexedComponent
  rw [SourceNAPotential.join_realizedComponent, SourcePositiveIModelTestCurve.castBackground_join]
  rfl

/-- Source `prop:NApotential:L404`, commutativity of `∨`. -/
theorem SourceNAPotential.join_comm (Γ Δ : SourceNAPotential θ) : Γ.join Δ = Δ.join Γ := by
  apply SourceNAPotential.ext
  intro κ
  exact SourcePositiveIModelTestCurve.join_comm _ _ _

/-- Source `prop:NApotential:L404`, associativity of `∨`. -/
theorem SourceNAPotential.join_assoc (Γ Δ Ξ : SourceNAPotential θ) :
    (Γ.join Δ).join Ξ = Γ.join (Δ.join Ξ) := by
  apply SourceNAPotential.ext
  intro κ
  exact SourcePositiveIModelTestCurve.join_assoc _ _ _ _

/-- `Γ ≤ Γ ∨ Γ'` in the order of `def:NApotential:L274`. -/
theorem SourceNAPotential.le_join_left (Γ Δ : SourceNAPotential θ) (omega : KahlerBackground n M) :
    SourceNAPOrder Γ (Γ.join Δ) :=
  let κ := sourceKahlerFormOfBackground omega
  ⟨κ, (Γ.component κ).val.order_join_left (sourceKahlerFormRepresentative κ) (Δ.component κ).val⟩

/-- `Γ' ≤ Γ ∨ Γ'` in the order of `def:NApotential:L274`. -/
theorem SourceNAPotential.le_join_right (Γ Δ : SourceNAPotential θ) (omega : KahlerBackground n M) :
    SourceNAPOrder Δ (Γ.join Δ) :=
  let κ := sourceKahlerFormOfBackground omega
  ⟨κ, (Γ.component κ).val.order_join_right (sourceKahlerFormRepresentative κ) (Δ.component κ).val⟩

/-- `Γ ∨ Γ'` is the least upper bound of `Γ` and `Γ'` in `PSH^NA(X, θ)`. -/
theorem SourceNAPotential.join_le {Γ Δ Ξ : SourceNAPotential θ} (hΓ : SourceNAPOrder Γ Ξ)
    (hΔ : SourceNAPOrder Δ Ξ) : SourceNAPOrder (Γ.join Δ) Ξ := by
  obtain ⟨κ, hκ⟩ := hΓ
  exact ⟨κ, (Γ.component κ).val.join_le (sourceKahlerFormRepresentative κ) (Δ.component κ).val
    (Ξ.component κ).val hκ ((sourceNAPOrder_iff_component Δ Ξ κ).mp hΔ)⟩

/-- The order of `def:NApotential:L274` with `∨` as supremum: a join-semilattice structure on
`PSH^NA(X, θ)`.  The finite maxima `⋁_{i ∈ I} Γ^i` of `prop:NApotential:L404` are its finite
suprema. -/
@[instance_reducible]
def sourceNASemilatticeSup (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) : SemilatticeSup (SourceNAPotential θ) :=
  { sourceNAPartialOrder omega θ with
    sup := SourceNAPotential.join
    le_sup_left := fun Γ Δ => Γ.le_join_left Δ omega
    le_sup_right := fun Γ Δ => Γ.le_join_right Δ omega
    sup_le := fun _ _ _ hΓ hΔ => SourceNAPotential.join_le hΓ hΔ }

/-- The maximum `⋁_{i ∈ s} Γ^i` of a finite non-empty family (`prop:NApotential:L404`). -/
def SourceNAPotential.finiteJoin {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (s : Finset I) (hs : s.Nonempty) : SourceNAPotential θ := by
  let : SemilatticeSup (SourceNAPotential θ) := sourceNASemilatticeSup omega θ
  exact s.sup' hs Γ

/-- The finite maximum over a singleton is the element itself. -/
theorem SourceNAPotential.finiteJoin_singleton {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (i : I) :
    SourceNAPotential.finiteJoin omega Γ {i} (Finset.singleton_nonempty i) = Γ i := by
  let : SemilatticeSup (SourceNAPotential θ) := sourceNASemilatticeSup omega θ
  show ({i} : Finset I).sup' (Finset.singleton_nonempty i) Γ = Γ i
  exact Finset.sup'_singleton Γ

/-- Adding one element to a finite family joins it to the finite maximum. -/
theorem SourceNAPotential.finiteJoin_insert {I : Type*} [DecidableEq I]
    (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ) (i : I) (s : Finset I)
    (hs : s.Nonempty) :
    SourceNAPotential.finiteJoin omega Γ (insert i s) (Finset.insert_nonempty i s) =
      (Γ i).join (SourceNAPotential.finiteJoin omega Γ s hs) := by
  let : SemilatticeSup (SourceNAPotential θ) := sourceNASemilatticeSup omega θ
  show (insert i s).sup' (Finset.insert_nonempty i s) Γ = Γ i ⊔ s.sup' hs Γ
  exact Finset.sup'_insert hs Γ

end SGPT.PSH.VariableComplexAtlas

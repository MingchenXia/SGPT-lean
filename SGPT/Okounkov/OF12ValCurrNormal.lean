import SGPT.Okounkov.OF12NormalResolution
import SGPT.Okounkov.OCModelCurrentValuation
import SGPT.Unibranch.PDThetaForms

/-!
# `rmk:valcurr` for a normal projective variety: `ν(T)` is well defined

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`:

> Suppose that `X` is a normal projective variety. Consider a rank `n` (surjective) valuation
> `ν : ℂ(X)^× → ℤⁿ` and a closed positive `(1,1)`-current `T` on `X`. Then we can always define
> `ν(T) ∈ ℝⁿ` as follows: take a resolution `π : Y → X` such that there is a smooth flag `Y•` on
> `Y` and `g ∈ Aut(ℤⁿ_lex)` such that `ν = ν_{Y•} g`. Then we define `ν(T) := ν_{Y•}(π^*T) g`.
> This definition does not depend on the choice of `π`, by passing to a common resolution and
> applying `prop:cormatrix`, `prop:cormult`.

## Objects

* `X`: an integral **normal** scheme (all local rings integrally closed), separated and of finite
  type over `ℂ` (projectivity of `X` is not used; the resolutions are projective);
  `X^an = UnibAn.analytification f` its complex space, unibranch
  (`isUnibranch_analytification_of_normal`).
* `T`: a closed positive `(1,1)`-current on the normal space `X^an`, presented as `θ + dd^c ψ` with
  `θ` a smooth closed real `(1,1)`-form in the sense of `PD.IsLocallyClosedOneOne` and `ψ` a
  `θ`-psh function (the reading of lanes TY2/TY4 for normal spaces).
* `Resolution f m` (**a resolution of `X`**): an integral smooth projective scheme `Y` of dimension
  `n = m + 1` with a morphism `ρ : Y → X` over `ℂ` which is birational (the induced field map
  `φ : ℂ(X) → ℂ(Y)` is an isomorphism, `IsStalkCompatible`), together with its analytification
  `π : Y(ℂ) → X^an`, a proper bimeromorphic morphism of complex spaces whose underlying map is
  `ρ` on complex points; `π` is determined by `ρ` (`Resolution.pi_unique`).
* `Presentation ν` (**a presentation of `ν`**): a resolution `Y` and a presentation
  `ν ∘ φ⁻¹ = ν_{F•} G` of the transported valuation of `ℂ(Y)` by a smooth flag `F•` on `Y`
  (`ofFlag`, the book's case) or, more generally, on a finite blow-up tower of `Y(ℂ)`
  (`OF9.BlowupPresentation`), with `G ∈ Aut(ℤⁿ_lex)` unipotent upper triangular.
* `Presentation.value`: `ν_{F•}(π^*T) G`, with `π^*T = π^*θ + dd^c(ψ ∘ π)`
  (`OCSpaceFormNative.nativePullback`).

## Results

* **`Presentation.value_eq`** (`rmk:valcurr`, independence of the resolution): any two
  presentations of a surjective `ν` give the same value, for every `T`.  Proof (the book's): a
  compact Kähler common resolution `U₀` of `Y₁(ℂ)` and `Y₂(ℂ)` over `X^an`
  (`OCKahlerCommonModel.exists_kahler_commonModel`), common modifications with the two blow-up
  towers, a lifting `W•` of `F₁•` (`thm:liftableflag`); the flag `W•` induces through `Y₁` and
  through `Y₂` the same valuation of `ℂ(X)` (`comap_modificationFlagValuation_eq`), so by OF9's
  recognition (`isFlagLifting_of_lexEquivalent`, rational embedding of the tower over `Y₂`) it is
  also the lifting of `F₂•`; `prop:cormatrix`/`prop:cormult`
  (`OF2.modificationPresentationValue_lifting`),
  uniqueness of the matrix and equality of the two pulled-back currents on `W` finish.
* `valuationCurrentValue` (**the definition of `ν(T)`**) and `valuationCurrentValue_eq`
  (well-definedness: every presentation computes it); `Presentation.ofFlag` (the book's
  presentations, a smooth flag on `Y` itself). Independence of the presentation `θ + dd^c ψ` of `T`
  is in `OF12CurrentPresentation`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification
open SGPT.Okounkov.OCSpaceFormNative SGPT.Okounkov.OCModelCurrentValuation
open scoped Topology Manifold ContDiff

/-! ### Smooth projective schemes as complex spaces -/

/-- The complex manifold `Y(ℂ)` of a smooth scheme `Y` over `ℂ`, as a reduced complex space. -/
abbrev smoothModel {Y : Scheme.{0}} (fY : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n fY] [IsSeparated fY] [QuasiCompact fY] :
    SourceReducedComplexSpace :=
  @wholeModel n (SchemeComplexPoint fY) (schemeAnalyticPointTopology fY)
    (schemeAnalyticTNChartedSpace fY n) (schemeAnalyticTN_isComplexManifold fY n)

/-! ### Resolutions of a normal projective variety -/

section Resolution

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) [IsSeparated f] [QuasiCompact f]
  [LocallyOfFiniteType f] (m : ℕ)

/-- **A resolution of `X`** (`rmk:valcurr`): an integral smooth projective complex scheme `Y` of
dimension `m + 1`, a morphism `ρ : Y → X` over `ℂ`, birational: the field map `φ : ℂ(X) → ℂ(Y)`
induced by `ρ` (it extends the stalk maps of `ρ`, `IsStalkCompatible`) is an isomorphism; together
with the analytification `π : Y(ℂ) → X^an` of `ρ`: a proper bimeromorphic morphism of complex
spaces whose underlying map is `ρ` on complex points. -/
structure Resolution where
  /-- The smooth projective model. -/
  Y : Scheme.{0}
  [integral : IsIntegral Y]
  /-- Its structure morphism. -/
  fY : Y ⟶ Spec (.of ℂ)
  [smooth : SmoothOfRelativeDimension (m + 1) fY]
  [separated : IsSeparated fY]
  [quasiCompact : QuasiCompact fY]
  /-- `Y` is projective. -/
  E : ClosedProjectiveEmbedding fY
  /-- The resolution morphism. -/
  ρ : Y ⟶ X
  comp_eq : ρ ≫ f = fY
  /-- The isomorphism of function fields induced by `ρ`. -/
  φ : X.functionField ≃+* Y.functionField
  stalkCompatible : IsStalkCompatible ρ φ.toRingHom
  /-- The analytification of `ρ`. -/
  π : smoothModel fY (m + 1) ⟶ UnibAn.analytification f
  isProperBimeromorphic : IsProperBimeromorphic π
  point_eq : ∀ y : SchemeComplexPoint fY,
    UnibAn.pointMap f (π.hom.left.base ⟨y, mem_univ y⟩) = schemeComplexPointMap fY f ρ comp_eq y

attribute [instance] Resolution.integral Resolution.smooth Resolution.separated
  Resolution.quasiCompact

variable {f m}

local instance of12RTop (R : Resolution f m) : TopologicalSpace (SchemeComplexPoint R.fY) :=
  schemeAnalyticPointTopology R.fY
local instance of12RCharts (R : Resolution f m) :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTNChartedSpace R.fY (m + 1)
local instance of12RManifold (R : Resolution f m) :
    IsComplexManifold (m + 1) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTN_isComplexManifold R.fY (m + 1)

/-- **The analytification of `ρ` is determined by `ρ`**: a morphism `Y(ℂ) → X^an` of reduced
complex spaces whose underlying map is `ρ` on complex points is `R.π`. So `π` is a property of `ρ`
(the existence of its analytification), not extra data. -/
theorem Resolution.pi_unique (R : Resolution f m)
    (π' : smoothModel R.fY (m + 1) ⟶ UnibAn.analytification f)
    (h : ∀ y : SchemeComplexPoint R.fY, UnibAn.pointMap f (π'.hom.left.base ⟨y, mem_univ y⟩) =
      schemeComplexPointMap R.fY f R.ρ R.comp_eq y) : π' = R.π :=
  morphism_eq_of_pointwise_eq _ _ fun x =>
    UnibAn.pointMap_injective ((h x.val).trans (R.point_eq x.val).symm)

/-- The valuation of `ℂ(Y)` corresponding to a valuation `ν` of `ℂ(X)`: `ν ∘ φ⁻¹`. -/
def Resolution.transport (R : Resolution f m)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) :
    AddValuation R.Y.functionField (WithTop (Lex (Fin (m + 1) → ℤ))) :=
  v.comap R.φ.symm.toRingHom

theorem Resolution.transport_comap (R : Resolution f m)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) :
    (R.transport v).comap R.φ.toRingHom = v := by
  ext q
  change v (R.φ.symm (R.φ q)) = v q
  rw [RingEquiv.symm_apply_apply]

/-- The pulled-back form `π^*θ` on `Y(ℂ)`. -/
def Resolution.pullbackForm (R : Resolution f m) (θ : SpaceForm (UnibAn.analytification f) 2)
    (hθ : PD.IsLocallyClosedOneOne θ) : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint R.fY) :=
  nativePullbackClosed R.π θ hθ.isClosed hθ.isOneOne

/-- The pulled-back potential `ψ ∘ π` on `Y(ℂ)`. -/
def Resolution.pullbackPotential (R : Resolution f m)
    (ψ : (UnibAn.analytification f).obj.left → EReal) : SchemeComplexPoint R.fY → EReal :=
  nativePotential R.π ψ

/-- `π^*T = π^*θ + dd^c(ψ ∘ π)` is a closed positive current: `ψ ∘ π` is `π^*θ`-psh (`X^an` is
unibranch). -/
theorem Resolution.isThetaPshPotential_pullback (R : Resolution f m)
    (hXu : (UnibAn.analytification f).IsUnibranch) (θ : SpaceForm (UnibAn.analytification f) 2)
    (hθ : PD.IsLocallyClosedOneOne θ) (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) :
    IsThetaPshPotential (R.pullbackForm θ hθ).val (R.pullbackPotential ψ) :=
  isThetaPshPotential_nativePullback R.π θ hψ hXu R.isProperBimeromorphic

/-- The complex manifold `Y(ℂ)` of a resolution is connected as soon as it is the target of an
analytic modification from a connected manifold (e.g. the model of a flag presentation). -/
theorem Resolution.connectedSpace (R : Resolution f m) {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [ConnectedSpace M]
    {p : M → SchemeComplexPoint R.fY} (hp : IsAnalyticModification (n := m + 1) p) :
    ConnectedSpace (SchemeComplexPoint R.fY) :=
  (AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hp).connectedSpace
    hp.1.continuous

end Resolution

/-! ### Presentations and their values -/

section Presentation

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} [IsSeparated f] [QuasiCompact f]
  [LocallyOfFiniteType f] {m : ℕ}

local instance of12PTop (R : Resolution f m) : TopologicalSpace (SchemeComplexPoint R.fY) :=
  schemeAnalyticPointTopology R.fY
local instance of12PCharts (R : Resolution f m) :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTNChartedSpace R.fY (m + 1)
local instance of12PManifold (R : Resolution f m) :
    IsComplexManifold (m + 1) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTN_isComplexManifold R.fY (m + 1)

variable (f m) in
/-- **A presentation `ν = ν_{Y•} g` on a resolution** (`rmk:valcurr`): a resolution `ρ : Y → X`
and a presentation `ν ∘ φ⁻¹ = ν_{F•} G` of the corresponding valuation of `ℂ(Y)` by a smooth flag
on `Y(ℂ)` or on a finite blow-up tower of `Y(ℂ)` (`OF9.BlowupPresentation`). -/
structure Presentation (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))) where
  /-- The resolution. -/
  R : Resolution f m
  /-- The flag presentation on the resolution. -/
  P : OF9.BlowupPresentation R.fY (R.transport v)

/-- **The value** `ν_{Y•}(π^*T) G` of a presentation, for `T = θ + dd^c ψ` on `X^an`. -/
def Presentation.value {v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (Q : Presentation f m v) (hXu : (UnibAn.analytification f).IsUnibranch)
    (θ : SpaceForm (UnibAn.analytification f) 2) (hθ : PD.IsLocallyClosedOneOne θ)
    (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) : Fin (m + 1) → ℝ :=
  OF2.modificationPresentationValue Q.R.fY Q.P.F Q.P.isModification Q.P.G
    (Q.R.pullbackForm θ hθ) (Q.R.pullbackPotential ψ)
    (Q.R.isThetaPshPotential_pullback hXu θ hθ ψ hψ)

/-- Two currents on the same flag with geometrically equal forms and equal potentials. -/
private theorem thetaPotentialCurrent_congr' {V : Type} [TopologicalSpace V]
    [ChartedSpace (ComplexModel (m + 1)) V] [IsComplexManifold (m + 1) V]
    {θ σ : SmoothRealForm (m + 1) V 2} {u w : V → EReal} (hθσ : θ.GeometricallyEq σ)
    (huw : u = w) (hu : IsThetaPshPotential θ u) (hw : IsThetaPshPotential σ w) :
    thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ w hw := by
  subst huw
  exact thetaPotentialCurrent_eq_of_geometricallyEq hθσ hu hw

end Presentation

section Helper

variable {Y₁ Y₂ : Scheme.{0}} (f₁ : Y₁ ⟶ Spec (.of ℂ)) (f₂ : Y₂ ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f₁] [IsSeparated f₁] [QuasiCompact f₁]
  [SmoothOfRelativeDimension (m + 1) f₂] [IsSeparated f₂] [QuasiCompact f₂]

local instance of12HTop₁ : TopologicalSpace (SchemeComplexPoint f₁) :=
  schemeAnalyticPointTopology f₁
local instance of12HCharts₁ : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f₁) :=
  schemeAnalyticTNChartedSpace f₁ (m + 1)
local instance of12HManifold₁ : IsComplexManifold (m + 1) (SchemeComplexPoint f₁) :=
  schemeAnalyticTN_isComplexManifold f₁ (m + 1)
local instance of12HTop₂ : TopologicalSpace (SchemeComplexPoint f₂) :=
  schemeAnalyticPointTopology f₂
local instance of12HCharts₂ : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f₂) :=
  schemeAnalyticTNChartedSpace f₂ (m + 1)
local instance of12HManifold₂ : IsComplexManifold (m + 1) (SchemeComplexPoint f₂) :=
  schemeAnalyticTN_isComplexManifold f₂ (m + 1)

/-- The value of a presentation only depends on the flag, the pulled-back current and the
matrix, not on the smooth model it is read on. -/
theorem modificationPresentationValue_eq_of_current_eq (W : OriginalFlagGeometry.{0} (m + 1))
    {κ₁ : W.carrier → SchemeComplexPoint f₁} (hκ₁ : IsAnalyticModification (n := m + 1) κ₁)
    {κ₂ : W.carrier → SchemeComplexPoint f₂} (hκ₂ : IsAnalyticModification (n := m + 1) κ₂)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (θ₁ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f₁))
    (u₁ : SchemeComplexPoint f₁ → EReal) (hu₁ : IsThetaPshPotential θ₁.val u₁)
    (θ₂ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f₂))
    (u₂ : SchemeComplexPoint f₂ → EReal) (hu₂ : IsThetaPshPotential θ₂.val u₂)
    (h : analyticModificationThetaCurrent hκ₁ θ₁ u₁ hu₁ =
      analyticModificationThetaCurrent hκ₂ θ₂ u₂ hu₂) :
    OF2.modificationPresentationValue f₁ W hκ₁ G θ₁ u₁ hu₁ =
      OF2.modificationPresentationValue f₂ W hκ₂ G θ₂ u₂ hu₂ := by
  unfold OF2.modificationPresentationValue
  rw [OF2.currentFlagValuation_congr_current' W h _ _ _
    (analyticModificationThetaCurrent_closed_type_positive hκ₂ θ₂ u₂ hu₂).1
    (analyticModificationThetaCurrent_closed_type_positive hκ₂ θ₂ u₂ hu₂).2.1
    (analyticModificationThetaCurrent_closed_type_positive hκ₂ θ₂ u₂ hu₂).2.2]

end Helper

section Main

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} [IsSeparated f] [QuasiCompact f]
  [LocallyOfFiniteType f] {m : ℕ}

local instance of12MTop (R : Resolution f m) : TopologicalSpace (SchemeComplexPoint R.fY) :=
  schemeAnalyticPointTopology R.fY
local instance of12MCharts (R : Resolution f m) :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTNChartedSpace R.fY (m + 1)
local instance of12MManifold (R : Resolution f m) :
    IsComplexManifold (m + 1) (SchemeComplexPoint R.fY) :=
  schemeAnalyticTN_isComplexManifold R.fY (m + 1)

theorem lexMapValuation_comap {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    {G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hG : IsUnitUpperTriangular G)
    (v : AddValuation L (WithTop (Lex (Fin (m + 1) → ℤ)))) :
    (lexMapValuation G hG v).comap φ = lexMapValuation G hG (v.comap φ) := by
  ext q
  rfl

/-- **`rmk:valcurr`: `ν(T)` does not depend on the resolution.** Let `X` be a normal projective
variety and `ν : ℂ(X)^× → ℤ^{m+1}_lex` a surjective valuation. Two presentations `ν = ν_{F₁•} G₁`
on a resolution `ρ₁ : Y₁ → X` and `ν = ν_{F₂•} G₂` on a resolution `ρ₂ : Y₂ → X` give the same
value `ν_{F₁•}(π₁^*T) G₁ = ν_{F₂•}(π₂^*T) G₂` for every closed positive `(1,1)`-current
`T = θ + dd^c ψ` on `X`. -/
theorem Presentation.value_eq (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (hv : Function.Surjective v) (Q₁ Q₂ : Presentation f m v)
    (θ : SpaceForm (UnibAn.analytification f) 2) (hθ : PD.IsLocallyClosedOneOne θ)
    (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) :
    Q₁.value (isUnibranch_analytification_of_normal f hX) θ hθ ψ hψ =
      Q₂.value (isUnibranch_analytification_of_normal f hX) θ hθ ψ hψ := by
  have hXu := isUnibranch_analytification_of_normal f hX
  obtain ⟨R₁, P₁⟩ := Q₁
  obtain ⟨R₂, P₂⟩ := Q₂
  let : CompactSpace (SchemeComplexPoint R₁.fY) := R₁.E.analyticCompact
  let : CompactSpace (SchemeComplexPoint R₂.fY) := R₂.E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint R₁.fY) := R₁.connectedSpace P₁.isModification
  let : ConnectedSpace (SchemeComplexPoint R₂.fY) := R₂.connectedSpace P₂.isModification
  -- a compact Kähler common resolution of `Y₁(ℂ)` and `Y₂(ℂ)` over `X^an`
  obtain ⟨U₀, tU₀, aU₀, mU₀, cU₀, conU₀, ωU₀, h₁, h₂, hh₁, hh₂, hsq⟩ :=
    OCKahlerCommonModel.exists_kahler_commonModel
      (Y₀ := SchemeComplexPoint R₁.fY) (Y₁ := SchemeComplexPoint R₂.fY)
      (schemeProjectiveTNKahlerBackground R₁.fY (m + 1) R₁.E)
      (schemeProjectiveTNKahlerBackground R₂.fY (m + 1) R₂.E) R₁.π R₂.π
      R₁.isProperBimeromorphic R₂.isProperBimeromorphic
  let := tU₀
  let := aU₀
  let := mU₀
  let := cU₀
  have hpt₀ (u : U₀) :
      R₁.π.hom.left.base ⟨h₁ u, mem_univ _⟩ = R₂.π.hom.left.base ⟨h₂ u, mem_univ _⟩ :=
    congrArg (fun H : wholeModel (n := m + 1) U₀ ⟶ UnibAn.analytification f =>
      H.hom.left.base ⟨u, mem_univ u⟩) hsq
  -- a common modification with the blow-up tower of `P₁`, over `Y₁(ℂ)`
  obtain ⟨U₁, tU₁, aU₁, mU₁, σ₁, ℓ₁, cU₁, ⟨ωU₁⟩, -, hσ₁, hℓ₁, hsq₁⟩ :=
    exists_kahler_commonModification_of_isBlowupSequence P₁.isBlowupSequence hh₁ ⟨ωU₀⟩
  let := tU₁
  let := aU₁
  let := mU₁
  let := cU₁
  -- a common modification with the blow-up tower of `P₂`, over `Y₂(ℂ)`
  have hc₂ : IsAnalyticModification (n := m + 1) (h₂ ∘ σ₁) :=
    AnalyticModificationComposition.isAnalyticModification_comp hh₂ hσ₁
  obtain ⟨U₂, tU₂, aU₂, mU₂, σ₂, ℓ₂, cU₂, ⟨ωU₂⟩, -, hσ₂, hℓ₂, hsq₂⟩ :=
    exists_kahler_commonModification_of_isBlowupSequence P₂.isBlowupSequence hc₂ ⟨ωU₁⟩
  let := tU₂
  let := aU₂
  let := mU₂
  let := cU₂
  -- lift `F₁•` to a further blow-up tower `W`
  have hlam : IsAnalyticModification (n := m + 1) (ℓ₁ ∘ σ₂) :=
    AnalyticModificationComposition.isAnalyticModification_comp hℓ₁ hσ₂
  obtain ⟨W, a, ha, hL₁⟩ :=
    exists_flagLifting_dominating_nativeModel (m + 1) P₁.F U₂ ωU₂ (ℓ₁ ∘ σ₂) hlam
  have ham : IsAnalyticModification (n := m + 1) a :=
    isAnalyticModification_of_isBlowupSequence ha
  have hq : IsAnalyticModification (n := m + 1) (ℓ₂ ∘ a) :=
    AnalyticModificationComposition.isAnalyticModification_comp hℓ₂ ham
  have hρ₁ := AnalyticModificationComposition.isAnalyticModification_comp P₁.isModification hL₁.1
  have hρ₂ := AnalyticModificationComposition.isAnalyticModification_comp P₂.isModification hq
  -- the two composites `W → X^an` agree
  have hk₁ (w : W.carrier) : P₁.π ((ℓ₁ ∘ σ₂) (a w)) = h₁ (σ₁ (σ₂ (a w))) :=
    congrFun hsq₁ (σ₂ (a w))
  have hk₂ (w : W.carrier) : P₂.π ((ℓ₂ ∘ a) w) = h₂ (σ₁ (σ₂ (a w))) :=
    congrFun hsq₂ (a w)
  have hbase (w : W.carrier) :
      R₁.π.hom.left.base ⟨P₁.π ((ℓ₁ ∘ σ₂) (a w)), mem_univ _⟩ =
        R₂.π.hom.left.base ⟨P₂.π ((ℓ₂ ∘ a) w), mem_univ _⟩ := by
    have e₁ : (⟨P₁.π ((ℓ₁ ∘ σ₂) (a w)), mem_univ _⟩ : (univ : Set (SchemeComplexPoint R₁.fY))) =
        ⟨h₁ (σ₁ (σ₂ (a w))), mem_univ _⟩ := Subtype.ext (hk₁ w)
    have e₂ : (⟨P₂.π ((ℓ₂ ∘ a) w), mem_univ _⟩ : (univ : Set (SchemeComplexPoint R₂.fY))) =
        ⟨h₂ (σ₁ (σ₂ (a w))), mem_univ _⟩ := Subtype.ext (hk₂ w)
    rw [e₁, e₂]
    exact hpt₀ _
  have hpt (w : W.carrier) :
      schemeComplexPointMap R₁.fY f R₁.ρ R₁.comp_eq (P₁.π ((ℓ₁ ∘ σ₂) (a w))) =
        schemeComplexPointMap R₂.fY f R₂.ρ R₂.comp_eq (P₂.π ((ℓ₂ ∘ a) w)) := by
    rw [← R₁.point_eq, ← R₂.point_eq, hbase w]
  -- the flag `W•` induces the same valuation of `ℂ(X)` through both resolutions
  have hcomp := comap_modificationFlagValuation_eq f R₁.fY R₂.fY R₁.E R₂.E R₁.ρ R₁.comp_eq R₂.ρ
    R₂.comp_eq R₁.φ.toRingHom R₁.stalkCompatible R₂.φ.toRingHom R₂.stalkCompatible W hρ₁ hρ₂ hpt
  -- the lifting of `P₁`
  obtain ⟨hv₁, hval₁⟩ := OF2.modificationPresentationValue_lifting R₁.fY P₁.isModification hL₁
    (R₁.transport v) P₁.unitriangular P₁.presents (R₁.pullbackForm θ hθ)
    (R₁.pullbackPotential ψ) (R₁.isThetaPshPotential_pullback hXu θ hθ ψ hψ)
  set A₁ := (flagLiftingCorrectionMatrix (m + 1) P₁.F W _ hL₁)⁻¹ * P₁.G with hA₁def
  have hA₁ : IsUnitUpperTriangular A₁ :=
    (isUnitUpperTriangular_flagLiftingCorrectionMatrix (m + 1) P₁.F W _ hL₁).inv.mul
      P₁.unitriangular
  -- `ν` read on `W` through `Y₁`
  set V := (OF2.modificationFlagValuation R₁.fY W hρ₁).comap R₁.φ.toRingHom with hVdef
  have hvV : v = lexMapValuation A₁ hA₁ V := by
    rw [← R₁.transport_comap v, hv₁, lexMapValuation_comap]
  -- `ν` read on `W` through `Y₂`
  have h2 : R₂.transport v =
      lexMapValuation A₁ hA₁ (OF2.modificationFlagValuation R₂.fY W hρ₂) := by
    ext q
    have e : v (R₂.φ.symm q) = lexMapValuation A₁ hA₁ V (R₂.φ.symm q) := by rw [← hvV]
    refine e.trans ?_
    change lexWithTopHom A₁ hA₁ (V (R₂.φ.symm q)) =
      lexWithTopHom A₁ hA₁ (OF2.modificationFlagValuation R₂.fY W hρ₂ q)
    rw [hcomp]
    change lexWithTopHom A₁ hA₁
        (OF2.modificationFlagValuation R₂.fY W hρ₂ (R₂.φ (R₂.φ.symm q))) = _
    rw [RingEquiv.apply_symm_apply]
  -- hence `F₂•` and `W•` induce equivalent valuations of `ℂ(Y₂)`; recognition: `W•` lifts `F₂•`
  have hequiv : ValuationsLexEquivalent
      (OF2.modificationFlagValuation R₂.fY P₂.F P₂.isModification)
      (OF2.modificationFlagValuation R₂.fY W hρ₂) :=
    valuationsLexEquivalent_equivalence.trans ⟨P₂.G, P₂.unitriangular, P₂.presents⟩
      (valuationsLexEquivalent_equivalence.symm ⟨A₁, hA₁, h2⟩)
  obtain ⟨-, N, Ψ, hΨ, hR⟩ :=
    OF9.exists_isRationalEmbedding_of_isBlowupSequence R₂.fY R₂.E P₂.isBlowupSequence
  have hL₂ : IsFlagLifting P₂.F W (ℓ₂ ∘ a) :=
    OF9.isFlagLifting_of_lexEquivalent R₂.fY P₂.F W P₂.isModification hΨ hR hq hρ₂ hequiv
  -- the lifting of `P₂`
  obtain ⟨hv₂, hval₂⟩ := OF2.modificationPresentationValue_lifting R₂.fY P₂.isModification hL₂
    (R₂.transport v) P₂.unitriangular P₂.presents (R₂.pullbackForm θ hθ)
    (R₂.pullbackPotential ψ) (R₂.isThetaPshPotential_pullback hXu θ hθ ψ hψ)
  set A₂ := (flagLiftingCorrectionMatrix (m + 1) P₂.F W _ hL₂)⁻¹ * P₂.G with hA₂def
  have hA₂ : IsUnitUpperTriangular A₂ :=
    (isUnitUpperTriangular_flagLiftingCorrectionMatrix (m + 1) P₂.F W _ hL₂).inv.mul
      P₂.unitriangular
  -- the two matrices agree
  have hsurjT : Function.Surjective (R₂.transport v) := fun z => by
    obtain ⟨q, hq⟩ := hv z
    exact ⟨R₂.φ q, by change v (R₂.φ.symm (R₂.φ q)) = z; rw [RingEquiv.symm_apply_apply, hq]⟩
  have hsurjW : Function.Surjective (OF2.modificationFlagValuation R₂.fY W hρ₂) :=
    OF4.surjective_of_lexMapValuation_surjective hA₁ (h2 ▸ hsurjT)
  have hA : A₁ = A₂ := OF2.matrix_eq_of_lexMapValuation_eq hsurjW hA₁ hA₂ (h2.symm.trans hv₂)
  -- the two pulled-back currents on `W` agree
  have hmor : nativeMorphism hρ₁.1 ≫ R₁.π = nativeMorphism hρ₂.1 ≫ R₂.π :=
    morphism_eq_of_pointwise_eq _ _ (fun x => hbase x.val)
  have hcur : analyticModificationThetaCurrent hρ₁ (R₁.pullbackForm θ hθ)
      (R₁.pullbackPotential ψ) (R₁.isThetaPshPotential_pullback hXu θ hθ ψ hψ) =
      analyticModificationThetaCurrent hρ₂ (R₂.pullbackForm θ hθ)
      (R₂.pullbackPotential ψ) (R₂.isThetaPshPotential_pullback hXu θ hθ ψ hψ) := by
    unfold analyticModificationThetaCurrent
    apply thetaPotentialCurrent_congr'
    · have e₁ := nativePullback_comp_geometricallyEq R₁.π θ hρ₁.1
      have e₂ := nativePullback_comp_geometricallyEq R₂.π θ hρ₂.1
      rw [hmor] at e₁
      exact e₁.symm.trans e₂
    · funext w
      exact congrArg ψ (hbase w)
  -- conclusion
  change OF2.modificationPresentationValue R₁.fY P₁.F P₁.isModification P₁.G _ _ _ =
    OF2.modificationPresentationValue R₂.fY P₂.F P₂.isModification P₂.G _ _ _
  rw [← hval₁, ← hval₂]
  rw [hA]
  exact modificationPresentationValue_eq_of_current_eq R₁.fY R₂.fY W hρ₁ hρ₂ A₂ _ _ _ _ _ _
    hcur

/-! ### The definition of `ν(T)` -/

variable (f m) in
/-- **`rmk:valcurr`, the definition of `ν(T)`** for a normal projective `X`: the value
`ν_{Y•}(π^*T) g` of any presentation `ν = ν_{Y•} g` on a resolution `π : Y → X`
(`0` if `ν` has none), for `T = θ + dd^c ψ` on `X^an`. -/
def valuationCurrentValue (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (θ : SpaceForm (UnibAn.analytification f) 2) (hθ : PD.IsLocallyClosedOneOne θ)
    (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) : Fin (m + 1) → ℝ := by
  classical
  exact if h : Nonempty (Presentation f m v) then
    h.some.value (isUnibranch_analytification_of_normal f hX) θ hθ ψ hψ else 0

/-- **`rmk:valcurr`: `ν(T)` is well defined.** For a surjective `ν` of `ℂ(X)` (`X` normal
projective), EVERY presentation `ν = ν_{Y•} g` on EVERY resolution `π : Y → X` computes
`ν(T) = ν_{Y•}(π^*T) g`. -/
theorem valuationCurrentValue_eq (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (hv : Function.Surjective v) (Q : Presentation f m v)
    (θ : SpaceForm (UnibAn.analytification f) 2) (hθ : PD.IsLocallyClosedOneOne θ)
    (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) :
    valuationCurrentValue f m hX v θ hθ ψ hψ =
      Q.value (isUnibranch_analytification_of_normal f hX) θ hθ ψ hψ := by
  classical
  have h : Nonempty (Presentation f m v) := ⟨Q⟩
  unfold valuationCurrentValue
  rw [dif_pos h]
  exact Presentation.value_eq hX hv h.some Q θ hθ ψ hψ

/-! ### The book's presentations: a smooth flag on the resolution itself -/

/-- **The book's presentation** `ν = ν_{Y•} g` with a smooth flag `Y•` on the resolution `Y`
itself (`ν_{Y•}` read on `ℂ(X)` through `ρ^*`), as a presentation (`π = id` on `Y(ℂ)`,
`G = g`). -/
def Presentation.ofFlag {v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (R : Resolution f m) (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint R.fY))
    (hY : IsSmoothFlag Y) (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hG : IsUnitUpperTriangular G)
    (hpres : v = lexMapValuation G hG
      ((schemeFubiniStudyFunctionFieldValuation R.fY (m + 1) R.E Y hY).comap R.φ.toRingHom)) :
    Presentation f m v where
  R := R
  P := { F := schemeFubiniStudyOriginalFlagGeometry R.fY (m + 1) R.E Y hY
         π := id
         isModification := OF4.isAnalyticModification_flagGeometry_id R.fY R.E Y hY
         isBlowupSequence := IsBlowupSequence.refl
         G := G
         unitriangular := hG
         presents := by
          rw [OF4.modificationFlagValuation_id_eq R.fY R.E Y hY]
          ext q
          change v (R.φ.symm q) = _
          rw [hpres]
          change lexWithTopHom G hG (schemeFubiniStudyFunctionFieldValuation R.fY (m + 1) R.E Y hY
            (R.φ (R.φ.symm q))) = _
          rw [RingEquiv.apply_symm_apply]
          rfl }

/-- The value of the book's presentation is `ν_{Y•}(π^*T) g`: the flag valuation of the
pulled-back current `π^*T = π^*θ + dd^c(ψ ∘ π)` on `Y(ℂ)`, times `g`. -/
theorem Presentation.ofFlag_value
    {v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ)))}
    (R : Resolution f m) (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint R.fY))
    (hY : IsSmoothFlag Y) (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hG : IsUnitUpperTriangular G)
    (hpres : v = lexMapValuation G hG
      ((schemeFubiniStudyFunctionFieldValuation R.fY (m + 1) R.E Y hY).comap R.φ.toRingHom))
    (hXu : (UnibAn.analytification f).IsUnibranch)
    (θ : SpaceForm (UnibAn.analytification f) 2) (hθ : PD.IsLocallyClosedOneOne θ)
    (ψ : (UnibAn.analytification f).obj.left → EReal)
    (hψ : (UnibAn.analytification f).IsThetaPSH θ ψ) :
    (Presentation.ofFlag R Y hY G hG hpres).value hXu θ hθ ψ hψ =
      OF2.modificationPresentationValue R.fY
        (schemeFubiniStudyOriginalFlagGeometry R.fY (m + 1) R.E Y hY)
        (OF4.isAnalyticModification_flagGeometry_id R.fY R.E Y hY) G
        (R.pullbackForm θ hθ) (R.pullbackPotential ψ)
        (R.isThetaPshPotential_pullback hXu θ hθ ψ hψ) := rfl

end Main

end SGPT.Okounkov.OF12

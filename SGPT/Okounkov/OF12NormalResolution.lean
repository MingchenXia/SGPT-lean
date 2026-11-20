import SGPT.Okounkov.OF9ValCurrIndependence
import SGPT.Okounkov.SchemeComplexPointStalkEvaluation
import SGPT.Unibranch.UnibAnSpace

/-!
# `rmk:valcurr` for a normal projective variety: resolutions and `ℂ(X)`

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`: *"Suppose that `X` is a normal
projective variety. Consider a rank `n` (surjective) valuation `ν : ℂ(X)^× → ℤⁿ` and a closed
positive `(1,1)`-current `T` on `X`. Take a resolution `π : Y → X` such that there is a smooth
flag `Y•` on `Y` and `g ∈ Aut(ℤⁿ_lex)` such that `ν = ν_{Y•} g` …"*

For a singular normal `X` the flag valuation `ν_{Y•}` lives on `ℂ(Y)`, and it is read on `ℂ(X)`
through the birational morphism `ρ : Y → X`: `q ↦ ν_{Y•}(ρ^* q)`.  This file provides the
algebraic part of that reading.

* `schemeIsUnibranch_of_isIntegrallyClosed`, `isUnibranch_analytification_of_normal`: a normal
  (integral) scheme is unibranch, hence (`prop:unibranch_gaga`) its analytification `X^an` is a
  unibranch complex space; this is what makes `θ`-psh functions on `X^an` pull back to
  resolutions.
* `IsStalkCompatible ρ φ`: the field map `φ : ℂ(X) → ℂ(Y)` is the one induced by `ρ` (it extends
  every stalk map `𝒪_{X,ρ(y)} → 𝒪_{Y,y}`); for a birational `ρ` it is an isomorphism.
* `comap_modificationFlagValuation_eq` (**the comparison through `X`**): let `ρᵢ : Yᵢ → X`
  (`i = 1, 2`) be morphisms from integral smooth projective schemes with induced field maps
  `φᵢ`, and `κᵢ : W → Yᵢ(ℂ)` analytic modifications from a flagged compact Kähler manifold `W`
  with `ρ₁ ∘ κ₁ = ρ₂ ∘ κ₂` on complex points.  Then the valuations of `ℂ(X)` induced by the flag of
  `W` through the two sides coincide: `ν_{W•} ∘ κ₁^* ∘ φ₁ = ν_{W•} ∘ κ₂^* ∘ φ₂`.  Proof: on the
  local ring of `X` at the image of the flag point, both pulled-back germs are the germ of
  `w ↦ a(ρᵢ(κᵢ(w)))` (canonical evaluation of the original algebraic stalk at complex points,
  `schemeComplexPointStalkEval`, and its compatibility with scheme morphisms); `ℂ(X)` is the
  fraction field of that local ring.
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
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Unibranch
open scoped Topology Manifold ContDiff

/-! ### Normal schemes are unibranch -/

/-- A normal local domain is unibranch: its integral closure in its fraction field is itself. -/
theorem sourceUnibranchLocalRing_of_isIntegrallyClosed (R : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsIntegrallyClosed R] : SourceUnibranchLocalRing R := by
  rw [sourceUnibranchLocalRing_iff_of_isReduced]
  refine ⟨inferInstance, ?_⟩
  have hbot := IsIntegrallyClosed.integralClosure_eq_bot R (FractionRing R)
  let e : R →+* integralClosure R (FractionRing R) := (algebraMap R _)
  refine IsLocalRing.of_surjective' e ?_
  intro y
  have hy : (y : FractionRing R) ∈ (⊥ : Subalgebra R (FractionRing R)) := by
    rw [← hbot]
    exact y.property
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hy
  exact ⟨r, Subtype.ext hr⟩

/-- **A normal integral scheme is unibranch** (Stacks 0BQ2): its local rings are normal local
domains. -/
theorem schemeIsUnibranch_of_isIntegrallyClosed (X : Scheme) [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : SchemeIsUnibranch X := fun x =>
  have := hX x
  sourceUnibranchLocalRing_of_isIntegrallyClosed (X.presheaf.stalk x)

/-- **The analytification of a normal variety is unibranch.** For `X` integral, normal,
separated and of finite type over `ℂ`, the complex space `X^an` is unibranch
(`prop:unibranch_gaga`). -/
theorem isUnibranch_analytification_of_normal {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℂ)) [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    (UnibAn.analytification f).IsUnibranch :=
  UnibAn.analytification_isUnibranch_iff.mpr (schemeIsUnibranch_of_isIntegrallyClosed X hX)

/-! ### The field map induced by a morphism -/

/-- `φ : ℂ(X) → ℂ(Y)` **is induced by** `ρ : Y → X`: it extends every stalk map
`ρ^♯ : 𝒪_{X,ρ(y)} → 𝒪_{Y,y}`. For a dominant `ρ` there is exactly one such map (`ℂ(X)` is the
fraction field of each local ring); `ρ` is birational iff it is bijective. -/
def IsStalkCompatible {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (ρ : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField) : Prop :=
  ∀ (y : Y) (a : X.presheaf.stalk (ρ.base y)),
    φ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField ((ρ.stalkMap y).hom a)

/-- There is at most one field map induced by `ρ`. -/
theorem IsStalkCompatible.unique {X Y : Scheme} [IsIntegral X] [IsIntegral Y] {ρ : Y ⟶ X}
    {φ ψ : X.functionField →+* Y.functionField} (hφ : IsStalkCompatible ρ φ)
    (hψ : IsStalkCompatible ρ ψ) : φ = ψ := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  ext q
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (ρ.base y)) q
  rw [map_div₀, map_div₀, hφ y a, hφ y b, hψ y a, hψ y b]

/-! ### The comparison through `X` -/

section Comparison

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {Y₁ Y₂ : Scheme.{0}} [IsIntegral Y₁] [IsIntegral Y₂]
  (f₁ : Y₁ ⟶ Spec (.of ℂ)) (f₂ : Y₂ ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f₁] [IsSeparated f₁] [QuasiCompact f₁]
  [SmoothOfRelativeDimension (m + 1) f₂] [IsSeparated f₂] [QuasiCompact f₂]

local instance of12Top₁ : TopologicalSpace (SchemeComplexPoint f₁) :=
  schemeAnalyticPointTopology f₁
local instance of12Charts₁ : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f₁) :=
  schemeAnalyticTNChartedSpace f₁ (m + 1)
local instance of12Manifold₁ : IsComplexManifold (m + 1) (SchemeComplexPoint f₁) :=
  schemeAnalyticTN_isComplexManifold f₁ (m + 1)
local instance of12Top₂ : TopologicalSpace (SchemeComplexPoint f₂) :=
  schemeAnalyticPointTopology f₂
local instance of12Charts₂ : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f₂) :=
  schemeAnalyticTNChartedSpace f₂ (m + 1)
local instance of12Manifold₂ : IsComplexManifold (m + 1) (SchemeComplexPoint f₂) :=
  schemeAnalyticTN_isComplexManifold f₂ (m + 1)

/-- The canonical value of a section `r ∈ Γ(X, U)` at a complex point of `X` (zero off `U`). -/
def sectionValue (U : X.Opens) (r : Γ(X, U)) (p : SchemeComplexPoint f) : ℂ := by
  classical
  exact if hp : schemeComplexPointImage f p ∈ U then
    schemeComplexPointStalkEval f p ((X.presheaf.germ U _ hp).hom r) else 0

omit [IsIntegral X] [IsIntegral Y₁] in
/-- **The pulled-back germ of a section.** For `ρ : Y → X` over `ℂ` (`Y` smooth projective) and
an analytic map `κ : W → Y(ℂ)`, the pull-back along `κ` of the germ at `κ(w)` of `ρ^* r` is the
germ of `w' ↦ r(ρ(κ(w')))`. -/
theorem comap_stalkGerm_eq (E₁ : ClosedProjectiveEmbedding f₁) (ρ₁ : Y₁ ⟶ X) (h₁ : ρ₁ ≫ f = f₁)
    {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel (m + 1)) W]
    [IsComplexManifold (m + 1) W] {κ : W → SchemeComplexPoint f₁}
    (hκ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ κ) (w : W)
    (U : X.Opens) (r : Γ(X, U)) (hw : ρ₁.base (schemeComplexPointImage f₁ (κ w)) ∈ U) :
    ((NativeHolGerm.comap κ hκ w (schemeNativeStalkGerm f₁ (m + 1) (κ w)
        ((Y₁.presheaf.germ (ρ₁ ⁻¹ᵁ U) _ hw).hom ((ρ₁.app U).hom r))) :
        NativeHolGerm (m + 1) W w) : Germ (𝓝 w) ℂ) =
      ((sectionValue f U r ∘ schemeComplexPointMap f₁ f ρ₁ h₁ ∘ κ : W → ℂ) :
        Germ (𝓝 w) ℂ) := by
  rw [← schemeOpenRegularFunction_germ f₁ (m + 1) E₁ (ρ₁ ⁻¹ᵁ U) ((ρ₁.app U).hom r) (κ w) hw,
    NativeHolGerm.comap_mk]
  apply Germ.coe_eq.mpr
  have hO : IsOpen ((schemeComplexPointImage f₁ ∘ κ) ⁻¹' (ρ₁ ⁻¹ᵁ U : Set Y₁)) :=
    (ρ₁ ⁻¹ᵁ U).isOpen.preimage ((schemeComplexPointImage_continuous f₁).comp hκ.continuous)
  filter_upwards [hO.mem_nhds hw] with z hz
  have hz' : schemeComplexPointImage f₁ (κ z) ∈ ρ₁ ⁻¹ᵁ U := hz
  simp only [Function.comp_apply]
  rw [schemeOpenRegularFunction_apply f₁ (m + 1) E₁ _ _ _ hz', schemeNativeStalkGerm_eval]
  have hU : schemeComplexPointImage f (schemeComplexPointMap f₁ f ρ₁ h₁ (κ z)) ∈ U := hz'
  rw [sectionValue, dif_pos hU, schemeComplexPointStalkEval_comp f₁ f ρ₁ h₁ (κ z)]
  rw [RingHom.comp_apply]
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply ρ₁ U _ hz' r).symm

/-- On a section, the valuation read through `ρ₁` is the flag valuation of the germ of
`w ↦ r(ρ₁(κ₁(w)))`. -/
theorem modificationFlagValuation_germToFunctionField
    (E₁ : ClosedProjectiveEmbedding f₁) (ρ₁ : Y₁ ⟶ X) (h₁ : ρ₁ ≫ f = f₁)
    (φ₁ : X.functionField →+* Y₁.functionField) (hφ₁ : IsStalkCompatible ρ₁ φ₁)
    (W : OriginalFlagGeometry.{0} (m + 1)) {κ₁ : W.carrier → SchemeComplexPoint f₁}
    (hκ₁ : IsAnalyticModification (n := m + 1) κ₁) (U : X.Opens) [Nonempty U]
    (r : Γ(X, U))
    (hw : ρ₁.base (schemeComplexPointImage f₁ (κ₁ (OF2.modificationFlagPoint (m + 1) W).1)) ∈ U) :
    ∃ H : NativeHolGerm (m + 1) W.carrier (OF2.modificationFlagPoint (m + 1) W).1,
      (H : Germ (𝓝 (OF2.modificationFlagPoint (m + 1) W).1) ℂ) =
          ((sectionValue f U r ∘ schemeComplexPointMap f₁ f ρ₁ h₁ ∘ κ₁ : W.carrier → ℂ) :
            Germ (𝓝 (OF2.modificationFlagPoint (m + 1) W).1) ℂ) ∧
        OF2.modificationFlagValuation f₁ W hκ₁ (φ₁ ((X.germToFunctionField U).hom r)) =
          originalFlagGermValuation W (OF2.modificationFlagPoint (m + 1) W) H := by
  set w₀ := (OF2.modificationFlagPoint (m + 1) W).1 with hw₀
  refine ⟨NativeHolGerm.comap κ₁ hκ₁.1 w₀ (schemeNativeStalkGerm f₁ (m + 1) (κ₁ w₀)
      ((Y₁.presheaf.germ (ρ₁ ⁻¹ᵁ U) _ hw).hom ((ρ₁.app U).hom r))),
    comap_stalkGerm_eq f f₁ E₁ ρ₁ h₁ hκ₁.1 w₀ U r hw, ?_⟩
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hw r, hφ₁,
    Scheme.Hom.germ_stalkMap_apply ρ₁ U _ hw r, OF2.modificationFlagValuation_stalk]

/-- **The comparison through `X`.** Let `ρᵢ : Yᵢ → X` be morphisms over `ℂ` from integral smooth
projective schemes with induced field maps `φᵢ`, and `κᵢ : W → Yᵢ(ℂ)` analytic modifications
from a flagged compact Kähler manifold with `ρ₁ ∘ κ₁ = ρ₂ ∘ κ₂` on complex points. Then the
valuations of `ℂ(X)` induced by the flag `W•` through the two sides coincide:
`ν_{W•} ∘ κ₁^* ∘ φ₁ = ν_{W•} ∘ κ₂^* ∘ φ₂`. -/
theorem comap_modificationFlagValuation_eq (E₁ : ClosedProjectiveEmbedding f₁)
    (E₂ : ClosedProjectiveEmbedding f₂) (ρ₁ : Y₁ ⟶ X) (h₁ : ρ₁ ≫ f = f₁) (ρ₂ : Y₂ ⟶ X)
    (h₂ : ρ₂ ≫ f = f₂) (φ₁ : X.functionField →+* Y₁.functionField)
    (hφ₁ : IsStalkCompatible ρ₁ φ₁) (φ₂ : X.functionField →+* Y₂.functionField)
    (hφ₂ : IsStalkCompatible ρ₂ φ₂) (W : OriginalFlagGeometry.{0} (m + 1))
    {κ₁ : W.carrier → SchemeComplexPoint f₁} (hκ₁ : IsAnalyticModification (n := m + 1) κ₁)
    {κ₂ : W.carrier → SchemeComplexPoint f₂} (hκ₂ : IsAnalyticModification (n := m + 1) κ₂)
    (hpt : ∀ w, schemeComplexPointMap f₁ f ρ₁ h₁ (κ₁ w) = schemeComplexPointMap f₂ f ρ₂ h₂ (κ₂ w)) :
    (OF2.modificationFlagValuation f₁ W hκ₁).comap φ₁ =
      (OF2.modificationFlagValuation f₂ W hκ₂).comap φ₂ := by
  set w₀ := (OF2.modificationFlagPoint (m + 1) W).1 with hw₀
  set x := ρ₁.base (schemeComplexPointImage f₁ (κ₁ w₀)) with hx
  have hx₂ : ρ₂.base (schemeComplexPointImage f₂ (κ₂ w₀)) = x :=
    (congrArg (schemeComplexPointImage f) (hpt w₀)).symm
  have hfun : schemeComplexPointMap f₁ f ρ₁ h₁ ∘ κ₁ = schemeComplexPointMap f₂ f ρ₂ h₂ ∘ κ₂ :=
    funext hpt
  -- agreement on the local ring of `X` at `x`
  have key : ∀ a : X.presheaf.stalk x,
      OF2.modificationFlagValuation f₁ W hκ₁ (φ₁ (algebraMap _ X.functionField a)) =
        OF2.modificationFlagValuation f₂ W hκ₂ (φ₂ (algebraMap _ X.functionField a)) := by
    intro a
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField X hxU r]
    obtain ⟨H₁, hH₁, e₁⟩ := modificationFlagValuation_germToFunctionField f f₁ E₁ ρ₁ h₁ φ₁ hφ₁ W
      hκ₁ U r hxU
    obtain ⟨H₂, hH₂, e₂⟩ := modificationFlagValuation_germToFunctionField f f₂ E₂ ρ₂ h₂ φ₂ hφ₂ W
      hκ₂ U r (hx₂ ▸ hxU)
    rw [e₁, e₂]
    congr 1
    apply Subtype.ext
    rw [hH₁, hH₂, hfun]
  apply AddValuation.ext
  intro q
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x) q
  change OF2.modificationFlagValuation f₁ W hκ₁ (φ₁ _) =
    OF2.modificationFlagValuation f₂ W hκ₂ (φ₂ _)
  rw [map_div₀ φ₁, map_div₀ φ₂, AddValuation.map_div, AddValuation.map_div, key a, key b]

end Comparison

end SGPT.Okounkov.OF12

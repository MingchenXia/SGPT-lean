import SGPT.Unibranch.KSManifoldForm
import SGPT.Unibranch.UnibNSIEnvelope
import SGPT.Unibranch.ComplexSpaceThetaBimeromorphicPullback
import SGPT.Unibranch.OriginalCommonResolution

/-!
# The `𝓘`-envelope on a unibranch compact Kähler space

Source `def:unibranch:L212` (`appendix_unibranch.tex`, §`sec:unib_ext`): let `X` be an
irreducible unibranch compact Kähler space of dimension `n`, `θ` a closed real smooth
`(1,1)`-form on `X` and `φ ∈ PSH(X, θ)`.  Then `P_θ[φ]_𝓘 ∈ PSH(X, θ)` is *the unique element*
such that `π^* P_θ[φ]_𝓘 = P_{π^*θ}[π^*φ]_𝓘` for every proper bimeromorphic morphism
`π : Y → X` from a compact Kähler manifold `Y`; "it follows from `cor:PSH` and
`prop:Ienvelopebimero` that `P_θ[φ]_𝓘` is independent of the choice of `π` and is well-defined."

Formalization, with the project's existing objects only:

* complex spaces `SourceReducedComplexSpace`, smooth forms `SpaceForm`, `θ`-psh functions
  `SourceReducedComplexSpace.IsThetaPSH` (`def:unibranch:L105`), proper bimeromorphic morphisms
  `IsProperBimeromorphic`;
* a compact Kähler manifold `Y` is a manifold with `KahlerBackground`, viewed as the complex space
  `wholeModel Y`; `π^*θ` is the manifold form `KSManifoldForm.manifoldPullback θ π`;
* `P_{π^*θ}[π^*φ]_𝓘` is the manifold `𝓘`-envelope `iSingularityEnvelope` (`def:Ienv`).

`IsUnibranchIEnvelope n X θ φ ψ` is the defining property.  `existsUnique_isUnibranchIEnvelope`
proves the well-definedness asserted by the book (exactly one `ψ` has the property) for every
unibranch `X`, every closed `(1,1)` form `θ` and every `φ ∈ PSH(X, θ)`, from

* a resolution `π₀ : Y₀ → X` by a connected compact Kähler manifold (`KahlerResolution`), and
* the reverse-descent half of `cor:PSH` along this `π₀` (`CorPSHDescentAlong`; `cor:PSH` is
  proved by lane PD; until then it is a hypothesis named after it).

The proof is the book's: `cor:PSH` descends `P_{π₀^*θ}[π₀^*φ]_𝓘` to `ψ ∈ PSH(X, θ)`; for any
other `π : Y → X`, a common resolution `Z` (`OriginalCommonResolution`) and
`prop:Ienvelopebimero` (`SGPT.Okounkov.iSingularityEnvelope_modification_pullback`) on
`Z → Y` and `Z → Y₀` give `π^*ψ = P_{π^*θ}[π^*φ]_𝓘`; uniqueness is `π = π₀` and surjectivity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

namespace SGPT.Unibranch.KSUnibranchIEnvelope

open SourceReducedComplexSpace OriginalNativeModification KSManifoldForm

/-- The points map `Y → X` of a morphism `π : wholeModel Y ⟶ X`. -/
def pt {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {X : SourceReducedComplexSpace} (π : wholeModel (n := n) Y ⟶ X) :
    Y → X.obj.left :=
  fun y => π.hom.left.base ⟨y, mem_univ y⟩

/-- **Source `def:unibranch:L212`: the defining property of `P_θ[φ]_𝓘`.**  `ψ` is `θ`-psh on the
complex space `X`, and for every proper bimeromorphic morphism `π : Y → X` from a compact Kähler
manifold `Y` (of the dimension `n` of `X`), `π^*ψ = P_{π^*θ}[π^*φ]_𝓘`. -/
def IsUnibranchIEnvelope (n : ℕ) (X : SourceReducedComplexSpace) (θ : SpaceForm X 2)
    (φ ψ : X.obj.left → EReal) : Prop :=
  X.IsThetaPSH θ ψ ∧
    ∀ (Y : Type) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
      [CompactSpace Y], Nonempty (KahlerBackground n Y) →
      ∀ π : wholeModel (n := n) Y ⟶ X, IsProperBimeromorphic π →
        (fun y => ψ (pt π y)) =
          iSingularityEnvelope (manifoldPullback θ π) (fun y => φ (pt π y))

/-- A resolution of `X` by a connected compact Kähler manifold of dimension `n`. -/
structure KahlerResolution (n : ℕ) (X : SourceReducedComplexSpace) where
  /-- The resolving manifold. -/
  Y : Type
  [topologicalSpace : TopologicalSpace Y]
  [chartedSpace : ChartedSpace (ComplexModel n) Y]
  [isComplexManifold : IsComplexManifold n Y]
  [compactSpace : CompactSpace Y]
  [connectedSpace : ConnectedSpace Y]
  /-- A Kähler form on `Y`. -/
  kahler : KahlerBackground n Y
  /-- The resolution morphism. -/
  map : wholeModel (n := n) Y ⟶ X
  isProperBimeromorphic : IsProperBimeromorphic map

attribute [instance] KahlerResolution.topologicalSpace KahlerResolution.chartedSpace
  KahlerResolution.isComplexManifold KahlerResolution.compactSpace KahlerResolution.connectedSpace

/-- **The reverse-descent half of `cor:PSH`** along a proper bimeromorphic `π : Y → X`: every
`π^*θ`-psh function on `Y` is the pull-back of a `θ`-psh function on `X`.  (`cor:PSH` is proved by
lane PD; this is the exact hypothesis used below.) -/
def CorPSHDescentAlong {X Y : SourceReducedComplexSpace} (π : Y ⟶ X) (θ : SpaceForm X 2) :
    Prop :=
  ∀ v : Y.obj.left → EReal, Y.IsThetaPSH (SpaceForm.pullback θ π) v →
    ∃ u : X.obj.left → EReal, X.IsThetaPSH θ u ∧ ∀ y, u (π.hom.left.base y) = v y

section Lemmas

variable {n : ℕ} {X : SourceReducedComplexSpace}

private theorem surjective_of_isProperBimeromorphic {Y : SourceReducedComplexSpace}
    {p : Y ⟶ X} (hp : IsProperBimeromorphic p) : Function.Surjective p.hom.left.base := by
  obtain ⟨hprop, Z, _hZa, hZt, _hpre, V, j, _hj, _hjr, _hjp, hjpr⟩ := hp
  have hclosed : IsClosed (range p.hom.left.base) := hprop.isClosedMap.isClosed_range
  have hsub : Zᶜ ⊆ range p.hom.left.base := by
    rw [← hjpr]
    rintro _ ⟨v, rfl⟩
    exact ⟨j.base v, rfl⟩
  have hdense : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp hZt
  have h := (hdense.mono hsub).closure_eq
  rw [hclosed.closure_eq] at h
  exact range_eq_univ.mp h

theorem pt_surjective {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {π : wholeModel (n := n) Y ⟶ X} (hπ : IsProperBimeromorphic π) :
    Function.Surjective (pt π) := by
  intro x
  obtain ⟨p, hp⟩ := surjective_of_isProperBimeromorphic hπ x
  exact ⟨p.val, hp⟩

/-- The pull-back of a `θ`-psh function on a unibranch space along a proper bimeromorphic
morphism from a manifold is a `π^*θ`-psh potential on the manifold. -/
theorem isThetaPshPotential_pullback (hX : X.IsUnibranch) {θ : SpaceForm X 2}
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : wholeModel (n := n) Y ⟶ X} (hπ : IsProperBimeromorphic π) :
    IsThetaPshPotential (manifoldPullback θ π) (fun y => φ (pt π y)) := by
  have h1 : (wholeModel (n := n) Y).IsThetaPSH (SpaceForm.pullback θ π)
      (ofManifold (fun y => φ (pt π y))) :=
    hφ.pullback_of_isProperBimeromorphic hX π hπ
  have hd : Dense {p : (wholeModel (n := n) Y).obj.left | φ (π.hom.left.base p) ≠ ⊥} :=
    hφ.dense_finite_pullback_of_isProperBimeromorphic hX hπ
  have hd' : Dense {y : Y | φ (pt π y) ≠ ⊥} := by
    have h := hd.preimage (Homeomorph.Set.univ Y).symm.isOpenMap
    refine Dense.mono ?_ h
    intro y hy
    exact hy
  exact isThetaPshPotential_of_isThetaPSH_of_dense h1 hd'

/-- Holomorphic maps from a common model: if `π ∘ g₀ = π₀ ∘ g₁` on points then
`g₀^*(π^*θ)` and `g₁^*(π₀^*θ)` are the same form. -/
theorem pullback_manifoldPullback_geometricallyEq (θ : SpaceForm X 2)
    {Y₀ Y₁ Z : Type} [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n Y₀] [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁]
    [IsComplexManifold n Y₁] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z]
    (π₀ : wholeModel (n := n) Y₀ ⟶ X) (π₁ : wholeModel (n := n) Y₁ ⟶ X)
    {g₀ : Z → Y₀} {g₁ : Z → Y₁}
    (hg₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀)
    (hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁)
    (hpt : ∀ z, pt π₀ (g₀ z) = pt π₁ (g₁ z)) :
    (SmoothRealForm.pullback hg₀ (manifoldPullback θ π₀)).GeometricallyEq
      (SmoothRealForm.pullback hg₁ (manifoldPullback θ π₁)) := by
  have hcongr : manifoldPullback θ (nativeMorphism hg₀ ≫ π₀) =
      manifoldPullback θ (nativeMorphism hg₁ ≫ π₁) :=
    manifoldPullback_congr θ (fun z => hpt z)
  have h0 := manifoldPullback_nativeMorphism θ π₀ hg₀
  have h1 := manifoldPullback_nativeMorphism θ π₁ hg₁
  rw [hcongr] at h0
  exact h0.trans h1.symm

end Lemmas

/-- **Source `def:unibranch:L212`, well-definedness.**  Let `X` be a unibranch complex space with
a resolution `π₀ : Y₀ → X` by a connected compact Kähler manifold of dimension `n`, let `θ` be a
closed smooth real `(1,1)`-form on `X` and `φ ∈ PSH(X, θ)`.  Assuming the reverse-descent half of
`cor:PSH` along `π₀`, there is exactly one `ψ` with the defining property of `P_θ[φ]_𝓘`: `ψ` is
`θ`-psh and `π^*ψ = P_{π^*θ}[π^*φ]_𝓘` for **every** proper bimeromorphic `π : Y → X` from a
compact Kähler manifold `Y`. -/
theorem existsUnique_isUnibranchIEnvelope {n : ℕ} {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (θ : SpaceForm X 2) (hθc : θ.IsClosed) (hθ : θ.IsOneOne)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) (R : KahlerResolution n X)
    (hdesc : CorPSHDescentAlong R.map θ) :
    ∃! ψ : X.obj.left → EReal, IsUnibranchIEnvelope n X θ φ ψ := by
  -- the envelope upstairs on `Y₀`
  let η₀ : ClosedRealOneOneForm n R.Y := manifoldPullbackClosed θ hθc hθ R.map
  let u₀ : R.Y → EReal := fun y => φ (pt R.map y)
  have hu₀ : IsThetaPshPotential η₀.val u₀ :=
    isThetaPshPotential_pullback hX hφ R.isProperBimeromorphic
  let E₀ : R.Y → EReal := iSingularityEnvelope η₀.val u₀
  have hE₀ : IsThetaPshPotential η₀.val E₀ :=
    iSingularityEnvelope_isThetaPshPotential η₀.val η₀.property.1 η₀.property.2
      hu₀.1.hasSmoothLocalPotentials u₀ hu₀
  -- `cor:PSH`: the envelope descends to `X`
  have hE₀' : (wholeModel (n := n) R.Y).IsThetaPSH (SpaceForm.pullback θ R.map)
      (ofManifold E₀) :=
    isThetaPSH_of_isThetaPshPotential (θ := SpaceForm.pullback θ R.map) hE₀
  obtain ⟨ψ, hψ, hψE⟩ := hdesc (ofManifold E₀) hE₀'
  have hψpt : (fun y => ψ (pt R.map y)) = E₀ := funext fun y => hψE ⟨y, mem_univ y⟩
  -- the defining property for every model
  have hprop : ∀ (Y : Type) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
      [IsComplexManifold n Y] [CompactSpace Y] (π : wholeModel (n := n) Y ⟶ X),
      IsProperBimeromorphic π →
        (fun y => ψ (pt π y)) =
          iSingularityEnvelope (manifoldPullback θ π) (fun y => φ (pt π y)) := by
    intro Y _ _ _ _ π hπ
    obtain ⟨Z, _, _, _, _, _, g₀, g₁, hg₀, hg₁, hbase, -⟩ :=
      OriginalCommonResolution.exists_original_common_model_of_isProperBimeromorphic
        (Y₀ := Y) (Y₁ := R.Y) π R.map hπ R.isProperBimeromorphic
    have hpt : ∀ z, pt π (g₀ z) = pt R.map (g₁ z) := fun z => congrFun hbase z
    have : Nonempty Y := ⟨g₀ (Classical.arbitrary Z)⟩
    let η : ClosedRealOneOneForm n Y := manifoldPullbackClosed θ hθc hθ π
    let u : Y → EReal := fun y => φ (pt π y)
    have hu : IsThetaPshPotential η.val u := isThetaPshPotential_pullback hX hφ hπ
    -- `prop:Ienvelopebimero` on both legs of the common model
    have P₀ := SGPT.Okounkov.iSingularityEnvelope_modification_pullback hg₀ η hu
    have P₁ := SGPT.Okounkov.iSingularityEnvelope_modification_pullback hg₁ η₀ hu₀
    have hforms : (ClosedRealOneOneForm.pullback hg₀.1 η).val.GeometricallyEq
        (ClosedRealOneOneForm.pullback hg₁.1 η₀).val := by
      rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val]
      exact pullback_manifoldPullback_geometricallyEq θ π R.map hg₀.1 hg₁.1 hpt
    have hfun : u ∘ g₀ = u₀ ∘ g₁ := funext fun z => congrArg φ (hpt z)
    have hZ : (iSingularityEnvelope η.val u) ∘ g₀ = E₀ ∘ g₁ := by
      rw [← P₀]
      refine Eq.trans ?_ P₁
      rw [hfun]
      exact BimeromorphicIEnvelope.iSingularityEnvelope_congr hforms _
    have hcomp : (fun y => ψ (pt π y)) ∘ g₀ = (iSingularityEnvelope η.val u) ∘ g₀ := by
      rw [hZ, ← hψpt]
      funext z
      exact congrArg ψ (hpt z)
    funext y
    obtain ⟨z, rfl⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hg₀ y
    exact congrFun hcomp z
  refine ⟨ψ, ⟨hψ, ?_⟩, ?_⟩
  · intro Y _ _ _ _ _ π hπ
    exact hprop Y π hπ
  -- uniqueness: test the defining property on `π₀` itself
  rintro ψ' ⟨-, hψ'⟩
  have h0 := hψ' R.Y ⟨R.kahler⟩ R.map R.isProperBimeromorphic
  have h1 := hprop R.Y R.map R.isProperBimeromorphic
  funext x
  obtain ⟨y, rfl⟩ := pt_surjective R.isProperBimeromorphic x
  exact congrFun (h0.trans h1.symm) y

/-- **`P_θ[φ]_𝓘` on a unibranch space** (`def:unibranch:L212`), under the hypotheses of
`existsUnique_isUnibranchIEnvelope`. -/
def unibranchIEnvelope {n : ℕ} {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (θ : SpaceForm X 2) (hθc : θ.IsClosed) (hθ : θ.IsOneOne)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) (R : KahlerResolution n X)
    (hdesc : CorPSHDescentAlong R.map θ) : X.obj.left → EReal :=
  (existsUnique_isUnibranchIEnvelope hX θ hθc hθ hφ R hdesc).exists.choose

theorem unibranchIEnvelope_spec {n : ℕ} {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (θ : SpaceForm X 2) (hθc : θ.IsClosed) (hθ : θ.IsOneOne)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) (R : KahlerResolution n X)
    (hdesc : CorPSHDescentAlong R.map θ) :
    IsUnibranchIEnvelope n X θ φ (unibranchIEnvelope hX θ hθc hθ hφ R hdesc) :=
  (existsUnique_isUnibranchIEnvelope hX θ hθc hθ hφ R hdesc).exists.choose_spec

/-- **Independence of the resolution.**  The element `P_θ[φ]_𝓘` produced from one Kähler
resolution satisfies the defining identity on every other compact Kähler model, and two Kähler
resolutions produce the same function. -/
theorem unibranchIEnvelope_eq {n : ℕ} {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (θ : SpaceForm X 2) (hθc : θ.IsClosed) (hθ : θ.IsOneOne)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) (R R' : KahlerResolution n X)
    (hdesc : CorPSHDescentAlong R.map θ) (hdesc' : CorPSHDescentAlong R'.map θ) :
    unibranchIEnvelope hX θ hθc hθ hφ R hdesc = unibranchIEnvelope hX θ hθc hθ hφ R' hdesc' :=
  (existsUnique_isUnibranchIEnvelope hX θ hθc hθ hφ R hdesc).unique
    (unibranchIEnvelope_spec hX θ hθc hθ hφ R hdesc)
    (unibranchIEnvelope_spec hX θ hθc hθ hφ R' hdesc')

end SGPT.Unibranch.KSUnibranchIEnvelope

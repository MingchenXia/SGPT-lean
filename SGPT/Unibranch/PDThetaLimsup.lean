import SGPT.Unibranch.PDLimsup
import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Unibranch.ComplexSpaceThetaUnibranchDescent
import SGPT.Unibranch.ComplexSpaceThetaBimeromorphicPullback

/-!
# The limsup formula for `θ`-psh functions and the reverse descent of `cor:PSH`

* `IsThetaPSH.eq_limsup_compl`: on every complex space `X`, a `θ`-psh function `η`
  (`def:unibranch:L105`) satisfies `η(x) = limsup_{X \ Z ∋ y → x} η(y)` for every analytic subset
  `Z` with empty interior (the psh case of `PDLimsup` applied to `g + η` in the local embeddings
  carrying local potentials `g` of `θ`).
* The pull-back map of `cor:PSH`, `π^* : PSH(X, θ) → PSH(Y, π^*θ)`, for a proper bimeromorphic
  `π : Y → X` onto a unibranch space (`thetaPSHPullback`), is injective
  (`thetaPSHPullback_injective`), and it is bijective iff every `u ∈ PSH(Y, π^*θ)` descends to a
  `θ`-psh function (`thetaPSHPullback_bijective_iff`).
* `descent_eq_limsup`: the (unique, `exists_unique_usc_descent_of_isProperBimeromorphic`)
  upper semicontinuous descent `v` of `u ∈ PSH(Y, π^*θ)` is the Grauert--Remmert upper-limit
  extension of its values off the exceptional locus: `v(x) = limsup_{X \ Z ∋ y → x} v(y)` for every
  analytic `Z ⊆ X` whose preimage has empty interior (in particular the exceptional locus of `π`).

What remains open in `cor:PSH` is that this upper-limit extension is `θ`-psh near the singular
points of `X`, i.e. the ambient extension of the Fornæss--Narasimhan theorem (`thm:FN`, (2) ⇒ (1),
[FN80]) together with the ramified lifting of discs through `π` (equivalently the existence part
of `thm:GRexten2` (2)).

Lane PD, blueprint `pd.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces

namespace SGPT.Unibranch.PD

open SourceReducedComplexSpace

noncomputable section

/-- Off a set with empty interior, the punctured neighbourhood filter is nontrivial. -/
theorem nhdsWithin_compl_neBot {α : Type*} [TopologicalSpace α] {Z : Set α}
    (hZi : interior Z = ∅) (x : α) : (𝓝[Zᶜ] x).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, (interior_eq_empty_iff_dense_compl.mp hZi).closure_eq]
  trivial

/-- `θ`-psh functions are bounded at every point by their upper limit off a nowhere dense
analytic subset. -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsThetaPSH.le_limsup_compl
    {X : SourceReducedComplexSpace} {θ : SpaceForm X 2}
    {η : X.obj.left → EReal} (hη : X.IsThetaPSH θ η) {Z : Set X.obj.left}
    (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅) (z : X.obj.left) :
    η z ≤ limsup η (𝓝[Zᶜ] z) := by
  obtain ⟨e, ⟨c, rfl⟩, -, g, hg, -, hpsh⟩ := hη z
  let V := sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic
  have hZ₁ : V.IsAnalyticSubset ((embeddingMorphism e).hom.left.base ⁻¹' Z) :=
    hZ.preimage (embeddingMorphism e)
  have hZ₁i : interior ((embeddingMorphism e).hom.left.base ⁻¹' Z) = ∅ := by
    change interior (e.toPoint ⁻¹' Z) = ∅
    rw [← e.isOpenEmbedding_toPoint.isOpenMap.preimage_interior_eq_interior_preimage
      e.isOpenEmbedding_toPoint.continuous, hZi, preimage_empty]
  have h1 := SGPT.Unibranch.PD.le_limsup_compl hpsh.2 hZ₁ hZ₁i c
  change (g c.val.val : EReal) + η (e.toPoint c) ≤
    limsup (fun c' : e.carrier => (g c'.val.val : EReal) + η (e.toPoint c'))
      (𝓝[(e.toPoint ⁻¹' Z)ᶜ] c) at h1
  have hZ₁i' : interior (e.toPoint ⁻¹' Z) = ∅ := hZ₁i
  have := nhdsWithin_compl_neBot hZ₁i' c
  have hgc : ContinuousAt (fun c' : e.carrier => g c'.val.val) c := by
    have h := (hg.continuousOn.continuousAt (e.ambient.isOpen.mem_nhds c.val.property))
    have hv : ContinuousAt (fun c' : e.carrier => (c'.val.val : ComplexModel e.dim)) c :=
      (continuous_subtype_val.comp continuous_subtype_val).continuousAt
    exact ContinuousAt.comp (g := g) h hv
  have hglim : limsup (fun c' : e.carrier => (g c'.val.val : EReal))
      (𝓝[(e.toPoint ⁻¹' Z)ᶜ] c) = (g c.val.val : EReal) := by
    apply Tendsto.limsup_eq
    exact ((continuous_coe_real_ereal.tendsto _).comp hgc.tendsto).mono_left nhdsWithin_le_nhds
  have hadd := EReal.limsup_add_le (f := 𝓝[(e.toPoint ⁻¹' Z)ᶜ] c)
    (u := fun c' : e.carrier => (g c'.val.val : EReal)) (v := fun c' => η (e.toPoint c'))
    (by rw [hglim]; exact Or.inl (EReal.coe_ne_bot _))
    (by rw [hglim]; exact Or.inl (EReal.coe_ne_top _))
  rw [hglim] at hadd
  have ht : Tendsto e.toPoint (𝓝[(e.toPoint ⁻¹' Z)ᶜ] c) (𝓝[Zᶜ] (e.toPoint c)) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨(e.isOpenEmbedding_toPoint.continuous.tendsto c).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with c' hc'
    exact hc'
  have hmap : limsup (fun c' : e.carrier => η (e.toPoint c')) (𝓝[(e.toPoint ⁻¹' Z)ᶜ] c) ≤
      limsup η (𝓝[Zᶜ] (e.toPoint c)) := by
    change limsup (η ∘ e.toPoint) _ ≤ _
    rw [limsup_comp]
    exact limsup_le_limsup_of_le ht
  have h2 : (g c.val.val : EReal) + η (e.toPoint c) ≤
      (g c.val.val : EReal) + limsup η (𝓝[Zᶜ] (e.toPoint c)) :=
    h1.trans (hadd.trans (add_le_add le_rfl hmap))
  exact EReal.addLECancellable_coe _ h2

/-- **Limsup formula for `θ`-psh functions on complex spaces.** -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsThetaPSH.eq_limsup_compl
    {X : SourceReducedComplexSpace} {θ : SpaceForm X 2}
    {η : X.obj.left → EReal} (hη : X.IsThetaPSH θ η) {Z : Set X.obj.left}
    (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅) (x : X.obj.left) :
    η x = limsup η (𝓝[Zᶜ] x) :=
  le_antisymm (hη.le_limsup_compl hZ hZi x) (limsup_compl_le hη.upperSemicontinuous Z x)

/-- `θ`-psh functions agreeing off a nowhere dense analytic subset agree everywhere. -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsThetaPSH.eq_of_eqOn_compl
    {X : SourceReducedComplexSpace} {θ : SpaceForm X 2}
    {η₁ η₂ : X.obj.left → EReal} (h₁ : X.IsThetaPSH θ η₁) (h₂ : X.IsThetaPSH θ η₂)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅)
    (heq : EqOn η₁ η₂ Zᶜ) : η₁ = η₂ := by
  funext x
  rw [h₁.eq_limsup_compl hZ hZi x, h₂.eq_limsup_compl hZ hZi x]
  apply limsup_congr
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact heq hy

/-! ### The pull-back map of `cor:PSH` -/

/-- Source `cor:PSH`: the pull-back map `π^* : PSH(X, θ) → PSH(Y, π^*θ)` for a proper bimeromorphic
morphism `π : Y → X` onto a unibranch complex space. -/
def thetaPSHPullback {X Y : SourceReducedComplexSpace} (θ : SpaceForm X 2) (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) :
    {φ : X.obj.left → EReal // X.IsThetaPSH θ φ} →
      {ψ : Y.obj.left → EReal // Y.IsThetaPSH (SpaceForm.pullback θ π) ψ} :=
  fun φ => ⟨fun y => φ.val (π.hom.left.base y),
    φ.property.pullback_of_isProperBimeromorphic hX π hπ⟩

@[simp] theorem thetaPSHPullback_apply {X Y : SourceReducedComplexSpace} (θ : SpaceForm X 2)
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    (φ : {φ : X.obj.left → EReal // X.IsThetaPSH θ φ}) (y : Y.obj.left) :
    (thetaPSHPullback θ π hπ hX φ).val y = φ.val (π.hom.left.base y) := rfl

/-- Source `cor:PSH`, injectivity ("injectivity follows from the surjectivity of `π`"). -/
theorem thetaPSHPullback_injective {X Y : SourceReducedComplexSpace} (θ : SpaceForm X 2)
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) :
    Function.Injective (thetaPSHPullback θ π hπ hX) := by
  intro φ₁ φ₂ h
  apply Subtype.ext
  funext x
  obtain ⟨y, rfl⟩ := hπ.surjective x
  exact congrFun (congrArg Subtype.val h) y

/-- Source `cor:PSH` is equivalent to the descent statement: every `π^*θ`-psh function on `Y` is
the pull-back of a `θ`-psh function on `X`. -/
theorem thetaPSHPullback_bijective_iff {X Y : SourceReducedComplexSpace} (θ : SpaceForm X 2)
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch) :
    Function.Bijective (thetaPSHPullback θ π hπ hX) ↔
      ∀ ψ : Y.obj.left → EReal, Y.IsThetaPSH (SpaceForm.pullback θ π) ψ →
        ∃ φ : X.obj.left → EReal, X.IsThetaPSH θ φ ∧ ∀ y, φ (π.hom.left.base y) = ψ y := by
  constructor
  · intro h ψ hψ
    obtain ⟨φ, hφ⟩ := h.2 ⟨ψ, hψ⟩
    exact ⟨φ.val, φ.property, fun y => congrFun (congrArg Subtype.val hφ) y⟩
  · intro h
    refine ⟨thetaPSHPullback_injective θ π hπ hX, ?_⟩
    rintro ⟨ψ, hψ⟩
    obtain ⟨φ, hφ, hφψ⟩ := h ψ hψ
    exact ⟨⟨φ, hφ⟩, Subtype.ext (funext hφψ)⟩

/-- **Source `cor:PSH`, reverse descent off the exceptional locus.** Let `π : Y → X` be proper
bimeromorphic onto a unibranch space, `u ∈ PSH(Y, π^*θ)` and `v` its upper semicontinuous descent
(`v ∘ π = u`). For every analytic `Z ⊆ X` whose preimage has empty interior (e.g. the exceptional
locus of `π`), `v` is the upper-limit extension of its values on `X \ Z`:
`v(x) = limsup_{X \ Z ∋ y → x} v(y)`. -/
theorem descent_eq_limsup {X Y : SourceReducedComplexSpace} (θ : SpaceForm X 2) (π : Y ⟶ X)
    (hπ : IsProperBimeromorphic π) {u : Y.obj.left → EReal}
    (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u) {v : X.obj.left → EReal}
    (hvusc : UpperSemicontinuous v) (hvu : ∀ y, v (π.hom.left.base y) = u y)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z)
    (hZi : interior (π.hom.left.base ⁻¹' Z) = ∅) (x : X.obj.left) :
    v x = limsup v (𝓝[Zᶜ] x) := by
  refine le_antisymm ?_ (limsup_compl_le hvusc Z x)
  obtain ⟨y, rfl⟩ := hπ.surjective x
  have h1 := hu.le_limsup_compl (hZ.preimage π) hZi y
  have hfun : u = v ∘ π.hom.left.base := funext fun y' => (hvu y').symm
  rw [hfun, limsup_comp] at h1
  refine h1.trans (limsup_le_limsup_of_le ?_)
  refine tendsto_nhdsWithin_iff.mpr
    ⟨(π.hom.left.base.hom.continuous.tendsto y).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y' hy'
  exact hy'

/-- The existing unique upper semicontinuous descent of `cor:PSH` is the upper-limit extension
across the exceptional locus `Z` of `π` (`v = limsup` off `Z`). -/
theorem exists_unique_usc_descent_eq_limsup {X Y : SourceReducedComplexSpace}
    (θ : SpaceForm X 2) (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (hX : X.IsUnibranch)
    {u : Y.obj.left → EReal} (hu : Y.IsThetaPSH (SpaceForm.pullback θ π) u) :
    ∃ Z : Set X.obj.left, X.IsAnalyticSubset Z ∧ interior Z = ∅ ∧ IsIsoOver π Zᶜ ∧
      ∃! v : X.obj.left → EReal, UpperSemicontinuous v ∧
        (∀ y, v (π.hom.left.base y) = u y) ∧ ∀ x, v x = limsup v (𝓝[Zᶜ] x) := by
  obtain ⟨hprop, Z, hZ, hZi, hZpi, hiso⟩ := hπ
  have hπ' : IsProperBimeromorphic π := ⟨hprop, Z, hZ, hZi, hZpi, hiso⟩
  refine ⟨Z, hZ, hZi, hiso, ?_⟩
  obtain ⟨v, ⟨hvusc, hvu⟩, hvuniq⟩ :=
    hu.exists_unique_usc_descent_of_isProperBimeromorphic θ π hπ' hX
  refine ⟨v, ⟨hvusc, hvu, descent_eq_limsup θ π hπ' hu hvusc hvu hZ hZpi⟩, ?_⟩
  intro w hw
  exact hvuniq w ⟨hw.1, hw.2.1⟩

end

end SGPT.Unibranch.PD

import SGPT.Unibranch.KSUnibranchIEnvelope
import SGPT.Unibranch.OriginalSmoothDimension

/-!
# Manifolds resolving the same complex space have the same dimension

In `def:unibranch:L212` the defining identity is required for every proper bimeromorphic
`π : Y → X` from a compact Kähler manifold `Y`; `IsUnibranchIEnvelope n X θ φ ψ` quantifies over
manifolds of the dimension `n` of `X`.  This file shows that nothing is lost: two manifolds with
proper bimeromorphic morphisms onto the same nonempty complex space have the same dimension
(`dim_eq_of_isProperBimeromorphic`), so the defining identity holds for proper bimeromorphic
morphisms from compact Kähler manifolds of *any* dimension
(`IsUnibranchIEnvelope.of_any_dimension`).

Proof: over a point of the common good locus both morphisms are isomorphisms, so the native
charts of the two manifolds give open immersions of domains of `ℂ^m` and `ℂ^n` through the same
point of `X`; two such charts have equal dimension (the complex derivative of the transition is a
linear isomorphism, `OriginalSmoothDimension.native_iso_dimension_eq`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex

namespace SGPT.Unibranch.KSUnibranchIEnvelope

open SourceReducedComplexSpace OriginalNativeModification KSManifoldForm

private def isoOfRangeEq' {A B T : LocallyRingedSpace} (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (h : range f.base = range g.base) : A ≅ B where
  hom := LocallyRingedSpace.IsOpenImmersion.lift g f (le_of_eq h)
  inv := LocallyRingedSpace.IsOpenImmersion.lift f g (le_of_eq h.symm)
  hom_inv_id := by
    apply (cancel_mono f).mp
    simp only [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono g).mp
    simp only [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      Category.id_comp]

private theorem nativeMap_point' {n m : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    {f : M → N} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f) :
    ChartedSpace.locallyRingedSpaceMap f hf ≫ ambientPointMap m N = ambientPointMap n M :=
  (ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel n))
    (IN := 𝓘(ℂ, ComplexModel m)) (IP := 𝓘(ℂ, ComplexModel 0)) hf
    (show ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel 0) ∞
      (fun _ : N => (0 : ComplexModel 0)) from contMDiff_const)).symm

/-- Two open immersions of complex manifolds (with their sheaves of holomorphic functions) into a
complex space through a common point have equal dimensions. -/
theorem manifold_chart_dimension_eq {X : SourceReducedComplexSpace} {n₀ n₁ : ℕ} {M₀ M₁ : Type}
    [TopologicalSpace M₀] [ChartedSpace (ComplexModel n₀) M₀] [IsComplexManifold n₀ M₀]
    [TopologicalSpace M₁] [ChartedSpace (ComplexModel n₁) M₁] [IsComplexManifold n₁ M₁]
    (i₀ : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n₀) M₀ ⟶ X.obj.left)
    (i₁ : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n₁) M₁ ⟶ X.obj.left)
    (hi₀ : LocallyRingedSpace.IsOpenImmersion i₀)
    (hi₁ : LocallyRingedSpace.IsOpenImmersion i₁)
    (hp₀ : i₀ ≫ X.obj.hom = ambientPointMap n₀ M₀)
    (hp₁ : i₁ ≫ X.obj.hom = ambientPointMap n₁ M₁)
    (x : X.obj.left) (hx₀ : x ∈ range i₀.base) (hx₁ : x ∈ range i₁.base) : n₀ = n₁ := by
  let := hi₀
  let := hi₁
  let O₀ : Opens M₀ := ⟨i₀.base ⁻¹' range i₁.base,
    hi₁.base_open.isOpen_range.preimage i₀.base.hom.continuous⟩
  let O₁ : Opens M₁ := ⟨i₁.base ⁻¹' range i₀.base,
    hi₀.base_open.isOpen_range.preimage i₁.base.hom.continuous⟩
  let j₀ := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O₀ → M₀)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n₀)))
  let j₁ := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O₁ → M₁)
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel n₁)))
  let f₀ := j₀ ≫ i₀
  let f₁ := j₁ ≫ i₁
  have hr : range f₀.base = range f₁.base := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := u.property
      exact ⟨⟨v, ⟨u.val, hv.symm⟩⟩, hv⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := v.property
      exact ⟨⟨u, ⟨v.val, hu.symm⟩⟩, hu⟩
  let e := isoOfRangeEq' f₀ f₁ hr
  have he : e.hom ≫ f₁ = f₀ :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac f₁ f₀ (le_of_eq hr)
  have hf₀ : f₀ ≫ X.obj.hom = ambientPointMap n₀ O₀ := by
    rw [show f₀ = j₀ ≫ i₀ from rfl, Category.assoc, hp₀]
    exact nativeMap_point' contMDiff_subtype_val
  have hf₁ : f₁ ≫ X.obj.hom = ambientPointMap n₁ O₁ := by
    rw [show f₁ = j₁ ≫ i₁ from rfl, Category.assoc, hp₁]
    exact nativeMap_point' contMDiff_subtype_val
  have hep : e.hom ≫ ambientPointMap n₁ O₁ = ambientPointMap n₀ O₀ := by
    rw [← hf₁, ← Category.assoc, he, hf₀]
  obtain ⟨u, hu⟩ := hx₀
  have huO : u ∈ O₀ := by
    change i₀.base u ∈ range i₁.base
    rwa [hu]
  exact OriginalSmoothDimension.native_iso_dimension_eq e hep ⟨u, huO⟩

/-- A morphism `π : V → X` from a manifold which is an isomorphism over `U` gives, through every
point of `U`, an open immersion into `X` of a manifold of the dimension of `V`. -/
theorem exists_manifold_chart_of_isIsoOver {X : SourceReducedComplexSpace} {m : ℕ} {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (π : wholeModel (n := m) Y ⟶ X) {U : Set X.obj.left} (hU : IsIsoOver π U)
    {x : X.obj.left} (hx : x ∈ U) :
    ∃ (O : Type) (_ : TopologicalSpace O) (_ : ChartedSpace (ComplexModel m) O)
      (_ : IsComplexManifold m O)
      (f : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel m) O ⟶ X.obj.left),
      LocallyRingedSpace.IsOpenImmersion f ∧ f ≫ X.obj.hom = ambientPointMap m O ∧
        x ∈ range f.base := by
  obtain ⟨V, j, hj, hjr, hjp, hjpr⟩ := hU
  have hxr : x ∈ range (j ≫ π.hom.left).base := by rw [hjpr]; exact hx
  obtain ⟨v, hv⟩ := hxr
  let y := j.base v
  obtain ⟨V', i, hi, hip, hyi⟩ := exists_native_chart (n := m) (univ : Set Y)
    (AnalyticIrreducibleComponents.regularAtDim_univ (n := m) (y : (wholeModel (n := m) Y).obj.left).val)
  let := hi
  let := hj
  let O : Opens V' := ⟨i.base ⁻¹' range j.base,
    hj.base_open.isOpen_range.preimage i.base.hom.continuous⟩
  let k := ChartedSpace.locallyRingedSpaceMap (Subtype.val : O → V')
    (contMDiff_subtype_val (I := 𝓘(ℂ, ComplexModel m)))
  have hk : LocallyRingedSpace.IsOpenImmersion k := inferInstance
  let := hk
  let g := k ≫ i
  have hg : range g.base ⊆ range j.base := by
    rintro _ ⟨w, rfl⟩
    exact w.property
  have := LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j g hg
  let L := LocallyRingedSpace.IsOpenImmersion.lift j g hg
  have hL : LocallyRingedSpace.IsOpenImmersion L := by
    show LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift j g hg)
    dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  let := hL
  let := hjp
  refine ⟨O, inferInstance, inferInstance, inferInstance, L ≫ (j ≫ π.hom.left), inferInstance,
    ?_, ?_⟩
  · have hLj : L ≫ j = g := LocallyRingedSpace.IsOpenImmersion.lift_fac j g hg
    rw [← Category.assoc, hLj, Category.assoc, Over.w π.hom]
    change k ≫ i ≫ subspacePointMap (n := m) (univ : Set Y) = _
    rw [hip]
    exact nativeMap_point' contMDiff_subtype_val
  · obtain ⟨a, ha⟩ := hyi
    have haO : a ∈ O := by
      change i.base a ∈ range j.base
      exact ⟨v, ha.symm⟩
    refine ⟨⟨a, haO⟩, ?_⟩
    have hLj : L ≫ j = g := LocallyRingedSpace.IsOpenImmersion.lift_fac j g hg
    have h1 : j.base (L.base ⟨a, haO⟩) = j.base v := by
      have := congrArg (fun h => h.base ⟨a, haO⟩) hLj
      exact this.trans ha
    have h2 : L.base ⟨a, haO⟩ = v := hj.base_open.injective h1
    change π.hom.left.base (j.base (L.base ⟨a, haO⟩)) = x
    rw [h2]
    exact hv

/-- **Dimension invariance.** Two manifolds with proper bimeromorphic morphisms onto the same
complex space, the first one nonempty, have the same dimension. -/
theorem dim_eq_of_isProperBimeromorphic {X : SourceReducedComplexSpace} {m n : ℕ}
    {Y Y₀ : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
    [Nonempty Y] (π : wholeModel (n := m) Y ⟶ X) (π₀ : wholeModel (n := n) Y₀ ⟶ X)
    (hπ : IsProperBimeromorphic π) (hπ₀ : IsProperBimeromorphic π₀) : m = n := by
  obtain ⟨-, Z, hZa, hZt, -, hiso⟩ := hπ
  obtain ⟨-, Z₀, hZ₀a, hZ₀t, -, hiso₀⟩ := hπ₀
  have hZc : IsClosed Z := hZa.isClosed
  have hZ₀c : IsClosed Z₀ := hZ₀a.isClosed
  have hint : interior (Z ∪ Z₀) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hZc hZ₀t]
    exact hZt
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hne : (Z ∪ Z₀)ᶜ.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    have : (π.hom.left.base ⟨y, mem_univ y⟩) ∈ interior (Z ∪ Z₀) := by
      rw [h, interior_univ]
      trivial
    rw [hint] at this
    exact this
  obtain ⟨x, hx⟩ := hne
  have hx₁ : x ∈ Zᶜ := fun h => hx (Or.inl h)
  have hx₂ : x ∈ Z₀ᶜ := fun h => hx (Or.inr h)
  obtain ⟨O, _, _, _, f, hf, hfp, hxf⟩ := exists_manifold_chart_of_isIsoOver π hiso hx₁
  obtain ⟨O₀, _, _, _, f₀, hf₀, hf₀p, hxf₀⟩ := exists_manifold_chart_of_isIsoOver π₀ hiso₀ hx₂
  exact manifold_chart_dimension_eq f f₀ hf hf₀ hfp hf₀p x hxf hxf₀

/-- **`def:unibranch:L212`: the defining identity holds for compact Kähler manifolds of every
dimension.** If `ψ` has the defining property (stated for manifolds of the dimension `n` of `X`)
and `X` has a resolution by a nonempty `n`-dimensional manifold, then
`π^*ψ = P_{π^*θ}[π^*φ]_𝓘` for every proper bimeromorphic `π : Y → X` from a nonempty compact
Kähler manifold `Y` of any dimension `m` (which then equals `n`). -/
theorem IsUnibranchIEnvelope.of_any_dimension {n : ℕ} {X : SourceReducedComplexSpace}
    {θ : SpaceForm X 2} {φ ψ : X.obj.left → EReal} (h : IsUnibranchIEnvelope n X θ φ ψ)
    (R : KahlerResolution n X) {m : ℕ} (Y : Type) [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y] [CompactSpace Y] [Nonempty Y]
    (hK : Nonempty (KahlerBackground m Y)) (π : wholeModel (n := m) Y ⟶ X)
    (hπ : IsProperBimeromorphic π) :
    (fun y => ψ (pt π y)) =
      iSingularityEnvelope (manifoldPullback θ π) (fun y => φ (pt π y)) := by
  obtain rfl := dim_eq_of_isProperBimeromorphic π R.map hπ R.isProperBimeromorphic
  exact h.2 Y hK π hπ

/-- **Source `def:unibranch:L212`: the defining property of `P_θ[φ]_𝓘`, for compact Kähler manifolds
of every dimension.**  `ψ` is `θ`-psh on `X` and `π^*ψ = P_{π^*θ}[π^*φ]_𝓘` for every proper
bimeromorphic morphism `π : Y → X` from a compact Kähler manifold `Y` (of any dimension). -/
def IsUnibranchIEnvelopeAnyDim (X : SourceReducedComplexSpace) (θ : SpaceForm X 2)
    (φ ψ : X.obj.left → EReal) : Prop :=
  X.IsThetaPSH θ ψ ∧
    ∀ (m : ℕ) (Y : Type) [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
      [IsComplexManifold m Y] [CompactSpace Y], Nonempty (KahlerBackground m Y) →
      ∀ π : wholeModel (n := m) Y ⟶ X, IsProperBimeromorphic π →
        (fun y => ψ (pt π y)) =
          iSingularityEnvelope (manifoldPullback θ π) (fun y => φ (pt π y))

/-- In presence of a resolution by an `n`-dimensional connected manifold, the defining property for
manifolds of every dimension is the one for manifolds of dimension `n`. -/
theorem isUnibranchIEnvelopeAnyDim_iff {n : ℕ} {X : SourceReducedComplexSpace}
    {θ : SpaceForm X 2} {φ ψ : X.obj.left → EReal} (R : KahlerResolution n X) :
    IsUnibranchIEnvelopeAnyDim X θ φ ψ ↔ IsUnibranchIEnvelope n X θ φ ψ := by
  constructor
  · rintro ⟨hψ, h⟩
    exact ⟨hψ, fun Y _ _ _ _ hK π hπ => h n Y hK π hπ⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro m Y _ _ _ _ hK π hπ
    rcases isEmpty_or_nonempty Y with hY | hY
    · funext y
      exact (IsEmpty.false y).elim
    · exact h.of_any_dimension R Y hK π hπ

/-- **Source `def:unibranch:L212`, well-definedness, with compact Kähler manifolds of every
dimension.** For `X` unibranch with a resolution by a connected compact Kähler manifold, `θ` closed of
type `(1,1)` and `φ ∈ PSH(X, θ)`, exactly one function has the defining property of `P_θ[φ]_𝓘`,
given the reverse descent of `cor:PSH` along the resolution. -/
theorem existsUnique_isUnibranchIEnvelopeAnyDim {n : ℕ} {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (θ : SpaceForm X 2) (hθc : θ.IsClosed) (hθ : θ.IsOneOne)
    {φ : X.obj.left → EReal} (hφ : X.IsThetaPSH θ φ) (R : KahlerResolution n X)
    (hdesc : CorPSHDescentAlong R.map θ) :
    ∃! ψ : X.obj.left → EReal, IsUnibranchIEnvelopeAnyDim X θ φ ψ := by
  obtain ⟨ψ, hψ, huniq⟩ := existsUnique_isUnibranchIEnvelope hX θ hθc hθ hφ R hdesc
  exact ⟨ψ, (isUnibranchIEnvelopeAnyDim_iff R).mpr hψ,
    fun ψ' hψ' => huniq ψ' ((isUnibranchIEnvelopeAnyDim_iff R).mp hψ')⟩

end SGPT.Unibranch.KSUnibranchIEnvelope

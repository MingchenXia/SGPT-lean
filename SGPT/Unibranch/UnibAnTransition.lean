import SGPT.Unibranch.UnibAnChart
import SGPT.Foundations.Analysis.Pending.HironakaIntrinsicMorphismGluingAnalytic

/-!
# Analytic transition maps between two embedded affine charts

Let `e, e'` be embedded affine charts of a scheme `X` over `ℂ` (`UnibAnChart`), with complex
models `V(I) ⊆ ℂⁿ` and `V(I') ⊆ ℂⁿ'` (`chartModel`, the project's reduced analytic model
`modelOver ⊤ V(I)`, i.e. the complex space `polynomialZeroSetComplexSpace I`).

* `overlapOpen e e'`: an open set of `ℂⁿ` whose trace on `V(I)` is exactly the set of points
  whose complex point of `X` lies in the chart `e'` (`mem_overlapOpen_iff`); `overlapModel e e'`
  is the analytic model of this trace, an open subspace of `chartModel e` (`overlapIncl`).
* `transition e e' : overlapModel e e' ⟶ overlapModel e' e`: the analytic transition map, a
  morphism of locally ringed spaces over the complex point. It is glued
  (`HironakaIntrinsicMorphismGluing.exists_unique_over`) from the holomorphic maps
  `z ↦ (p_k(z) / r(z)^{m_k})_k` of `exists_local_fracMap` on the open sets `r ≠ 0`; the local
  pieces agree on overlaps because morphisms into a reduced model are determined by their
  points (`HironakaIntrinsicMorphismGluingAnalytic.morphism_eq_of_base_eq`).
* `transition_chartPoint`: the transition preserves the complex points of `X`; morphisms into
  the models are determined by these points (`hom_ext_chartModel`, `hom_ext_overlapModel`).

Lane UNIB-AN; blueprint `claude-unib-an.tex`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
open scoped Manifold ContDiff

namespace SGPT.Unibranch.UnibAn

noncomputable section

open SGPT.Unibranch SGPT.Foundations.Schemes

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}

theorem comp_base_apply {A B C : LocallyRingedSpace} (F : A ⟶ B) (G : B ⟶ C) (x : A) :
    (F ≫ G).base x = G.base (F.base x) := rfl

/-! ### Chart models -/

/-- The coordinate space `ℂⁿ` of a chart, as the open `⊤ ⊆ ℂⁿ`. -/
abbrev Amb (e : EmbeddedChart f) := ↥(⊤ : Opens (ComplexModel e.dim))

/-- The analytic model `V(I)` of an embedded chart: the reduced complex space
`polynomialZeroSetComplexSpace I`. -/
abbrev chartModel (e : EmbeddedChart f) : LocallyRingedSpace :=
  actualSubspaceLocallyRingedSpace (n := e.dim) (polynomialZeroSet e.ideal)

/-- The structure morphism of the chart model to the complex point. -/
abbrev chartPointMap (e : EmbeddedChart f) : chartModel e ⟶ complexPoint :=
  subspacePointMap (n := e.dim) (polynomialZeroSet e.ideal)

theorem chartModel_hasAnalyticCharts (e : EmbeddedChart f) :
    hasAnalyticCharts (Over.mk (chartPointMap e)) :=
  hasAnalyticCharts_model ⊤ (polynomialZeroSet e.ideal)
    (polynomialZeroSet_isComplexAnalyticSubset e.ideal)

/-- Morphisms into a chart model are determined by the complex points of `X` they hit. -/
theorem hom_ext_chartModel (e : EmbeddedChart f) {T : LocallyRingedSpace}
    (σT : T ⟶ complexPoint) (hT : hasAnalyticCharts (Over.mk σT))
    (F G : T ⟶ chartModel e) (hF : F ≫ chartPointMap e = σT) (hG : G ≫ chartPointMap e = σT)
    (h : ∀ x, chartPoint e (F.base x) = chartPoint e (G.base x)) : F = G := by
  apply HironakaIntrinsicMorphismGluingAnalytic.morphism_eq_of_base_eq σT hT F G hF hG
  ext x
  exact chartPoint_injective e (h x)

/-! ### Overlaps -/

/-- The points of `V(I)` whose complex point of `X` lies in the chart `e'`. -/
def overlapSet (e e' : EmbeddedChart f) : Set (polynomialZeroSet e.ideal) :=
  {c | ∃ d, chartPoint e' d = chartPoint e c}

/-- The data of a local regular transition at a point of the overlap. -/
structure LocalFrac (e e' : EmbeddedChart f) (c : polynomialZeroSet e.ideal) where
  /-- The denominator. -/
  r : MvPolynomial (Fin e.dim) ℂ
  /-- The numerators. -/
  p : Fin e'.dim → MvPolynomial (Fin e.dim) ℂ
  /-- The exponents. -/
  m : Fin e'.dim → ℕ
  ne : polyEval r (c.val : ComplexModel e.dim) ≠ 0
  spec : ∀ c' : polynomialZeroSet e.ideal, polyEval r (c'.val : ComplexModel e.dim) ≠ 0 →
    ∃ d' : polynomialZeroSet e'.ideal,
      (d'.val : ComplexModel e'.dim) = fracMap r p m (c'.val : ComplexModel e.dim) ∧
      chartPoint e' d' = chartPoint e c'

theorem overlapSet_spec {e e' : EmbeddedChart f} (c : overlapSet e e') :
    ∃ d, chartPoint e' d = chartPoint e c.val :=
  c.property

/-- A chosen local regular transition at every point of the overlap. -/
def localFrac (e e' : EmbeddedChart f) (c : overlapSet e e') : LocalFrac e e' c.val := by
  choose r p m hc H using exists_local_fracMap e e' c.val (overlapSet_spec c).choose
    (overlapSet_spec c).choose_spec
  exact ⟨r, p, m, hc, H⟩

/-- An open set of `ℂⁿ` whose trace on `V(I)` is the overlap with the chart `e'`. -/
def overlapOpen (e e' : EmbeddedChart f) : Opens (Amb e) :=
  ⟨⋃ c : overlapSet e e', {z : Amb e | polyEval (localFrac e e' c).r (z : ComplexModel e.dim) ≠ 0},
    isOpen_iUnion fun c =>
      (isOpen_ne_fun (contDiff_polyEval (localFrac e e' c).r).continuous continuous_const).preimage
        continuous_subtype_val⟩

theorem coe_overlapOpen (e e' : EmbeddedChart f) :
    (overlapOpen e e' : Set (Amb e)) =
      ⋃ c : overlapSet e e',
        {z : Amb e | polyEval (localFrac e e' c).r (z : ComplexModel e.dim) ≠ 0} :=
  rfl

theorem mem_overlapOpen_iff (e e' : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    c.val ∈ overlapOpen e e' ↔ c ∈ overlapSet e e' := by
  rw [← SetLike.mem_coe, coe_overlapOpen, Set.mem_iUnion]
  constructor
  · intro hc
    obtain ⟨c₀, hc₀⟩ := hc
    obtain ⟨d', _, hd'⟩ := (localFrac e e' c₀).spec c hc₀
    exact ⟨d', hd'⟩
  · intro hc
    exact ⟨⟨c, hc⟩, (localFrac e e' ⟨c, hc⟩).ne⟩

theorem mem_overlapSet_symm {e e' : EmbeddedChart f} {c : polynomialZeroSet e.ideal}
    {d : polynomialZeroSet e'.ideal} (h : chartPoint e' d = chartPoint e c) :
    d ∈ overlapSet e' e :=
  ⟨c, h.symm⟩

/-- The trace of `overlapOpen e e'` on `V(I)`. -/
abbrev overlapCarrier (e e' : EmbeddedChart f) : Set (overlapOpen e e') :=
  (Subtype.val : overlapOpen e e' → Amb e) ⁻¹' polynomialZeroSet e.ideal

/-- The analytic model of the overlap of the charts `e` and `e'`, inside the chart `e`. -/
abbrev overlapModel (e e' : EmbeddedChart f) : LocallyRingedSpace :=
  actualSubspaceLocallyRingedSpace (n := e.dim) (overlapCarrier e e')

/-- The structure morphism of the overlap model. -/
abbrev overlapPointMap (e e' : EmbeddedChart f) : overlapModel e e' ⟶ complexPoint :=
  subspacePointMap (n := e.dim) (overlapCarrier e e')

/-- The open immersion of the overlap model into the chart model. -/
abbrev overlapIncl (e e' : EmbeddedChart f) : overlapModel e e' ⟶ chartModel e :=
  actualOpenSubspaceMap (n := e.dim) (polynomialZeroSet e.ideal) (overlapOpen e e')

theorem overlapIncl_point (e e' : EmbeddedChart f) :
    overlapIncl e e' ≫ chartPointMap e = overlapPointMap e e' :=
  actualSubspaceMap_point (f := (Subtype.val : overlapOpen e e' → Amb e)) contMDiff_subtype_val
    (fun _ hx => hx)

/-- The point of `V(I)` underlying a point of the overlap model. -/
def ovPt {e e' : EmbeddedChart f} (u : overlapCarrier e e') : polynomialZeroSet e.ideal :=
  ⟨u.val.val, u.property⟩

theorem overlapIncl_base (e e' : EmbeddedChart f) (u : overlapCarrier e e') :
    (overlapIncl e e').base u = ovPt u := rfl

theorem ovPt_injective (e e' : EmbeddedChart f) :
    Function.Injective (ovPt (e := e) (e' := e')) := by
  intro u v h
  have h1 : (u.val.val : Amb e) = v.val.val :=
    congrArg (fun x : polynomialZeroSet e.ideal => (x.val : Amb e)) h
  exact Subtype.ext (Subtype.ext h1)

theorem ovPt_mem (e e' : EmbeddedChart f) (u : overlapCarrier e e') :
    ovPt u ∈ overlapSet e e' :=
  (mem_overlapOpen_iff e e' (ovPt u)).mp u.val.property

/-- The overlap point lying over a point of the overlap set. -/
def ofOverlapSet {e e' : EmbeddedChart f} (c : polynomialZeroSet e.ideal)
    (hc : c ∈ overlapSet e e') : overlapCarrier e e' :=
  ⟨⟨c.val, (mem_overlapOpen_iff e e' c).mpr hc⟩, c.property⟩

theorem ovPt_ofOverlapSet {e e' : EmbeddedChart f} (c : polynomialZeroSet e.ideal)
    (hc : c ∈ overlapSet e e') : ovPt (ofOverlapSet c hc) = c := rfl

theorem overlapModel_hasAnalyticCharts (e e' : EmbeddedChart f) :
    hasAnalyticCharts (Over.mk (overlapPointMap e e')) :=
  HironakaIntrinsicMorphismGluingAnalytic.hasAnalyticCharts_of_openImmersion _ _
    (chartModel_hasAnalyticCharts e) (overlapIncl e e') (overlapIncl_point e e')

/-- Morphisms into an overlap model are determined by the complex points of `X` they hit. -/
theorem hom_ext_overlapModel (e e' : EmbeddedChart f) {T : LocallyRingedSpace}
    (σT : T ⟶ complexPoint) (hT : hasAnalyticCharts (Over.mk σT))
    (F G : T ⟶ overlapModel e e') (hF : F ≫ overlapPointMap e e' = σT)
    (hG : G ≫ overlapPointMap e e' = σT)
    (h : ∀ x, chartPoint e (ovPt (F.base x)) = chartPoint e (ovPt (G.base x))) : F = G := by
  apply HironakaIntrinsicMorphismGluingAnalytic.morphism_eq_of_base_eq σT hT F G hF hG
  ext x
  exact ovPt_injective e e' (chartPoint_injective e (h x))

/-- Open immersions over the complex point into a space with analytic charts give spaces with
analytic charts. -/
theorem hasAnalyticCharts_comp {T S : LocallyRingedSpace} (σS : S ⟶ complexPoint)
    (hS : hasAnalyticCharts (Over.mk σS)) (j : T ⟶ S) [LocallyRingedSpace.IsOpenImmersion j] :
    hasAnalyticCharts (Over.mk (j ≫ σS)) :=
  HironakaIntrinsicMorphismGluingAnalytic.hasAnalyticCharts_of_openImmersion _ _ hS j rfl

/-! ### Local transition maps -/

section Local

variable (e e' : EmbeddedChart f) (u : overlapCarrier e e')

/-- The local regular transition data at a point of the overlap model. -/
abbrev locFrac : LocalFrac e e' (ovPt u) := localFrac e e' ⟨ovPt u, ovPt_mem e e' u⟩

/-- The image of `overlapOpen e' e` in `ℂⁿ'`. -/
def targetSet : Set (ComplexModel e'.dim) :=
  Subtype.val '' (overlapOpen e' e : Set (Amb e'))

theorem isOpen_targetSet : IsOpen (targetSet e e') :=
  (⊤ : Opens (ComplexModel e'.dim)).isOpen.isOpenMap_subtype_val _ (overlapOpen e' e).isOpen

/-- The ambient open of the local transition: `r ≠ 0`, and the transition lands in the
overlap of `e'` with `e`. -/
def localAmbient : Set (ComplexModel e.dim) :=
  {z | polyEval (locFrac e e' u).r z ≠ 0} ∩
    fracMap (locFrac e e' u).r (locFrac e e' u).p (locFrac e e' u).m ⁻¹' targetSet e e'

theorem isOpen_localAmbient : IsOpen (localAmbient e e' u) := by
  apply ContinuousOn.isOpen_inter_preimage _
    (isOpen_ne_fun (contDiff_polyEval _).continuous continuous_const) (isOpen_targetSet e e')
  intro z hz
  exact (contDiffAt_fracMap _ _ _ hz).continuousAt.continuousWithinAt

/-- The local open of the overlap on which the transition is given by one fraction. -/
def localOpen : Opens (overlapOpen e e') :=
  ⟨(fun w : overlapOpen e e' => ((w.val : Amb e) : ComplexModel e.dim)) ⁻¹' localAmbient e e' u,
    (isOpen_localAmbient e e' u).preimage (continuous_subtype_val.comp continuous_subtype_val)⟩

theorem mem_targetSet {d : polynomialZeroSet e'.ideal} (hd : d ∈ overlapSet e' e) :
    (d.val : ComplexModel e'.dim) ∈ targetSet e e' :=
  ⟨d.val, (mem_overlapOpen_iff e' e d).mpr hd, rfl⟩

theorem mem_localOpen_iff (w : overlapOpen e e') : w ∈ localOpen e e' u ↔
    polyEval (locFrac e e' u).r ((w.val : Amb e) : ComplexModel e.dim) ≠ 0 ∧
      fracMap (locFrac e e' u).r (locFrac e e' u).p (locFrac e e' u).m
        ((w.val : Amb e) : ComplexModel e.dim) ∈ targetSet e e' :=
  Iff.rfl

theorem localOpen_ne (w : localOpen e e' u) :
    polyEval (locFrac e e' u).r ((w.val.val : Amb e) : ComplexModel e.dim) ≠ 0 :=
  ((mem_localOpen_iff e e' u w.val).mp w.property).1

theorem localOpen_target (w : localOpen e e' u) :
    fracMap (locFrac e e' u).r (locFrac e e' u).p (locFrac e e' u).m
      ((w.val.val : Amb e) : ComplexModel e.dim) ∈ targetSet e e' :=
  ((mem_localOpen_iff e e' u w.val).mp w.property).2

theorem self_mem_localOpen : u.val ∈ localOpen e e' u := by
  rw [mem_localOpen_iff]
  refine ⟨(locFrac e e' u).ne, ?_⟩
  obtain ⟨d', hd', hpt⟩ := (locFrac e e' u).spec (ovPt u) (locFrac e e' u).ne
  change fracMap _ _ _ ((ovPt u).val : ComplexModel e.dim) ∈ targetSet e e'
  rw [← hd']
  exact mem_targetSet e e' (mem_overlapSet_symm hpt)

/-- The trace of the local open on `V(I)`. -/
abbrev localCarrier : Set (localOpen e e' u) :=
  (Subtype.val : localOpen e e' u → overlapOpen e e') ⁻¹' overlapCarrier e e'

/-- The local model of the overlap. -/
abbrev localModel : LocallyRingedSpace :=
  actualSubspaceLocallyRingedSpace (n := e.dim) (localCarrier e e' u)

/-- Its open immersion into the overlap model. -/
abbrev localIncl : localModel e e' u ⟶ overlapModel e e' :=
  actualOpenSubspaceMap (n := e.dim) (overlapCarrier e e') (localOpen e e' u)

theorem fracMap_mem (w : localOpen e e' u) :
    ∃ y : overlapOpen e' e, ((y.val : Amb e') : ComplexModel e'.dim) =
      fracMap (locFrac e e' u).r (locFrac e e' u).p (locFrac e e' u).m
        (((w.val.val : Amb e)) : ComplexModel e.dim) := by
  obtain ⟨y, hy, hyeq⟩ := localOpen_target e e' u w
  exact ⟨⟨y, hy⟩, hyeq⟩

/-- The local holomorphic transition `w ↦ (p_k(w)/r(w)^{m_k})_k`. -/
def localMapFun (w : localOpen e e' u) : overlapOpen e' e :=
  (fracMap_mem e e' u w).choose

theorem localMapFun_val (w : localOpen e e' u) :
    (((localMapFun e e' u w).val : Amb e') : ComplexModel e'.dim) =
      fracMap (locFrac e e' u).r (locFrac e e' u).p (locFrac e e' u).m
        (((w.val.val : Amb e)) : ComplexModel e.dim) :=
  (fracMap_mem e e' u w).choose_spec

theorem localMapFun_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e'.dim) ∞ (localMapFun e e' u) := by
  apply (ContMDiff.subtypeVal_comp_iff (overlapOpen e' e) _).mp
  apply (ContMDiff.subtypeVal_comp_iff (⊤ : Opens (ComplexModel e'.dim)) _).mp
  intro w
  have hfun : (Subtype.val ∘ Subtype.val ∘ localMapFun e e' u) =
      fun w : localOpen e e' u => fracMap (locFrac e e' u).r (locFrac e e' u).p
        (locFrac e e' u).m (((w.val.val : Amb e)) : ComplexModel e.dim) := by
    funext w
    exact localMapFun_val e e' u w
  rw [hfun]
  have h0 : ContMDiffAt 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e'.dim) ∞
      (fracMap (locFrac e e' u).r (locFrac e e' u).p (locFrac e e' u).m)
      (((w.val.val : Amb e)) : ComplexModel e.dim) :=
    (contDiffAt_fracMap _ _ _ (localOpen_ne e e' u w)).contMDiffAt
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e'.dim) ∞
      (fun z : Amb e => fracMap (locFrac e e' u).r (locFrac e e' u).p (locFrac e e' u).m
        (z : ComplexModel e.dim)) (w.val.val : Amb e) :=
    contMDiffAt_subtype_iff.mpr h0
  have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel e.dim) 𝓘(ℂ, ComplexModel e'.dim) ∞
      (fun y : overlapOpen e e' => fracMap (locFrac e e' u).r (locFrac e e' u).p
        (locFrac e e' u).m ((y.val : Amb e) : ComplexModel e.dim)) w.val :=
    contMDiffAt_subtype_iff.mpr h1
  exact contMDiffAt_subtype_iff.mpr h2

theorem localMapFun_mapsTo :
    ∀ w ∈ localCarrier e e' u, localMapFun e e' u w ∈ overlapCarrier e' e := by
  intro w hw
  obtain ⟨d', hd', -⟩ := (locFrac e e' u).spec ⟨w.val.val, hw⟩ (localOpen_ne e e' u w)
  have : (localMapFun e e' u w).val = d'.val := by
    apply Subtype.ext
    rw [localMapFun_val]
    exact hd'.symm
  change (localMapFun e e' u w).val ∈ polynomialZeroSet e'.ideal
  rw [this]
  exact d'.property

/-- The local transition morphism of analytic models. -/
abbrev localMap : localModel e e' u ⟶ overlapModel e' e :=
  actualSubspaceMap (localMapFun_contMDiff e e' u) (localMapFun_mapsTo e e' u)

theorem localMap_chartPoint (z : localCarrier e e' u) :
    chartPoint e' (ovPt ((localMap e e' u).base z)) =
      chartPoint e (ovPt ((localIncl e e' u).base z)) := by
  obtain ⟨d', hd', hpt⟩ := (locFrac e e' u).spec ⟨z.val.val.val, z.property⟩
    (localOpen_ne e e' u z.val)
  have : ovPt ((localMap e e' u).base z) = d' := by
    apply Subtype.ext
    apply Subtype.ext
    change (((localMapFun e e' u z.val).val : Amb e') : ComplexModel e'.dim) = _
    rw [localMapFun_val]
    exact hd'.symm
  rw [this]
  exact hpt

theorem localMap_point :
    localMap e e' u ≫ overlapPointMap e' e = localIncl e e' u ≫ overlapPointMap e e' :=
  (actualSubspaceMap_point (localMapFun_contMDiff e e' u) (localMapFun_mapsTo e e' u)).trans
    (actualSubspaceMap_point (f := (Subtype.val : localOpen e e' u → overlapOpen e e'))
      contMDiff_subtype_val (fun _ hx => hx)).symm

end Local

/-! ### The glued transition -/

theorem localIncl_cover (e e' : EmbeddedChart f) (t : overlapCarrier e e') :
    ∃ (u : overlapCarrier e e') (z : localCarrier e e' u), (localIncl e e' u).base z = t :=
  ⟨t, ⟨⟨t.val, self_mem_localOpen e e' t⟩, t.property⟩, rfl⟩

theorem localMap_compat (e e' : EmbeddedChart f) (u v : overlapCarrier e e') :
    pullback.fst (localIncl e e' u) (localIncl e e' v) ≫ localMap e e' u =
      pullback.snd (localIncl e e' u) (localIncl e e' v) ≫ localMap e e' v := by
  have hP := hasAnalyticCharts_comp _ (overlapModel_hasAnalyticCharts e e')
    (pullback.fst (localIncl e e' u) (localIncl e e' v) ≫ localIncl e e' u)
  apply hom_ext_overlapModel e' e _ hP
  · simp only [Category.assoc, localMap_point]
  · simp only [Category.assoc, localMap_point]
    rw [pullback.condition_assoc]
  · intro x
    rw [comp_base_apply, comp_base_apply, localMap_chartPoint, localMap_chartPoint,
      ← comp_base_apply, ← comp_base_apply, pullback.condition]

theorem exists_transition (e e' : EmbeddedChart f) :
    ∃! F : Over.mk (overlapPointMap e e') ⟶ Over.mk (overlapPointMap e' e),
      ∀ u, localIncl e e' u ≫ F.left = localMap e e' u :=
  HironakaIntrinsicMorphismGluing.exists_unique_over (fun u => localModel e e' u)
    (fun u => localIncl e e' u) (localIncl_cover e e') (overlapPointMap e e')
    (overlapPointMap e' e) (fun u => localMap e e' u) (localMap_compat e e')
    (fun u => localMap_point e e' u)

/-- **The analytic transition map** between two embedded charts, a morphism of locally ringed
spaces over the complex point from the overlap model in `e` to the overlap model in `e'`. -/
def transition (e e' : EmbeddedChart f) : overlapModel e e' ⟶ overlapModel e' e :=
  (exists_transition e e').exists.choose.left

theorem localIncl_transition (e e' : EmbeddedChart f) (u : overlapCarrier e e') :
    localIncl e e' u ≫ transition e e' = localMap e e' u :=
  (exists_transition e e').exists.choose_spec u

theorem transition_point (e e' : EmbeddedChart f) :
    transition e e' ≫ overlapPointMap e' e = overlapPointMap e e' :=
  Over.w (exists_transition e e').exists.choose

/-- The transition map preserves the complex points of `X`. -/
theorem transition_chartPoint (e e' : EmbeddedChart f) (t : overlapCarrier e e') :
    chartPoint e' (ovPt ((transition e e').base t)) = chartPoint e (ovPt t) := by
  obtain ⟨u, z, rfl⟩ := localIncl_cover e e' t
  rw [← comp_base_apply, localIncl_transition]
  exact localMap_chartPoint e e' u z

end

end SGPT.Unibranch.UnibAn

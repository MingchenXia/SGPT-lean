import SGPT.Unibranch.UnibAnGlue
import SGPT.Foundations.Schemes.SchemeAnalyticSeparation
import SGPT.Foundations.Schemes.SchemeAnalyticAtlas
import SGPT.Foundations.Schemes.SchemeAnalyticCountability

/-!
# The analytification `𝒳^An` as a complex space, and `prop:unibranch_gaga`

Let `X` be a scheme with structure morphism `f : X ⟶ Spec ℂ`, and `𝒳^An =
analytificationLRS f` the gluing of the reduced analytic models of all embedded affine charts
(`UnibAnGlue`).

* `chartEmbedding_eq_iff`, `pointMap`: the points of `𝒳^An` are the complex points of `X`;
  two chart points are identified in `𝒳^An` iff they are the same complex point of `X`.
* `pointHomeomorph`: if `f` is locally of finite type, `pointMap` is a homeomorphism from
  `𝒳^An` onto the complex points `X(ℂ)` with their analytic topology
  (`SGPT.Foundations.Schemes.schemeAnalyticPointTopology`, coinduced by all affine charts).
* `analytification f`: for `X` separated and of finite type over `ℂ`, `𝒳^An` is Hausdorff
  (from the separatedness of `X`, `SGPT.Foundations.Schemes.schemeAnalyticPoint_t2Space`) and
  paracompact, hence a reduced complex space in the sense of the book
  (`SourceReducedComplexSpace`): the complex space associated with `X`, whose open subspaces
  `V(I)` are the embedded affine charts of `X`.
* `analytification_isUnibranch_iff` (**`prop:unibranch_gaga`**): for `X` reduced, separated
  and of finite type over `ℂ`, `𝒳^An` is unibranch (`def:unibranch:L21`) iff `X` is unibranch
  (Stacks 0BQ2). The pointwise form `analytification_unibranchAt_iff` (the claim of the
  book's proof) and the form `analytificationLRS_unibranch_iff` without separatedness (the
  stalkwise reading of ERRATA I03) hold as well.

Lane UNIB-AN; blueprint `claude-unib-an.tex`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace

namespace SGPT.Unibranch.UnibAn

noncomputable section

open SGPT.Unibranch SGPT.Foundations.Schemes

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}

/-! ### Points of `𝒳^An` -/

/-! The points of a glued locally ringed space, as for schemes
(`AlgebraicGeometry.Scheme.GlueData.ι_eq_iff`). -/

theorem lrsGlue_f_open (D : LocallyRingedSpace.GlueData.{0}) (i j : D.J) :
    PresheafedSpace.IsOpenImmersion (D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f i j) :=
  D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f_open i j

attribute [local instance] lrsGlue_f_open

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying space of a glued locally ringed space is the gluing of the underlying
spaces. -/
def lrsGlueIsoCarrier (D : LocallyRingedSpace.GlueData.{0}) :
    D.toGlueData.glued.carrier ≅
      D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.glued := by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    CategoryTheory.GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, 0} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  exact LocallyRingedSpace.GlueData.isoSheafedSpace _

set_option backward.isDefEq.respectTransparency false in
theorem lrsGlue_ι_isoCarrier_inv (D : LocallyRingedSpace.GlueData.{0}) (i : D.J) :
    D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.ι i ≫
      (lrsGlueIsoCarrier D).inv = (D.toGlueData.ι i).base := by
  delta lrsGlueIsoCarrier
  rw [Iso.trans_inv, CategoryTheory.GlueData.ι_gluedIso_inv_assoc, Functor.mapIso_inv,
    Iso.trans_inv, Functor.mapIso_inv, SheafedSpace.forgetToPresheafedSpace_map,
    PresheafedSpace.forget_map, PresheafedSpace.forget_map, ← PresheafedSpace.comp_base,
    ← Category.assoc, D.toSheafedSpaceGlueData.ι_isoPresheafedSpace_inv i,
    ← InducedCategory.comp_hom, LocallyRingedSpace.GlueData.ι_isoSheafedSpace_inv]
  rfl

theorem lrsGlue_isoCarrier_inv_ι (D : LocallyRingedSpace.GlueData.{0}) (i : D.J) (x : D.U i) :
    (lrsGlueIsoCarrier D).inv
        (D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.ι i x) =
      (D.toGlueData.ι i).base x := by
  rw [← lrsGlue_ι_isoCarrier_inv D i]
  rfl

/-- Two points of the pieces of a glued locally ringed space are identified iff they
correspond under a transition map. -/
theorem lrsGlue_ι_eq_iff (D : LocallyRingedSpace.GlueData.{0}) (i j : D.J) (x : D.U i)
    (y : D.U j) :
    (D.toGlueData.ι i).base x = (D.toGlueData.ι j).base y ↔
      ∃ v : D.V (i, j), (D.f i j).base v = x ∧ (D.f j i).base ((D.t i j).base v) = y := by
  have hinj : Function.Injective (lrsGlueIsoCarrier D).inv :=
    (TopCat.mono_iff_injective _).mp inferInstance
  rw [← lrsGlue_isoCarrier_inv_ι, ← lrsGlue_isoCarrier_inv_ι, hinj.eq_iff]
  exact TopCat.GlueData.ι_eq_iff_rel
    D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData i j x y

/-- Two chart points are the same point of `𝒳^An` iff they are the same complex point
of `X`. -/
theorem chartEmbedding_eq_iff {e e' : EmbeddedChart f} (c : polynomialZeroSet e.ideal)
    (c' : polynomialZeroSet e'.ideal) :
    (chartEmbedding e).base c = (chartEmbedding e').base c' ↔
      chartPoint e c = chartPoint e' c' := by
  constructor
  · intro h
    obtain ⟨v, hv, hv'⟩ := (lrsGlue_ι_eq_iff (glueData f) e e' c c').mp h
    have hv1 : ovPt (v : overlapCarrier e e') = c := hv
    have hv2 : ovPt ((transition e e').base (v : overlapCarrier e e')) = c' := hv'
    rw [← hv1, ← hv2]
    exact (transition_chartPoint e e' v).symm
  · intro h
    exact chartEmbedding_eq_of_chartPoint_eq h.symm

variable (f) in
/-- The complex point of `X` of a point of `𝒳^An`. -/
def pointMap (x : analytificationLRS f) : SchemeComplexPoint f :=
  chartPoint (chartEmbedding_jointly_surjective x).choose
    (chartEmbedding_jointly_surjective x).choose_spec.choose

theorem pointMap_chartEmbedding (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    pointMap f ((chartEmbedding e).base c) = chartPoint e c :=
  (chartEmbedding_eq_iff _ _).mp
    (chartEmbedding_jointly_surjective ((chartEmbedding e).base c)).choose_spec.choose_spec

theorem pointMap_injective : Function.Injective (pointMap f) := by
  intro x y h
  obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective x
  obtain ⟨e', c', rfl⟩ := chartEmbedding_jointly_surjective y
  rw [pointMap_chartEmbedding, pointMap_chartEmbedding] at h
  exact (chartEmbedding_eq_iff c c').mpr h

theorem pointMap_surjective [LocallyOfFiniteType f] : Function.Surjective (pointMap f) := by
  intro p
  obtain ⟨e, c, rfl⟩ := exists_chartPoint_eq p
  exact ⟨_, pointMap_chartEmbedding e c⟩

/-! ### Comparison with the analytic topology on `X(ℂ)` -/

/-- An embedded chart as an affine chart in the sense of `SGPT.Foundations.Schemes`. -/
def bweChart (e : EmbeddedChart f) : ComplexAffineChart X :=
  ⟨coordRing e.ideal, e.map, inferInstance⟩

theorem continuous_chartSpecPoint (e : EmbeddedChart f) :
    @Continuous (polynomialZeroSet e.ideal) (ComplexAffineChartPoint f (bweChart e)) _ _
      (chartSpecPoint e) := by
  let := affinePointFieldAlgebra ((bweChart e).map ≫ f)
  apply continuous_induced_rng.mpr
  apply (continuous_complexPoint_iff _).mpr
  intro a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ((contDiff_polyEval q).continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).congr ?_
  intro c
  have h1 := affineSchemePointEquivOfStructure_apply ((bweChart e).map ≫ f) (chartSpecPoint e c)
    (Ideal.Quotient.mk e.ideal q)
  refine Eq.trans ?_ h1.symm
  change _ = (Spec.preimage (Spec.map (CommRingCat.ofHom (pointEval c)))).hom _
  rw [Spec.preimage_map, CommRingCat.hom_ofHom, pointEval_mk]
  rfl

theorem continuous_ofSpecPoint (e : EmbeddedChart f) :
    @Continuous (ComplexAffineChartPoint f (bweChart e)) (polynomialZeroSet e.ideal) _ _
      (ofSpecPoint e) := by
  let := affinePointFieldAlgebra ((bweChart e).map ≫ f)
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun p : ComplexAffineChartPoint f (bweChart e) =>
    WithLp.toLp 2 (fun k : Fin e.dim =>
      (Spec.preimage p.val).hom (Ideal.Quotient.mk e.ideal (MvPolynomial.X k))))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  have hcont : @Continuous (ComplexAffineChartPoint f (bweChart e))
      (ComplexAlgebraPoint (bweChart e).ring) _ _
      (affineSchemePointEquivOfStructure ((bweChart e).map ≫ f)) := continuous_induced_dom
  refine ((complexPoint_evaluation_continuous (A := (bweChart e).ring)
    (Ideal.Quotient.mk e.ideal (MvPolynomial.X k))).comp hcont).congr ?_
  intro p
  exact affineSchemePointEquivOfStructure_apply ((bweChart e).map ≫ f) p _

/-- The points of an embedded chart `V(I)` are homeomorphic to the complex points of the chart
scheme with their analytic topology. -/
def chartSpecHomeomorph (e : EmbeddedChart f) :
    polynomialZeroSet e.ideal ≃ₜ ComplexAffineChartPoint f (bweChart e) where
  toFun := chartSpecPoint e
  invFun := ofSpecPoint e
  left_inv := ofSpecPoint_chartSpecPoint e
  right_inv := chartSpecPoint_ofSpecPoint e
  continuous_toFun := continuous_chartSpecPoint e
  continuous_invFun := continuous_ofSpecPoint e

/-- Each embedded chart `V(I)` is an open subspace of `X(ℂ)` with its analytic topology. -/
theorem chartPoint_isOpenEmbedding (e : EmbeddedChart f) :
    letI := schemeAnalyticPointTopology f
    IsOpenEmbedding (chartPoint e) := by
  let := schemeAnalyticPointTopology f
  have h : chartPoint e = complexAffineChartPointMap f (bweChart e) ∘ chartSpecHomeomorph e := rfl
  rw [h]
  exact (complexAffineChartPointMap_isOpenEmbedding f (bweChart e)).comp
    (chartSpecHomeomorph e).isOpenEmbedding

theorem chartEmbedding_isOpenEmbedding (e : EmbeddedChart f) :
    IsOpenEmbedding (chartEmbedding e).base :=
  (inferInstance : LocallyRingedSpace.IsOpenImmersion (chartEmbedding e)).base_open

theorem pointMap_continuous :
    letI := schemeAnalyticPointTopology f
    Continuous (pointMap f) := by
  let := schemeAnalyticPointTopology f
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective x
  have h1 : pointMap f ∘ (chartEmbedding e).base = chartPoint e :=
    funext (pointMap_chartEmbedding e)
  rw [← (chartEmbedding_isOpenEmbedding e).continuousAt_iff, h1]
  exact (chartPoint_isOpenEmbedding e).continuous.continuousAt

theorem pointMap_isOpenMap :
    letI := schemeAnalyticPointTopology f
    IsOpenMap (pointMap f) := by
  let := schemeAnalyticPointTopology f
  intro U hU
  have : pointMap f '' U =
      ⋃ e : EmbeddedChart f, chartPoint e '' ((chartEmbedding e).base ⁻¹' U) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective x
      exact Set.mem_iUnion.mpr ⟨e, c, hx, (pointMap_chartEmbedding e c).symm⟩
    · intro hp
      obtain ⟨e, c, hc, rfl⟩ := Set.mem_iUnion.mp hp
      exact ⟨_, hc, pointMap_chartEmbedding e c⟩
  rw [this]
  exact isOpen_iUnion fun e => (chartPoint_isOpenEmbedding e).isOpenMap _
    (hU.preimage (chartEmbedding e).base.hom.continuous)

variable (f) in
/-- **The points of `𝒳^An` are `X(ℂ)`.** For `f` locally of finite type, the point map is a
homeomorphism from `𝒳^An` onto the complex points of `X` with their analytic topology; on
every embedded chart it is the chart point map (`pointMap_chartEmbedding`). -/
def pointHomeomorph [LocallyOfFiniteType f] :
    letI := schemeAnalyticPointTopology f
    analytificationLRS f ≃ₜ SchemeComplexPoint f := by
  letI := schemeAnalyticPointTopology f
  exact (Equiv.ofBijective (pointMap f) ⟨pointMap_injective, pointMap_surjective⟩)
    |>.toHomeomorphOfContinuousOpen pointMap_continuous pointMap_isOpenMap

/-! ### `𝒳^An` is a complex space -/

theorem isClosed_polynomialZeroSet {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (polynomialZeroSet I) := by
  have : polynomialZeroSet I = ⋂ p ∈ I,
      {y : (⊤ : Opens (ComplexModel n)) | polyEval p (y : ComplexModel n) = 0} := by
    ext y
    simp [polynomialZeroSet, polyEval]
  rw [this]
  exact isClosed_biInter fun p _ =>
    isClosed_eq ((contDiff_polyEval p).continuous.comp continuous_subtype_val) continuous_const

instance polynomialZeroSet_locallyCompactSpace {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    LocallyCompactSpace (polynomialZeroSet I) := by
  have : LocallyCompactSpace (⊤ : Opens (ComplexModel n)) :=
    (⊤ : Opens (ComplexModel n)).isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  exact (isClosed_polynomialZeroSet I).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem analytification_t2Space [IsSeparated f] : T2Space (analytificationLRS f) := by
  let := schemeAnalyticPointTopology f
  have : T2Space (SchemeComplexPoint f) := schemeAnalyticPoint_t2Space f
  exact T2Space.of_injective_continuous pointMap_injective pointMap_continuous

theorem analytification_secondCountable [QuasiCompact f] [LocallyOfFiniteType f] :
    SecondCountableTopology (analytificationLRS f) := by
  let := schemeAnalyticPointTopology f
  have : SecondCountableTopology (SchemeComplexPoint f) :=
    schemeAnalyticPoint_secondCountable f
  exact (pointHomeomorph f).isEmbedding.secondCountableTopology

theorem analytification_weaklyLocallyCompact :
    WeaklyLocallyCompactSpace (analytificationLRS f) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective x
  obtain ⟨K, hK, hKc⟩ := exists_compact_mem_nhds c
  exact ⟨_, hK.image (chartEmbedding_isOpenEmbedding e).continuous,
    (chartEmbedding_isOpenEmbedding e).isOpenMap.image_mem_nhds hKc⟩

theorem analytification_paracompact [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] :
    ParacompactSpace (analytificationLRS f) := by
  have := analytification_t2Space (f := f)
  have := analytification_secondCountable (f := f)
  have := analytification_weaklyLocallyCompact (f := f)
  exact paracompact_of_locallyCompact_sigmaCompact

variable (f) in
/-- **The complex space `𝒳^An` associated with a separated scheme of finite type over `ℂ`**
(`prop:unibranch_gaga`): the gluing of the reduced analytic models `V(I)` of the embedded
affine charts of `X` along the analytic transition maps, a reduced Hausdorff paracompact
complex space (`SourceReducedComplexSpace`). Its points are the complex points of `X`
(`pointHomeomorph`) and every embedded chart `V(I)` is an open subspace (`chartEmbedding`). -/
def analytification [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] :
    SourceReducedComplexSpace :=
  ⟨Over.mk (structureMap f), analytification_t2Space, analytification_paracompact, fun x => by
    obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective x
    exact ⟨e.dim, ⊤, polynomialZeroSet e.ideal, polynomialZeroSet_isComplexAnalyticSubset e.ideal,
      chartEmbedding e, chartEmbedding_isOpenImmersion e, chartEmbedding_structureMap e, c,
      rfl⟩⟩

theorem analytification_obj_left [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] :
    (analytification f).obj.left = analytificationLRS f := rfl

/-! ### `prop:unibranch_gaga` -/

/-- **`prop:unibranch_gaga`, pointwise** (the claim of the book's proof). For a reduced scheme
`X` over `ℂ` and a point `x` of `𝒳^An`, the local ring `𝒪_{𝒳^An,x}` is unibranch iff `X` is
unibranch at the image in `X` of the complex point `x`. -/
theorem analytification_unibranchAt_iff [IsReduced X] (x : analytificationLRS f) :
    SourceUnibranchReducedRing ((analytificationLRS f).presheaf.stalk x).carrier ↔
      SchemeIsUnibranchAt X (schemeComplexPointImage f (pointMap f x)) := by
  obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective x
  rw [pointMap_chartEmbedding, chartPoint_image_eq]
  exact analytification_stalk_unibranch_iff e c

/-- **`prop:unibranch_gaga`.** Let `X` be a reduced scheme of finite type over `ℂ`, separated
(so that `𝒳^An` is a Hausdorff complex space, ERRATA I03), and `𝒳^An` its associated complex
space. Then `𝒳^An` is unibranch in the sense of `def:unibranch:L21` iff `X` is unibranch in
the algebraic sense (Stacks 0BQ2). -/
theorem analytification_isUnibranch_iff [IsReduced X] [IsSeparated f] [QuasiCompact f]
    [LocallyOfFiniteType f] :
    (analytification f).IsUnibranch ↔ SchemeIsUnibranch X :=
  analytificationLRS_unibranch_iff

end

end SGPT.Unibranch.UnibAn

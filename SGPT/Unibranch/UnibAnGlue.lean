import SGPT.Unibranch.UnibAnTransition
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# The analytification of a complex scheme as a glued locally ringed space

Let `X` be a scheme with structure morphism `f : X ⟶ Spec ℂ`. The embedded affine charts
`e : Spec ℂ[z]/I ⟶ X` (`EmbeddedChart f`, all of them) with their reduced analytic models
`V(I)` (`chartModel e`), the overlap models (`overlapModel`) and the analytic transition maps
(`transition`) form native gluing data of locally ringed spaces (`glueData`): the cocycle
condition holds because morphisms into the reduced models are determined by the complex
points of `X` (`hom_ext_chartModel`), which all transition maps preserve.

* `analytificationLRS f`: the glued locally ringed space `𝒳^An`, with its structure morphism
  to the complex point (`structureMap`); every embedded chart `V(I)` is an open subspace
  (`chartEmbedding`, an open immersion over the complex point) and these cover `𝒳^An`.
* `chartEmbedding_base_eq_iff`: two chart points are identified in `𝒳^An` iff they are the
  same complex point of `X`.
* `analytification_stalk_unibranch_iff`: at the point `c ∈ V(I)` of a chart `e`, the local
  ring of `𝒳^An` is unibranch (`def:unibranch:L21`) iff `X` is unibranch at `e(c)` (Stacks
  0BQ2); for `X` reduced. No separatedness is used (ERRATA I03).

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

/-! ### Triple overlaps -/

section Triple

variable (e₁ e₂ e₃ : EmbeddedChart f)

/-- The triple overlap, as a pullback of two overlap inclusions into the chart `e₁`. -/
abbrev tripleObj : LocallyRingedSpace :=
  pullback (overlapIncl e₁ e₂) (overlapIncl e₁ e₃)

/-- The complex point of `X` of a point of the triple overlap. -/
def triplePt (x : tripleObj e₁ e₂ e₃) : SchemeComplexPoint f :=
  chartPoint e₁ (ovPt ((pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃)).base x))

/-- The structure morphism of the triple overlap. -/
abbrev triplePointMap : tripleObj e₁ e₂ e₃ ⟶ complexPoint :=
  pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃) ≫ overlapPointMap e₁ e₂

theorem triple_hasAnalyticCharts : hasAnalyticCharts (Over.mk (triplePointMap e₁ e₂ e₃)) :=
  hasAnalyticCharts_comp _ (overlapModel_hasAnalyticCharts e₁ e₂) _

theorem triple_snd_pt (x : tripleObj e₁ e₂ e₃) :
    chartPoint e₁ (ovPt ((pullback.snd (overlapIncl e₁ e₂) (overlapIncl e₁ e₃)).base x)) =
      triplePt e₁ e₂ e₃ x := by
  have h := congrArg (fun F => F.base x)
    (pullback.condition (f := overlapIncl e₁ e₂) (g := overlapIncl e₁ e₃))
  simp only [comp_base_apply, overlapIncl_base] at h
  rw [triplePt, h]

theorem triple_range :
    Set.range (pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃) ≫ transition e₁ e₂ ≫
      overlapIncl e₂ e₁).base ⊆ Set.range (overlapIncl e₂ e₃).base := by
  rintro _ ⟨x, rfl⟩
  have hc : ovPt ((transition e₁ e₂).base
      ((pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃)).base x)) ∈ overlapSet e₂ e₃ := by
    obtain ⟨d₃, hd₃⟩ := ovPt_mem e₁ e₃
      ((pullback.snd (overlapIncl e₁ e₂) (overlapIncl e₁ e₃)).base x)
    refine ⟨d₃, ?_⟩
    rw [hd₃, triple_snd_pt, transition_chartPoint, triplePt]
  exact ⟨ofOverlapSet _ hc, rfl⟩

/-- The rotation of triple overlaps required by the gluing data. -/
def tripleMap : tripleObj e₁ e₂ e₃ ⟶ tripleObj e₂ e₃ e₁ :=
  pullback.lift
    (LocallyRingedSpace.IsOpenImmersion.lift (overlapIncl e₂ e₃)
      (pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃) ≫ transition e₁ e₂ ≫
        overlapIncl e₂ e₁) (triple_range e₁ e₂ e₃))
    (pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃) ≫ transition e₁ e₂)
    (by rw [LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.assoc])

theorem tripleMap_fac :
    tripleMap e₁ e₂ e₃ ≫ pullback.snd (overlapIncl e₂ e₃) (overlapIncl e₂ e₁) =
      pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃) ≫ transition e₁ e₂ :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem tripleMap_fst_incl :
    tripleMap e₁ e₂ e₃ ≫ pullback.fst (overlapIncl e₂ e₃) (overlapIncl e₂ e₁) ≫
        overlapIncl e₂ e₃ =
      pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃) ≫ transition e₁ e₂ ≫
        overlapIncl e₂ e₁ := by
  rw [tripleMap, pullback.lift_fst_assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac]

theorem tripleMap_pt (x : tripleObj e₁ e₂ e₃) :
    triplePt e₂ e₃ e₁ ((tripleMap e₁ e₂ e₃).base x) = triplePt e₁ e₂ e₃ x := by
  have h := congrArg (fun F => F.base x) (tripleMap_fst_incl e₁ e₂ e₃)
  simp only [comp_base_apply, overlapIncl_base] at h
  unfold triplePt
  rw [h, transition_chartPoint]

theorem tripleMap_point :
    tripleMap e₁ e₂ e₃ ≫ pullback.fst (overlapIncl e₂ e₃) (overlapIncl e₂ e₁) ≫
        overlapPointMap e₂ e₃ =
      pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃) ≫ overlapPointMap e₁ e₂ := by
  rw [← overlapIncl_point e₂ e₃, tripleMap_fst_incl_assoc, overlapIncl_point, transition_point]

theorem tripleMap_cocycle :
    tripleMap e₁ e₂ e₃ ≫ tripleMap e₂ e₃ e₁ ≫ tripleMap e₃ e₁ e₂ = 𝟙 _ := by
  apply (cancel_mono (pullback.fst (overlapIncl e₁ e₂) (overlapIncl e₁ e₃) ≫
    overlapIncl e₁ e₂)).mp
  rw [Category.id_comp]
  apply hom_ext_chartModel e₁ (triplePointMap e₁ e₂ e₃) (triple_hasAnalyticCharts e₁ e₂ e₃)
  · simp only [Category.assoc, overlapIncl_point, tripleMap_point]
  · simp only [Category.assoc, overlapIncl_point]
  · intro x
    change triplePt e₁ e₂ e₃ ((tripleMap e₃ e₁ e₂).base ((tripleMap e₂ e₃ e₁).base
      ((tripleMap e₁ e₂ e₃).base x))) = triplePt e₁ e₂ e₃ x
    rw [tripleMap_pt, tripleMap_pt, tripleMap_pt]

end Triple

/-! ### The gluing data -/

instance overlapIncl_self_isIso (e : EmbeddedChart f) : IsIso (overlapIncl e e) := by
  have hs : Function.Surjective (overlapIncl e e).base := by
    intro c
    exact ⟨ofOverlapSet c ⟨c, rfl⟩, rfl⟩
  have : Epi (overlapIncl e e).base := (TopCat.epi_iff_surjective _).mpr hs
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

theorem transition_self (e : EmbeddedChart f) : transition e e = 𝟙 _ :=
  hom_ext_overlapModel e e (overlapPointMap e e) (overlapModel_hasAnalyticCharts e e) _ _
    (transition_point e e) (Category.id_comp _) (fun x => transition_chartPoint e e x)

variable (f) in
/-- The gluing data of all embedded affine charts of `X` along the analytic transition maps. -/
def glueData : LocallyRingedSpace.GlueData where
  J := EmbeddedChart f
  U := chartModel
  V p := overlapModel p.1 p.2
  f e e' := overlapIncl e e'
  f_id e := overlapIncl_self_isIso e
  t e e' := transition e e'
  t_id e := transition_self e
  t' := tripleMap
  t_fac := tripleMap_fac
  cocycle := tripleMap_cocycle
  f_open _ _ := inferInstance

variable (f) in
/-- **The analytification `𝒳^An`** of a scheme `X` over `ℂ`, as a locally ringed space: the
gluing of the reduced analytic models `V(I)` of all embedded affine charts of `X` along the
analytic transition maps. -/
def analytificationLRS : LocallyRingedSpace := (glueData f).toGlueData.glued

/-- The open subspace `V(I) ⊆ 𝒳^An` of an embedded chart. -/
def chartEmbedding (e : EmbeddedChart f) : chartModel e ⟶ analytificationLRS f :=
  (glueData f).toGlueData.ι e

instance chartEmbedding_isOpenImmersion (e : EmbeddedChart f) :
    LocallyRingedSpace.IsOpenImmersion (chartEmbedding e) :=
  LocallyRingedSpace.GlueData.ι_isOpenImmersion (glueData f) e

theorem chartEmbedding_jointly_surjective (x : analytificationLRS f) :
    ∃ (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal), (chartEmbedding e).base c = x :=
  LocallyRingedSpace.GlueData.ι_jointly_surjective (glueData f) x

theorem glue_compat (e e' : EmbeddedChart f) :
    (glueData f).f e e' ≫ chartPointMap e =
      ((glueData f).t e e' ≫ (glueData f).f e' e) ≫ chartPointMap e' := by
  change overlapIncl e e' ≫ chartPointMap e =
    (transition e e' ≫ overlapIncl e' e) ≫ chartPointMap e'
  rw [Category.assoc, overlapIncl_point, overlapIncl_point, transition_point]

variable (f) in
/-- The structure morphism of `𝒳^An` to the complex point. -/
def structureMap : analytificationLRS f ⟶ complexPoint :=
  Multicoequalizer.desc (glueData f).toGlueData.diagram complexPoint (fun e => chartPointMap e)
    (fun p => glue_compat p.1 p.2)

theorem chartEmbedding_structureMap (e : EmbeddedChart f) :
    chartEmbedding e ≫ structureMap f = chartPointMap e :=
  Multicoequalizer.π_desc (glueData f).toGlueData.diagram complexPoint _ _ e

/-- Two points of the overlap are glued: the transition and the inclusions commute with the
chart embeddings. -/
theorem chartEmbedding_overlap (e e' : EmbeddedChart f) (u : overlapCarrier e e') :
    (chartEmbedding e).base (ovPt u) =
      (chartEmbedding e').base (ovPt ((transition e e').base u)) :=
  (congrArg (fun F => F.base u) ((glueData f).toGlueData.glue_condition e e')).symm

/-- Two chart points with the same complex point of `X` are the same point of `𝒳^An`. -/
theorem chartEmbedding_eq_of_chartPoint_eq {e e' : EmbeddedChart f}
    {c : polynomialZeroSet e.ideal} {c' : polynomialZeroSet e'.ideal}
    (h : chartPoint e' c' = chartPoint e c) :
    (chartEmbedding e).base c = (chartEmbedding e').base c' := by
  have hc : c ∈ overlapSet e e' := ⟨c', h⟩
  have h1 := chartEmbedding_overlap e e' (ofOverlapSet c hc)
  rw [ovPt_ofOverlapSet] at h1
  rw [h1]
  congr 1
  apply chartPoint_injective e'
  rw [transition_chartPoint, ovPt_ofOverlapSet, h]

/-- The stalk of `𝒳^An` at the point `c` of a chart is the stalk of the model `V(I)` at `c`. -/
def chartEmbeddingStalkEquiv (e : EmbeddedChart f) (c : polynomialZeroSet e.ideal) :
    ((analytificationLRS f).presheaf.stalk ((chartEmbedding e).base c)).carrier ≃+*
      ((chartModel e).presheaf.stalk c).carrier :=
  (asIso ((chartEmbedding e).stalkMap c)).commRingCatIsoToRingEquiv

/-- **`prop:unibranch_gaga`, stalkwise.** For a reduced scheme `X` over `ℂ` and a point
`c ∈ V(I)` of an embedded chart `e`, the local ring of `𝒳^An` at `c` is unibranch
(`def:unibranch:L21`) iff `X` is unibranch at the closed point `e(c)` (Stacks 0BQ2). -/
theorem analytification_stalk_unibranch_iff [IsReduced X] (e : EmbeddedChart f)
    (c : polynomialZeroSet e.ideal) :
    SourceUnibranchReducedRing
        ((analytificationLRS f).presheaf.stalk ((chartEmbedding e).base c)).carrier ↔
      SchemeIsUnibranchAt X (e.map (UnibAlg.closedPoint c)) :=
  (sourceUnibranchReducedRing_iff_of_ringEquiv (chartEmbeddingStalkEquiv e c)).trans
    (UnibAlg.schemeIsUnibranchAt_iff_modelStalk e.ideal e.ideal_isRadical e.map c).symm

/-- **`prop:unibranch_gaga` for the analytification as a locally ringed space.** For a reduced
scheme `X` locally of finite type over `ℂ` (not necessarily separated), every local ring of
`𝒳^An` is unibranch iff `X` is unibranch at every point (Stacks 0BQ2). -/
theorem analytificationLRS_unibranch_iff [IsReduced X] [LocallyOfFiniteType f] :
    (∀ x : analytificationLRS f,
        SourceUnibranchReducedRing ((analytificationLRS f).presheaf.stalk x).carrier) ↔
      SchemeIsUnibranch X := by
  constructor
  · intro h
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
    apply schemeIsUnibranch_of_closedPoints X
    intro x hx
    obtain ⟨e, c, rfl⟩ := exists_closedPoint_eq (f := f) x hx
    exact (analytification_stalk_unibranch_iff e c).mp (h _)
  · intro h x
    obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective x
    exact (analytification_stalk_unibranch_iff e c).mpr (h _)

end

end SGPT.Unibranch.UnibAn

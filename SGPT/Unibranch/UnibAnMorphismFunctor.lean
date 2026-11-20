import SGPT.Unibranch.UnibAnMorphismGlobal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology SGPT.Foundations.Analysis.FirstPass
open SGPT.Unibranch SGPT.Foundations.Schemes

namespace SGPT.Unibranch.UnibAn

noncomputable section

section Maps

variable {X Y Z : Scheme.{0}}
variable {f : X ⟶ Spec (.of ℂ)} {g : Y ⟶ Spec (.of ℂ)} {k : Z ⟶ Spec (.of ℂ)}
variable [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
  [IsSeparated g] [QuasiCompact g] [LocallyOfFiniteType g]

/-- The analytic map induced by a scheme morphism over the complex point. -/
def analytificationMorphism (ρ : Y ⟶ X) (h : ρ ≫ f = g) :
    analytification g ⟶ analytification f := by
  subst g
  exact (exists_analytification_morphism f ρ).choose

theorem pointMap_analytificationMorphism (ρ : Y ⟶ X) (h : ρ ≫ f = g)
    (y : analytificationLRS g) :
    pointMap f ((analytificationMorphism ρ h).hom.left.base y) =
      schemeComplexPointMap g f ρ h (pointMap g y) := by
  subst g
  exact (exists_analytification_morphism f ρ).choose_spec y

/-- Pointwise equality determines the entire analytic morphism. -/
theorem analytification_morphism_ext {F G : analytification g ⟶ analytification f}
    (h : ∀ y : analytificationLRS g, pointMap f (F.hom.left.base y) =
      pointMap f (G.hom.left.base y)) : F = G :=
  SourceReducedComplexSpace.morphism_eq_of_pointwise_eq F G (fun y => pointMap_injective (h y))

@[simp] theorem analytificationMorphism_id :
    analytificationMorphism (𝟙 X) (Category.id_comp f) = 𝟙 (analytification f) := by
  apply analytification_morphism_ext
  intro x
  rw [pointMap_analytificationMorphism]
  refine Subtype.ext ?_
  change (pointMap f x).val ≫ 𝟙 X = (pointMap f x).val
  exact Category.comp_id _

variable [IsSeparated k] [QuasiCompact k] [LocallyOfFiniteType k]

theorem analytificationMorphism_comp (ρ : Z ⟶ Y) (σ : Y ⟶ X)
    (hρ : ρ ≫ g = k) (hσ : σ ≫ f = g) :
    analytificationMorphism (ρ ≫ σ) (by rw [Category.assoc, hσ, hρ]) =
      analytificationMorphism ρ hρ ≫ analytificationMorphism σ hσ := by
  apply analytification_morphism_ext
  intro z
  change pointMap f ((analytificationMorphism (ρ ≫ σ) _).hom.left.base z) =
    pointMap f ((analytificationMorphism σ hσ).hom.left.base
      ((analytificationMorphism ρ hρ).hom.left.base z))
  exact (pointMap_analytificationMorphism (ρ ≫ σ) _ z).trans
    ((Subtype.ext (Category.assoc _ _ _).symm).trans
      ((congrArg (schemeComplexPointMap g f σ hσ)
        (pointMap_analytificationMorphism ρ hρ z)).symm.trans
        (pointMap_analytificationMorphism σ hσ _).symm))

end Maps

section OpenImmersion

open SGPT.Foundations.Analysis.Pending

variable {X Y : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {g : Y ⟶ Spec (.of ℂ)}
variable (ρ : Y ⟶ X) (h : ρ ≫ f = g) [IsOpenImmersion ρ]

/-- A source affine chart also serves as a target chart through an open immersion. -/
def mapOpenChart (e : EmbeddedChart g) : EmbeddedChart f where
  dim := e.dim
  ideal := e.ideal
  map := e.map ≫ ρ
  isOpenImmersion := inferInstance
  isOver := by rw [Category.assoc, h, e.isOver]

theorem chartPoint_mapOpenChart (e : EmbeddedChart g) (c : polynomialZeroSet e.ideal) :
    chartPoint (mapOpenChart ρ h e) c = schemeComplexPointMap g f ρ h (chartPoint e c) := by
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

variable [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
  [IsSeparated g] [QuasiCompact g] [LocallyOfFiniteType g]

theorem chartEmbedding_analytificationMorphism (e : EmbeddedChart g) :
    chartEmbedding e ≫ (analytificationMorphism ρ h).hom.left =
      chartEmbedding (mapOpenChart ρ h e) := by
  refine @HironakaG10GenGluing.lrs_hom_eq_of_base_eq (analytification g) (analytification f)
    (chartModel e) (chartEmbedding e) (chartEmbedding_isOpenImmersion e) _ _ ?_ ?_ ?_
  · change (chartEmbedding e ≫ (analytificationMorphism ρ h).hom.left) ≫ structureMap f =
      chartEmbedding e ≫ structureMap g
    have hOver : (analytificationMorphism ρ h).hom.left ≫ structureMap f = structureMap g :=
      Over.w (analytificationMorphism ρ h).hom
    exact (Category.assoc _ _ _).trans (congrArg (chartEmbedding e ≫ ·) hOver)
  · exact (chartEmbedding_structureMap (mapOpenChart ρ h e)).trans
      (chartEmbedding_structureMap e).symm
  · ext c
    apply pointMap_injective
    change pointMap f ((analytificationMorphism ρ h).hom.left.base ((chartEmbedding e).base c)) =
      pointMap f ((chartEmbedding (mapOpenChart ρ h e)).base c)
    exact (pointMap_analytificationMorphism ρ h _).trans
      ((congrArg (schemeComplexPointMap g f ρ h) (pointMap_chartEmbedding e c)).trans
        ((chartPoint_mapOpenChart ρ h e c).symm.trans
          (pointMap_chartEmbedding (mapOpenChart ρ h e) c).symm))

/-- An algebraic open immersion induces an open immersion of the reduced analytic LRS. -/
theorem analytificationMorphism_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (analytificationMorphism ρ h).hom.left := by
  let K : analytificationLRS g ⟶ analytificationLRS f := (analytificationMorphism ρ h).hom.left
  have hcomp (e : EmbeddedChart g) :
      LocallyRingedSpace.IsOpenImmersion (chartEmbedding e ≫ K) := by
    have heq : chartEmbedding e ≫ K = chartEmbedding (mapOpenChart ρ h e) :=
      chartEmbedding_analytificationMorphism ρ h e
    exact heq.symm ▸ chartEmbedding_isOpenImmersion (mapOpenChart ρ h e)
  have hinj : Function.Injective K.base := by
    intro x y heq
    apply pointMap_injective
    have hxy := congrArg (pointMap f) heq
    change pointMap f ((analytificationMorphism ρ h).hom.left.base x) =
      pointMap f ((analytificationMorphism ρ h).hom.left.base y) at hxy
    rw [pointMap_analytificationMorphism, pointMap_analytificationMorphism] at hxy
    apply Subtype.ext
    exact (cancel_mono ρ).mp (congrArg Subtype.val hxy)
  let s : (Σ e : EmbeddedChart g, chartModel e) → analytificationLRS g :=
    fun v => (chartEmbedding v.1).base v.2
  have hs : Continuous s := continuous_sigma (fun e => (chartEmbedding e).base.hom.continuous)
  have hsurj : Function.Surjective s := by
    intro y
    obtain ⟨e, c, hc⟩ := chartEmbedding_jointly_surjective y
    exact ⟨⟨e, c⟩, hc⟩
  have hopen : IsOpenMap (K.base ∘ s) :=
    isOpenMap_sigma.mpr (fun e => (hcomp e).base_open.isOpenMap)
  have hemb : IsOpenEmbedding K.base :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap K.base.hom.continuous hinj
      (IsOpenMap.of_comp hs hsurj hopen)
  have : ∀ y : analytificationLRS g, IsIso (K.stalkMap y) := by
    intro y
    obtain ⟨e, c, rfl⟩ := chartEmbedding_jointly_surjective y
    let := hcomp e
    have hc : IsIso ((chartEmbedding e ≫ K).stalkMap c) := inferInstance
    rw [LocallyRingedSpace.stalkMap_comp] at hc
    have : IsIso (K.stalkMap ((chartEmbedding e).base c) ≫ (chartEmbedding e).stalkMap c) := hc
    exact IsIso.of_isIso_comp_right (K.stalkMap ((chartEmbedding e).base c))
      ((chartEmbedding e).stalkMap c)
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso K hemb

end OpenImmersion

end

end SGPT.Unibranch.UnibAn

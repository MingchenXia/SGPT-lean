import SGPT.Unibranch.HironakaG11BlowupLocality
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationProperNormalShrink

/-! Actual full original-category restriction, proper finite point map, and ENTIRE new-source stalk normality.
Blueprint: prime-nov16-analytic-normalization-original-proper-restriction.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction
open HironakaG11BlowupLocality PrimeNov16AnalyticNormalizationProperNormalShrink

variable {X Y : SourceReducedComplexSpace}

def sourceOpen (f : Y ⟶ X) (U : Opens X.obj.left) : Opens Y.obj.left :=
  ⟨f.hom.left.base ⁻¹' (U : Set X.obj.left),U.isOpen.preimage f.hom.left.base.hom.continuous⟩

theorem sourceOpen_paracompact (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] : ParacompactSpace (sourceOpen f U) := by
  have h := paracompactSpace_preimage_range f hf (openSubspaceInclusion X U) inferInstance
  change ParacompactSpace (f.hom.left.base ⁻¹' (U : Set X.obj.left))
  have hr : range (openSubspaceInclusion X U).hom.left.base=(U : Set X.obj.left) :=
    range_openSubspaceInclusion X U
  rw [hr] at h
  exact h

def restrictedBase (U : Opens X.obj.left) [ParacompactSpace U] : SourceReducedComplexSpace :=
  openSubspace X U

def restrictedSource (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] : SourceReducedComplexSpace := by
  let := sourceOpen_paracompact f hf U
  exact openSubspace Y (sourceOpen f U)

def baseInclusion (U : Opens X.obj.left) [ParacompactSpace U] : restrictedBase U ⟶ X :=
  openSubspaceInclusion X U

def sourceInclusion (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] : restrictedSource f hf U ⟶ Y := by
  let := sourceOpen_paracompact f hf U
  exact openSubspaceInclusion Y (sourceOpen f U)

instance baseInclusion_isOpenImmersion (U : Opens X.obj.left) [ParacompactSpace U] :
    LocallyRingedSpace.IsOpenImmersion (baseInclusion U).hom.left := by
  exact openSubspaceInclusion_isOpenImmersion X U

instance sourceInclusion_isOpenImmersion (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion f hf U).hom.left := by
  let := sourceOpen_paracompact f hf U
  exact openSubspaceInclusion_isOpenImmersion Y (sourceOpen f U)

private theorem restriction_lands (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] :
    range (sourceInclusion f hf U ≫ f).hom.left.base ⊆ range (baseInclusion U).hom.left.base := by
  rintro _ ⟨p,rfl⟩
  let p0 : sourceOpen f U := p
  exact ⟨⟨f.hom.left.base p0.val,p0.property⟩,rfl⟩

def restrictedMap (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] : restrictedSource f hf U ⟶ restrictedBase U := by
  let i := sourceInclusion f hf U
  let j := baseInclusion U
  let L := LocallyRingedSpace.IsOpenImmersion.lift j.hom.left (i ≫ f).hom.left (restriction_lands f hf U)
  have hL : L ≫ j.hom.left = (i ≫ f).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac j.hom.left (i ≫ f).hom.left (restriction_lands f hf U)
  have hp : L ≫ (restrictedBase U).obj.hom=(restrictedSource f hf U).obj.hom := by
    rw [← Over.w j.hom,← Category.assoc,hL]
    exact Over.w (i ≫ f).hom
  exact ObjectProperty.homMk (Over.homMk L hp)

theorem restrictedMap_square (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] :
    restrictedMap f hf U ≫ baseInclusion U=sourceInclusion f hf U ≫ f := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (restriction_lands f hf U)

theorem restrictedMap_point (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] (p : sourceOpen f U) :
    ((restrictedMap f hf U).hom.left.base p).val=f.hom.left.base p.val := by
  have h := congrArg (fun g : restrictedSource f hf U ⟶ X => g.hom.left.base p) (restrictedMap_square f hf U)
  exact h

theorem restrictedMap_proper (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U] : IsProperMap (restrictedMap f hf U).hom.left.base := by
  have hp : (fun p : sourceOpen f U => (show U from (restrictedMap f hf U).hom.left.base p)) =
      (U : Set X.obj.left).restrictPreimage f.hom.left.base := by
    funext p
    exact Subtype.ext (restrictedMap_point f hf U p)
  change IsProperMap (fun p : sourceOpen f U => (show U from (restrictedMap f hf U).hom.left.base p))
  rw [hp]
  exact actual_proper_restrict_preimage _ hf (U : Set X.obj.left)

theorem restrictedMap_fibres_finite (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U]
    (hfinite : ∀ b : X.obj.left,(f.hom.left.base ⁻¹' {b}).Finite) (b : U) :
    ((restrictedMap f hf U).hom.left.base ⁻¹' {b}).Finite := by
  have hp : (fun p : sourceOpen f U => (show U from (restrictedMap f hf U).hom.left.base p)) =
      (U : Set X.obj.left).restrictPreimage f.hom.left.base := by
    funext p
    exact Subtype.ext (restrictedMap_point f hf U p)
  change ((fun p : sourceOpen f U => (show U from (restrictedMap f hf U).hom.left.base p)) ⁻¹' {b}).Finite
  rw [hp]
  exact actual_finite_restrict_preimage _ hfinite (U : Set X.obj.left) b

theorem restrictedSource_normal_stalks (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base)
    (U : Opens X.obj.left) [ParacompactSpace U]
    (hNormal : ∀ p : Y.obj.left,f.hom.left.base p ∈ U →
      IsDomain (Y.obj.left.presheaf.stalk p).carrier ∧ IsIntegrallyClosed (Y.obj.left.presheaf.stalk p).carrier)
    (p : (restrictedSource f hf U).obj.left) :
    IsDomain ((restrictedSource f hf U).obj.left.presheaf.stalk p).carrier ∧
      IsIntegrallyClosed ((restrictedSource f hf U).obj.left.presheaf.stalk p).carrier := by
  let p0 : sourceOpen f U := p
  obtain ⟨hd,hn⟩ := hNormal p0.val p0.property
  let := hd
  let := hn
  let E : (Y.obj.left.presheaf.stalk p0.val).carrier ≃+*
      ((restrictedSource f hf U).obj.left.presheaf.stalk p).carrier :=
    (asIso ((sourceInclusion f hf U).hom.left.stalkMap p)).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain E.symm E.symm.injective,IsIntegrallyClosed.of_equiv E⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction

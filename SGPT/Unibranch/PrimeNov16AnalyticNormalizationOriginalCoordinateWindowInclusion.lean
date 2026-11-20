import SGPT.Unibranch.NativeNov16SectionCoordinateMorphism
import SGPT.Unibranch.OriginalLocalStrictWindowRegularity

/-! Actual full original inclusions between literal Source(C,W) windows, retaining the exact native quotient spaces.
Blueprint: prime-nov16-analytic-normalization-original-coordinate-window-inclusion.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion
open NativeNov16SectionCoordinateMorphism
open HironakaG11BlowupLocality

variable {n : ℕ} (P : Opens (ComplexModel n)) (C : Set P)
  (hC : IsComplexAnalyticSubset (n := n) C)

private theorem window_pc (W : Opens (TopCat.of C)) : ParacompactSpace W := by
  change ParacompactSpace {x : C // x ∈ W}
  infer_instance

def coordinateInclusion (W : Opens (TopCat.of C)) :
    coordinateSource P C hC W ⟶ sourceReducedComplexSpaceModel P C hC := by
  exact @openSubspaceInclusion (sourceReducedComplexSpaceModel P C hC) W (window_pc P C W)

instance coordinateInclusion_isOpenImmersion (W : Opens (TopCat.of C)) :
    LocallyRingedSpace.IsOpenImmersion (coordinateInclusion P C hC W).hom.left := by
  exact @openSubspaceInclusion_isOpenImmersion (sourceReducedComplexSpaceModel P C hC) W (window_pc P C W)

private theorem source_lands (V W : Opens (TopCat.of C)) (hVW : V ≤ W) :
    range (coordinateInclusion P C hC V).hom.left.base ⊆
      range (coordinateInclusion P C hC W).hom.left.base := by
  rintro _ ⟨p,rfl⟩
  let p0 : V := p
  exact ⟨⟨p0.val,hVW p0.property⟩,rfl⟩

def windowInclusion (V W : Opens (TopCat.of C)) (hVW : V ≤ W) :
    coordinateSource P C hC V ⟶ coordinateSource P C hC W := by
  let j := coordinateInclusion P C hC W
  let i := coordinateInclusion P C hC V
  let L := LocallyRingedSpace.IsOpenImmersion.lift j.hom.left i.hom.left (source_lands P C hC V W hVW)
  have hL := LocallyRingedSpace.IsOpenImmersion.lift_fac j.hom.left i.hom.left (source_lands P C hC V W hVW)
  have hs : L ≫ (coordinateSource P C hC W).obj.hom=(coordinateSource P C hC V).obj.hom := by
    rw [← Over.w j.hom,← Category.assoc,hL]
    exact Over.w i.hom
  exact ObjectProperty.homMk (Over.homMk L hs)

theorem windowInclusion_square (V W : Opens (TopCat.of C)) (hVW : V ≤ W) :
    windowInclusion P C hC V W hVW ≫ coordinateInclusion P C hC W=coordinateInclusion P C hC V := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (source_lands P C hC V W hVW)

instance windowInclusion_isOpenImmersion (V W : Opens (TopCat.of C)) (hVW : V ≤ W) :
    LocallyRingedSpace.IsOpenImmersion (windowInclusion P C hC V W hVW).hom.left := by
  have hc : LocallyRingedSpace.IsOpenImmersion
      ((windowInclusion P C hC V W hVW).hom.left ≫ (coordinateInclusion P C hC W).hom.left) := by
    have hs := congrArg (fun f => f.hom.left) (windowInclusion_square P C hC V W hVW)
    change (windowInclusion P C hC V W hVW).hom.left ≫ (coordinateInclusion P C hC W).hom.left=
      (coordinateInclusion P C hC V).hom.left at hs
    exact hs.symm ▸ coordinateInclusion_isOpenImmersion P C hC V
  let := hc
  exact HironakaG10ChowStrictTransformCalculus.isOpenImmersion_of_comp
    (windowInclusion P C hC V W hVW).hom.left (coordinateInclusion P C hC W).hom.left

theorem windowInclusion_point (V W : Opens (TopCat.of C)) (hVW : V ≤ W)
    (p : V) : ((windowInclusion P C hC V W hVW).hom.left.base p).val=p.val :=
  congrArg (fun f => f.hom.left.base p) (windowInclusion_square P C hC V W hVW)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion

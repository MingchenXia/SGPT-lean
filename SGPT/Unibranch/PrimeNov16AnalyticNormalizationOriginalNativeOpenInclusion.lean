import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeInclusion
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction
import SGPT.Unibranch.OriginalLocalStrictWindowRegularity
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceOpenRestriction
import SGPT.Foundations.Analysis.Pending.HironakaEmbeddedNativeMorphismCommon

/-! Full original smaller ambient model equals the literal original open restriction, without global analytic extension.
Blueprint: prime-nov16-analytic-normalization-original-native-open-inclusion.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeOpenInclusion
open PrimeNov16AnalyticNormalizationOriginalNativeInclusion
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
open HironakaActualAnalyticSubspaceOpenRestriction HironakaEmbeddedNativeMorphism

variable {n : ℕ} (B : Set (ComplexModel n)) (U V : Opens (ComplexModel n))
  (hU : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' B))
  (hV : IsComplexAnalyticSubset (n := n) ((Subtype.val : V → ComplexModel n) ⁻¹' B)) (hUV : U ≤ V)

abbrev nativeOpenMap := nativeInclusion U V hU hV hUV (fun c => c.property)

theorem nativeOpenMap_square :
    (nativeOpenMap B U V hU hV hUV).hom.left ≫ actualOpenSubspaceMap (n := n) B V=
      actualOpenSubspaceMap (n := n) B U := by
  change actualSubspaceMap (f := Opens.inclusion hUV) (contMDiff_inclusion hUV) (fun _ hx => hx) ≫
    actualOpenSubspaceMap (n := n) B V=actualOpenSubspaceMap (n := n) B U
  exact (actualSubspaceMap_comp (contMDiff_inclusion hUV)
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (Subtype.val : V → ComplexModel n))
    (fun _ hx => hx) (fun _ hx => hx)).symm

instance nativeOpenMap_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (nativeOpenMap B U V hU hV hUV).hom.left := by
  have hi : LocallyRingedSpace.IsOpenImmersion
      ((nativeOpenMap B U V hU hV hUV).hom.left ≫ actualOpenSubspaceMap (n := n) B V) := by
    rw [nativeOpenMap_square]
    infer_instance
  let := hi
  exact HironakaG10ChowStrictTransformCalculus.isOpenImmersion_of_comp
    (nativeOpenMap B U V hU hV hUV).hom.left (actualOpenSubspaceMap (n := n) B V)

def smallerBaseOpen : Opens (sourceReducedComplexSpaceModel V ((Subtype.val : V → ComplexModel n) ⁻¹' B) hV).obj.left :=
  ⟨{b | b.val.val ∈ U},U.isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)⟩

theorem smallerBaseOpen_pc : ParacompactSpace (smallerBaseOpen B U V hV) := by
  change ParacompactSpace {b : {z : V | z.val ∈ B} // b.val.val ∈ U}
  infer_instance

theorem nativeOpenMap_range : range (nativeOpenMap B U V hU hV hUV).hom.left.base=
    (smallerBaseOpen B U V hV : Set (sourceReducedComplexSpaceModel V ((Subtype.val : V → ComplexModel n) ⁻¹' B) hV).obj.left) := by
  ext b
  constructor
  · rintro ⟨c,rfl⟩
    exact c.val.property
  · intro hb
    refine ⟨⟨⟨b.val.val,hb⟩,b.property⟩,?_⟩
    exact Subtype.ext (Subtype.ext rfl)

def nativeOpenIso :
    let _ := smallerBaseOpen_pc B U V hV
    sourceReducedComplexSpaceModel U ((Subtype.val : U → ComplexModel n) ⁻¹' B) hU ≅
      restrictedBase (smallerBaseOpen B U V hV) := by
  let := smallerBaseOpen_pc B U V hV
  let j := nativeOpenMap B U V hU hV hUV
  let i := baseInclusion (smallerBaseOpen B U V hV)
  have hr : range j.hom.left.base=range i.hom.left.base :=
    (nativeOpenMap_range B U V hU hV hUV).trans
      (HironakaG11BlowupLocality.range_openSubspaceInclusion _ _).symm
  let E := openImmersionIsoOfRangeEq j.hom.left i.hom.left hr
  have hE : E.hom ≫ i.hom.left=j.hom.left := openImmersionIsoOfRangeEq_hom_fac _ _ hr
  have hs : E.hom ≫ (restrictedBase (smallerBaseOpen B U V hV)).obj.hom=
      (sourceReducedComplexSpaceModel U ((Subtype.val : U → ComplexModel n) ⁻¹' B) hU).obj.hom := by
    rw [← Over.w i.hom,← Category.assoc,hE]
    exact Over.w j.hom
  exact ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk E hs)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeOpenInclusion

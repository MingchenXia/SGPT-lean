import SGPT.Foundations.Schemes.AffineQuasicoherentSectionSurjectivity
import SGPT.Foundations.Schemes.AffinePushforwardQuasicoherence
import SGPT.Foundations.Schemes.LineSectionTwistedAffineExactness
import Mathlib.Topology.Sheaves.LocallySurjective

/-! The actual zero-subscheme tensor restriction is an epimorphism and is
surjective on ORIGINAL affine sections without a line frame there. -/

universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine line-frame tensor coefficients descend quasicoherence of the
actual sheafified tensor with an arbitrary quasicoherent module. -/
theorem LineBundleAtlas.tensorModule_isQuasicoherent {X : Scheme.{u}}
    {B : X.Modules} (b : LineBundleAtlas B) (M : X.Modules) [M.IsQuasicoherent] :
    (bundleTensor B M).IsQuasicoherent := by
  let : ∀ i, ((bundleTensor B M).over (b.opens i)).IsQuasicoherent := fun i ↦ by
    let : (M.over (b.opens i)).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_over M (b.opens i)
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (b.opens i))).prop_of_iso
      ((b.frame i).tensorModule M).symm inferInstance
  apply SheafOfModules.IsQuasicoherent.of_coversTop (bundleTensor B M) b.opens
  rw [_root_.Opens.coversTop_iff]
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr (b.covers x)

/-- The target is the ORIGINAL sheafified line tensor with the actual closed
zero-subscheme structure pushforward. Its quasicoherence is produced. -/
theorem sectionZeroTensorQuotient_isQuasicoherent {X : Scheme.{u}}
    {L B : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (b : LineBundleAtlas B) :
    (bundleTensor B (sectionZeroPushforwardStructure a s)).IsQuasicoherent := by
  let : (SheafOfModules.unit (sectionZeroSubscheme a s).ringCatSheaf).IsQuasicoherent :=
    (trivialIntrinsicLineBundle (sectionZeroSubscheme a s)).atlas.isQuasicoherent
  let : (sectionZeroPushforwardStructure a s).IsQuasicoherent :=
    closedImmersionPushforward_isQuasicoherent (sectionZeroι a s)
      (SheafOfModules.unit (sectionZeroSubscheme a s).ringCatSheaf)
  exact b.tensorModule_isQuasicoherent _

/-- Actual affine framed quotient lifts give an epimorphism of the ORIGINAL
module sheaves. No global-section surjectivity is assumed. -/
theorem sectionZeroTensorRestriction_epi {X : Scheme.{u}}
    {L B : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (b : LineBundleAtlas B) :
    Epi (sectionZeroTensorRestriction a s B) := by
  let α := sectionZeroTensorRestriction a s B
  let Q := bundleTensor B (sectionZeroPushforwardStructure a s)
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hl : TopCat.Presheaf.IsLocallySurjective (F.map α).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro V t x hx
    obtain ⟨j, hxj⟩ := b.covers x
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ V ⊓ b.opens j from ⟨hx, hxj⟩)
    let k : W ≤ V := hWV.trans inf_le_left
    obtain ⟨v, hv⟩ := sectionZeroAffineTensorRestriction_surjective a s ⟨W, hW⟩
      (b.frame j) (homOfLE (hWV.trans inf_le_right)) (Q.val.map (homOfLE k).op t)
    exact ⟨W, k, ⟨v, hv⟩, hxW⟩
  let : CategoryTheory.Sheaf.IsLocallySurjective (F.map α) := hl
  exact F.epi_of_epi_map (show Epi (F.map α) from inferInstance)

/-- The literal tensor restriction is surjective on EVERY ORIGINAL affine
open, without a frame there and without regularity or nonempty hypotheses. -/
theorem sectionZeroAffineTensorRestriction_surjective_unframed {X : Scheme.{u}}
    {L B : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (b : LineBundleAtlas B)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((sectionZeroTensorRestriction a s B).app U) := by
  let : B.IsQuasicoherent := b.isQuasicoherent
  let : (bundleTensor B (sectionZeroPushforwardStructure a s)).IsQuasicoherent :=
    sectionZeroTensorQuotient_isQuasicoherent a s b
  let : Epi (sectionZeroTensorRestriction a s B) := sectionZeroTensorRestriction_epi a s b
  exact affineOpenSections_surjective_of_epi (sectionZeroTensorRestriction a s B) hU

end
end SGPT.Foundations.Schemes

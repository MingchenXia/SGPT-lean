import SGPT.PSH.AtlasOpenComponentEmbedding
import SGPT.PSH.AtlasNativeComponentHolomorphicOn
import Mathlib.Geometry.Manifold.Immersion

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- ORIGINAL A,U,p internally supply the FULL native complex manifold on
its SAME actual open component, without any paracompact/native/countability premise on U. -/
theorem openRestriction_componentComplexManifold (A : VariableComplexAtlas X)
    (U : Opens X) (p : U) :
    letI := (A.openRestriction U).componentChartedSpace p
    IsComplexManifold ((A.openRestriction U).pointDimension p)
      ((A.openRestriction U).componentOpen p) := by
  let := (A.openRestriction U).componentChartedSpace p
  let := A.componentSecondCountable p.val
  let := (A.openRestriction_componentMap_isOpenEmbedding U p).isEmbedding.secondCountableTopology
  exact {
    toT2Space := inferInstance
    toSecondCountableTopology := inferInstance
    toIsManifold := (A.openRestriction U).componentIsManifold p }

/-- ORIGINAL A,U,p manufacture the SAME entire native complex biholomorphism
onto the ACTUAL open range, with actual equal dimensions also OUTPUT, including0. -/
theorem exists_native_open_component_biholomorphism (A : VariableComplexAtlas X)
    (U : Opens X) (p : U) :
    letI := (A.openRestriction U).componentChartedSpace p
    letI := A.openRestriction_componentComplexManifold U p
    letI := A.componentChartedSpace p.val
    letI := A.componentComplexManifold_of_paracompact p.val
    (A.openRestriction U).pointDimension p = A.pointDimension p.val ∧
      ∃ O : Opens (A.componentOpen p.val),
      ∃ e : ((A.openRestriction U).componentOpen p) ≃ₘ⟮
        𝓘(ℂ, ComplexModel ((A.openRestriction U).pointDimension p)),
        𝓘(ℂ, ComplexModel (A.pointDimension p.val))⟯ O,
      ∀ q, (e q).val = (A.openRestriction_inclusion_isHolomorphic U).componentMap p q := by
  classical
  let := (A.openRestriction U).componentChartedSpace p
  let := A.openRestriction_componentComplexManifold U p
  let := A.componentChartedSpace p.val
  let := A.componentComplexManifold_of_paracompact p.val
  let B := A.openRestriction U
  let F := (A.openRestriction_inclusion_isHolomorphic U).componentMap p
  have hF := A.openRestriction_componentMap_isOpenEmbedding U p
  let O : Opens (A.componentOpen p.val) := ⟨range F, hF.isOpen_range⟩
  let e : B.componentOpen p ≃ₜ O := hF.isEmbedding.toHomeomorph
  have he : ContMDiff 𝓘(ℂ, ComplexModel (B.pointDimension p))
      𝓘(ℂ, ComplexModel (A.pointDimension p.val)) ∞ e := by
    apply (ContMDiff.iff_comp_isImmersionOfComplement
      (Manifold.IsImmersionOfComplement.of_opens.{0, 0, 0, u, 0} O)).mpr
    refine ⟨e.continuous, ?_⟩
    change ContMDiff 𝓘(ℂ, ComplexModel (B.pointDimension p))
      𝓘(ℂ, ComplexModel (A.pointDimension p.val)) ∞ F
    exact (A.openRestriction_inclusion_isHolomorphic U).componentMap_contMDiff p
  let Q : Set X := (Subtype.val : U → X) '' (B.componentOpen p : Set U)
  have hQ : IsOpen Q := U.isOpen.isOpenMap_subtype_val _ (B.componentOpen p).isOpen
  have hQU : Q ⊆ (U : Set X) := by
    rintro y ⟨r, _, rfl⟩
    exact r.property
  have hrange : range F = (Subtype.val : A.componentOpen p.val → X) ⁻¹' Q := by
    ext q
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.val, r.property, rfl⟩
    · rintro ⟨r, hr, hq⟩
      exact ⟨⟨r, hr⟩, Subtype.ext hq⟩
  let s := (U.openPartialHomeomorphSubtypeCoe ⟨p⟩).symm
  have hsU : A.IsHolomorphicOn B s (U : Set X) := A.openRestriction_inverse_isHolomorphicOn U p
  have hs : A.IsHolomorphicOn B s Q := by
    refine ⟨hsU.1.mono hQU, ?_⟩
    intro i j
    exact (hsU.2 i j).mono fun z hz => ⟨hz.1, hQU hz.2.1, hz.2.2⟩
  let p0 : B.componentOpen p := ⟨p, mem_connectedComponent⟩
  let g : A.componentOpen p.val → B.componentOpen p := fun q =>
    if hq : q ∈ (O : Set (A.componentOpen p.val)) then e.symm ⟨q, hq⟩
    else p0
  have hgs (q : A.componentOpen p.val) (hq : q.val ∈ Q) : (g q).val = s q.val := by
    have hqO : q ∈ (O : Set (A.componentOpen p.val)) := by
      change q ∈ range F
      rw [hrange]
      exact hq
    dsimp only [g]
    rw [dif_pos hqO]
    apply Subtype.ext
    have hv := congrArg (fun r : O => r.val.val) (e.apply_symm_apply ⟨q, hqO⟩)
    change (e.symm ⟨q, hqO⟩).val.val = q.val at hv
    have hsval : (s q.val).val = q.val := by
      change (U.openPartialHomeomorphSubtypeCoe ⟨p⟩) (s q.val) = q.val
      exact (U.openPartialHomeomorphSubtypeCoe ⟨p⟩).right_inv
        (by rw [Opens.openPartialHomeomorphSubtypeCoe_target]; exact hQU hq)
    exact hv.trans hsval.symm
  have hg := hs.component_restriction_contMDiffOn hQ p.val p g hgs
  have hgO : ContMDiffOn 𝓘(ℂ, ComplexModel (A.pointDimension p.val))
      𝓘(ℂ, ComplexModel (B.pointDimension p)) ∞ g (O : Set (A.componentOpen p.val)) := by
    change ContMDiffOn 𝓘(ℂ, ComplexModel (A.pointDimension p.val))
      𝓘(ℂ, ComplexModel (B.pointDimension p)) ∞ g (range F)
    rw [hrange]
    exact hg
  have hinv : e.symm = g ∘ (Subtype.val : O → A.componentOpen p.val) := by
    funext q
    dsimp only [Function.comp_apply, g]
    rw [dif_pos (show q.val ∈ (O : Set (A.componentOpen p.val)) from q.property)]
  have hei : ContMDiff 𝓘(ℂ, ComplexModel (A.pointDimension p.val))
      𝓘(ℂ, ComplexModel (B.pointDimension p)) ∞ e.symm := by
    rw [hinv]
    exact hgO.comp_contMDiff contMDiff_subtype_val fun q => q.property
  refine ⟨A.openRestriction_pointDimension U p, O,
    { e.toEquiv with contMDiff_toFun := he, contMDiff_invFun := hei }, fun _ => rfl⟩

end SGPT.PSH.VariableComplexAtlas

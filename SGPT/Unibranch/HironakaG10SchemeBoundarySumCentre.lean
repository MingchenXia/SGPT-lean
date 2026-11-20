import SGPT.Unibranch.HironakaG10SchemeBoundaryThickening
import SGPT.Unibranch.HironakaG10FiniteIdealSumCentre
import SGPT.Unibranch.HironakaG10SourceIdentifiedSumCentre

/-! # Sum centres from the powered reduced boundary support -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace SGPT.Unibranch.HironakaG10SchemeBoundarySumCentre

open SGPT.Foundations.Analysis.Pending HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreOpenPullback
open SGPT.Unibranch.HironakaG10HirLocalFlattener
  SGPT.Unibranch.HironakaG10LocallyAnalyticTrace
  SGPT.Unibranch.HironakaG10RelativeNonflatStrata
  SGPT.Unibranch.HironakaG10AnalyticStratumBoundary
  SGPT.Unibranch.HironakaG10LocalBoundaryGlobalCut
  SGPT.Unibranch.HironakaG10SchemeBoundaryThickening
  SGPT.Unibranch.HironakaG10FiniteIdealSumCentre
  SGPT.Unibranch.HironakaG10SourceIdentifiedSumCentre
  SGPT.Unibranch.HironakaG10ChowTrackedDatum
  SGPT.Unibranch.HironakaG10ChowFlatteningDriver
  SGPT.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- A globally extended powered reduced-support boundary ideal produces
  admissible tracked sum centres with the stated stalk equations and support. -/
theorem exists_scheme_boundary_sumCentre {X Y : SourceReducedComplexSpace}
    [CompactSpace X.obj.left] (f : Y ⟶ X) (B C : Set X.obj.left)
    (Z : LocalFlattener f) (i ω : ℕ) (hω : ω ≠ 0)
    (hS : IsLocallyAnalyticOn X Z.V (strata f B (i + 1)))
    (hC : IsLocallyAnalyticOn X Z.V C) (hCclosed : IsClosed C) (hCV : C ⊆ Z.V)
    (hCdense : Dense Cᶜ) :
    let G := closure ((strata f B (i + 1) ∩ Z.V) \ Z.support)
    let E := stratumBoundary f B Z.V Z.support i
    let Q := C ∩ E
    ∃ (D : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
      (d : D ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)),
      D.IsFiniteType ∧ nonunitLocus D d = Q ∧
      (∀ x ∈ Z.V, LinearMap.range
        (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf D d x) =
          (intrinsicCentreStalkRange X.obj.left C x) ^ ω ⊔
            (intrinsicCentreStalkRange X.obj.left G x ⊔ Z.H x)) ∧
      ∃ α : ℕ, ∀ β : ℕ, α ≤ β → ∃ c : AdmissibleCentre f,
        nonunitLocus c.B c.b = Q ∧ IsSumCentreFor c.B c.b f β ∧
        ∀ x ∈ Z.V, LinearMap.range
          (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf c.B c.b x) =
            (wholeIdealFamily D d x) ^ β ⊔ Z.H x := by
  let E := stratumBoundary f B Z.V Z.support i
  let Q := C ∩ E
  have hQZ : Q ⊆ Z.support := fun _ hx => hx.2.2
  obtain ⟨hQcompact,hQnonflat⟩ := compact_global_cut_of_local_data f B C Z i hS hC hCclosed hCV
  have hQdense : Dense Qᶜ := hCdense.mono (Set.compl_subset_compl.mpr inter_subset_left)
  obtain ⟨D,d,hfinite,hDQ,hsource,_⟩ :=
    exists_scheme_boundary_thickening f B C Z i ω hω hS hC hCclosed hCV
  let : D.IsFiniteType := hfinite
  let IS := wholeIdealFamily D d
  have hIS : IsLocallyFinitelyGeneratedOn X.obj.left Z.V IS :=
    locallyFinite_wholeIdealFamily D d Z.V
  have hQIS : {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤} = Q := by
    ext x
    constructor
    · intro hx
      have hxD : x ∈ nonunitLocus D d := hx.2
      rw [hDQ] at hxD
      exact hxD
    · intro hx
      have hxD : x ∈ nonunitLocus D d := by rw [hDQ]; exact hx
      exact ⟨hQZ hx, hxD⟩
  have hcompact : IsCompact {x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤} := hQIS.symm ▸ hQcompact
  have hdense : Dense {x : X.obj.left | ¬ (x ∈ Z.support ∧ IS x ≠ ⊤)} := by
    change Dense ({x : X.obj.left | x ∈ Z.support ∧ IS x ≠ ⊤}ᶜ)
    rw [hQIS]
    exact hQdense
  obtain ⟨α,hα⟩ := exists_sourceIdentified_sumCentre f Z IS hIS hcompact hdense
  refine ⟨D,d,hfinite,hDQ,hsource,α,fun β hαβ => ?_⟩
  obtain ⟨T,t,htfinite,htQ,htdense,htsum,htsource⟩ := hα β hαβ
  let c : AdmissibleCentre f := ⟨T,t,htfinite,htdense,by rw [htQ,hQIS]; exact hQnonflat⟩
  exact ⟨c,htQ.trans hQIS,htsum,htsource⟩

end
end SGPT.Unibranch.HironakaG10SchemeBoundarySumCentre

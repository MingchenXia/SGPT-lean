import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalPartialScalarRegularity
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphPullbackDensity
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionBimeromorphic

/-! SAME smaller original germ window internally manufactures actual entire good densities and book bimeromorphicity.
Blueprint: prime-nov16-analytic-normalization-original-family-bimeromorphic.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFamilyBimeromorphic
open NativeNov16PartialBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalPartialScalarRegularity
open PrimeNov16AnalyticNormalizationOriginalGraphPullbackDensity
open PrimeNov16AnalyticNormalizationOriginalSectionBimeromorphic
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalGoodDensity
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open PrimeNov16AnalyticNormalizationLocalGraph
open HironakaActualAnalyticSubspace
open HironakaG1NativeDisjointCoproduct
open SourceReducedComplexSpace

theorem actual_family_bimeromorphic_of_original_window {n k : ℕ} {Z : Set (ComplexModel n)}
    (B : Fin k → Set (ComplexModel n)) (P Ω : Opens (ComplexModel n)) (hΩP : Ω ≤ P)
    (hZ : IsComplexAnalyticSubset (n := n) ((Subtype.val : P → ComplexModel n) ⁻¹' Z))
    (hZΩ : IsComplexAnalyticSubset (n := n) ((Subtype.val : Ω → ComplexModel n) ⁻¹' Z))
    (hBΩ : ∀ i,IsComplexAnalyticSubset (n := n) ((Subtype.val : Ω → ComplexModel n) ⁻¹' B i))
    (d : ∀ i,GraphPresentation n (B i)) (hΩd : ∀ i,Ω ≤ ballDomain (n := n) (d i).radius)
    (g : ∀ i,(d i).target ⟶ sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ)
    (hcoord : ∀ i,∀ b : (d i).target.obj.left,((g i).hom.left.base b).val.val=b.val.val.val)
    (U : Opens (sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ).obj.left)
    [ParacompactSpace U] (V : Set Ω) (Q : ComplexModel n → ℂ) (hQ : DifferentiableOn ℂ Q Ω)
    (hland : ∀ p : ((Subtype.val : P → ComplexModel n) ⁻¹' Z),p ∈ U → p.val.val ∈ Ω)
    (hWindow : ∀ p : ((Subtype.val : P → ComplexModel n) ⁻¹' Z),∀ hp : p ∈ U,
      (⟨p.val.val,hland p hp⟩ : Ω) ∈ V)
    (hNZ : ∀ p : ((Subtype.val : Ω → ComplexModel n) ⁻¹' Z),p.val ∈ V →
      originalFunctionImage _ p (fun y : Ω => Q y.val)
        (function_holomorphicAt Ω Ω Q hQ p.val p.val.property) ≠ 0)
    (hNZi : ∀ i,∀ p : ((Subtype.val : Ω → ComplexModel n) ⁻¹' B i),p.val ∈ V →
      originalFunctionImage _ p (fun y : Ω => Q y.val)
        (function_holomorphicAt Ω Ω Q hQ p.val p.val.property) ≠ 0)
    (hp : IsProperMap (desc (fun i => (commonGraph (d i) (g i) U).source)
      (fun i => commonMap (d i) (g i) U)).hom.left.base)
    (hi : IsIsoOver (desc (fun i => (commonGraph (d i) (g i) U).source)
      (fun i => commonMap (d i) (g i) U)) {x | Q x.val.val.val ≠ 0}) :
    let Y : Fin k → SourceReducedComplexSpace := fun i => (commonGraph (d i) (g i) U).source
    let F : ∀ i,Y i ⟶ restrictedBase U := fun i => commonMap (d i) (g i) U
    IsProperBimeromorphic (desc Y F) ∧
      Dense {x : (restrictedBase U).obj.left | Q x.val.val.val ≠ 0} ∧
      Dense ((desc Y F).hom.left.base ⁻¹' {x | Q x.val.val.val ≠ 0}) := by
  let X := sourceReducedComplexSpaceModel P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) hZ
  let Y : Fin k → SourceReducedComplexSpace := fun i => (commonGraph (d i) (g i) U).source
  let F : ∀ i,Y i ⟶ restrictedBase U := fun i => commonMap (d i) (g i) U
  let E : Set (restrictedBase U).obj.left := {x | Q x.val.val.val ≠ 0}
  have hBase := actual_partial_scalar_nonzero_dense Z P Ω hΩP hZ hZΩ U V Q hQ hland hWindow hNZ
  have hCompCoord (i : Fin k) (b : (commonGraph (d i) (g i) U).target.obj.left) :
      ((commonComponent (d i) (g i) U).hom.left.base b).val.val.val=b.val.val.val := by
    have hs := congrArg (fun m => (m.hom.left.base b).val.val)
      (commonComponent_square (d i) (g i) U)
    have ht := targetEmbedding_point (d i) _ (commonBaseOpen_le (d i) (g i) U) b
    exact hs.trans ((hcoord i _).trans (congrArg (fun x => x.val.val) ht))
  have hEach : ∀ i,Dense ((F i).hom.left.base ⁻¹' E) := by
    intro i
    let Wi : Opens (TopCat.of {z : ballDomain (n := n) (d i).radius | z.val ∈ B i}) :=
      commonBaseOpen (d i) (g i) U
    have hlandi : ∀ b : {z : ballDomain (n := n) (d i).radius | z.val ∈ B i},b ∈ Wi → b.val.val ∈ Ω := by
      intro b hb
      let b0 : (commonGraph (d i) (g i) U).target.obj.left := ⟨b,hb⟩
      let x := (commonComponent (d i) (g i) U).hom.left.base b0
      exact (hCompCoord i b0) ▸ hland x.val x.property
    have hWindowi : ∀ b : {z : ballDomain (n := n) (d i).radius | z.val ∈ B i},∀ hb : b ∈ Wi,
        (⟨b.val.val,hlandi b hb⟩ : Ω) ∈ V := by
      intro b hb
      let b0 : (commonGraph (d i) (g i) U).target.obj.left := ⟨b,hb⟩
      let x := (commonComponent (d i) (g i) U).hom.left.base b0
      have hv := hWindow x.val x.property
      have he : (⟨x.val.val.val,hland x.val x.property⟩ : Ω)=(⟨b.val.val,hlandi b hb⟩ : Ω) :=
        Subtype.ext (hCompCoord i b0)
      exact he ▸ hv
    have hBi := actual_partial_scalar_nonzero_dense (B i) (ballDomain (n := n) (d i).radius) Ω
      (hΩd i) (d i).carrier_analytic (hBΩ i) Wi V Q hQ hlandi hWindowi (hNZi i)
    have hDense : Dense ((commonComponent (d i) (g i) U).hom.left.base ⁻¹' E) := by
      have he : (commonComponent (d i) (g i) U).hom.left.base ⁻¹' E=
          {b : (commonGraph (d i) (g i) U).target.obj.left | Q b.val.val.val ≠ 0} := by
        ext b
        change Q ((commonComponent (d i) (g i) U).hom.left.base b).val.val.val ≠ 0 ↔ Q b.val.val.val ≠ 0
        rw [hCompCoord]
      have hd : Dense {b : (commonGraph (d i) (g i) U).target.obj.left | Q b.val.val.val ≠ 0} := hBi.2
      exact he.symm ▸ hd
    exact actual_common_graph_dense_preimage (d i) (g i) U E hDense
  have hSource : Dense ((desc Y F).hom.left.base ⁻¹' E) := dense_preimage_coproduct Y F E hEach
  let s := scalarSection P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) U Ω Q hQ hland
  have hEq : {x : (restrictedBase U).obj.left | original_value_hom _ U x s ≠ 0}=E := by
    ext x
    have hv := scalarSection_value P ((Subtype.val : P → ComplexModel n) ⁻¹' Z) U Ω Q hQ hland x
    change original_value_hom _ U x s ≠ 0 ↔ Q x.val.val.val ≠ 0
    exact ⟨fun h he => h (hv.trans he),fun h he => h (hv.symm.trans he)⟩
  have hBim : IsProperBimeromorphic (desc Y F) := by
    apply actual_proper_bimeromorphic_of_section_density P _ hZ U s (desc Y F) hp
    · exact hEq.symm ▸ hBase.2
    · exact hEq.symm ▸ hSource
    · exact hEq.symm ▸ hi
  exact ⟨hBim,hBase.2,hSource⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFamilyBimeromorphic

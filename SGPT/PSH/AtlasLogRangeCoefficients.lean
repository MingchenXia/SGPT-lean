import SGPT.PSH.AtlasLogRangeQSquare

/-! ALL actual original range coefficients equal the SAME native open
coefficients, produced from ORIGINAL D alone and actual prime carriers. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- ORIGINAL D,x,O and any ACTUAL native prime ALONE give its complete
coefficient on SAME original D restricted to the literal range. The actual
prime index, component square and full Cartier-order readbacks are internal. -/
theorem original_range_coefficient (D : AtlasEffectiveGeometricQDivisor A)
    (x : X) (O : Opens (A.componentOpen x)) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ P : GeometricPrimeCarrier (A.pointDimension x) O,
    let U := flattenOpen (A.componentOpen x) O
    letI := A.openRestriction_paracompactSpace U
    (D.openRestriction U).coefficient (originalPrimeOnRange A x O P)=
      (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent x) O).coefficient P := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro P
  let U := flattenOpen (A.componentOpen x) O
  let B := A.openRestriction U
  let e := flattenHomeomorph (A.componentOpen x) O
  let := A.openRestriction_paracompactSpace U
  let W := originalPrimeOnRange A x O P
  have hW : W.val=e '' P.val := originalPrimeOnRange_carrier A x O P
  obtain ⟨q,hq⟩ := P.nonempty
  let p := e q
  have hp : p∈W.val := by
    rw [hW]
    exact ⟨q,hq,rfl⟩
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  obtain ⟨PB,hPB⟩ := W.exists_native_component p ⟨p,hp,mem_connectedComponent⟩
  let C := nativeConnectedOpen (n := A.pointDimension x) q
  let r : B.componentOpen p ≃ₜ C := connectedComponentHomeomorph e q
  let PC := primePreimageOfDimensionEq (range_component_dimension A x O q).symm r.symm
    (range_component_symm_contMDiff A x O q) (range_component_contMDiff A x O q) PB
  have hPCpre : PC.val=r.symm ⁻¹' PB.val :=
    primePreimageOfDimensionEq_carrier (range_component_dimension A x O q).symm r.symm
      (range_component_symm_contMDiff A x O q) (range_component_contMDiff A x O q) PB
  have hPBpre : (Subtype.val : B.componentOpen p → U) ⁻¹' W.val=PB.val := by
    rw [←hPB]
    exact Set.preimage_image_eq PB.val Subtype.val_injective
  have hPC : PC.val=(Subtype.val : C → O) ⁻¹' P.val := by
    rw [hPCpre]
    ext z
    change r.symm z∈PB.val ↔ z.val∈P.val
    rw [←hPBpre]
    change e z.val∈W.val ↔ z.val∈P.val
    rw [hW]
    constructor
    · rintro ⟨t,ht,heq⟩
      exact e.injective heq ▸ ht
    · intro hz
      exact ⟨z.val,hz,rfl⟩
  have hBW : B.nativePrimeOriginalCarrier p PB=W := AtlasGeometricPrimeCarrier.ext hPB
  have hread : (D.openRestriction U).coefficient W=
      (D.nativeOpenRestrictionComponent U p).coefficient PB := by
    rw [←hBW]
    exact openRestriction_original_coefficient_arbitrary_anchor D U p PB
  have hsq := original_range_component_q_square D x O q
  have hsqCoef : (geometricQDivisorOpenRestrictionAnyDimension
      (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent x) O) C).coefficient PC=
      (D.nativeOpenRestrictionComponent U p).coefficient PB := by
    rw [hsq]
    exact geometricQPreimageOfDimensionEq_coefficient (range_component_dimension A x O q).symm
      (D.nativeOpenRestrictionComponent U p) r.symm
      (range_component_symm_contMDiff A x O q) (range_component_contMDiff A x O q) PB
  exact hread.trans (hsqCoef.symm.trans (geometricQOpen_component_coefficient
    (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent x) O) q P PC hPC))

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft

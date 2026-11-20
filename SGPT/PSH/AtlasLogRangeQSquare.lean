import SGPT.PSH.GeometricQComponentCoefficient
import SGPT.PSH.AtlasLogRangePrimeEquivalence

/-! ENTIRE actual original/native range divisor square, retaining all
independently produced native dimensions, without a compatibility premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.SourceLogSingularitiesDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u

/-- All coefficients of the genuine prime preimage survive pure dimension
substitution; the actual original prime and divisor are retained. -/
theorem geometricQPreimageOfDimensionEq_coefficient
    {a b : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a=b) (D : EffectiveGeometricQDivisor b N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ e.symm)
    (P : GeometricPrimeCarrier b N) :
    (geometricQDivisorBiholomorphicPreimageOfDimensionEq h D e he hei).coefficient
      (primePreimageOfDimensionEq h e he hei P)=D.coefficient P := by
  subst b
  exact geometricQDivisorBiholomorphicPreimage_coefficient D e he hei P

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- ORIGINAL D,x,O,q ALONE prove the ENTIRE original-range/native-open
square. Every map, open image, dimension equality, divisor and compatibility
field is produced from actual original geometry and full coefficients. -/
theorem original_range_component_q_square (D : AtlasEffectiveGeometricQDivisor A)
    (x : X) (O : Opens (A.componentOpen x)) (q : O) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    let U := flattenOpen (A.componentOpen x) O
    let B := A.openRestriction U
    let e := flattenHomeomorph (A.componentOpen x) O
    let p := e q
    letI := A.openRestriction_paracompactSpace U
    letI := B.componentChartedSpace p
    letI := B.componentComplexManifold_of_paracompact p
    let C := nativeConnectedOpen (n := A.pointDimension x) q
    let r : B.componentOpen p ≃ₜ C := connectedComponentHomeomorph e q
    geometricQDivisorOpenRestrictionAnyDimension
      (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent x) O) C=
    geometricQDivisorBiholomorphicPreimageOfDimensionEq (range_component_dimension A x O q).symm
      (D.nativeOpenRestrictionComponent U p) r.symm
      (range_component_symm_contMDiff A x O q) (range_component_contMDiff A x O q) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let U := flattenOpen (A.componentOpen x) O
  let B := A.openRestriction U
  let e := flattenHomeomorph (A.componentOpen x) O
  let p := e q
  let := A.openRestriction_paracompactSpace U
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  let := A.componentChartedSpace p.val
  let := A.componentComplexManifold_of_paracompact p.val
  let C := nativeConnectedOpen (n := A.pointDimension x) q
  let r : B.componentOpen p ≃ₜ C := connectedComponentHomeomorph e q
  have hpx : p.val∈connectedComponent x := q.val.property
  let a := A.componentReanchorHomeomorph x p.val hpx
  obtain ⟨Va,k,hkval,hD⟩ :=
    (Classical.choose_spec (exists_native_open_component_q_divisor D U p)).2
  let W := flattenOpen O C
  let w := flattenHomeomorph O C
  have hcomm (z : C) : a (w z).val=(k (r.symm z)).val := by
    apply Subtype.ext
    rw [hkval (r.symm z)]
    rfl
  have hsq := geometricQOpen_square_of_dimensions
    (A.pointDimension_eq_on_connectedComponent x hpx).symm rfl
    (A.openRestriction_pointDimension U p) (range_component_dimension A x O q).symm
    (D.nativeComponent p.val) a W Va w k.toHomeomorph r.symm
    (A.componentReanchorHomeomorph_contMDiff x p.val hpx)
    (A.componentReanchorHomeomorph_symm_contMDiff x p.val hpx)
    (flattenHomeomorph_contMDiff O C) (flattenHomeomorph_symm_contMDiff O C)
    k.contMDiff k.symm.contMDiff (range_component_symm_contMDiff A x O q)
    (range_component_contMDiff A x O q) hcomm
  rw [←D.nativeComponent_reanchor x p.val hpx,←hD] at hsq
  change geometricQDivisorBiholomorphicPreimage
    (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent x) W) w
    (flattenHomeomorph_contMDiff O C) (flattenHomeomorph_symm_contMDiff O C)=_ at hsq
  exact (geometricQOpen_nested (D.nativeComponent x) O C).trans hsq

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft

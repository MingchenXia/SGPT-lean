import SGPT.PSH.AtlasLogRangePrime
import SGPT.PSH.GeometricPrimeClopenExtension

/-! The entire actual original/native prime index on a range open, not a
supplied positive-prime catalog or a support-only compatibility record. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  (A : VariableComplexAtlas X) (x : X)

/-- EVERY actual original range prime has an actual native prime on the
SAME native open with the SAME whole image. All components and dimensions
are internally constructed from the original atlas and prime. -/
theorem exists_native_prime_of_original_range (O : Opens (A.componentOpen x)) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    let U := flattenOpen (A.componentOpen x) O
    letI := A.openRestriction_paracompactSpace U
    ∀ Q : AtlasGeometricPrimeCarrier (A.openRestriction U),
      ∃ P : GeometricPrimeCarrier (A.pointDimension x) O,
        flattenHomeomorph (A.componentOpen x) O '' P.val=Q.val := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let U := flattenOpen (A.componentOpen x) O
  let B := A.openRestriction U
  let e := flattenHomeomorph (A.componentOpen x) O
  let := A.openRestriction_paracompactSpace U
  change ∀ Q : AtlasGeometricPrimeCarrier B,
    ∃ P : GeometricPrimeCarrier (A.pointDimension x) O,e '' P.val=Q.val
  intro Q
  obtain ⟨p,hp⟩ := Q.nonempty
  let q := e.symm p
  let p0 := e q
  have hp0 : p0∈Q.val := by
    change e (e.symm p)∈Q.val
    rwa [e.apply_symm_apply]
  let := B.componentChartedSpace p0
  let := B.componentComplexManifold_of_paracompact p0
  obtain ⟨PB,hPB⟩ := Q.exists_native_component p0 ⟨p0,hp0,mem_connectedComponent⟩
  let C := nativeConnectedOpen (n := A.pointDimension x) q
  have hC : IsClopen (C : Set O) := ⟨isClosed_connectedComponent,C.isOpen⟩
  let r : B.componentOpen p0 ≃ₜ C := connectedComponentHomeomorph e q
  let PC := primePreimageOfDimensionEq (range_component_dimension A x O q).symm r.symm
    (range_component_symm_contMDiff A x O q) (range_component_contMDiff A x O q) PB
  obtain ⟨P,hP⟩ := exists_prime_of_clopen_image C hC PC
  refine ⟨P,?_⟩
  have hPC : PC.val=r.symm ⁻¹' PB.val :=
    primePreimageOfDimensionEq_carrier (range_component_dimension A x O q).symm r.symm
      (range_component_symm_contMDiff A x O q) (range_component_contMDiff A x O q) PB
  rw [hP,←hPB,hPC]
  ext y
  constructor
  · rintro ⟨z,⟨c,hc,rfl⟩,rfl⟩
    exact ⟨r.symm c,hc,rfl⟩
  · rintro ⟨s,hs,rfl⟩
    refine ⟨(r s).val,⟨r s,?_,rfl⟩,?_⟩
    · change r.symm (r s)∈PB.val
      rwa [r.symm_apply_apply]
    · exact e.apply_symm_apply s.val

/-- Choose ONLY the actual original prime constructed from the native one. -/
def originalPrimeOnRange (O : Opens (A.componentOpen x)) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    let U := flattenOpen (A.componentOpen x) O
    letI := A.openRestriction_paracompactSpace U
    GeometricPrimeCarrier (A.pointDimension x) O → AtlasGeometricPrimeCarrier (A.openRestriction U) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let U := flattenOpen (A.componentOpen x) O
  let := A.openRestriction_paracompactSpace U
  exact fun P => Classical.choose (exists_original_prime_on_range A x O P)

/-- The literal whole carrier, independent of any witness choices. -/
theorem originalPrimeOnRange_carrier (O : Opens (A.componentOpen x)) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    let U := flattenOpen (A.componentOpen x) O
    letI := A.openRestriction_paracompactSpace U
    ∀ P : GeometricPrimeCarrier (A.pointDimension x) O,
      (originalPrimeOnRange A x O P).val=flattenHomeomorph (A.componentOpen x) O '' P.val := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let U := flattenOpen (A.componentOpen x) O
  let := A.openRestriction_paracompactSpace U
  change ∀ P : GeometricPrimeCarrier (A.pointDimension x) O,
    (originalPrimeOnRange A x O P).val=flattenHomeomorph (A.componentOpen x) O '' P.val
  intro P
  exact Classical.choose_spec (exists_original_prime_on_range A x O P)

/-- The produced actual entire prime map is a genuine bijection, including
all coefficient-zero indices and actual empty zero-dimensional prime types. -/
theorem originalPrimeOnRange_bijective (O : Opens (A.componentOpen x)) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    let U := flattenOpen (A.componentOpen x) O
    letI := A.openRestriction_paracompactSpace U
    Function.Bijective (originalPrimeOnRange A x O) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let U := flattenOpen (A.componentOpen x) O
  let := A.openRestriction_paracompactSpace U
  constructor
  · intro P Q h
    apply GeometricPrimeCarrier.ext
    apply (Set.image_injective.mpr (flattenHomeomorph (A.componentOpen x) O).injective)
    exact ((originalPrimeOnRange_carrier A x O P).symm.trans
      (congrArg Subtype.val h)).trans (originalPrimeOnRange_carrier A x O Q)
  · intro Q
    obtain ⟨P,hP⟩ := exists_native_prime_of_original_range A x O Q
    refine ⟨P,AtlasGeometricPrimeCarrier.ext ?_⟩
    exact (originalPrimeOnRange_carrier A x O P).trans hP

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft

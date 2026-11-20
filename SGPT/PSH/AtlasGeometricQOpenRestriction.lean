import SGPT.PSH.AtlasOpenParacompact
import SGPT.PSH.AtlasNativeReanchor
import SGPT.PSH.NativeLogAnyDimension

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u

/-- The EXISTING pure dimension substitution retains the ENTIRE actual
biholomorphic rational support preimage, including dimension zero. -/
theorem geometricQDivisorBiholomorphicPreimageOfDimensionEq_support
    {a b : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a = b) (D : EffectiveGeometricQDivisor b N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel a) ∞ e.symm) :
    (geometricQDivisorBiholomorphicPreimageOfDimensionEq h D e he hei).support =
      e ⁻¹' D.support := by
  subst b
  exact geometricQDivisorBiholomorphicPreimage_support D e he hei

namespace VariableComplexAtlas
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- ORIGINAL D,U,p manufacture a genuine native Q restriction on SAME
component, its FULL original support preimage and the SAME actual native
open-biholomorphic restriction equation. ALL geometry/dimensions are output. -/
theorem exists_native_open_component_q_divisor (D : AtlasEffectiveGeometricQDivisor A)
    (U : Opens X) (p : U) :
    letI := A.openRestriction_paracompactSpace U
    letI := (A.openRestriction U).componentChartedSpace p
    letI := (A.openRestriction U).componentComplexManifold_of_paracompact p
    letI := A.componentChartedSpace p.val
    letI := A.componentComplexManifold_of_paracompact p.val
    ∃ Q : EffectiveGeometricQDivisor ((A.openRestriction U).pointDimension p)
        ((A.openRestriction U).componentOpen p),
      Q.support = (fun q : (A.openRestriction U).componentOpen p => q.val.val) ⁻¹' D.support ∧
      ∃ O : Opens (A.componentOpen p.val),
      ∃ e : ((A.openRestriction U).componentOpen p) ≃ₘ⟮
        𝓘(ℂ, ComplexModel ((A.openRestriction U).pointDimension p)),
        𝓘(ℂ, ComplexModel (A.pointDimension p.val))⟯ O,
      (∀ q, (e q).val = (A.openRestriction_inclusion_isHolomorphic U).componentMap p q) ∧
      Q = geometricQDivisorBiholomorphicPreimageOfDimensionEq
        (A.openRestriction_pointDimension U p)
        (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent p.val) O)
        e.toHomeomorph e.contMDiff e.symm.contMDiff := by
  let := A.openRestriction_paracompactSpace U
  let := (A.openRestriction U).componentChartedSpace p
  let := (A.openRestriction U).componentComplexManifold_of_paracompact p
  let := A.componentChartedSpace p.val
  let := A.componentComplexManifold_of_paracompact p.val
  obtain ⟨hdim, O, e, heval⟩ := A.exists_native_open_component_biholomorphism U p
  let Q := geometricQDivisorBiholomorphicPreimageOfDimensionEq hdim
    (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent p.val) O)
    e.toHomeomorph e.contMDiff e.symm.contMDiff
  refine ⟨Q, ?_, O, e, heval, rfl⟩
  calc
    Q.support = e.toHomeomorph ⁻¹'
        (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent p.val) O).support :=
      geometricQDivisorBiholomorphicPreimageOfDimensionEq_support hdim _
        e.toHomeomorph e.contMDiff e.symm.contMDiff
    _ = (fun q : (A.openRestriction U).componentOpen p => q.val.val) ⁻¹' D.support := by
      rw [geometricQDivisorOpenRestrictionAnyDimension_support, D.nativeComponent_support]
      ext q
      change (e q).val.val ∈ D.support ↔ q.val.val ∈ D.support
      rw [heval q]
      rfl


/-- Choose ONLY the genuine native restriction internally manufactured from
ORIGINAL D,U,p; no component family or coefficient certificate is supplied. -/
def AtlasEffectiveGeometricQDivisor.nativeOpenRestrictionComponent
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) (p : U) :
    letI := A.openRestriction_paracompactSpace U
    letI := (A.openRestriction U).componentChartedSpace p
    letI := (A.openRestriction U).componentComplexManifold_of_paracompact p
    EffectiveGeometricQDivisor ((A.openRestriction U).pointDimension p)
      ((A.openRestriction U).componentOpen p) := by
  let := A.openRestriction_paracompactSpace U
  let := (A.openRestriction U).componentChartedSpace p
  let := (A.openRestriction U).componentComplexManifold_of_paracompact p
  exact Classical.choose (exists_native_open_component_q_divisor D U p)

/-- The SAME internally selected native restriction retains the ENTIRE
successive original inclusion support preimage, including all zero branches. -/
theorem AtlasEffectiveGeometricQDivisor.nativeOpenRestrictionComponent_support
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) (p : U) :
    letI := A.openRestriction_paracompactSpace U
    letI := (A.openRestriction U).componentChartedSpace p
    letI := (A.openRestriction U).componentComplexManifold_of_paracompact p
    (D.nativeOpenRestrictionComponent U p).support =
      (fun q : (A.openRestriction U).componentOpen p => q.val.val) ⁻¹' D.support := by
  let := A.openRestriction_paracompactSpace U
  let := (A.openRestriction U).componentChartedSpace p
  let := (A.openRestriction U).componentComplexManifold_of_paracompact p
  exact (Classical.choose_spec (exists_native_open_component_q_divisor D U p)).1

/-- ORIGINAL D and ANY ORIGINAL U internally manufacture EVERY genuine
component restriction and assemble the entire original-atlas Q divisor. -/
def AtlasEffectiveGeometricQDivisor.openRestriction
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) :
    letI := A.openRestriction_paracompactSpace U
    AtlasEffectiveGeometricQDivisor (A.openRestriction U) := by
  let := A.openRestriction_paracompactSpace U
  exact (A.openRestriction U).divisorOfNativeComponents
    (fun c => D.nativeOpenRestrictionComponent U (componentAnchor c))

/-- EVERY native prime on EVERY internally selected actual open component
retains its EXACT genuine coefficient on the literal original carrier image. -/
theorem AtlasEffectiveGeometricQDivisor.openRestriction_coefficient
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) :
    letI := A.openRestriction_paracompactSpace U
    ∀ t : (c : ConnectedComponents U) × (A.openRestriction U).componentNativePrime c,
      letI := (A.openRestriction U).componentChartedSpace (componentAnchor t.1)
      letI := (A.openRestriction U).componentComplexManifold_of_paracompact (componentAnchor t.1)
      (D.openRestriction U).coefficient ((A.openRestriction U).componentPrimeOriginalCarrier t) =
        (D.nativeOpenRestrictionComponent U (componentAnchor t.1)).coefficient t.2 := by
  let := A.openRestriction_paracompactSpace U
  intro t
  let := (A.openRestriction U).componentChartedSpace (componentAnchor t.1)
  let := (A.openRestriction U).componentComplexManifold_of_paracompact (componentAnchor t.1)
  exact (A.openRestriction U).divisorOfNativeComponents_coefficient
    (fun c => D.nativeOpenRestrictionComponent U (componentAnchor c)) t

/-- ENTIRE actual original-open restriction support is the literal inclusion
preimage of ORIGINAL D support, including the empty open and dimension zero. -/
theorem AtlasEffectiveGeometricQDivisor.openRestriction_support
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) :
    letI := A.openRestriction_paracompactSpace U
    (D.openRestriction U).support = Subtype.val ⁻¹' D.support := by
  let := A.openRestriction_paracompactSpace U
  let family : ∀ c : ConnectedComponents U, (A.openRestriction U).componentNativeDivisor c :=
    fun c => D.nativeOpenRestrictionComponent U (componentAnchor c)
  change ((A.openRestriction U).divisorOfNativeComponents family).support = _
  rw [(A.openRestriction U).divisorOfNativeComponents_support family]
  ext x
  constructor
  · intro hx
    obtain ⟨c, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
    let := (A.openRestriction U).componentChartedSpace (componentAnchor c)
    let := (A.openRestriction U).componentComplexManifold_of_paracompact (componentAnchor c)
    exact (Set.ext_iff.mp (D.nativeOpenRestrictionComponent_support U (componentAnchor c)) p).mp hp
  · intro hx
    let c := ConnectedComponents.mk x
    let := (A.openRestriction U).componentChartedSpace (componentAnchor c)
    let := (A.openRestriction U).componentComplexManifold_of_paracompact (componentAnchor c)
    have hxc : x ∈ (A.openRestriction U).componentOpen (componentAnchor c) :=
      (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec c).symm
    apply Set.mem_iUnion.mpr
    refine ⟨c, ⟨⟨x, hxc⟩, ?_, rfl⟩⟩
    change ⟨x, hxc⟩ ∈ (D.nativeOpenRestrictionComponent U (componentAnchor c)).support
    rw [D.nativeOpenRestrictionComponent_support]
    exact hx

end VariableComplexAtlas
end SGPT.PSH

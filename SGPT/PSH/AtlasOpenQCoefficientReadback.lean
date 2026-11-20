import SGPT.PSH.AtlasGeometricQOpenRestriction
import SGPT.PSH.AtlasVanishingIdeal

/-! Full original coefficient readback of the unchanged original rational
open restriction at every actual component anchor. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

private theorem native_divisor_ext {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {D E : EffectiveGeometricQDivisor n M} (h : ∀ P,D.coefficient P=E.coefficient P) : D=E := by
  rcases D with ⟨d,hd,hdf⟩
  rcases E with ⟨e,he,hef⟩
  have hde : d=e := funext h
  cases hde
  rfl

/-- The entire independently assembled original divisor projects to the
same actual native divisor, with every coefficient, not just support. -/
theorem nativeComponent_divisorOfNativeComponents
    (F : ∀ c : ConnectedComponents X,A.componentNativeDivisor c)
    (c : ConnectedComponents X) :
    letI := A.componentChartedSpace (componentAnchor c)
    letI := A.componentComplexManifold_of_paracompact (componentAnchor c)
    ((A.divisorOfNativeComponents F).nativeComponent (componentAnchor c))=F c := by
  let := A.componentChartedSpace (componentAnchor c)
  let := A.componentComplexManifold_of_paracompact (componentAnchor c)
  apply native_divisor_ext
  intro P
  rw [AtlasEffectiveGeometricQDivisor.nativeComponent_coefficient]
  exact divisorOfNativeComponents_coefficient F ⟨c,P⟩

/-- Actual SAME original open restriction, read at its internally chosen
component anchor, has the whole internally produced native restriction. -/
theorem nativeComponent_openRestriction_anchor
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) (c : ConnectedComponents U) :
    letI := A.openRestriction_paracompactSpace U
    letI := (A.openRestriction U).componentChartedSpace (componentAnchor c)
    letI := (A.openRestriction U).componentComplexManifold_of_paracompact (componentAnchor c)
    (D.openRestriction U).nativeComponent (componentAnchor c)=
      D.nativeOpenRestrictionComponent U (componentAnchor c) := by
  let := A.openRestriction_paracompactSpace U
  let := (A.openRestriction U).componentChartedSpace (componentAnchor c)
  let := (A.openRestriction U).componentComplexManifold_of_paracompact (componentAnchor c)
  exact nativeComponent_divisorOfNativeComponents
    (fun c => D.nativeOpenRestrictionComponent U (componentAnchor c)) c

/-- Every arbitrary original anchor retains the FULL coefficient divisor
through the actual accepted reanchor map, with dimensions produced internally. -/
theorem nativeComponent_openRestriction_arbitrary_anchor
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) (p : U) :
    letI := A.openRestriction_paracompactSpace U
    let B := A.openRestriction U
    let q := componentAnchor (ConnectedComponents.mk p)
    let hq : q ∈ connectedComponent p :=
      (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec (ConnectedComponents.mk p))
    letI := B.componentChartedSpace p
    letI := B.componentComplexManifold_of_paracompact p
    letI := B.componentChartedSpace q
    letI := B.componentComplexManifold_of_paracompact q
    (D.openRestriction U).nativeComponent p =
      geometricQDivisorBiholomorphicPreimageOfDimensionEq
        (B.pointDimension_eq_on_connectedComponent p hq).symm
        (D.nativeOpenRestrictionComponent U q)
        (B.componentReanchorHomeomorph p q hq)
        (B.componentReanchorHomeomorph_contMDiff p q hq)
        (B.componentReanchorHomeomorph_symm_contMDiff p q hq) := by
  let := A.openRestriction_paracompactSpace U
  let B := A.openRestriction U
  let q := componentAnchor (ConnectedComponents.mk p)
  have hq : q ∈ connectedComponent p :=
    (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec (ConnectedComponents.mk p))
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  let := B.componentChartedSpace q
  let := B.componentComplexManifold_of_paracompact q
  have h := (D.openRestriction U).nativeComponent_reanchor p q hq
  rw [nativeComponent_openRestriction_anchor D U (ConnectedComponents.mk p)] at h
  exact h

end SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft

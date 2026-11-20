import SGPT.PSH.AtlasOpenQCoefficientReadback
import SGPT.PSH.GeometricQOpenBiholomorphicSquare

/-! The SAME original rational open restriction has the exact actual native
restriction at EVERY original anchor. All square data are produced internally. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- ORIGINAL D,U,p ALONE produce the full native equality for SAME original
open restriction at ANY anchor, including every split and zero coefficient.
No map, dimension, prime, ideal or coefficient-compatibility cert is supplied. -/
theorem nativeComponent_openRestriction_actual
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) (p : U) :
    letI := A.openRestriction_paracompactSpace U
    letI := (A.openRestriction U).componentChartedSpace p
    letI := (A.openRestriction U).componentComplexManifold_of_paracompact p
    (D.openRestriction U).nativeComponent p=D.nativeOpenRestrictionComponent U p := by
  let := A.openRestriction_paracompactSpace U
  let B := A.openRestriction U
  let q := componentAnchor (ConnectedComponents.mk p)
  have hq : q∈connectedComponent p :=
    (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec (ConnectedComponents.mk p))
  have hqval : q.val∈connectedComponent p.val :=
    ((A.openRestriction_inclusion_isHolomorphic U).componentMap p ⟨q,hq⟩).property
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  let := B.componentChartedSpace q
  let := B.componentComplexManifold_of_paracompact q
  let := A.componentChartedSpace p.val
  let := A.componentComplexManifold_of_paracompact p.val
  let := A.componentChartedSpace q.val
  let := A.componentComplexManifold_of_paracompact q.val
  have hp : ∃ Op : Opens (A.componentOpen p.val),
      ∃ ep : B.componentOpen p ≃ₘ⟮𝓘(ℂ,ComplexModel (B.pointDimension p)),
        𝓘(ℂ,ComplexModel (A.pointDimension p.val))⟯ Op,
      (∀ s,(ep s).val=(A.openRestriction_inclusion_isHolomorphic U).componentMap p s) ∧
      D.nativeOpenRestrictionComponent U p = geometricQDivisorBiholomorphicPreimageOfDimensionEq
        (A.openRestriction_pointDimension U p)
        (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent p.val) Op)
        ep.toHomeomorph ep.contMDiff ep.symm.contMDiff :=
    (Classical.choose_spec (exists_native_open_component_q_divisor D U p)).2
  have hqdata : ∃ Oq : Opens (A.componentOpen q.val),
      ∃ eq : B.componentOpen q ≃ₘ⟮𝓘(ℂ,ComplexModel (B.pointDimension q)),
        𝓘(ℂ,ComplexModel (A.pointDimension q.val))⟯ Oq,
      (∀ s,(eq s).val=(A.openRestriction_inclusion_isHolomorphic U).componentMap q s) ∧
      D.nativeOpenRestrictionComponent U q = geometricQDivisorBiholomorphicPreimageOfDimensionEq
        (A.openRestriction_pointDimension U q)
        (geometricQDivisorOpenRestrictionAnyDimension (D.nativeComponent q.val) Oq)
        eq.toHomeomorph eq.contMDiff eq.symm.contMDiff :=
    (Classical.choose_spec (exists_native_open_component_q_divisor D U q)).2
  obtain ⟨Op,ep,hep,hDp⟩ := hp
  obtain ⟨Oq,eq,heq,hDq⟩ := hqdata
  let e := A.componentReanchorHomeomorph p.val q.val hqval
  let r := B.componentReanchorHomeomorph p q hq
  have hcomm (s : B.componentOpen p) : e (ep s).val=(eq (r s)).val := by
    apply Subtype.ext
    change (ep s).val.val=(eq (r s)).val.val
    rw [hep s,heq (r s)]
    rfl
  have hD := D.nativeComponent_reanchor p.val q.val hqval
  have hsquare := geometricQOpen_square_of_dimensions
    (A.pointDimension_eq_on_connectedComponent p.val hqval).symm
    (A.openRestriction_pointDimension U p) (A.openRestriction_pointDimension U q)
    (B.pointDimension_eq_on_connectedComponent p hq).symm
    (D.nativeComponent q.val) e Op Oq ep.toHomeomorph eq.toHomeomorph r
    (A.componentReanchorHomeomorph_contMDiff p.val q.val hqval)
    (A.componentReanchorHomeomorph_symm_contMDiff p.val q.val hqval)
    ep.contMDiff ep.symm.contMDiff eq.contMDiff eq.symm.contMDiff
    (B.componentReanchorHomeomorph_contMDiff p q hq)
    (B.componentReanchorHomeomorph_symm_contMDiff p q hq) hcomm
  rw [←hD,←hDp,←hDq] at hsquare
  exact (nativeComponent_openRestriction_arbitrary_anchor D U p).trans hsquare.symm

/-- Every genuine native prime at the ORIGINAL arbitrary anchor reads the
actual complete coefficient of SAME original D restricted to SAME original U. -/
theorem openRestriction_original_coefficient_arbitrary_anchor
    (D : AtlasEffectiveGeometricQDivisor A) (U : Opens X) (p : U) :
    letI := A.openRestriction_paracompactSpace U
    letI := (A.openRestriction U).componentChartedSpace p
    letI := (A.openRestriction U).componentComplexManifold_of_paracompact p
    ∀ P : GeometricPrimeCarrier ((A.openRestriction U).pointDimension p)
        ((A.openRestriction U).componentOpen p),
      (D.openRestriction U).coefficient ((A.openRestriction U).nativePrimeOriginalCarrier p P) =
        (D.nativeOpenRestrictionComponent U p).coefficient P := by
  let := A.openRestriction_paracompactSpace U
  let := (A.openRestriction U).componentChartedSpace p
  let := (A.openRestriction U).componentComplexManifold_of_paracompact p
  intro P
  rw [←AtlasEffectiveGeometricQDivisor.nativeComponent_coefficient,
    nativeComponent_openRestriction_actual]

end SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft

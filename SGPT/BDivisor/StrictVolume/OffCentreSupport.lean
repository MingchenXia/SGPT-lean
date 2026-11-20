import SGPT.BDivisor.CartierBDivisor
import SGPT.BDivisor.BlowupModel2Order
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound

/-! Actual off-centre fibre support kills the pulled exceptional current.
Source-facing route is BLUEPRINT.tex, ex:volbdivnetstrict:103.
No current/class pushforward equality or common-resolution certificate is input.
Checks and provider-boundary receipts are preserved separately. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SGPT.BDivisor.TraceOffCentreNext

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.GlobalCurrents
open SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
open SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
open SGPT.Currents.AnalyticSupport

section Fibre

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel 2) X] [IsComplexManifold 2 X]
  [ChartedSpace (ComplexModel 2) Y] [IsComplexManifold 2 Y]

omit [IsComplexManifold 2 X] [IsComplexManifold 2 Y] in
/-- Actual bijectivity over U internally manufactures the unique full fibre over p. -/
theorem exists_unique_fibre_of_isomorphism_over {rho : Y → X} {U : Set X} {p : X}
    (hiso : IsIsomorphismOver 2 rho U) (hp : p ∈ U) :
    ∃ y : Y, rho y = p ∧ ∀ y' : Y, rho y' = p → y' = y := by
  obtain ⟨y, hyU, hyp⟩ := hiso.1.2.2 hp
  refine ⟨y, hyp, ?_⟩
  intro y' hy'p
  exact hiso.1.2.1 (show y' ∈ rho ⁻¹' U from by change rho y' ∈ U; rwa [hy'p])
    hyU (hy'p.trans hyp.symm)

end Fibre

section ThinTarget

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  [ChartedSpace (ComplexModel 2) Y] [IsComplexManifold 2 Y]
  [ChartedSpace (ComplexModel 2) Z] [IsComplexManifold 2 Z]

private theorem surface_singleton_interior_empty (y : Y) :
    interior ({y} : Set Y) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxy : x = y := mem_singleton_iff.mp (interior_subset hx)
  subst x
  have hreg := (DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := 2) y).2.2
    y (mem_singleton y)
  have hEq : ({y} : Set Y) ∩ interior {y} = univ ∩ interior {y} := by
    ext z
    constructor
    · intro hz
      exact ⟨mem_univ z, hz.2⟩
    · intro hz
      exact ⟨interior_subset hz.2, hz.2⟩
  have hregU := RegularPointDimension.regularAtDim_of_inter_eq
    isOpen_interior hx hEq hreg
  have hdim := AnalyticIrreducibleComponents.eq_of_regularAtDim_univ hregU
  omega

/-- An actual positive-dimensional prime carrier cannot be contained in a point. -/
theorem not_prime_subset_singleton (D : SGPT.PSH.GeometricPrimeCarrier 2 Y) (y : Y) :
    ¬ D.val ⊆ {y} := by
  intro hsub
  obtain ⟨x, hx, hreg⟩ := D.subvariety.exists_regular_point
  have hxD : x ∈ D.val := by rwa [← D.subvariety_carrier]
  have hxy : x = y := mem_singleton_iff.mp (hsub hxD)
  subst x
  have hCarrier : D.subvariety.carrier = {y} := by
    apply Subset.antisymm
    · simpa only [D.subvariety_carrier] using hsub
    · exact singleton_subset_iff.mpr hx
  rw [hCarrier] at hreg
  have hzero := (DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := 2) y).2.2
    y (mem_singleton y)
  have hdim := RegularPointDimension.eq_of_regularAtDim hreg hzero
  have hcodim := D.subvariety_codimension
  omega

/-- The actual singleton fibre point plus the actual differential exceptional
image has the precise analytic thinness required by the native support theorem. -/
theorem singleton_union_exceptionalImage_thin {beta : Z → Y}
    (hbeta : IsAnalyticModification (n := 2) beta) (y : Y) :
    IsComplexAnalyticSubset (n := 2) ({y} ∪ beta '' exceptionalLocus 2 beta) ∧
      interior ({y} ∪ beta '' exceptionalLocus 2 beta) = ∅ ∧
      ∀ D : SGPT.PSH.GeometricPrimeCarrier 2 Y,
        ¬ D.val ⊆ {y} ∪ beta '' exceptionalLocus 2 beta := by
  let A : Set Y := beta '' exceptionalLocus 2 beta
  have hA : IsComplexAnalyticSubset (n := 2) A :=
    AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus hbeta
  have hAi : interior A = ∅ := Modification4.interior_image_exceptionalLocus_eq_empty hbeta
  have hPoint := FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (n := 2) y
  refine ⟨ConstantRankImage.IsComplexAnalyticSubset.union hPoint hA, ?_, ?_⟩
  · have hClosed : IsClosed ({y} : Set Y) := isClosed_singleton
    have hsub : interior ({y} ∪ A) ⊆ ({y} : Set Y) := by
      simpa only [hAi, union_empty] using (hClosed.interior_union_left (t := A))
    have hsubi := interior_maximal hsub isOpen_interior
    rw [surface_singleton_interior_empty] at hsubi
    exact subset_empty_iff.mp hsubi
  · intro D hD
    let V := D.subvariety
    have hDA : V.carrier ⊆ {y} ∪ A := by
      simpa only [V, D.subvariety_carrier] using hD
    have hsplit : V.carrier = (V.carrier ∩ {y}) ∪ (V.carrier ∩ A) := by
      ext z
      constructor
      · intro hz
        rcases hDA hz with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
      · rintro (hz | hz) <;> exact hz.1
    rcases V.irreducible_carrier.2.2 _ _ (V.analytic.inter hPoint)
      (V.analytic.inter hA) inter_subset_left inter_subset_left hsplit with h | h
    · apply not_prime_subset_singleton D y
      intro z hz
      have hzV : z ∈ V.carrier := by simpa only [V, D.subvariety_carrier] using hz
      exact (h ▸ hzV : z ∈ V.carrier ∩ {y}).2
    · apply AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one
        hbeta V D.subvariety_codimension
      intro z hz
      exact (h ▸ hz : z ∈ V.carrier ∩ A).2

end ThinTarget

section Current

variable {X B Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X] [IsComplexManifold 2 X]
  [TopologicalSpace B] [ChartedSpace (ComplexModel 2) B] [IsComplexManifold 2 B] [CompactSpace B]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel 2) Y] [IsComplexManifold 2 Y] [CompactSpace Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel 2) Z] [IsComplexManifold 2 Z] [CompactSpace Z]

omit [IsComplexManifold 2 X] in
/-- Actual common-refinement maps, the actual isomorphism fibre and the actual
divisor support produce the ZERO full current. No desired class equality is input. -/
theorem pushforward_pulled_metered_fibre_current_eq_zero
    {pi : B → X} {rho : Y → X} {q : Z → B} {beta : Z → Y}
    (hq : IsAnalyticModification (n := 2) q)
    (hbeta : IsAnalyticModification (n := 2) beta)
    (hcomm : pi ∘ q = rho ∘ beta) {U : Set X} {p : X}
    (hiso : IsIsomorphismOver 2 rho U) (hp : p ∈ U)
    (F : MeteredEffectiveQDivisor 2 B)
    (hF : IsThetaPshPotential F.curvature.val F.weight)
    (hsupp : F.support ⊆ pi ⁻¹' {p}) :
    currentPushforward hbeta.1
      (Modification4.pull hq (thetaPotentialCurrent F.curvature.val F.weight hF)
        (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hF)) = 0 := by
  obtain ⟨y, hyp, hyUnique⟩ := exists_unique_fibre_of_isomorphism_over hiso hp
  let T := thetaPotentialCurrent F.curvature.val F.weight hF
  have hT : SGPT.Siu.IsClosedPositiveCurrent T :=
    SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hF
  let Fq := MeteredDivisorOperations.pullback hq.1
    (Modification4.interior_exceptionalLocus_eq_empty hq) F
  have hFq : IsThetaPshPotential Fq.curvature.val Fq.weight :=
    isThetaPshPotential_comp_of_isAnalyticModification hq F.curvature hF
  have hPull : Modification4.pull hq T hT =
      integrationCurrent (canonicalBasis 2) (by decide) Fq := by
    rw [PrimePushforward.pull_eq_thetaPotentialCurrent hq hT hF rfl]
    exact PrimePushforward.thetaPotentialCurrent_eq_integrationCurrent Fq hFq
  have hZero : CurrentEqOn (Modification4.pull hq T hT) 0 (q ⁻¹' F.support)ᶜ := by
    rw [hPull]
    have h := PrimePushforward.currentEqOn_integrationCurrent_zero Fq
    rw [MeteredDivisorOperations.pullback_support] at h
    exact h
  have hFibre {z : Z} (hz : q z ∈ F.support) : beta z = y := by
    apply hyUnique
    have hzpi : pi (q z) = p := hsupp hz
    have hc := congrFun hcomm z
    exact hc.symm.trans hzpi
  have hPre : CurrentEqOn (Modification4.pull hq T hT) 0 (beta ⁻¹' ({y} : Set Y)ᶜ) :=
    PrimePushforward.currentEqOn_mono hZero (fun z hz hbad => hz (hFibre hbad))
  have hPush := PrimePushforward.currentEqOn_currentPushforward_zero hbeta hPre
  have hOff : CurrentEqOn (currentPushforward hbeta.1 (Modification4.pull hq T hT)) 0
      ({y} ∪ beta '' exceptionalLocus 2 beta)ᶜ :=
    PrimePushforward.currentEqOn_mono hPush (fun z hz =>
      ⟨fun h => hz (Or.inl h), fun h => hz (Or.inr h)⟩)
  obtain ⟨hA, hAi, hAnod⟩ := singleton_union_exceptionalImage_thin hbeta y
  exact SGPT.Currents.AnalyticSupport.eq_zero_of_currentEqOn_zero
    (SGPT.Siu.isClosedPositiveCurrent_currentPushforward hbeta.1
      (Modification4.isClosedPositiveCurrent_pull hq hT)) hA hAi hAnod hOff

omit [IsComplexManifold 2 X] in
/-- Actual current support manufactures the ZERO push-pull curvature class. -/
theorem pushforward_pullback_metered_fibre_class_eq_zero
    {pi : B → X} {rho : Y → X} {q : Z → B} {beta : Z → Y}
    (hq : IsAnalyticModification (n := 2) q)
    (hbeta : IsAnalyticModification (n := 2) beta)
    (hcomm : pi ∘ q = rho ∘ beta) {U : Set X} {p : X}
    (hiso : IsIsomorphismOver 2 rho U) (hp : p ∈ U)
    (F : MeteredEffectiveQDivisor 2 B)
    (hF : IsThetaPshPotential F.curvature.val F.weight)
    (hsupp : F.support ⊆ pi ⁻¹' {p}) :
    classPushforward hbeta.1 (canonicalBasis 2) (by decide)
      (classPullback hq.1 (RealBottChern.ofRepresentative F.curvature)) = 0 := by
  let T := thetaPotentialCurrent F.curvature.val F.weight hF
  have hT : SGPT.Siu.IsClosedPositiveCurrent T :=
    SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hF
  let P := Modification4.pull hq T hT
  have hP := Modification4.isClosedPositiveCurrent_pull hq hT
  have hClass : bottChernClass (canonicalBasis 2) (by decide) ⟨P, hP.1, hP.2.1⟩ =
      classPullback hq.1 (RealBottChern.ofRepresentative F.curvature) := by
    rw [PrimePushforward.bottChernClass_pull hq hT]
    exact congrArg (classPullback hq.1)
      (bottChernClass_thetaClosedCurrent F.curvature F.weight hF)
  have hZero := pushforward_pulled_metered_fibre_current_eq_zero
    hq hbeta hcomm hiso hp F hF hsupp
  rw [← hClass, ← bottChernClass_closedCurrentPushforward]
  have hClosedZero : closedCurrentPushforward hbeta.1 (canonicalBasis 2) (by decide)
      ⟨P, hP.1, hP.2.1⟩ = 0 := Subtype.ext hZero
  rw [hClosedZero]
  exact (bottChernClassLinearMap (M := Y) (canonicalBasis 2) (by decide)).map_zero

end Current

end SGPT.BDivisor.TraceOffCentreNext

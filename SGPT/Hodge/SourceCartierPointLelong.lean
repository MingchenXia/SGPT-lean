import SGPT.Hodge.SourceCartierPullNonDivisorial
import SGPT.Hodge.SourceZeroLelongNefClass
import SGPT.PSH.SourcePointBlowupLelong
import SGPT.Foundations.Analysis.Pending.BlowupExistence

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.BDivisor.PrimePushforward
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X]

include m in
omit [CompactSpace X] in
/-- The singleton centre is genuinely nowhere dense on a connected positive
dimensional original model; this consumes the existing manifold chart theorem. -/
theorem interior_singleton_eq_empty (x : X) : interior ({x} : Set X)=∅ := by
  by_contra h
  obtain ⟨y,hy⟩ := Set.nonempty_iff_ne_empty.mpr h
  have hyx : y=x := Set.mem_singleton_iff.mp (interior_subset hy)
  subst y
  have he : interior ({x} : Set X)=({x} : Set X) :=
    Set.Subset.antisymm interior_subset (Set.singleton_subset_iff.mpr hy)
  have ho : IsOpen ({x} : Set X) := he ▸ isOpen_interior
  exact DominationLogResolution.singleton_ne_univ (Nat.succ_pos m) x
    (IsClopen.eq_univ ⟨isClosed_singleton,ho⟩ (Set.singleton_nonempty x))

/-- For an actual current whose actual b-divisor is Cartier on an arbitrary
model, the genuine regular current there has zero original point Lelong number.
The point blowup, its higher original model and its exact prime are constructed
internally from the existing geometry, rather than supplied as hypotheses. -/
theorem potential_lelong_zero_of_actual_cartier_realization
    (T : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X)
    (π : (ModelSystem.blowup (m+1) X).Model)
    (α : RealBottChern (m+1) π.1.carrier)
    (hr : (currentBDivisor T).IsRealization π α)
    (θ : ClosedRealOneOneForm (m+1) π.1.carrier) (u : π.1.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u)
    (heq : π.1.regPull T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)=
      thetaPotentialCurrent θ.val u hu) :
    ∀ x,lelongNumber (n := m+1) u x=0 := by
  let : ConnectedSpace π.1.carrier := Modification.IsBlowupModel.connectedSpace π.property
  intro x
  have hx := DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := m+1) x
  have hcentre : IsClosedSubmanifold (m+1) ({x} : Set π.1.carrier) :=
    ⟨hx.1,fun y hy => ⟨0,hx.2.2 y hy⟩⟩
  obtain ⟨Z,tZ,cZ,mZ,f,hf⟩ := BlowupExistence.exists_isBlowupAlong
    ({x} : Set π.1.carrier) hcentre (interior_singleton_eq_empty (m := m) x)
  let hseq := IsBlowupSequence.step π.1.map ({x} : Set π.1.carrier) f π.property hf
  let ρ : (ModelSystem.blowup (m+1) X).Model :=
    ⟨Modification.ofIsBlowupSequence hseq,hseq⟩
  let hmod := PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hf
  let : CompactSpace Z := AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hmod
  let R := π.1.regPull T.current (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)
  let hR := π.1.isClosedPositiveCurrent_regPull (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)
  have hnd := isNonDivisorial_pull_regPull_of_actual_cartier_realization T π ρ α hr f hmod rfl
  obtain ⟨V,hV,hVdim⟩ := SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold
    (PointBlowupLelong.point_exceptional_carrier_is_prime hf)
  let E : SGPT.PSH.GeometricPrimeCarrier (m+1) Z :=
    ⟨(BlowupExceptionalDivisor.exceptionalDivisor hf).support,V,hV,by omega⟩
  have hzero := (SGPT.Siu.isNonDivisorial_iff
    (Modification4.isClosedPositiveCurrent_pull hmod hR)).mp hnd E
  rw [SGPT.Siu.currentGenericLelong_eq_primeGenericLelong _
    (pull_eq_thetaPotentialCurrent hmod hR hu heq)] at hzero
  change (⨅ z ∈ (BlowupExceptionalDivisor.exceptionalDivisor hf).support,
    SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m+1)
      (fun t => u (f t)) z)=0 at hzero
  rw [BlowupExceptionalDivisor.support_exceptionalDivisor] at hzero
  rw [PointBlowupLelong.lelongNumber_eq_iInf_pointBlowup hf hu.1,
    SquaredLogLelongSourceNormalization.iInf_lelongNumber_eq_two_mul_squaredLog
      (Nat.succ_ne_zero m),hzero,mul_zero]

end SGPT.Hodge.BDivChain.SourceNefCartierEquivalenceDraft

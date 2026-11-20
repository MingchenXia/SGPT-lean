import SGPT.Hodge.SourceRegFamily
import SGPT.Okounkov.SourceCurrentValuationWhole
import SGPT.Hodge.BDivChainCartier

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceLexmin
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending NaturalThetaPshGeometricCurrent
open SGPT.PSH.VariableComplexAtlas
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
open SGPT.Hodge.BDivChain.SourceCorrespondenceDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- Genuine actual divisorial annihilation for every REAL nonnegative
coefficient, with all native current/positivity witnesses produced internally. -/
theorem regular_weightCurrent_smul (E : MeteredEffectiveQDivisor (m + 1) X)
    {c : ℝ} (hc : 0 ≤ c) :
    let hu := TranscendentalLifting.isThetaPshPotential_weight E
    let hA := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu
    SGPT.Siu.siuRegularPart
      (c • thetaPotentialCurrent E.curvature.val E.weight hu) (hA.smul hc) = 0 := by
  let hu := TranscendentalLifting.isThetaPshPotential_weight E
  let hA := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu
  change SGPT.Siu.siuRegularPart
    (c • thetaPotentialCurrent E.curvature.val E.weight hu) (hA.smul hc) = 0
  rw [SGPT.BDivisor.PrimePushforward.siuRegularPart_smul hA hc (hA.smul hc)]
  have hD := SGPT.Hodge.BDivChain.siuDivisorialPart_weightCurrent E hu hA
  have hzero : SGPT.Siu.siuRegularPart
      (thetaPotentialCurrent E.curvature.val E.weight hu) hA = 0 := by
    unfold SGPT.Siu.siuRegularPart
    rw [hD]
    exact sub_self (thetaPotentialCurrent E.curvature.val E.weight hu)
  rw [hzero, smul_zero]

variable [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Actual original scalar I-volume is invariant under adding an actual
REAL divisor current to an arbitrary original positive current. No volume
equality, I-goodness, bigness or representation certificate is supplied. -/
theorem currentIVolumeAny_add_weight
    (ω : KahlerBackground (m + 1) X) (R : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X)
    (E : MeteredEffectiveQDivisor (m + 1) X) {c : ℝ} (hc : 0 ≤ c) :
    let hu := TranscendentalLifting.isThetaPshPotential_weight E
    let A := thetaPotentialCurrent E.curvature.val E.weight hu
    let hA := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu
    let hR := SGPT.Siu.isClosedPositiveCurrent_bookCurrent R
    let S := SGPT.Siu.toBookCurrent (R.current + c • A) (hR.add (hA.smul hc))
    currentIVolumeAny (ofBookCurrent S) = currentIVolumeAny (ofBookCurrent R) := by
  let hu := TranscendentalLifting.isThetaPshPotential_weight E
  let A := thetaPotentialCurrent E.curvature.val E.weight hu
  let hA := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hu
  let hR := SGPT.Siu.isClosedPositiveCurrent_bookCurrent R
  let S := SGPT.Siu.toBookCurrent (R.current + c • A) (hR.add (hA.smul hc))
  have hreg : SGPT.Siu.bookSiuRegularPart S = SGPT.Siu.bookSiuRegularPart R := by
    apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
    change SGPT.Siu.siuRegularPart (R.current + c • A) (hR.add (hA.smul hc)) =
      SGPT.Siu.siuRegularPart R.current hR
    rw [SGPT.BDivisor.PrimePushforward.siuRegularPart_add hR (hA.smul hc)
      (hR.add (hA.smul hc)), regular_weightCurrent_smul E hc, add_zero]
  have hwhole : regularCurrentAny (ofBookCurrent S) = regularCurrentAny (ofBookCurrent R) := by
    rw [← ofBookCurrent_toBookCurrent (regularCurrentAny (ofBookCurrent S)),
      ← ofBookCurrent_toBookCurrent (regularCurrentAny (ofBookCurrent R)),
      regularCurrentAny_pos, regularCurrentAny_pos,
      toBookCurrent_ofBookCurrent, toBookCurrent_ofBookCurrent, hreg]
  change currentIVolumeAny (ofBookCurrent S) = currentIVolumeAny (ofBookCurrent R)
  rw [← SGPT.Hodge.BDivChain.SourceReg.currentIVolumeAny_regular_eq ω (ofBookCurrent S),
    hwhole, SGPT.Hodge.BDivChain.SourceReg.currentIVolumeAny_regular_eq ω (ofBookCurrent R)]

end SGPT.Okounkov.SourceLexmin

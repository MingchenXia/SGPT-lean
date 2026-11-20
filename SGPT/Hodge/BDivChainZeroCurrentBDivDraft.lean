import SGPT.Hodge.BDivChainZeroGlobalCurrentDraft
import SGPT.Hodge.BDivChainZeroWeilDraft
import SGPT.BDivisor.BlowupModel2DT
import SGPT.PSH.GeometricQDivisor

/-!
# Dimension-uniform current pullback, Siu regular part and model classes

The carrier is the literal global distribution chart family,
not a Unit type. At dimension zero its entries are zero by alternation and the
existing `GeometricPrimeCarrier 0 X` is empty. At positive dimension each
operation is transported from the original book current and existing Siu /
modification operations. The results here establish modelwise compatibility
and comparison with the existing positive-dimensional construction; they do
not alone establish every all-dimensional source theorem.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Pullback of an actual closed positive current on an actual modification.
The zero-dimensional branch is the unique genuine distributional chart
family; the positive branch is exactly the existing potential-current pullback. -/
def pullCurrentAny (π : Modification n X) (T : ClosedPositive (n := n) (X := X)) :
    ClosedPositive (n := n) (X := π.carrier) := by
  cases n with
  | zero => exact closedPositiveZeroDim
  | succ m =>
    let U := toBookCurrent T
    let hU := SGPT.Siu.isClosedPositiveCurrent_bookCurrent U
    exact ofBookCurrent (SGPT.Siu.toBookCurrent
      (Modification4.pull π.isAnalyticModification U.current hU)
      (Modification4.isClosedPositiveCurrent_pull π.isAnalyticModification hU))

/-- The Siu regular part of an actual closed positive current. In dimension
zero it is the current itself: the actual prime carrier index is empty and the
only actual degree-two chart family is zero. In positive dimension it is the
existing Siu regular part. -/
def regularCurrentAny (T : ClosedPositive (n := n) (X := X)) :
    ClosedPositive (n := n) (X := X) := by
  cases n with
  | zero => exact T
  | succ m => exact ofBookCurrent (SGPT.Siu.bookSiuRegularPart (toBookCurrent T))

/-- The class of the actual closed positive current, valued in the existing
Bott--Chern group. In dimension zero the actual target group is zero. -/
def currentClassAny (T : ClosedPositive (n := n) (X := X)) : RealBottChern n X := by
  cases n with
  | zero => exact 0
  | succ m => exact SGPT.PSH.BookCurrent.currentClass (toBookCurrent T)

/-- `Reg π* T` as an actual current, followed by its actual model class. -/
def regPullClassAny (π : Modification n X) (T : ClosedPositive (n := n) (X := X)) :
    RealBottChern n π.carrier := currentClassAny (regularCurrentAny (pullCurrentAny π T))

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X]

/-- The dimension-zero Siu sum is indexed by the genuinely empty prime-carrier
type; no local hypersurface or invented index is supplied. -/
theorem primeCarrier_isEmpty_zero {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y] :
    IsEmpty (SGPT.PSH.GeometricPrimeCarrier 0 Y) := inferInstance

omit [CompactSpace X] in
/-- Any closed positive degree-two current has exactly the actual zero
chart coefficients in dimension zero. -/
theorem closedPositive_eq_zeroDim (T : ClosedPositive (n := 0) (X := X)) :
    T = closedPositiveZeroDim := by
  apply Subtype.ext
  exact eq_of_dim_zero T.val closedPositiveZeroDim.val

/-- The zero-dimensional pullback has the actual zero distributional chart
coefficients on the real model. -/
theorem pullCurrentAny_zero (π : Modification 0 X)
    (T : ClosedPositive (n := 0) (X := X)) :
    pullCurrentAny π T = closedPositiveZeroDim := rfl

/-- The zero-dimensional regular part is literally the original current. -/
theorem regularCurrentAny_zero (T : ClosedPositive (n := 0) (X := X)) :
    regularCurrentAny T = T := rfl

/-- On every zero-dimensional model the actual class of `Reg π* T` is zero. -/
theorem regPullClassAny_zero (π : Modification 0 X)
    (T : ClosedPositive (n := 0) (X := X)) : regPullClassAny π T = 0 := by
  rfl

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- The positive-dimensional operation really is the original current
pullback, identified through the positive-dimensional book-current equivalence. -/
theorem pullCurrentAny_current_pos (π : Modification (m + 1) X)
    (T : ClosedPositive (n := m + 1) (X := X)) :
    (toBookCurrent (pullCurrentAny π T)).current =
      Modification4.pull π.isAnalyticModification (toBookCurrent T).current
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)) := by
  change (toBookCurrent (ofBookCurrent (SGPT.Siu.toBookCurrent _ _))).current = _
  rw [toBookCurrent_ofBookCurrent]
  rfl

/-- The positive-dimensional regular operation really is the original
Siu regular part, identified through the same equivalence. -/
theorem regularCurrentAny_pos (T : ClosedPositive (n := m + 1) (X := X)) :
    toBookCurrent (regularCurrentAny T) = SGPT.Siu.bookSiuRegularPart (toBookCurrent T) := by
  change toBookCurrent (ofBookCurrent _) = _
  exact toBookCurrent_ofBookCurrent _

/-- The positive model class agrees with the original `Reg π* T` class. -/
theorem regPullClassAny_eq_existing (π : Modification (m + 1) X)
    (T : ClosedPositive (n := m + 1) (X := X)) :
    regPullClassAny π T = π.regPullClass (toBookCurrent T).current
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)) := by
  change SGPT.PSH.BookCurrent.currentClass (toBookCurrent (regularCurrentAny (pullCurrentAny π T))) = _
  rw [regularCurrentAny_pos]
  unfold SGPT.PSH.BookCurrent.currentClass SGPT.Siu.bookSiuRegularPart
    Modification.regPullClass Modification.regPull
  congr 1
  apply Subtype.ext
  change SGPT.Siu.siuRegularPart (toBookCurrent (pullCurrentAny π T)).current _ =
    SGPT.Siu.siuRegularPart (Modification4.pull π.isAnalyticModification (toBookCurrent T).current
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))) _
  exact PrimePushforward.siuRegularPart_congr (pullCurrentAny_current_pos π T) _ _

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- The actual `Reg π* T` model classes satisfy the existing pushforward law
in positive dimension and the actual zero-class law in dimension zero. -/
theorem classPushforwardAny_regPullClassAny {π π' : Modification n X} (h : π ≤ π')
    (T : ClosedPositive (n := n) (X := X)) :
    classPushforwardAny h (regPullClassAny π' T) = regPullClassAny π T := by
  cases n with
  | zero =>
    exact (realBottChern_eq_zero_of_dim_zero _).trans
      (realBottChern_eq_zero_of_dim_zero _).symm
  | succ m =>
    simpa only [classPushforwardAny_pos (Nat.succ_pos m), regPullClassAny_eq_existing] using
      (Modification.classPushforwardOfLE_regPullClass h
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)))

/-- The actual model-class family `π ↦ {Reg π* T}`, over the existing model
system. The zero branch uses actual zero chart currents and actual zero classes;
the positive branch is intended to agree with the established `currentBDivisorOn`. -/
def currentBDivisorAnyOn (S : ModelSystem n X)
    (T : ClosedPositive (n := n) (X := X)) : WeilFamilyAny S :=
  ⟨fun π => regPullClassAny π.1 T,
    fun _ _ h => classPushforwardAny_regPullClassAny h T⟩

/-- Every trace of the family is literally the class of the constructed
regular pulled-back current. -/
theorem currentBDivisorAnyOn_onModel (S : ModelSystem n X)
    (T : ClosedPositive (n := n) (X := X)) (π : S.Model) :
    (currentBDivisorAnyOn S T).val π = currentClassAny (regularCurrentAny (pullCurrentAny π.1 T)) := rfl

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- Positive-dimensional comparison is an equality of actual compatible
model-class families, not merely an equality of their root classes. -/
theorem currentBDivisorAnyOn_eq_existing (S : ModelSystem (m + 1) X)
    (T : ClosedPositive (n := m + 1) (X := X)) :
    toExisting S (Nat.succ_pos m) (currentBDivisorAnyOn S T) =
      currentBDivisorOn S (toBookCurrent T).current
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)) := by
  apply WeilBDivisorOn.ext
  intro π
  change regPullClassAny π.1 T = π.1.regPullClass (toBookCurrent T).current
    (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T))
  exact regPullClassAny_eq_existing π.1 T

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
open scoped ENNReal

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X] [ConnectedSpace X]

/-- The constructed zero-dimensional family has value one for the proposed
conditional infimum of the actual model class volumes. Its identification
with the book's volume is a separate obligation. -/
theorem volumeAny_currentBDivisorAnyOn_zero (S : ModelSystem 0 X)
    (T : ClosedPositive (n := 0) (X := X)) : volumeAny (currentBDivisorAnyOn S T) = 1 :=
  volumeAny_eq_one_of_dim_zero _

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.LocalCurrents SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X]

omit [CompactSpace X] in
/-- Every chart coordinate function on the zero vector space is constant, so
its real-valued representative is locally integrable for the actual Haar
measure. This does not assert that an arbitrary function is theta-psh. -/
theorem chartLocallyIntegrable_zero (u : X → EReal) :
    ChartLocallyIntegrable (canonicalBasis 0) u := by
  intro e
  have hconst : (fun z => (chartFunction u e z).toReal) =
      (fun _ => (chartFunction u e (0 : ComplexModel 0)).toReal) := by
    funext z
    rw [Subsingleton.elim z (0 : ComplexModel 0)]
  rw [hconst]
  exact continuousOn_const.locallyIntegrableOn e.val.open_target.measurableSet

/-- Actual chart coefficients of `θ + ddᶜ u` in dimension zero, constructed
from the repository's genuine smooth-form distribution and the genuine
regular-distribution `chartDDC`. Local integrability is explicitly carried; it
is produced without extra assumptions by `chartLocallyIntegrable_zero`. -/
def thetaCurrentZero (θ : ClosedRealOneOneForm 0 X) (u : X → EReal)
    (hu : ChartLocallyIntegrable (canonicalBasis 0) u) :
    GlobalDistributionTwo (n := 0) (X := X) := by
  refine ⟨fun e => smoothFormDistribution (canonicalBasis 0) θ.val e +
    chartDDC (canonicalBasis 0) u e (hu e), ?_⟩
  intro hn
  omega

/-- Compatibility with actual pulled-back local-potential coefficients, under
the explicit integrability needed to form the genuine regular distributions.
No equality with a fictitious zero-dimensional native `GlobalCurrent` is used. -/
theorem pullCurrentAny_zero_eq_thetaCurrent
    (π : Modification 0 X) (T : ClosedPositive (n := 0) (X := X))
    (θ : ClosedRealOneOneForm 0 X) (u : X → EReal)
    (hu : ChartLocallyIntegrable (canonicalBasis 0) (u ∘ π.map)) :
    (pullCurrentAny π T).val = thetaCurrentZero
      (ClosedRealOneOneForm.pullback π.isAnalyticModification.1 θ) (u ∘ π.map) hu :=
  eq_of_dim_zero _ _

/-- The same actual pulled-back theta-potential formula with its chart
integrability built internally from zero-dimensional geometry. -/
theorem pullCurrentAny_zero_eq_thetaCurrent_unconditional
    (π : Modification 0 X) (T : ClosedPositive (n := 0) (X := X))
    (θ : ClosedRealOneOneForm 0 X) (u : X → EReal) :
    (pullCurrentAny π T).val = thetaCurrentZero
      (ClosedRealOneOneForm.pullback π.isAnalyticModification.1 θ) (u ∘ π.map)
      (chartLocallyIntegrable_zero (u ∘ π.map)) :=
  pullCurrentAny_zero_eq_thetaCurrent π T θ u _

end SGPT.Hodge.BDivChain.NativeDraft

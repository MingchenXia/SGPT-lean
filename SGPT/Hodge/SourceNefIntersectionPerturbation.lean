import SGPT.Hodge.SourcePolarizedNefIntersection
import SGPT.Hodge.SourceRegPositiveCone

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup n X

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Evaluation at the actual root, with its literal original class type. -/
def rootClassLinear : WeilFamilyAny Sys →ₗ[ℝ] RealBottChern n X where
  toFun D := D.val ModelSystem.Model.root
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem rootClassLinear_rootCartier (α : RealBottChern n X) :
    rootClassLinear (rootCartierAny α)=α := rootCartierAny_root α

/-- Actual semipositive smooth addition supplies a genuine positive CURRENT
difference, so the original mixed reader increases in all dimensions. -/
theorem currentMixedIVolumeAny_mono_semipositive_shift (ω : KahlerBackground n X)
    (T : Fin n → ClosedPositive (n := n) (X := X))
    (σ : Fin n → ClosedRealOneOneForm n X) (hσ : ∀ i,(σ i).val.IsSemipositive) :
    currentMixedIVolumeAny ω T≤
      currentMixedIVolumeAny ω (fun i => semipositiveShiftCurrent (T i) (σ i) (hσ i)) := by
  cases n with
  | zero =>
    have he : (fun i : Fin 0 => semipositiveShiftCurrent (T i) (σ i) (hσ i))=T :=
      funext fun i => Fin.elim0 i
    rw [he]
  | succ m =>
    have hp i : SGPT.Hodge.BDivChain.SourceRegCone.CurrentLE
        (toBookCurrent (T i)) (toBookCurrent (semipositiveShiftCurrent (T i) (σ i) (hσ i))) := by
      let hz := (LocalPotentials.isThetaPshPotential_zero_iff (σ i)).mpr (hσ i)
      let Z : SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X := SGPT.Siu.toBookCurrent
        (thetaPotentialCurrent (σ i).val (fun _ => (0 : EReal)) hz)
        (SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hz)
      refine ⟨Z,?_⟩
      apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
      exact semipositiveShiftCurrent_book_add (T i) (σ i) (hσ i)
    have h := SGPT.Hodge.BDivChain.SourceRegCone.mixed_mono_current ω
      (fun i => toBookCurrent (T i))
      (fun i => toBookCurrent (semipositiveShiftCurrent (T i) (σ i) (hσ i))) hp
    simpa only [SGPT.Hodge.BDivChain.SourceRegCone.mixed,ofBookCurrent_toBookCurrent] using h

/-- The exact original perturbed big-nef intersections increase with the
scalar, by ACTUAL smooth current addition; no general b-divisor mixed-order
monotonicity is assumed. -/
theorem bigNefIntersection_kahlerPerturbation_monotone (ω κ : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i)) :
    Monotone (fun ε : Ioi (0 : ℝ) =>
      bigNefIntersection ω (fun i => kahlerPerturbedBigNef ω κ (D i) (hD i) ε.val ε.property)) := by
  intro a b hab
  let A : Fin n → BigNefFamily (n := n) (X := X) :=
    fun i => kahlerPerturbedBigNef ω κ (D i) (hD i) a.val a.property
  let B : Fin n → BigNefFamily (n := n) (X := X) :=
    fun i => kahlerPerturbedBigNef ω κ (D i) (hD i) b.val b.property
  let T : Fin n → ClosedPositive (n := n) (X := X) := fun i => (realizingCurrent ω (A i)).val
  let σ : ClosedRealOneOneForm n X := (b.val-a.val) • κ.form
  have hσ : σ.val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul κ.isSemipositive (sub_nonneg.mpr hab)
  let U : Fin n → ClosedPositive (n := n) (X := X) := fun i => semipositiveShiftCurrent (T i) σ hσ
  have hclass i : currentClassAny (U i)=(B i).val.val ModelSystem.Model.root := by
    have htc : currentClassAny (T i)=rootClassLinear (A i).val := realizingCurrent_class ω (A i)
    change currentClassAny (U i)=rootClassLinear (B i).val
    rw [semipositiveShiftCurrent_class,htc]
    change rootClassLinear (D i+a.val • rootCartierAny (RealBottChern.ofRepresentative κ.form))+
      RealBottChern.ofRepresentative ((b.val-a.val) • κ.form)=
      rootClassLinear (D i+b.val • rootCartierAny (RealBottChern.ofRepresentative κ.form))
    rw [map_add,map_smul,map_add,map_smul,rootClassLinear_rootCartier,
      RealBottChern.ofRepresentative_smul]
    module
  have hfamily i : currentBDivisorAnyOn Sys (U i)=(B i).val := by
    rw [semipositiveShiftCurrent_bdivisor,realizingCurrent_family]
    change (D i)+a.val • rootCartierAny (RealBottChern.ofRepresentative κ.form)+
      rootCartierAny (RealBottChern.ofRepresentative ((b.val-a.val) • κ.form))=
      (D i)+b.val • rootCartierAny (RealBottChern.ofRepresentative κ.form)
    rw [RealBottChern.ofRepresentative_smul,rootCartierAny_smul]
    module
  have hB := bigNefIntersection_eq_of_realization ω B U hclass hfamily
  change bigNefIntersection ω A≤bigNefIntersection ω B
  rw [hB]
  exact currentMixedIVolumeAny_mono_semipositive_shift ω T (fun _ => σ) (fun _ => hσ)

end SGPT.Hodge.BDivChain.SourceNefIntersectionDraft

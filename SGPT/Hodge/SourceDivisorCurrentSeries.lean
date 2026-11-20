import SGPT.Hodge.SourceMovingClassNetCompactness
import SGPT.Hodge.ExceptionalBDivisor
import SGPT.Siu.SiuDecomposition

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceAugmentedDraft
open Set Filter
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  SGPT.Foundations.Analysis.Pending.CanonicalComplementaryCurrentTests
  _root_.SGPT.Foundations.Analysis.LocalCurrents
open SGPT.BDivisor

variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
  [CompactSpace M] [ConnectedSpace M]
local notation "Cur" => GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))
local notation "Prime" => SGPT.PSH.GeometricPrimeCarrier (m+1) M
local notation "ClosedCur" => ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m)

/-- The ORIGINAL actual finite divisor-current sum on the original full current carrier. -/
def divisorPartial (c : Prime → ℝ) (F : Finset Prime) : Cur :=
  ∑ D ∈ F, c D • SGPT.Siu.primeDivisorCurrent D

omit [ConnectedSpace M] in
theorem divisorPartial_positive (c : Prime → ℝ) (hc : ∀ D, 0 ≤ c D) (F : Finset Prime) :
    SGPT.Siu.IsClosedPositiveCurrent (divisorPartial c F) :=
  SGPT.Siu.isClosedPositiveCurrent_finsetSum F c _ (fun D _ => hc D)
    (fun D _ => SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D)

def divisorPartialClosed (c : Prime → ℝ) (hc : ∀ D, 0 ≤ c D) (F : Finset Prime) : ClosedCur :=
  ⟨divisorPartial c F,(divisorPartial_positive c hc F).1,(divisorPartial_positive c hc F).2.1⟩

omit [ConnectedSpace M] in
theorem divisorPartial_class (c : Prime → ℝ) (hc : ∀ D, 0 ≤ c D) (F : Finset Prime) :
    bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) (divisorPartialClosed c hc F) =
      ∑ D ∈ F, c D • primeDivisorClass D :=
  SGPT.Hodge.Exceptional.bottChernClass_sum_primeDivisorCurrent F c
    (divisorPartial_positive c hc F).1 (divisorPartial_positive c hc F).2.1

omit [ConnectedSpace M] in
/-- Finite positive original sums are monotone in the actual current cone. -/
theorem divisorPartial_mono (c : Prime → ℝ) (hc : ∀ D, 0 ≤ c D)
    (F G : Finset Prime) (hFG : F ⊆ G) :
    IsFullPositive (divisorPartial c G - divisorPartial c F) := by
  classical
  have heq : divisorPartial c G - divisorPartial c F =
      ∑ D ∈ G \ F, c D • SGPT.Siu.primeDivisorCurrent D := by
    rw [divisorPartial,divisorPartial,←Finset.sum_sdiff hFG]
    abel
  rw [heq]
  exact (SGPT.Siu.isClosedPositiveCurrent_finsetSum _ _ _ (fun D _ => hc D)
    (fun D _ => SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D)).2.2

/-- The original cohomology-class sum INTERNALLY produces an ACTUAL positive
whole-current sum on EVERY original full chart test, in the SAME class.
No dominating current, countable enumeration, weak sum or limit is supplied. -/
theorem exists_positive_divisor_current_of_class_sum
    (ω : KahlerBackground (m+1) M) (c : Prime → ℝ) (hc : ∀ D, 0 ≤ c D)
    (α : RealBottChern (m+1) M) (hsum : HasDivisorClassSum c α) :
    ∃ S : Cur, ∃ hS : SGPT.Siu.IsClosedPositiveCurrent S,
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) ⟨S,hS.1,hS.2.1⟩ = α ∧
      (∀ F, IsFullPositive (S - divisorPartial c F)) ∧
      ∀ (e : ComplexChart (m+1) M)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m+1))-2)),
        HasSum (fun D => (c D • SGPT.Siu.primeDivisorCurrent D).inChart e η) (S.inChart e η) := by
  classical
  have hclass : Tendsto (fun F : Finset Prime => bottChernClass (canonicalBasis (m+1))
      (Nat.succ_pos m) (divisorPartialClosed c hc F)) atTop
      (@nhds _ (SGPT.BDivisor.euclideanTopology _) α) := by
    simp_rw [divisorPartial_class]
    exact hsum
  let U : Ultrafilter (Finset Prime) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset Prime)) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨S,hSp,hSclass,hSlim⟩ :=
    SourceAugmentedNetDraft.exists_tendsto_moving_class_originalClosedPositiveCurrent
      ω U hU α (divisorPartialClosed c hc)
      (fun F => (divisorPartial_positive c hc F).2.2) hclass
  have hS : SGPT.Siu.IsClosedPositiveCurrent S.val := ⟨S.property.1,S.property.2,hSp⟩
  have hcast : 2*m = Module.finrank ℝ (ComplexModel (m+1))-2 := by
    rw [complexModel_real_finrank]
    omega
  have hdom (F : Finset Prime) : IsFullPositive (S.val - divisorPartial c F) := by
    intro e η hη
    have hlim := (hSlim e (castTestDegree hcast η)).sub_const
      ((divisorPartial c F).inChart e (castTestDegree hcast η))
    have htail : ∀ᶠ G in (U : Filter (Finset Prime)), F ⊆ G := hU (eventually_ge_atTop F)
    exact ge_of_tendsto hlim (htail.mono
      (fun G hFG => divisorPartial_mono c hc F G hFG e η hη))
  obtain ⟨S',hS',-,hSP',hfull⟩ := SGPT.Siu.exists_tendsto_of_monotone_dominated
    (divisorPartial c) S.val (divisorPartial_positive c hc)
    (fun F G hFG => divisorPartial_mono c hc F G hFG) hdom
  have hEq : S' = S.val := by
    apply GlobalCurrent.ext
    intro e η
    exact tendsto_nhds_unique ((hfull e η).mono_left hU) (hSlim e η)
  refine ⟨S.val,hS,hSclass,hdom,?_⟩
  intro e η
  have hl := hfull e η
  rw [hEq] at hl
  change Tendsto (fun F : Finset Prime => ∑ D ∈ F,
    (c D • SGPT.Siu.primeDivisorCurrent D).inChart e η) atTop (𝓝 (S.val.inChart e η))
  convert hl using 1
  funext F
  exact (SGPT.Siu.inChart_finsetSum F (fun D => c D • SGPT.Siu.primeDivisorCurrent D) e η).symm

end SGPT.Hodge.BDivChain.SourceAugmentedDraft

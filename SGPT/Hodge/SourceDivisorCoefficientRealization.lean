import SGPT.Hodge.SourceDivisorCurrentSeries
import SGPT.BDivisor.BlowupModel2Linear
import SGPT.BDivisor.BlowupModel2Divisor

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
open SGPT.BDivisor SGPT.BDivisor.PrimePushforward SGPT.Currents.AnalyticSupport
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
  [CompactSpace M] [ConnectedSpace M]
local notation "Cur" => GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))
local notation "Prime" => SGPT.PSH.GeometricPrimeCarrier (m+1) M

omit [ConnectedSpace M] in
/-- Any actual weak sum of nonnegative prime currents dominates its actual finite sums. -/
theorem divisorPartial_dominated_of_hasSum
    (c : Prime → ℝ) (hc : ∀ D, 0 ≤ c D) (S : Cur)
    (hsum : ∀ e η, HasSum (fun D => (c D • SGPT.Siu.primeDivisorCurrent D).inChart e η)
      (S.inChart e η)) (F : Finset Prime) : IsFullPositive (S - divisorPartial c F) := by
  intro e η hη
  have hcast : 2*m = Module.finrank ℝ (ComplexModel (m+1))-2 := by
    rw [complexModel_real_finrank]
    omega
  let ξ := castTestDegree hcast η
  have hlim : Tendsto (fun G : Finset Prime => (divisorPartial c G).inChart e ξ)
      atTop (𝓝 (S.inChart e ξ)) := by
    have h := hsum e ξ
    change Tendsto (fun G : Finset Prime => ∑ D ∈ G,
      (c D • SGPT.Siu.primeDivisorCurrent D).inChart e ξ) atTop (𝓝 (S.inChart e ξ)) at h
    exact h.congr (fun G => (SGPT.Siu.inChart_finsetSum G _ e ξ).symm)
  exact ge_of_tendsto (hlim.sub_const ((divisorPartial c F).inChart e ξ))
    ((eventually_ge_atTop F).mono (fun G hFG => divisorPartial_mono c hc F G hFG e η hη))

omit [ConnectedSpace M] in
/-- The original weak sum determines exactly the original generic Lelong coefficients
and is genuinely purely divisorial. No coefficient, regularity or tail certificate is supplied. -/
theorem coefficients_and_divisorial_of_weak_sum
    (c : Prime → ℝ) (hc : ∀ D, 0 ≤ c D) (S : Cur) (hS : SGPT.Siu.IsClosedPositiveCurrent S)
    (hsum : ∀ e η, HasSum (fun D => (c D • SGPT.Siu.primeDivisorCurrent D).inChart e η)
      (S.inChart e η)) :
    (∀ D, (SGPT.Siu.currentGenericLelong S hS D).toReal = c D) ∧
    S = SGPT.Siu.siuDivisorialPart S hS := by
  classical
  have hdom := divisorPartial_dominated_of_hasSum c hc S hsum
  let ν := fun D => (SGPT.Siu.currentGenericLelong S hS D).toReal
  have hle (D : Prime) : c D ≤ ν D := by
    let A := c D • SGPT.Siu.primeDivisorCurrent D
    have hA : SGPT.Siu.IsClosedPositiveCurrent A :=
      (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).smul (hc D)
    have hsub : IsFullPositive (S-A) := by
      simpa only [divisorPartial,Finset.sum_singleton] using hdom {D}
    have hR := SGPT.Siu.IsClosedPositiveCurrent.sub_of_isFullPositive hA hS hsub
    have hAR := hA.add hR
    have heq : A+(S-A)=S := by abel
    have hνA : SGPT.Siu.currentGenericLelong A hA D = ENNReal.ofReal (c D) := by
      rw [currentGenericLelong_smul (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D)
        (hc D) hA D,currentGenericLelong_primeDivisorCurrent_self,mul_one]
    have hνS : SGPT.Siu.currentGenericLelong (A+(S-A)) hAR D =
        SGPT.Siu.currentGenericLelong S hS D := by congr 1
    have hineq : ENNReal.ofReal (c D) ≤ SGPT.Siu.currentGenericLelong S hS D := by
      rw [←hνS,currentGenericLelong_add hA hR hAR D,hνA]
      exact le_self_add
    exact (ENNReal.ofReal_le_iff_le_toReal (SGPT.Siu.currentGenericLelong_ne_top hS D)).mp hineq
  let d := fun D => ν D-c D
  have hd (D) : 0 ≤ d D := sub_nonneg.mpr (hle D)
  let V := SGPT.Siu.siuDivisorialPart S hS
  have hdiff : ∀ e η, HasSum (fun D => (d D • SGPT.Siu.primeDivisorCurrent D).inChart e η)
      ((V-S).inChart e η) := by
    intro e η
    have h := (SGPT.Siu.hasSum_siuDivisorialPart hS e η).sub (hsum e η)
    change HasSum (fun D => (d D • SGPT.Siu.primeDivisorCurrent D).inChart e η)
      (V.inChart e η-S.inChart e η)
    have hterm : (fun D => (d D • SGPT.Siu.primeDivisorCurrent D).inChart e η) =
        fun D => ((ν D • SGPT.Siu.primeDivisorCurrent D).inChart e η)-
          ((c D • SGPT.Siu.primeDivisorCurrent D).inChart e η) := by
      funext D
      change (ν D-c D)*((SGPT.Siu.primeDivisorCurrent D).inChart e η) =
        ν D*((SGPT.Siu.primeDivisorCurrent D).inChart e η)-
          c D*((SGPT.Siu.primeDivisorCurrent D).inChart e η)
      ring
    rw [hterm]
    exact h
  have hdiffDom := divisorPartial_dominated_of_hasSum d hd (V-S) hdiff
  have hV := SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hS
  have hSV := SGPT.Siu.isClosedPositiveCurrent_siuRegularPart hS
  change SGPT.Siu.IsClosedPositiveCurrent (S-V) at hSV
  have hdiffpos : IsFullPositive (V-S) := by
    have h := hdiffDom ∅
    have he : (V-S)-divisorPartial d ∅ = V-S := by
      simp only [divisorPartial,Finset.sum_empty]
      abel
    rw [he] at h
    exact h
  have hd0 (D : Prime) : d D = 0 := by
    let A := d D • SGPT.Siu.primeDivisorCurrent D
    have hA : SGPT.Siu.IsClosedPositiveCurrent A :=
      (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D).smul (hd D)
    have hneg : IsFullPositive (-A) := by
      have htail : IsFullPositive ((V-S)-A) := by
        simpa only [divisorPartial,Finset.sum_singleton] using hdiffDom {D}
      have ht := SGPT.Siu.IsClosedPositiveCurrent.sub_of_isFullPositive hA
        (SGPT.Siu.IsClosedPositiveCurrent.sub_of_isFullPositive hS hV hdiffpos) htail
      have hsumpos := (ht.add hSV).2.2
      have heq : ((V-S)-A)+(S-V) = -A := by abel
      change IsFullPositive (((V-S)-A)+(S-V)) at hsumpos
      rw [heq] at hsumpos
      exact hsumpos
    have hzero := eq_zero_of_isFullPositive_of_neg hA hneg
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · have hD := currentGenericLelong_primeDivisorCurrent_self D
      have hz : SGPT.Siu.currentGenericLelong (SGPT.Siu.primeDivisorCurrent D)
          (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D) D = 0 := by
        unfold SGPT.Siu.currentGenericLelong
        obtain ⟨x,hx⟩ := D.nonempty
        apply le_antisymm (le_trans (iInf₂_le x hx) ?_) bot_le
        have hle0 : SGPT.Siu.currentLelong (SGPT.Siu.primeDivisorCurrent D)
            (SGPT.Siu.isClosedPositiveCurrent_primeDivisorCurrent D) x = 0 := by
          simpa only [h] using SGPT.Siu.currentLelong_zero (M := M) x
        exact hle0.le
      rw [hD] at hz
      exact False.elim (one_ne_zero hz)
  have hcoeff (D : Prime) : ν D = c D := sub_eq_zero.mp (hd0 D)
  refine ⟨hcoeff,?_⟩
  apply SGPT.Siu.eq_siuDivisorialPart_of_hasSum hS
  intro e η
  have hcoeff' (D : Prime) : (SGPT.Siu.currentGenericLelong S hS D).toReal = c D := hcoeff D
  simpa only [hcoeff'] using hsum e η

/-- The ORIGINAL cohomology summability condition alone internally realizes the full
prime coefficient family by an actual purely divisorial current in the exact prescribed class. -/
theorem exists_divisorial_current_of_class_sum
    (ω : KahlerBackground (m+1) M) (c : Prime → ℝ) (hc : ∀ D, 0 ≤ c D)
    (α : RealBottChern (m+1) M) (hsum : HasDivisorClassSum c α) :
    ∃ S : Cur, ∃ hS : SGPT.Siu.IsClosedPositiveCurrent S,
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) ⟨S,hS.1,hS.2.1⟩ = α ∧
      (∀ D, (SGPT.Siu.currentGenericLelong S hS D).toReal = c D) ∧
      S = SGPT.Siu.siuDivisorialPart S hS := by
  obtain ⟨S,hS,hclass,-,hweak⟩ := exists_positive_divisor_current_of_class_sum ω c hc α hsum
  obtain ⟨hcoeff,hdiv⟩ := coefficients_and_divisorial_of_weak_sum c hc S hS hweak
  exact ⟨S,hS,hclass,hcoeff,hdiv⟩

end SGPT.Hodge.BDivChain.SourceAugmentedDraft

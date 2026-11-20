import SGPT.BDivisor.BD7EffectiveCone
import SGPT.Hodge.SourceSiuClassSeries

/-! The same-background order in the QEA proof is witnessed by effective prime sums. -/

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.BD7

open Filter Set
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open CurrentBottChernClass CanonicalCurrentFrame

variable {m : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] [CompactSpace Y]

local notation "BC" => RealBottChern (m + 1) Y
local notation "Prime" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y
local notation "Cur" => GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m))

theorem primeDivisorClass_eq_cycleClass (P : Prime) :
    primeDivisorClass P = DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P) := by
  rw [SGPT.Hodge.Exceptional.primeDivisorClass_eq, DFAlg.cycleClass]
  apply congrArg (bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m))
  apply Subtype.ext
  let E := (DivisorMetric.exists_divisorMetric (SGPT.Siu.primeEffectiveDivisor P)).choose
  let hE := (DivisorMetric.exists_divisorMetric (SGPT.Siu.primeEffectiveDivisor P)).choose_spec.2
  exact (SGPT.Siu.primeDivisorCurrent_eq_thetaPotentialCurrent P E hE).trans
    (DFAlg.divisorCurrent_val_eq (SGPT.Siu.primeEffectiveDivisor P) E hE).symm

/-- The class difference of the divisorial Siu parts belongs to the closed effective cone
when the second positive current has at most the first's generic Lelong numbers. -/
theorem siuDivisorialClass_sub_mem_effectiveClosure [ConnectedSpace Y]
    (κ : KahlerBackground (m + 1) Y) {S T : Cur}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) (hT : SGPT.Siu.IsClosedPositiveCurrent T)
    (hν : ∀ P, SGPT.Siu.currentGenericLelong T hT P ≤ SGPT.Siu.currentGenericLelong S hS P) :
    let divClass := fun (U : Cur) (hU : SGPT.Siu.IsClosedPositiveCurrent U) =>
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ⟨SGPT.Siu.siuDivisorialPart U hU,
          (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hU).1,
          (SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hU).2.1⟩
    divClass S hS - divClass T hT ∈ @closure _ (euclideanTopology BC)
      (finiteEffectiveCone fun P : Prime => DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P)) := by
  dsimp only
  classical
  letI := euclideanTopology BC
  let cS := fun P : Prime => (SGPT.Siu.currentGenericLelong S hS P).toReal
  let cT := fun P : Prime => (SGPT.Siu.currentGenericLelong T hT P).toReal
  have hc (P : Prime) : 0 ≤ cS P - cT P :=
    sub_nonneg.mpr (ENNReal.toReal_mono (SGPT.Siu.currentGenericLelong_ne_top hS P) (hν P))
  have hs := SGPT.Hodge.BDivChain.SourceAugmentedDraft.hasDivisorClassSum_siuDivisorialPart κ hS
  have ht := SGPT.Hodge.BDivChain.SourceAugmentedDraft.hasDivisorClassSum_siuDivisorialPart κ hT
  unfold HasDivisorClassSum at hs ht
  apply mem_closure_of_tendsto (b := (atTop : Filter (Finset Prime))) (f := fun F : Finset Prime =>
    ∑ P ∈ F, (cS P - cT P) • DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P))
  · apply tendsto_euclideanTopology_iff.mpr
    intro φ
    have hsφ := tendsto_euclideanTopology_iff.mp hs φ
    have htφ := tendsto_euclideanTopology_iff.mp ht φ
    simp only [SummationFilter.unconditional_filter] at hsφ htφ
    convert hsφ.sub htφ using 1
    · funext F
      rw [← map_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro P _
      rw [sub_smul, primeDivisorClass_eq_cycleClass]
    · rw [map_sub]
  · exact Eventually.of_forall fun F => ⟨F, fun P => cS P - cT P, fun P _ => hc P, rfl⟩

end SGPT.BDivisor.BD7

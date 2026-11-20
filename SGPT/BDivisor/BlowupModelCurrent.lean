import SGPT.BDivisor.Modification4SiuPullPush

/-!
# Two inputs of `def:DT`: push-forward along weak series, Lelong numbers along strict transforms

Source `def:DT` (chapter *The theory of b-divisors*): for a closed positive `(1,1)`-current `T` on
`X` and a model `π : Y → X`, `𝔻(T)_Y = {Reg π^*T}`; "this assignment is compatible with
push-forwards: if `g : Z → Y` is a modification, `g_* Reg(g^*π^*T) = Reg(π^*T)` by Siu's
decomposition and `lma:Siudec_pullpush`". Writing `S = π^*T` and
`g^*S = Reg(g^*S) + ∑_{D'} ν(g^*S, D')[D']` (Siu), the identity amounts to
`g_* ∑_{D'} ν(g^*S, D')[D'] = ∑_D ν(S, D)[D]`, which uses
1. that `g_*` commutes with weak sums of currents,
2. `ν(g^*S, D̃) = ν(S, D)` for the strict transform `D̃` of a prime divisor `D` of `Y`,
3. `g_*[D'] = [g(D')]` for non-exceptional prime divisors `D'` and `g_*[D'] = 0` for exceptional
   ones (with `D' ↦ g(D')` a bijection from non-exceptional primes of `Z` onto primes of `Y`).

This file proves 1 (`hasSum_currentPushforward_inChart`, from the finite chart decomposition of
the global pairing) and 2 (`currentGenericLelong_pull_strictTransformPrime`, from
`π_*π^*S = S` and the Lelong-number transfer of `lma:ndvpush`). Item 3 (push-forward of currents
of integration of prime divisors) is not formalized; it is the remaining input of the
compatibility in `def:DT`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology ContDiff Manifold

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormChartTests
  SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

section Pairing

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] {k : CurrentDegree n}

/-- **The global pairing is continuous along weak sums**: if `∑ᵢ Aᵢ = B` weakly (in every chart,
on every test form), then `∑ᵢ ⟨Aᵢ, γ⟩ = ⟨B, γ⟩` for every smooth form `γ` on the compact
manifold. -/
theorem hasSum_pairingLM {ι : Type*} {A : ι → GlobalCurrent n M k} {B : GlobalCurrent n M k}
    (h : ∀ (e : ComplexChart n M)
      (η : LocalCurrents.TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)),
      HasSum (fun i => (A i).inChart e η) (B.inChart e η))
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
    HasSum (fun i => pairingLM (A i) γ) (pairingLM B γ) := by
  let P : ChartPartitionOfUnity n M := ChartPartitionOfUnity.choice
  choose η hη _ using fun j => exists_testForm (P.chart j) γ (P.weight j) (P.smooth j)
    (P.compact j) (P.subset j)
  have hA : (fun i => pairingLM (A i) γ) = fun i => ∑ j, (A i).inChart (P.chart j) (η j) :=
    funext fun i => P.pairingLM_eq_sum (A i) γ η hη
  rw [hA, P.pairingLM_eq_sum B γ η hη]
  exact hasSum_sum fun j _ => h (P.chart j) (η j)

variable {Z Y : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [CompactSpace Z] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Push-forward commutes with weak sums of currents** (input 1 of the compatibility in
`def:DT`). -/
theorem hasSum_currentPushforward_inChart {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {ι : Type*}
    {A : ι → GlobalCurrent n Z k} {B : GlobalCurrent n Z k}
    (h : ∀ (e : ComplexChart n Z)
      (η : LocalCurrents.TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)),
      HasSum (fun i => (A i).inChart e η) (B.inChart e η))
    (e : ComplexChart n Y)
    (η : LocalCurrents.TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)) :
    HasSum (fun i => (currentPushforward hg (A i)).inChart e η)
      ((currentPushforward hg B).inChart e η) := by
  simp only [currentPushforward_inChart]
  exact hasSum_pairingLM h _

end Pairing

section Lelong

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

omit [CompactSpace X] in
/-- Generic Lelong numbers only depend on the current. -/
theorem currentGenericLelong_congr {T T' : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))}
    (h : T = T') (hT : SGPT.Siu.IsClosedPositiveCurrent T)
    (hT' : SGPT.Siu.IsClosedPositiveCurrent T') (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    SGPT.Siu.currentGenericLelong T hT D = SGPT.Siu.currentGenericLelong T' hT' D := by
  subst h
  rfl

/-- **Lelong numbers of a pulled-back current along strict transforms** (input 2 of the
compatibility in `def:DT`): for a modification `π : Y → X` of compact manifolds, a closed
positive `(1,1)`-current `S` on `X` and a prime divisor `D` of `X` with strict transform `D̃`,
`ν(π^*S, D̃) = ν(S, D)`. -/
theorem currentGenericLelong_pull_strictTransformPrime {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    {S : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))}
    (hS : SGPT.Siu.IsClosedPositiveCurrent S) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) :
    SGPT.Siu.currentGenericLelong (Modification4.pull hπ S hS)
        (Modification4.isClosedPositiveCurrent_pull hπ hS) (SGPT.Siu.strictTransformPrime hπ D) =
      SGPT.Siu.currentGenericLelong S hS D := by
  rw [← SGPT.Siu.currentGenericLelong_currentPushforward hπ
    (Modification4.isClosedPositiveCurrent_pull hπ hS) D]
  exact currentGenericLelong_congr (Modification4.pushforward_pull_eq hπ hS) _ _ D

end Lelong

end SGPT.BDivisor

import SGPT.Siu.PrimeDivisorCurrent
import SGPT.Foundations.Analysis.Pending.RawQuasiPshLelongSuperlevels
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Siu's theorem for closed positive currents

Source: `thm:Siusemi` of the book (stated there for psh functions; the current version is the
convention `ν(T, x) = ν(φ, x)` of `ex:Lelongcurrent`), following Xia, *Foundations of
pluripotential theory*, `thm:siu-lelong-level-sets` (last paragraph): for a closed positive
`(1,1)`-current `T` on a compact complex manifold and every `c`, the upper level set
`E_c(T) = {x : ν(T, x) ≥ c}` is an analytic subset
(`isComplexAnalyticSubset_currentLelong_superlevel`).
Consequently it is closed, and `x ↦ ν(T, x)` is upper semicontinuous for the usual topology
(`currentLelong_upperSemicontinuous`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SquaredLogLelongSourceNormalization

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- **Siu's theorem for currents.**  For a closed positive `(1,1)`-current `T` on a compact complex
manifold and every real `c`, the upper level set `E_c(T) = {x : ν(T, x) ≥ c}` of the Lelong
numbers (book normalization) is a complex analytic subset. -/
theorem isComplexAnalyticSubset_currentLelong_superlevel [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (c : ℝ) :
    IsComplexAnalyticSubset (n := m + 1) {x : M | ENNReal.ofReal c ≤ currentLelong T hT x} := by
  obtain ⟨σ, φ, hφ, heq⟩ := hT.exists_thetaPotential
  have hset : {x : M | ENNReal.ofReal c ≤ currentLelong T hT x} =
      {x : M | ENNReal.ofReal (2 * c) ≤ lelongNumber (n := m + 1) φ x} := by
    ext x
    rw [currentLelong_eq_of_eq_thetaPotentialCurrent hT heq]
    simp only [mem_ofPred_eq]
    rw [lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
    rcases le_or_gt c 0 with hc | hc
    · rw [ENNReal.ofReal_of_nonpos hc, ENNReal.ofReal_of_nonpos (by linarith)]
      simp
    · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).symm
  rw [hset]
  exact RawQuasiPshLelongSuperlevels.isComplexAnalyticSubset_superlevel
    hφ.1.quasiPlurisubharmonic (2 * c)

/-- The upper level sets of the Lelong numbers of a closed positive current are closed. -/
theorem isClosed_currentLelong_superlevel [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (a : ℝ≥0∞) : IsClosed {x : M | a ≤ currentLelong T hT x} := by
  by_cases ha : a = ⊤
  · have : {x : M | a ≤ currentLelong T hT x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, ha, top_le_iff, mem_empty_iff_false, iff_false]
      exact currentLelong_ne_top hT x
    rw [this]; exact isClosed_empty
  · have h := (isComplexAnalyticSubset_currentLelong_superlevel hT a.toReal).isClosed
    rwa [ENNReal.ofReal_toReal ha] at h

/-- **Upper semicontinuity of Lelong numbers** of a closed positive current, in the usual
topology. -/
theorem currentLelong_upperSemicontinuous [CompactSpace M]
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T) :
    UpperSemicontinuous (currentLelong T hT) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro a
  exact isClosed_currentLelong_superlevel hT a

end SGPT.Siu

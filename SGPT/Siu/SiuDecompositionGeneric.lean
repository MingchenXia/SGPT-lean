import SGPT.Siu.SiuDecomposition

/-!
# Simultaneously almost generic points along a prime divisor

Source: Xia, *Foundations of pluripotential theory*, `prop:generic-divisorial-lelong` (the
infimum `ν(T, D) = inf_{x ∈ D} ν(T, x)` is attained off a countable union of proper analytic
subsets of `D`), in the form used in `prop:big-class-minimal-multiplicity` for two currents.

* `dense_diff_currentLelong_superlevel`: for `c > ν(T, D)`, the points of `D` with
  `ν(T, x) < c` are dense in `D` (the level set `E_c(T)` is analytic by Siu's theorem, and an
  analytic subset of the irreducible set `D` with interior in `D` is `D`).
* `exists_mem_lt_currentGenericLelong_add`: for two closed positive currents `A`, `B` and `δ > 0`
  there is `x ∈ D` with `ν(A, x) < ν(A, D) + δ` and `ν(B, x) < ν(B, D) + δ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [CompactSpace M]

/-- Points of a prime divisor `D` where `ν(T, x)` is below a level `c > ν(T, D)` are dense in
`D`. -/
theorem exists_mem_inter_lt_currentLelong
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) {c : ℝ}
    (hc : currentGenericLelong T hT D < ENNReal.ofReal c) {O : Set M} (hO : IsOpen O)
    (hne : (D.val ∩ O).Nonempty) :
    ∃ y ∈ D.val ∩ O, currentLelong T hT y < ENNReal.ofReal c := by
  by_contra hcon
  push Not at hcon
  have hV : IsComplexAnalyticSubset (n := m + 1)
      (D.val ∩ {x | ENNReal.ofReal c ≤ currentLelong T hT x}) :=
    (isComplexAnalyticSubset_primeCarrier D).inter
      (isComplexAnalyticSubset_currentLelong_superlevel hT c)
  have heq := ClosureDifferenceAnalytic.eq_of_subset_of_inter_open_subset hV
    (isIrreducible_primeCarrier D) inter_subset_left hO hne (fun y hy => ⟨hy.1, hcon y hy⟩)
  have hge : ENNReal.ofReal c ≤ currentGenericLelong T hT D :=
    le_iInf₂ fun x hx => (heq.symm ▸ hx : x ∈ D.val ∩ _).2
  exact absurd hc (not_lt.mpr hge)

/-- **Simultaneously almost generic points**: for closed positive currents `A`, `B`, a prime
divisor `D` and `δ > 0`, some `x ∈ D` has `ν(A, x) < ν(A, D) + δ` and `ν(B, x) < ν(B, D) + δ`. -/
theorem exists_mem_lt_currentGenericLelong_add
    {A B : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hA : IsClosedPositiveCurrent A) (hB : IsClosedPositiveCurrent B)
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x ∈ D.val, currentLelong A hA x < currentGenericLelong A hA D + ENNReal.ofReal δ ∧
      currentLelong B hB x < currentGenericLelong B hB D + ENNReal.ofReal δ := by
  have hlevel : ∀ {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
      (hT : IsClosedPositiveCurrent T),
      currentGenericLelong T hT D + ENNReal.ofReal δ =
        ENNReal.ofReal ((currentGenericLelong T hT D).toReal + δ) ∧
      currentGenericLelong T hT D <
        ENNReal.ofReal ((currentGenericLelong T hT D).toReal + δ) := by
    intro T hT
    have hfin := currentGenericLelong_ne_top hT D
    have h1 : currentGenericLelong T hT D + ENNReal.ofReal δ =
        ENNReal.ofReal ((currentGenericLelong T hT D).toReal + δ) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hδ.le, ENNReal.ofReal_toReal hfin]
    refine ⟨h1, ?_⟩
    rw [← h1]
    exact ENNReal.lt_add_right hfin (ENNReal.ofReal_pos.mpr hδ).ne'
  obtain ⟨hA1, hA2⟩ := hlevel hA
  obtain ⟨hB1, hB2⟩ := hlevel hB
  obtain ⟨y, ⟨hyD, -⟩, hyA⟩ := exists_mem_inter_lt_currentLelong hA D hA2 isOpen_univ
    (by obtain ⟨x, hx⟩ := D.nonempty; exact ⟨x, hx, mem_univ x⟩)
  have hOA : IsOpen {x | currentLelong A hA x <
      ENNReal.ofReal ((currentGenericLelong A hA D).toReal + δ)} := by
    have := (isClosed_currentLelong_superlevel hA
      (ENNReal.ofReal ((currentGenericLelong A hA D).toReal + δ))).isOpen_compl
    simpa only [compl_ofPred, not_le] using this
  obtain ⟨x, ⟨hxD, hxA⟩, hxB⟩ := exists_mem_inter_lt_currentLelong hB D hB2 hOA ⟨y, hyD, hyA⟩
  refine ⟨x, hxD, ?_, ?_⟩
  · rw [hA1]; exact hxA
  · rw [hB1]; exact hxB

end SGPT.Siu

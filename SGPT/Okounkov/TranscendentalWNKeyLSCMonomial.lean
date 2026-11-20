import SGPT.Okounkov.TranscendentalWNKeyLSCGlobal

/-!
# Coordinate algebra of the two monomial charts of the deformation (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-lsc`, node `tok-wn-lsc:monomial-algebra`; source WN21 §5 (the charts
`(w, z', τ)`, `z₁ = wτ`).

The centre `Z × {0}` of the deformation `μ : 𝒳 → X × ℙ¹` has codimension two; in flattening
coordinates `(z', z₁, τ) ∈ ℂ^{m} × ℂ × ℂ` of `X × ℙ¹` (`z₁` the equation of `Z`, `τ` the affine
coordinate of `ℙ¹` at `0`) the blow-up is covered by the two monomial charts
(`BlowupMonomialCharts.monomial m j`, `j ∈ {m, m + 1}`):

* `j = m + 1` (`idxT`): `(z', z₁, τ) = (w', w_m w_{m+1}, w_{m+1})`, `ℰ = {w_{m+1} = 0}`;
* `j = m` (`idxZ`): `(z', z₁, τ) = (w', w_m, w_m w_{m+1})`, `ℰ = {w_m = 0}`.

This file records the algebra: the swap `swapNormal` of the two normal coordinates intertwines
the two charts (`monomial_idxZ_swapNormal`), the chart `idxT` in the splitting
`ℂ^{m+2} = ℂ^{m+1} × ℂ` (`monomial_idxT_split`), injectivity off `ℰ`
(`eq_of_monomial_eq`), and the centre in monomial coordinates (`monomial_mem_plane_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Okounkov.TranscendentalWN.LSC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {m : ℕ}

/-- The index `m` of the coordinate `z₁` (the equation of `Z`). -/
abbrev idxZ (m : ℕ) : Fin (m + 1 + 1) := Fin.castSucc (Fin.last m)

/-- The index `m + 1` of the coordinate `τ` of `ℙ¹`. -/
abbrev idxT (m : ℕ) : Fin (m + 1 + 1) := Fin.last (m + 1)

theorem idxZ_ne_idxT : idxZ m ≠ idxT m := Fin.castSucc_lt_last _ |>.ne

theorem le_iff_mem_normal {i : Fin (m + 1 + 1)} : m ≤ i.1 ↔ i = idxZ m ∨ i = idxT m := by
  constructor
  · intro h
    rcases Nat.lt_or_ge i.1 (m + 1) with h1 | h1
    · left; ext; simp; omega
    · right; ext; simp; omega
  · rintro (rfl | rfl) <;> simp

/-- The swap of the two normal coordinates `z₁ ↔ τ`. -/
def swapNormal (m : ℕ) : ComplexModel (m + 1 + 1) ≃L[ℂ] ComplexModel (m + 1 + 1) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap (idxZ m) (idxT m))).toContinuousLinearEquiv

@[simp] theorem swapNormal_apply (w : ComplexModel (m + 1 + 1)) (i : Fin (m + 1 + 1)) :
    swapNormal m w i = w (Equiv.swap (idxZ m) (idxT m) i) := by
  simp [swapNormal, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Equiv.symm_swap]

@[simp] theorem swapNormal_swapNormal (w : ComplexModel (m + 1 + 1)) :
    swapNormal m (swapNormal m w) = w := by
  ext i
  simp

theorem swapNormal_symm_apply (w : ComplexModel (m + 1 + 1)) :
    (swapNormal m).symm w = swapNormal m w := by
  apply (swapNormal m).injective
  simp

/-- The splitting `ℂ^{m+2} = ℂ^{m+1} × ℂ` of the product charts. -/
abbrev splitL (m : ℕ) : (ComplexModel (m + 1) × ComplexModel 1) ≃L[ℂ] ComplexModel (m + 1 + 1) :=
  prodModelEquiv (m + 1) 1

@[simp] theorem splitL_last (y : ComplexModel (m + 1)) (s : ComplexModel 1) :
    splitL m (y, s) (idxT m) = s 0 := by
  simp [prodModelEquiv]

@[simp] theorem splitL_castSucc (y : ComplexModel (m + 1)) (s : ComplexModel 1) (i : Fin (m + 1)) :
    splitL m (y, s) (Fin.castSucc i) = y i := by
  simp [prodModelEquiv]

@[simp] theorem splitL_symm_fst (w : ComplexModel (m + 1 + 1)) (i : Fin (m + 1)) :
    ((splitL m).symm w).1 i = w (Fin.castSucc i) := by
  simp [prodModelEquiv]
  rfl

@[simp] theorem splitL_symm_snd (w : ComplexModel (m + 1 + 1)) :
    ((splitL m).symm w).2 0 = w (idxT m) := by
  simp [prodModelEquiv]
  rfl

theorem splitL_symm_snd_eq (w : ComplexModel (m + 1 + 1)) :
    ((splitL m).symm w).2 = EuclideanSpace.single 0 (w (idxT m)) := by
  ext i
  fin_cases i
  simp

/-- `ℂ^{m+1}`: scaling the last coordinate. -/
def scaleLast (y : ComplexModel (m + 1)) (c : ℂ) : ComplexModel (m + 1) :=
  WithLp.toLp 2 fun i => if i = Fin.last m then y i * c else y i

theorem monomial_idxT_split (y : ComplexModel (m + 1)) (s : ComplexModel 1) :
    monomial m (idxT m) (splitL m (y, s)) = splitL m (scaleLast y (s 0), s) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [monomial_apply]
  | cast i =>
    simp only [monomial_apply, splitL_castSucc, splitL_last, scaleLast, Fin.val_castSucc]
    by_cases hi : i = Fin.last m
    · subst hi
      simp
    · have hi' : ¬ m ≤ i.1 := by
        intro h
        exact hi (Fin.ext (by simp; omega))
      simp [hi, hi']

theorem monomial_idxZ_swapNormal (v : ComplexModel (m + 1 + 1)) :
    monomial m (idxZ m) (swapNormal m v) = swapNormal m (monomial m (idxT m) v) := by
  ext i
  simp only [monomial_apply, swapNormal_apply]
  by_cases hZ : i = idxZ m
  · subst hZ
    simp [Equiv.swap_apply_left]
  · by_cases hT : i = idxT m
    · subst hT
      simp [Equiv.swap_apply_right, idxZ_ne_idxT.symm]
    · have hi : ¬ m ≤ i.1 := fun h => (le_iff_mem_normal.mp h).elim hZ hT
      rw [Equiv.swap_apply_of_ne_of_ne hZ hT]
      simp [hi]

/-- **Injectivity of a monomial chart off the exceptional divisor.** -/
theorem eq_of_monomial_eq {n k : ℕ} {j : Fin n} {v w : ComplexModel n}
    (h : monomial k j v = monomial k j w) (hw : w j ≠ 0) : v = w := by
  have hj : v j = w j := by
    have := congrArg (fun u : ComplexModel n => u j) h
    simpa [monomial_apply] using this
  ext i
  have hi := congrArg (fun u : ComplexModel n => u i) h
  simp only [monomial_apply] at hi
  split_ifs at hi with hc
  · rw [hj] at hi
    exact mul_right_cancel₀ hw hi
  · exact hi

/-- **The centre in monomial coordinates**: `σ_j(w) ∈ ℂ^k × 0` iff `w_j = 0` (`j ≥ k`). -/
theorem monomial_mem_plane_iff {n k : ℕ} {j : Fin n} (hj : k ≤ j.1) (w : ComplexModel n) :
    monomial k j w ∈ complexCoordinatePlane n k ↔ w j = 0 := by
  constructor
  · intro h
    have := h j hj
    simpa [monomial_apply] using this
  · intro h i hi
    simp only [monomial_apply]
    split_ifs with hc
    · rw [h, mul_zero]
    · have : i = j := by
        by_contra hne
        exact hc ⟨hi, hne⟩
      rw [this, h]

end SGPT.Okounkov.TranscendentalWN.LSC

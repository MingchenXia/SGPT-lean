import SGPT.PSH.BookDeepDomination

/-! Locally bounded Bedford–Taylor products are monotone under the addition
of a locally bounded plurisubharmonic function in each slot. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.Envelopes.DinewDirichlet

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.PSH.BookDeepDomination

variable {n : ℕ}

/-- Add a locally bounded psh function in each slot. The empty-tuple case is
retained and the two measures are equal there. -/
theorem isBTLimit_le_add_each_slot {Ω : Opens (ComplexModel n)}
    {a b : Fin n → ComplexModel n → ℝ}
    (ha : ∀ i, IsLocallyBoundedPshOn Ω (a i))
    (hb : ∀ i, IsLocallyBoundedPshOn Ω (b i))
    {μ ν : Measure (ComplexModel n)} (hμ : IsBTLimit Ω a μ)
    (hν : IsBTLimit Ω (fun i z => a i z + b i z) ν) : μ ≤ ν := by
  classical
  set T : ℕ → Fin n → ComplexModel n → ℝ :=
    fun k i => if i.val < k then (fun z => a i z + b i z) else a i with hT
  have hTb : ∀ k i, IsLocallyBoundedPshOn Ω (T k i) := by
    intro k i
    simp only [hT]
    split_ifs
    · exact isLocallyBoundedPshOn_add (ha i) (hb i)
    · exact ha i
  have key : ∀ k, k ≤ n → ∀ μk, IsBTLimit Ω (T k) μk → μ ≤ μk := by
    intro k
    induction k with
    | zero =>
      intro _ μk hμk
      have hzero : T 0 = a := by
        funext i
        simp [hT]
      rw [hzero] at hμk
      exact (hμ.unique hμk).le
    | succ k ih =>
      intro hk μk hμk
      let i₀ : Fin n := ⟨k, hk⟩
      have hT1 : T (k + 1) = Function.update (T k) i₀
          (fun z => a i₀ z + b i₀ z) := by
        funext i
        by_cases hi : i = i₀
        · rw [hi, Function.update_self]
          simp [hT, i₀]
        · rw [Function.update_of_ne hi]
          have hik : i.val ≠ k := fun h => hi (Fin.ext h)
          simp only [hT]
          by_cases hlt : i.val < k
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have hlt' : ¬ i.val < k + 1 := by omega
            simp [hlt, hlt']
      have hT0 : Function.update (T k) i₀ (a i₀) = T k := by
        funext i
        by_cases hi : i = i₀
        · rw [hi, Function.update_self]
          simp [hT, i₀]
        · rw [Function.update_of_ne hi]
      obtain ⟨μb, hμb⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
        (u := Function.update (T k) i₀ (b i₀)) (fun i => by
          by_cases hi : i = i₀
          · subst hi
            simpa using hb i₀
          · rw [Function.update_of_ne hi]
            exact hTb k i)
      obtain ⟨μa, hμa⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (u := T k) (hTb k)
      rw [hT1] at hμk
      have hsum := hμk.add_slot i₀ (by rw [hT0]; exact hμa) hμb
      rw [hsum]
      exact Measure.le_add_right (ih (Nat.le_of_succ_le hk) μa hμa)
  have hn : T n = fun i z => a i z + b i z := by
    funext i
    simp [hT, i.isLt]
  exact key n le_rfl ν (by rw [hn]; exact hν)


/-- A finite constant is locally bounded psh in the actual open domain. -/
theorem isLocallyBoundedPshOn_const (Ω : Opens (ComplexModel n)) (c : ℝ) :
    IsLocallyBoundedPshOn Ω (fun _ => c) := by
  refine ⟨fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) x, ?_⟩
  intro z hz
  exact ⟨Ω, hz, le_rfl, |c|, fun _ _ => le_rfl⟩

/-- In positive dimension the diagonal product of a sum contains the two
actual diagonal products as distinct positive summands. -/
theorem isBTLimit_diagonal_superadditive (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    {μu μv μsum : Measure (ComplexModel n)}
    (hμu : IsBTLimit Ω (fun _ => u) μu)
    (hμv : IsBTLimit Ω (fun _ => v) μv)
    (hμsum : IsBTLimit Ω (fun _ z => u z + v z) μsum) :
    μu + μv ≤ μsum := by
  classical
  let j : Fin n := ⟨0, hn⟩
  let s : ComplexModel n → ℝ := fun z => u z + v z
  have hs : IsLocallyBoundedPshOn Ω s := isLocallyBoundedPshOn_add hu hv
  let U : Fin n → ComplexModel n → ℝ := Function.update (fun _ => s) j u
  let V : Fin n → ComplexModel n → ℝ := Function.update (fun _ => s) j v
  have hU : ∀ i, IsLocallyBoundedPshOn Ω (U i) := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa [U] using hu
    · simpa [U, Function.update_of_ne hi] using hs
  have hV : ∀ i, IsLocallyBoundedPshOn Ω (V i) := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa [V] using hv
    · simpa [V, Function.update_of_ne hi] using hs
  obtain ⟨μU, hμU⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn hU
  obtain ⟨μV, hμV⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn hV
  have hsum : μsum = μU + μV := by
    have heq : Function.update (fun _ : Fin n => s) j (fun z => u z + v z) =
        (fun _ : Fin n => s) := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [s]
      · simp [Function.update_of_ne hi]
    have hh : IsBTLimit Ω
        (Function.update (fun _ : Fin n => s) j (fun z => u z + v z)) μsum := by
      rw [heq]
      exact hμsum
    exact hh.add_slot j hμU hμV
  let bU : Fin n → ComplexModel n → ℝ := fun i => if i = j then fun _ => 0 else v
  let bV : Fin n → ComplexModel n → ℝ := fun i => if i = j then fun _ => 0 else u
  have hbU : ∀ i, IsLocallyBoundedPshOn Ω (bU i) := by
    intro i
    by_cases hi : i = j
    · simpa [bU, hi] using isLocallyBoundedPshOn_const Ω 0
    · simpa [bU, hi] using hv
  have hbV : ∀ i, IsLocallyBoundedPshOn Ω (bV i) := by
    intro i
    by_cases hi : i = j
    · simpa [bV, hi] using isLocallyBoundedPshOn_const Ω 0
    · simpa [bV, hi] using hu
  have hUeq : (fun i z => u z + bU i z) = U := by
    funext i z
    by_cases hi : i = j
    · subst i
      simp [U, bU]
    · simp [U, bU, s, hi]
  have hVeq : (fun i z => v z + bV i z) = V := by
    funext i z
    by_cases hi : i = j
    · subst i
      simp [V, bV]
    · simp [V, bV, s, hi, add_comm]
  have huU : μu ≤ μU := isBTLimit_le_add_each_slot (fun _ => hu) hbU hμu (by
    rw [hUeq]
    exact hμU)
  have hvV : μv ≤ μV := isBTLimit_le_add_each_slot (fun _ => hv) hbV hμv (by
    rw [hVeq]
    exact hμV)
  rw [hsum]
  exact add_le_add huU hvV

end SGPT.Envelopes.DinewDirichlet

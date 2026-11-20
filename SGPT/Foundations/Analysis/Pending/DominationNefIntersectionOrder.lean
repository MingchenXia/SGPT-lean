import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers

set_option autoImplicit false

/-! # Actual mixed intersections ordered by genuine pseudoeffective differences -/

open Set

namespace SGPT.Foundations.Analysis.Pending.DominationNefIntersectionOrder

open FirstPass FirstPass.PositiveClasses NefMixedMass DominationIntersectionNumbers

noncomputable section

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M]
  [CompactSpace M]

/-- Actual one-slot multilinearity and genuine pseudoeffective-versus-nef positivity give numerical order without nefness of the changed slot. -/
theorem slotIntegral_update_le_of_pseudoeffective_difference (w : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M) (j : Fin N)
    (A B : ClosedRealOneOneForm N M)
    (hP : PseudoeffectiveViaPotentials (B - A))
    (hnef : ∀ i, i ≠ j → NefWithRespectTo w (θ i)) :
    slotIntegral w (Function.update θ j A) ≤ slotIntegral w (Function.update θ j B) := by
  classical
  have hnonneg : 0 ≤ slotIntegral w (Function.update θ j (B - A)) := by
    apply slotIntegral_nonneg_of_pseudoeffective w j
    · simpa using hP
    · intro i hi
      simpa only [Function.update_of_ne hi] using hnef i hi
  have heq := slotIntegral_update_add_smul w θ j A (B - A) 1
  have hab : A + (1 : ℝ) • (B - A) = B := by module
  rw [hab, one_mul] at heq
  linarith

/-- Replacing finitely many genuine nef slots by nef slots with pseudoeffective differences increases the actual intersection, including the empty tuple. Equal slots require no extra potential witness. -/
theorem slotIntegral_le_of_nef_pseudoeffective_differences (w : KahlerBackground N M)
    (A B : Fin N → ClosedRealOneOneForm N M)
    (hA : ∀ i, NefWithRespectTo w (A i)) (hB : ∀ i, NefWithRespectTo w (B i))
    (hP : ∀ i, A i ≠ B i → PseudoeffectiveViaPotentials (B i - A i)) :
    slotIntegral w A ≤ slotIntegral w B := by
  classical
  let mixed (s : Finset (Fin N)) : Fin N → ClosedRealOneOneForm N M :=
    fun i => if i ∈ s then B i else A i
  have hstep : ∀ s : Finset (Fin N), slotIntegral w A ≤ slotIntegral w (mixed s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [mixed]
    | @insert j s hjs ih =>
      have hnext : slotIntegral w (mixed s) ≤ slotIntegral w (mixed (insert j s)) := by
        by_cases hab : A j = B j
        · apply le_of_eq
          congr 1
          funext i
          by_cases hij : i = j
          · subst i
            simp only [mixed, Finset.mem_insert_self, if_pos, hjs, if_false, hab]
          · simp only [mixed, Finset.mem_insert, hij, false_or]
        · have hnef : ∀ i, i ≠ j → NefWithRespectTo w (mixed s i) := by
            intro i _
            by_cases his : i ∈ s
            · simpa only [mixed, if_pos his] using hB i
            · simpa only [mixed, if_neg his] using hA i
          have h := slotIntegral_update_le_of_pseudoeffective_difference w (mixed s) j
            (A j) (B j) (hP j hab) hnef
          have ha : Function.update (mixed s) j (A j) = mixed s := by
            funext i
            by_cases hij : i = j
            · subst i
              simp [mixed, hjs]
            · simp only [Function.update_of_ne hij]
          have hb : Function.update (mixed s) j (B j) = mixed (insert j s) := by
            funext i
            by_cases hij : i = j
            · subst i
              simp [mixed]
            · simp only [Function.update_of_ne hij, mixed, Finset.mem_insert, hij, false_or]
          rw [ha, hb] at h
          exact h
      exact ih.trans hnext
  simpa only [mixed, Finset.mem_univ, if_true] using hstep Finset.univ

end

end SGPT.Foundations.Analysis.Pending.DominationNefIntersectionOrder

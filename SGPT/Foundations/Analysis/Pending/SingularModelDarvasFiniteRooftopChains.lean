import SGPT.Foundations.Analysis.Pending.SingularModelDarvasContraction

set_option autoImplicit false

/-!
# Actual finite rooftop chains and their Darvas distance bounds

An independent finite precursor to the tail-rooftop construction whose
conclusion continues in Xia SGPT PDF0169, Lemma 4.3.5. Actual finite-energy
rooftop closure and the actual contraction/triangle laws (PDF0160--0161)
produce the finite chains and their cumulative distance and energy bounds.
Infinite limiting finite-energy closure and metric completeness remain separate.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteRooftopChains

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}
  {u : ℕ → M → EReal}

/-- The actual iterated rooftop of the finite tail from `i` through `i + k`. -/
def finiteTailRooftop (θ : ClosedRealOneOneForm n M) (u : ℕ → M → EReal)
    (i : ℕ) : ℕ → M → EReal
  | 0 => u i
  | k + 1 => rooftop θ (finiteTailRooftop θ u i k) (u (i + k + 1))

/-- Actual finite-energy membership of each finite tail rooftop is produced by induction. -/
theorem relativeFiniteEnergyPreceq_finiteTailRooftop (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (i k : ℕ) :
    RelativeFiniteEnergyPreceq θ φ (finiteTailRooftop θ u i k) hφ := by
  induction k with
  | zero => exact hu i
  | succ k ih => exact relativeFiniteEnergyPreceq_rooftop omega ih (hu (i + k + 1))

/-- A finite tail rooftop lies below its last actual obstacle. -/
theorem finiteTailRooftop_le_last (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (i k : ℕ) :
    finiteTailRooftop θ u i k ≤ u (i + k) := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
    exact rooftop_le_right
      (relativeFiniteEnergyPreceq_finiteTailRooftop omega hu i k).1.plurisubharmonic
      (hu (i + k + 1)).1.plurisubharmonic

/-- The actual finite tail rooftops decrease with the length of the tail. -/
theorem finiteTailRooftop_antitone (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (i : ℕ) :
    Antitone (finiteTailRooftop θ u i) := by
  apply antitone_nat_of_succ_le
  intro k
  exact rooftop_le_left
    (relativeFiniteEnergyPreceq_finiteTailRooftop omega hu i k).1.plurisubharmonic
    (hu (i + k + 1)).1.plurisubharmonic

/-- Actual rooftop contraction controls each new finite tail step by the original step. -/
theorem relativeD1_finiteTailRooftop_step_le (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (i k : ℕ) :
    relativeD1 θ φ hφ (finiteTailRooftop θ u i k)
      (finiteTailRooftop θ u i (k + 1)) ≤
        relativeD1 θ φ hφ (u (i + k)) (u (i + k + 1)) := by
  have hr := relativeFiniteEnergyPreceq_finiteTailRooftop omega hu i k
  have hc := SingularModelDarvasContraction.relativeD1_rooftop_le omega
    (hu (i + k)) (hu (i + k + 1)) hr
  rw [rooftop_comm θ (u (i + k)),
    rooftop_eq_left_of_le hr.1.plurisubharmonic (finiteTailRooftop_le_last omega hu i k),
    rooftop_comm θ (u (i + k + 1))] at hc
  exact hc

/-- Actual finite tail distance is bounded by the finite sum of original consecutive distances. -/
theorem relativeD1_finiteTailRooftop_le_sum (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (i k : ℕ) :
    relativeD1 θ φ hφ (u i) (finiteTailRooftop θ u i k) ≤
      ∑ a ∈ Finset.range k, relativeD1 θ φ hφ (u (i + a)) (u (i + a + 1)) := by
  induction k with
  | zero =>
    simpa only [finiteTailRooftop, Finset.range_zero, Finset.sum_empty] using
      (relativeD1_self (θ := θ) (φ := φ) (hφ := hφ) (hu i).1.plurisubharmonic).le
  | succ k ih =>
    calc
      relativeD1 θ φ hφ (u i) (finiteTailRooftop θ u i (k + 1)) ≤
          relativeD1 θ φ hφ (u i) (finiteTailRooftop θ u i k) +
            relativeD1 θ φ hφ (finiteTailRooftop θ u i k)
              (finiteTailRooftop θ u i (k + 1)) :=
        SingularModelDarvasContraction.relativeD1_triangle omega (hu i)
          (relativeFiniteEnergyPreceq_finiteTailRooftop omega hu i (k + 1))
          (relativeFiniteEnergyPreceq_finiteTailRooftop omega hu i k)
      _ ≤ (∑ a ∈ Finset.range k, relativeD1 θ φ hφ (u (i + a)) (u (i + a + 1))) +
          relativeD1 θ φ hφ (u (i + k)) (u (i + k + 1)) :=
        add_le_add ih (relativeD1_finiteTailRooftop_step_le omega hu i k)
      _ = _ := (Finset.sum_range_succ _ _).symm

/-- The same actual finite distance bound gives a lower bound on the actual finite energy. -/
theorem energy_finiteTailRooftop_ge_sub_sum (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (i k : ℕ) :
    (energy θ φ hφ (u i)).toReal -
        (∑ a ∈ Finset.range k, relativeD1 θ φ hφ (u (i + a)) (u (i + a + 1))) ≤
      (energy θ φ hφ (finiteTailRooftop θ u i k)).toReal := by
  have hd := relativeD1_finiteTailRooftop_le_sum omega hu i k
  have hr := relativeFiniteEnergyPreceq_finiteTailRooftop omega hu i k
  have hle : finiteTailRooftop θ u i k ≤ u i :=
    finiteTailRooftop_antitone omega hu i (Nat.zero_le k)
  rw [relativeD1_comm, relativeD1_eq_sub_of_le hr.1.plurisubharmonic hle] at hd
  linarith

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteRooftopChains

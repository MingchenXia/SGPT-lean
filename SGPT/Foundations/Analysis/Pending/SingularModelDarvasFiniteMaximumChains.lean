import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMaximumBound

set_option autoImplicit false

/-!
# Actual finite maximum chains and their weighted Darvas bound

Xia SGPT PDF0168, the finite weighted estimate in Lemma 4.3.5.
Actual binary maximum closure produces every finite-energy membership.
The actual exact-source maximum estimate and metric triangle inequality
produce the dimension-weighted finite sum. Infinite tail suprema and
the full monotone sandwich conclusion remain separate.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteMaximumChains

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}
  {u : ℕ → M → EReal}

/-- The actual finite tail maximum, associated from the first obstacle to the remaining tail. -/
def finiteTailMaximum (u : ℕ → M → EReal) (i : ℕ) : ℕ → M → EReal
  | 0 => u i
  | k + 1 => fun x => max (u i x) (finiteTailMaximum u (i + 1) k x)

omit [ConnectedSpace M] in
/-- Actual finite-energy membership of the finite maximum is produced by induction. -/
theorem relativeFiniteEnergyPreceq_finiteTailMaximum (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (i k : ℕ) :
    RelativeFiniteEnergyPreceq θ φ (finiteTailMaximum u i k) hφ := by
  induction k generalizing i with
  | zero => exact hu i
  | succ k ih =>
    exact SingularModelFiniteEnergyGapMax.relativeFiniteEnergyPreceq_max omega (hu i) (ih (i + 1))

omit [BorelSpace M] [ConnectedSpace M] [CompactSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [TopologicalSpace M] in
/-- Every actual finite tail maximum dominates its first obstacle. -/
theorem le_finiteTailMaximum (i k : ℕ) : u i ≤ finiteTailMaximum u i k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact fun _ => le_max_left _ _

omit [BorelSpace M] [ConnectedSpace M] [CompactSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [TopologicalSpace M] in
/-- The actual finite tail maximum increases with the length of the tail. -/
theorem finiteTailMaximum_monotone (i : ℕ) : Monotone (finiteTailMaximum u i) := by
  have hstep (k : ℕ) : ∀ i, finiteTailMaximum u i k ≤ finiteTailMaximum u i (k + 1) := by
    induction k with
    | zero => exact fun _ _ => le_max_left _ _
    | succ k ih => exact fun i x => max_le_max le_rfl (ih (i + 1) x)
  exact monotone_nat_of_le_succ fun k => hstep k i

/-- The exact source finite weighted maximum estimate, with an empty sum at length zero. -/
theorem relativeD1_finiteTailMaximum_le_weighted_sum (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (i k : ℕ) :
    relativeD1 θ φ hφ (u i) (finiteTailMaximum u i k) ≤
      ∑ r ∈ Finset.range k,
        (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) ^ (r + 1) *
          relativeD1 θ φ hφ (u (i + r)) (u (i + r + 1)) := by
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  change relativeD1 θ φ hφ (u i) (finiteTailMaximum u i k) ≤
    ∑ r ∈ Finset.range k, C ^ (r + 1) * relativeD1 θ φ hφ (u (i + r)) (u (i + r + 1))
  induction k generalizing i with
  | zero =>
    simpa only [finiteTailMaximum, Finset.range_zero, Finset.sum_empty] using
      (relativeD1_self (θ := θ) (φ := φ) (hφ := hφ) (hu i).1.plurisubharmonic).le
  | succ k ih =>
    have hm := relativeFiniteEnergyPreceq_finiteTailMaximum omega hu (i + 1) k
    have hmax := SingularModelDarvasMaximumBound.relativeD1_max_le_mul omega (hu i) hm
    rw [relativeD1_comm θ φ hφ (fun x => max (u i x) (finiteTailMaximum u (i + 1) k x)) (u i)] at hmax
    have htri := SingularModelDarvasContraction.relativeD1_triangle omega (hu i) hm (hu (i + 1))
    have hsum : relativeD1 θ φ hφ (u (i + 1)) (finiteTailMaximum u (i + 1) k) ≤
        ∑ r ∈ Finset.range k, C ^ (r + 1) *
          relativeD1 θ φ hφ (u (i + 1 + r)) (u (i + 1 + r + 1)) := ih (i + 1)
    have htotal : relativeD1 θ φ hφ (u i) (finiteTailMaximum u (i + 1) k) ≤
        relativeD1 θ φ hφ (u i) (u (i + 1)) +
          ∑ r ∈ Finset.range k, C ^ (r + 1) *
            relativeD1 θ φ hφ (u (i + 1 + r)) (u (i + 1 + r + 1)) :=
      htri.trans (add_le_add le_rfl hsum)
    calc
      _ ≤ C * relativeD1 θ φ hφ (u i) (finiteTailMaximum u (i + 1) k) := hmax
      _ ≤ C * (relativeD1 θ φ hφ (u i) (u (i + 1)) +
          ∑ r ∈ Finset.range k, C ^ (r + 1) *
            relativeD1 θ φ hφ (u (i + 1 + r)) (u (i + 1 + r + 1))) :=
        mul_le_mul_of_nonneg_left htotal hC
      _ = _ := by
        rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
        simp only [Nat.add_zero, zero_add, pow_one]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        rw [show i + 1 + r = i + (r + 1) by omega]
        rw [pow_succ]
        ring

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteMaximumChains

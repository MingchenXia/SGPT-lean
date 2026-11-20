import SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.DiagonalMass

set_option autoImplicit false

/-! # Actual positive convex perturbations and their diagonal masses -/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularPositiveConvexMixedMass

open FirstPass FirstPass.PositiveClasses RelativeEnergy DiagonalMass GlobalNonPluripolar
  ThetaPshConvexCombination EndpointMixedMassConvexCombination MixedMass
  GlobalDiagonalConvexScaling GlobalDiagonalScaling

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
private theorem endpointMixedMass_last {θ : ClosedRealOneOneForm n M}
    {p u : M → EReal} (hp : IsThetaPshPotential θ.val p)
    (hu : IsThetaPshPotential θ.val u) :
    endpointMixedMass θ p u hp hu (Fin.last n) = diagonalPotentialMass θ u hu := by
  have ht : endpointMixedPotential (Fin.last n) u p = (fun _ : Fin n => u) := by
    funext i
    simp only [endpointMixedPotential, Fin.val_last, if_pos i.isLt]
  exact congrArg (fun μ : Measure M => μ univ)
    (UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple ht
      (endpointMixedPotential_thetaPlurisubharmonic θ (Fin.last n) u p hu hp)
      (fun _ : Fin n => hu.1))

/-- Actual convex measure domination internally produces positive mass from
the genuine right reference; the left original mass may vanish. -/
theorem hasPositivePotentialMass_convexComb_of_right
    {θ : ClosedRealOneOneForm n M} {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (hpp : HasPositivePotentialMass θ p hp) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasPositivePotentialMass θ (convexComb a u p)
      (isThetaPshPotential_convexComb_closed hu hp ha0.le ha1.le) := by
  have hr0 : 0 < 1 - a := sub_pos.mpr ha1
  have hr1 : 1 - a < 1 := by linarith
  have hswap : convexComb (1 - a) p u = convexComb a u p := by
    funext x
    simp only [convexComb, show 1 - (1 - a) = a by ring]
    exact add_comm _ _
  have hle := globalMixedMeasure_diagonal_convexComb_le hp hu hr0 hr1 univ
  have hpos := ENNReal.mul_pos_iff.mpr
    ⟨ENNReal.ofReal_pos.mpr (pow_pos hr0 n), hpp⟩
  have hrewrite := globalMixedMeasure_congr rfl
    (show (fun _ : Fin n => convexComb (1 - a) p u) =
      (fun _ : Fin n => convexComb a u p) from congrArg (fun q => fun _ : Fin n => q) hswap)
    (fun _ => (isThetaPshPotential_convexComb hp hu hr0 hr1).1)
    (fun _ => (isThetaPshPotential_convexComb_closed hu hp ha0.le ha1.le).1)
  rw [hrewrite] at hle
  exact lt_of_lt_of_le hpos hle

/-- The actual binary slot permutation identifies every coefficient mass.
Thus supplied original endpoint equalities internally produce the equality
of the actual convex diagonal masses at every closed coefficient. -/
theorem diagonalPotentialMass_convexComb_eq_of_endpointMixedMass_eq
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u v p : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hp : IsThetaPshPotential θ.val p)
    (hmass : ∀ j : Fin (n + 1), endpointMixedMass θ p u hp hu j =
      endpointMixedMass θ p v hp hv j) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    diagonalPotentialMass θ (convexComb a u p)
      (isThetaPshPotential_convexComb_closed hu hp ha0 ha1) =
    diagonalPotentialMass θ (convexComb a v p)
      (isThetaPshPotential_convexComb_closed hv hp ha0 ha1) := by
  classical
  have hcoeff (σ : Fin n → Bool) :
      globalMixedMass (fun _ : Fin n => θ) (fun i => if σ i then u else p)
        (fun i => by split_ifs <;> first | exact hu.1 | exact hp.1) =
      globalMixedMass (fun _ : Fin n => θ) (fun i => if σ i then v else p)
        (fun i => by split_ifs <;> first | exact hv.1 | exact hp.1) := by
    let j : Fin (n + 1) := ⟨Fintype.card {i : Fin n // σ i = true}, by
      exact Nat.lt_succ_of_le (by simpa only [Fintype.card_fin] using
        (Fintype.card_subtype_le (fun i : Fin n => σ i = true)))⟩
    have hmu := congrArg (fun μ : Measure M => μ univ)
      (globalMixedMeasure_binary_eq_endpointMixedMeasure hu hp σ j rfl)
    have hmv := congrArg (fun μ : Measure M => μ univ)
      (globalMixedMeasure_binary_eq_endpointMixedMeasure hv hp σ j rfl)
    exact hmu.trans ((hmass j).trans hmv.symm)
  have hpolyU := endpointMixedMass_convexComb_eq_sum omega hu hp ha0 ha1 (Fin.last n)
  have hpolyV := endpointMixedMass_convexComb_eq_sum omega hv hp ha0 ha1 (Fin.last n)
  rw [endpointMixedMass_last hp _] at hpolyU hpolyV
  have heq : (diagonalPotentialMass θ (convexComb a u p)
      (isThetaPshPotential_convexComb_closed hu hp ha0 ha1)).toReal =
      (diagonalPotentialMass θ (convexComb a v p)
        (isThetaPshPotential_convexComb_closed hv hp ha0 ha1)).toReal := by
    rw [hpolyU, hpolyV]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hcoeff σ]
  exact (ENNReal.toReal_eq_toReal_iff'
    (globalMixedMass_lt_top omega
      (fun _ : Fin n => (isThetaPshPotential_convexComb_closed hu hp ha0 ha1).1)).ne
    (globalMixedMass_lt_top omega
      (fun _ : Fin n => (isThetaPshPotential_convexComb_closed hv hp ha0 ha1).1)).ne).mp heq

end

end SGPT.Foundations.Analysis.Pending.SingularPositiveConvexMixedMass

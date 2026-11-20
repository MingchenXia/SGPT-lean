import SGPT.Foundations.Analysis.Pending.PositiveCurrentRooftop
import SGPT.Foundations.Analysis.Pending.IncreasingDiagonalContinuity

set_option autoImplicit false

/-! # Actual vanishing affine barriers at genuine increasing positive-mass limits -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IncreasingPositiveMassAffineBarriers

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass ConvexCombEnvelopeMass ThetaPshConvexCombination
  PositiveCurrentRooftop IncreasingDiagonalContinuity

noncomputable section

/-- Lower masses tending to a fixed finite positive mass internally make
any fixed affine weight admissible eventually. -/
theorem eventually_isAdmissibleWeight_of_lower_mass_tendsto
    {n : ℕ} {I : Type*} (F : Filter I) {m : I → ℝ≥0∞} {L : ℝ≥0∞}
    (hL : 0 < L) (hLtop : L ≠ ⊤) (hm : Tendsto m F (𝓝 L))
    {a : ℝ} (ha : 1 < a) :
    ∀ᶠ i in F, IsAdmissibleWeight n (m i) L a := by
  have hgap : Tendsto (fun i => L - m i) F (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [tsub_self] using
      ENNReal.Tendsto.sub (tendsto_const_nhds (x := L)) hm (Or.inl hLtop)
  have hmul : Tendsto (fun i => ENNReal.ofReal (a ^ n) * (L - m i)) F (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (a ^ n)) hgap
        (Or.inr ENNReal.ofReal_ne_top)
  exact (hmul.eventually (gt_mem_nhds hL)).mono fun i hi => ⟨ha, hi⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual increasing diagonal continuity produces the masses, then true
big-class affine obstacles produce potentials and vanishing coefficients. -/
theorem exists_vanishing_affine_barriers_of_monotone_regularized
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {v : ℕ → M → EReal} {u : M → EReal}
    (hv : ∀ j, IsThetaPshPotential θ.val (v j)) (hmono : Monotone v)
    (hu : IsThetaPshPotential θ.val u) (hreg : uscRegularization (⨆ j, v j) = u)
    (hpos : HasPositivePotentialMass θ u hu) :
    ∃ (N : ℕ → ℕ), (∀ j, j ≤ N j) ∧
      ∃ (ε : ℕ → Ioo (0 : ℝ) 1),
        Tendsto (fun j => (ε j).val) atTop (𝓝 (0 : ℝ)) ∧
        ∃ η : ℕ → M → EReal,
          (∀ j, IsThetaPshPotential θ.val (η j)) ∧
          ∀ j, convexComb (ε j).val (η j) u ≤ v (N j) := by
  classical
  let m : ℕ → ℝ≥0∞ := fun j => diagonalPotentialMass θ (v j) (hv j)
  let L : ℝ≥0∞ := diagonalPotentialMass θ u hu
  have hL : 0 < L := hpos
  have hLtop : L ≠ ⊤ := (MixedMass.globalMixedMass_lt_top omega
    (fun _ : Fin n => hu.1)).ne
  have hU : IsThetaPshPotential θ.val (uscRegularization (⨆ j, v j)) := hreg.symm ▸ hu
  have heq : L = ⨆ j, m j := by
    simpa only [hreg] using diagonalPotentialMass_eq_iSup omega hv hmono hU
  have hm : Tendsto m atTop (𝓝 L) := by
    rw [heq]
    exact tendsto_atTop_iSup (diagonalPotentialMass_monotone omega hv hmono)
  have hmpos : ∀ᶠ i in atTop, 0 < m i := hm.eventually (lt_mem_nhds hL)
  have hselect (j : ℕ) : ∃ i : ℕ, j ≤ i ∧ 0 < m i ∧
      IsAdmissibleWeight n (m i) L ((j : ℝ) + 2) := by
    have ha : (1 : ℝ) < (j : ℝ) + 2 := by
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hadm := eventually_isAdmissibleWeight_of_lower_mass_tendsto
      (n := n) atTop hL hLtop hm ha
    exact ((eventually_ge_atTop j).and (hmpos.and hadm)).exists
  choose N hN hmN hAdm using hselect
  have hle (i : ℕ) : v i ≤ u := by
    rw [← hreg]
    exact (le_iSup v i).trans (le_uscRegularization _)
  have hbar (j : ℕ) : ∃ η : M → EReal,
      IsThetaPshPotential θ.val η ∧ convexComb ((j : ℝ) + 2)⁻¹ η u ≤ v (N j) :=
    exists_thetaPsh_convexCombBarrier_of_isBigClass omega θ hbig
      (hv (N j)) hu (hle (N j)) (hmN j) (hAdm j)
  choose η hη hbarη using hbar
  let ε : ℕ → Ioo (0 : ℝ) 1 := fun j => ⟨((j : ℝ) + 2)⁻¹, by
    constructor
    · positivity
    · exact inv_lt_one_of_one_lt₀ (by
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith)⟩
  have hε : Tendsto (fun j => (ε j).val) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, ε, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two, one_div] using hh
  exact ⟨N, hN, ε, hε, η, hη, hbarη⟩

end

end SGPT.Foundations.Analysis.Pending.IncreasingPositiveMassAffineBarriers

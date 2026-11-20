import SGPT.Foundations.Analysis.Pending.ActualMixedMassAdmissibleBarrier

set_option autoImplicit false

/-! # Actual mixed-mass convergence from ordered diagonal limits

SGPT PDF0236 Step 2, with a fixed-weight arbitrary-filter adaptation.
Natural ordered genuine potentials and their actual positive diagonal
mass limits internally produce admissible weights and the mixed-mass
limit. No model sandwich or full dS mixed-mass continuity is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedMassOrderedContinuity

open FirstPass FirstPass.PositiveClasses DiagonalMass MixedMass
  GlobalMixedMassMonotone ActualMixedMassAdmissibleBarrier ConvexCombEnvelopeMass

noncomputable section

private theorem eventually_admissible_of_tendsto {n : ℕ} {I : Type*} {F : Filter I}
    {L : ℝ≥0∞} {m : I → ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (hm : Tendsto m F (𝓝 L)) {b : ℝ} (hb : 1 < b) :
    ∀ᶠ a in F, IsAdmissibleWeight n L (m a) b := by
  have hsub : Tendsto (fun a => m a - L) F (𝓝 0) := by
    simpa only [tsub_self] using
      ENNReal.Tendsto.sub hm (tendsto_const_nhds (x := L)) (Or.inr hLtop)
  have hmul : Tendsto (fun a => ENNReal.ofReal (b ^ n) * (m a - L)) F (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (b ^ n)) hsub (Or.inr ENNReal.ofReal_ne_top)
  have h1 : ∀ᶠ a in F, ENNReal.ofReal (b ^ n) * (m a - L) < L / 2 :=
    hmul.eventually (gt_mem_nhds (ENNReal.half_pos hL.ne'))
  have h2 : ∀ᶠ a in F, L / 2 < m a :=
    hm.eventually (lt_mem_nhds (ENNReal.half_lt_self hL.ne' hLtop))
  filter_upwards [h1, h2] with a ha1 ha2
  exact ⟨hb, ha1.trans ha2⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual ordered genuine tuples and their positive diagonal mass limits
internally produce the limit of the real actual independent mixed masses. -/
theorem tendsto_globalMixedMass_toReal_of_le_of_diagonal_tendsto
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {I : Type*} (F : Filter I) {φ : Fin n → M → EReal} {ψ : I → Fin n → M → EReal}
    (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (hψ : ∀ a i, IsThetaPshPotential (θ i).val (ψ a i))
    (hle : ∀ a i, φ i ≤ ψ a i)
    (hpos : ∀ i, 0 < diagonalPotentialMass (θ i) (φ i) (hφ i))
    (hdiag : ∀ i, Tendsto (fun a => diagonalPotentialMass (θ i) (ψ a i) (hψ a i)) F
      (𝓝 (diagonalPotentialMass (θ i) (φ i) (hφ i)))) :
    Tendsto (fun a => (globalMixedMass θ (ψ a) (fun i => (hψ a i).1)).toReal) F
      (𝓝 (globalMixedMass θ φ (fun i => (hφ i).1)).toReal) := by
  classical
  let m : ℝ := (globalMixedMass θ φ (fun i => (hφ i).1)).toReal
  let x : I → ℝ := fun a => (globalMixedMass θ (ψ a) (fun i => (hψ a i).1)).toReal
  have hfinite : globalMixedMass θ φ (fun i => (hφ i).1) ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun i => (hφ i).1)).ne
  have hfiniteψ (a : I) : globalMixedMass θ (ψ a) (fun i => (hψ a i).1) ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun i => (hψ a i).1)).ne
  have hdiagfinite (i : Fin n) : diagonalPotentialMass (θ i) (φ i) (hφ i) ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => (hφ i).1)).ne
  have hlow (a : I) : m ≤ x a := ENNReal.toReal_mono (hfiniteψ a)
    (globalMixedMass_mono_of_isThetaPshPotential omega hφ (hψ a)
      (fun i => MoreSingularOn.of_le fun y _ => hle a i y))
  change Tendsto x F (𝓝 m)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hcoef : Tendsto (fun b : ℝ => (1 - b⁻¹) ^ n * (m + ε)) atTop (𝓝 (m + ε)) := by
    have hinv : Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa only [sub_zero, one_pow, one_mul] using
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).pow n).mul_const (m + ε)
  have he : ∀ᶠ b : ℝ in atTop, m < (1 - b⁻¹) ^ n * (m + ε) :=
    hcoef.eventually (lt_mem_nhds (by linarith : m < m + ε))
  obtain ⟨b, hb, hbm⟩ := ((eventually_gt_atTop (1 : ℝ)).and he).exists
  have hs : 0 < 1 - b⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hb)
  have hc : 0 < (1 - b⁻¹) ^ n := pow_pos hs n
  have hadm : ∀ᶠ a in F, ∀ i : Fin n,
      IsAdmissibleWeight n (diagonalPotentialMass (θ i) (φ i) (hφ i))
        (diagonalPotentialMass (θ i) (ψ a i) (hψ a i)) b :=
    eventually_all.mpr fun i =>
      eventually_admissible_of_tendsto (hpos i) (hdiagfinite i) (hdiag i) hb
  filter_upwards [hadm] with a ha
  have hmass := globalMixedMass_le_of_admissibleWeights omega hφ (hψ a) (hle a) hpos ha
  have hprod : (∏ _ : Fin n, (1 - b⁻¹)) = (1 - b⁻¹) ^ n := by simp
  have hbound : (1 - b⁻¹) ^ n * x a ≤ m := by
    have h := ENNReal.toReal_mono hfinite hmass
    simpa only [hprod, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using h
  have hupper : x a < m + ε := by
    nlinarith
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hlow a))]
  linarith

/-- Actual finiteness recovers the genuine extended nonnegative mixed-mass
limit from its internally produced real limit. -/
theorem tendsto_globalMixedMass_of_le_of_diagonal_tendsto
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {I : Type*} (F : Filter I) {φ : Fin n → M → EReal} {ψ : I → Fin n → M → EReal}
    (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (hψ : ∀ a i, IsThetaPshPotential (θ i).val (ψ a i))
    (hle : ∀ a i, φ i ≤ ψ a i)
    (hpos : ∀ i, 0 < diagonalPotentialMass (θ i) (φ i) (hφ i))
    (hdiag : ∀ i, Tendsto (fun a => diagonalPotentialMass (θ i) (ψ a i) (hψ a i)) F
      (𝓝 (diagonalPotentialMass (θ i) (φ i) (hφ i)))) :
    Tendsto (fun a => globalMixedMass θ (ψ a) (fun i => (hψ a i).1)) F
      (𝓝 (globalMixedMass θ φ (fun i => (hφ i).1))) := by
  have h := ENNReal.tendsto_ofReal
    (tendsto_globalMixedMass_toReal_of_le_of_diagonal_tendsto omega F hφ hψ hle hpos hdiag)
  simpa only [ENNReal.ofReal_toReal (globalMixedMass_lt_top omega _).ne] using h

end

end SGPT.Foundations.Analysis.Pending.ActualMixedMassOrderedContinuity

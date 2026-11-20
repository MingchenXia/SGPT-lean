import SGPT.Foundations.Analysis.Pending.ActualMaximumMassAdmissibleBarrier

set_option autoImplicit false

/-! # Actual ordered maximum mass limits for arbitrary filters

SGPT PDF0240--0241 Step 3, with an independent fixed-weight
arbitrary-filter adaptation. Actual diagonal limits internally produce
the two admissible weights and the actual maximum mass limit.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMaximumMassOrderedContinuity

open FirstPass FirstPass.PositiveClasses DiagonalMass MixedMass
  ConvexCombEnvelopeMass GlobalMixedMassMonotone
  ActualMaximumMassAdmissibleBarrier

noncomputable section

private theorem eventually_admissible_of_tendsto {n : ℕ} {I : Type*} {F : Filter I}
    {L : ℝ≥0∞} {m : I → ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (hm : Tendsto m F (𝓝 L)) {b : ℝ} (hb : 1 < b) :
    ∀ᶠ i in F, IsAdmissibleWeight n L (m i) b := by
  have hsub : Tendsto (fun i => m i - L) F (𝓝 0) := by
    simpa only [tsub_self] using
      ENNReal.Tendsto.sub hm (tendsto_const_nhds (x := L)) (Or.inr hLtop)
  have hmul : Tendsto (fun i => ENNReal.ofReal (b ^ n) * (m i - L)) F (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (b ^ n)) hsub (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [hmul.eventually (gt_mem_nhds (ENNReal.half_pos hL.ne')),
    hm.eventually (lt_mem_nhds (ENNReal.half_lt_self hL.ne' hLtop))] with i h1 h2
  exact ⟨hb, h1.trans h2⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The two natural ordered diagonal mass limits internally produce the
actual extended nonnegative maximum mass limit, for every incoming filter. -/
theorem tendsto_diagonalPotentialMass_max_of_le_of_diagonal_tendsto
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {I : Type*} (F : Filter I) {φ ψ : M → EReal} {Φ Ψ : I → M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ)
    (hΦ : ∀ i, IsThetaPshPotential θ.val (Φ i))
    (hΨ : ∀ i, IsThetaPshPotential θ.val (Ψ i))
    (hφle : ∀ i, φ ≤ Φ i) (hψle : ∀ i, ψ ≤ Ψ i)
    (hφpos : 0 < diagonalPotentialMass θ φ hφ)
    (hψpos : 0 < diagonalPotentialMass θ ψ hψ)
    (hφlim : Tendsto (fun i => diagonalPotentialMass θ (Φ i) (hΦ i)) F
      (𝓝 (diagonalPotentialMass θ φ hφ)))
    (hψlim : Tendsto (fun i => diagonalPotentialMass θ (Ψ i) (hΨ i)) F
      (𝓝 (diagonalPotentialMass θ ψ hψ))) :
    Tendsto (fun i => diagonalPotentialMass θ (fun x => max (Φ i x) (Ψ i x))
      (IsThetaPshPotential.max (hΦ i) (hΨ i))) F
      (𝓝 (diagonalPotentialMass θ (fun x => max (φ x) (ψ x))
        (IsThetaPshPotential.max hφ hψ))) := by
  let Z : M → EReal := fun x => max (φ x) (ψ x)
  let X : I → M → EReal := fun i x => max (Φ i x) (Ψ i x)
  let Y : I → M → EReal := fun i x => max (φ x) (Ψ i x)
  have hZ : IsThetaPshPotential θ.val Z := IsThetaPshPotential.max hφ hψ
  have hX (i : I) : IsThetaPshPotential θ.val (X i) := IsThetaPshPotential.max (hΦ i) (hΨ i)
  have hY (i : I) : IsThetaPshPotential θ.val (Y i) := IsThetaPshPotential.max hφ (hΨ i)
  have hfinite {w : M → EReal} (hw : IsThetaPshPotential θ.val w) :
      diagonalPotentialMass θ w hw ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => hw.1)).ne
  let m : ℝ := (diagonalPotentialMass θ Z hZ).toReal
  let x : I → ℝ := fun i => (diagonalPotentialMass θ (X i) (hX i)).toReal
  let y : I → ℝ := fun i => (diagonalPotentialMass θ (Y i) (hY i)).toReal
  have hlow (i : I) : m ≤ x i := ENNReal.toReal_mono (hfinite (hX i))
    (globalMixedMass_mono_of_isThetaPshPotential omega
      (fun _ : Fin n => hZ) (fun _ : Fin n => hX i)
      (fun _ => MoreSingularOn.of_le fun z _ => max_le_max (hφle i z) (hψle i z)))
  have hreal : Tendsto x F (𝓝 m) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hcoef : Tendsto (fun b : ℝ => ((1 - b⁻¹) ^ n) ^ 2 * (m + ε)) atTop
        (𝓝 (m + ε)) := by
      have hinv : Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      simpa only [sub_zero, one_pow, one_mul] using
        ((((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).pow n).pow 2).mul_const (m + ε)
    have he : ∀ᶠ b : ℝ in atTop, m < ((1 - b⁻¹) ^ n) ^ 2 * (m + ε) :=
      hcoef.eventually (lt_mem_nhds (by linarith : m < m + ε))
    obtain ⟨b, hb, hbm⟩ := ((eventually_gt_atTop (1 : ℝ)).and he).exists
    have hs : 0 < 1 - b⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hb)
    have hc : 0 < (1 - b⁻¹) ^ n := pow_pos hs n
    have haφ : ∀ᶠ i in F, IsAdmissibleWeight n (diagonalPotentialMass θ φ hφ)
        (diagonalPotentialMass θ (Φ i) (hΦ i)) b :=
      eventually_admissible_of_tendsto hφpos (hfinite hφ) hφlim hb
    have haψ : ∀ᶠ i in F, IsAdmissibleWeight n (diagonalPotentialMass θ ψ hψ)
        (diagonalPotentialMass θ (Ψ i) (hΨ i)) b :=
      eventually_admissible_of_tendsto hψpos (hfinite hψ) hψlim hb
    filter_upwards [haφ, haψ] with i hiφ hiψ
    have h1 : (1 - b⁻¹) ^ n * x i ≤ y i := by
      have h := ENNReal.toReal_mono (hfinite (hY i))
        (diagonalPotentialMass_max_le_of_admissibleWeight omega hφ (hΦ i) (hΨ i)
          (hφle i) hφpos hiφ)
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using h
    have h2 : (1 - b⁻¹) ^ n * y i ≤ m := by
      have h := diagonalPotentialMass_max_le_of_admissibleWeight omega hψ (hΨ i) hφ
        (hψle i) hψpos hiψ
      have h' : ENNReal.ofReal ((1 - b⁻¹) ^ n) * diagonalPotentialMass θ (Y i) (hY i) ≤
          diagonalPotentialMass θ Z hZ := by
        simpa only [Y, Z, max_comm] using h
      have hr := ENNReal.toReal_mono (hfinite hZ) h'
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using hr
    have hbound : ((1 - b⁻¹) ^ n) ^ 2 * x i ≤ m := by
      have h := (mul_le_mul_of_nonneg_left h1 hc.le).trans h2
      simpa only [pow_two, mul_assoc] using h
    have hupper : x i < m + ε := by nlinarith [sq_pos_of_pos hc]
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hlow i))]
    linarith
  have he := ENNReal.tendsto_ofReal hreal
  simpa only [x, m, X, Z, ENNReal.ofReal_toReal (hfinite (hX _)),
    ENNReal.ofReal_toReal (hfinite hZ)] using he

end
end SGPT.Foundations.Analysis.Pending.ActualMaximumMassOrderedContinuity

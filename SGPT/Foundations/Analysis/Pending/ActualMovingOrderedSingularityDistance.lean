import SGPT.Foundations.Analysis.Pending.ActualMixedMassAdmissibleBarrier
import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance
import SGPT.Foundations.Analysis.Pending.Envelopes

set_option autoImplicit false

/-! # Actual distance zero from two moving ordered diagonal mass limits

Independent fixed-weight consequence of SGPT PDF0240--0241 Step 3,
with the genuine ordered canonical distance identity. Actual minimal
singularity mass bounds and admissible endpoint barriers are produced
internally. No common native limit or moving-distance input is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMovingOrderedSingularityDistance

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass MixedMass RelativeEnergy ConvexCombEnvelopeMass
  ActualMixedMassAdmissibleBarrier GlobalMixedMassMonotone
  SingularMinimalCanonicalRay SingularCanonicalOrderedMixedMassDistance
  SingularCanonicalSingularityDistance

noncomputable section

private theorem eventually_positive_admissible_of_common_limit
    {n : ℕ} {I : Type*} {F : Filter I} {L : ℝ≥0∞} {a b : I → ℝ≥0∞}
    (hL : 0 < L) (hLtop : L ≠ ⊤) (ha : Tendsto a F (𝓝 L))
    (hb : Tendsto b F (𝓝 L)) {q : ℝ} (hq : 1 < q) :
    ∀ᶠ i in F, 0 < a i ∧ IsAdmissibleWeight n (a i) (b i) q := by
  have hsub : Tendsto (fun i => b i - a i) F (𝓝 0) := by
    simpa only [tsub_self] using ENNReal.Tendsto.sub hb ha (Or.inr hLtop)
  have hmul : Tendsto (fun i => ENNReal.ofReal (q ^ n) * (b i - a i)) F (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (q ^ n)) hsub (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [ha.eventually (lt_mem_nhds hL),
    hmul.eventually (gt_mem_nhds (ENNReal.half_pos hL.ne')),
    hb.eventually (lt_mem_nhds (ENNReal.half_lt_self hL.ne' hLtop))] with i hi h1 h2
  exact ⟨hi, hq, h1.trans h2⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem tendsto_endpoint_difference_of_common_diagonal_limit
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {I : Type*} (F : Filter I)
    {u v : I → M → EReal} (hu : ∀ i, IsThetaPshPotential θ.val (u i))
    (hv : ∀ i, IsThetaPshPotential θ.val (v i)) (hle : ∀ i, u i ≤ v i)
    {L : ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (hulim : Tendsto (fun i => diagonalPotentialMass θ (u i) (hu i)) F (𝓝 L))
    (hvlim : Tendsto (fun i => diagonalPotentialMass θ (v i) (hv i)) F (𝓝 L))
    (j : Fin (n + 1)) :
    Tendsto (fun i =>
      (endpointMixedMass θ (thetaPshSupremum θ.val) (v i)
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (hv i) j).toReal -
      (endpointMixedMass θ (thetaPshSupremum θ.val) (u i)
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (hu i) j).toReal)
      F (𝓝 0) := by
  let V := thetaPshSupremum θ.val
  have hV : IsModelPotential θ V := isModelPotential_thetaPshSupremum omega θ hbig
  let P : I → Fin n → M → EReal := fun i => endpointMixedPotential j (u i) V
  let Q : I → Fin n → M → EReal := fun i => endpointMixedPotential j (v i) V
  have hP (i : I) (a : Fin n) : IsThetaPshPotential θ.val (P i a) := by
    by_cases ha : a.val < j.val
    · simpa only [P, endpointMixedPotential, if_pos ha] using hu i
    · simpa only [P, endpointMixedPotential, if_neg ha] using hV.plurisubharmonic
  have hQ (i : I) (a : Fin n) : IsThetaPshPotential θ.val (Q i a) := by
    by_cases ha : a.val < j.val
    · simpa only [Q, endpointMixedPotential, if_pos ha] using hv i
    · simpa only [Q, endpointMixedPotential, if_neg ha] using hV.plurisubharmonic
  have hPQ (i : I) (a : Fin n) : P i a ≤ Q i a := by
    by_cases ha : a.val < j.val
    · simpa only [P, Q, endpointMixedPotential, if_pos ha] using hle i
    · simp only [P, Q, endpointMixedPotential, if_neg ha, le_refl]
  have hfinite {w : M → EReal} (hw : IsThetaPshPotential θ.val w) :
      endpointMixedMass θ V w hV.plurisubharmonic hw j ≠ ⊤ :=
    (globalMixedMass_lt_top omega
      (endpointMixedPotential_thetaPlurisubharmonic θ j w V hw hV.plurisubharmonic)).ne
  have hVfinite : diagonalPotentialMass θ V hV.plurisubharmonic ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => hV.plurisubharmonic.1)).ne
  let A : I → ℝ := fun i => (endpointMixedMass θ V (u i) hV.plurisubharmonic (hu i) j).toReal
  let B : I → ℝ := fun i => (endpointMixedMass θ V (v i) hV.plurisubharmonic (hv i) j).toReal
  let M : ℝ := (diagonalPotentialMass θ V hV.plurisubharmonic).toReal
  have hAB (i : I) : A i ≤ B i := ENNReal.toReal_mono (hfinite (hv i))
    (globalMixedMass_mono_of_isThetaPshPotential omega (hP i) (hQ i)
      (fun a => MoreSingularOn.of_le fun x _ => hPQ i a x))
  have hBM (i : I) : B i ≤ M := by
    have hvV : MoreSingularOn (v i) V univ :=
      FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
        (hv i).1.hasSmoothLocalPotentials ⟨_, hv i⟩ (v i) (hv i)
    have hQV (a : Fin n) : MoreSingularOn (Q i a) V univ := by
      by_cases ha : a.val < j.val
      · simpa only [Q, endpointMixedPotential, if_pos ha] using hvV
      · simpa only [Q, endpointMixedPotential, if_neg ha] using MoreSingularOn.refl V univ
    exact ENNReal.toReal_mono hVfinite
      (globalMixedMass_mono_of_isThetaPshPotential omega (hQ i)
        (fun _ : Fin n => hV.plurisubharmonic) hQV)
  change Tendsto (fun i => B i - A i) F (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hcoef : Tendsto (fun b : ℝ => (1 - (1 - b⁻¹) ^ n) * M) atTop (𝓝 0) := by
    have hinv : Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hpow := ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).pow n
    simpa only [sub_zero, one_pow, sub_self, zero_mul] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).mul_const M
  obtain ⟨b, hb, hbm⟩ :=
    ((eventually_gt_atTop (1 : ℝ)).and (hcoef.eventually (gt_mem_nhds hε))).exists
  have hs0 : 0 < 1 - b⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hb)
  have hs1 : 1 - b⁻¹ < 1 := sub_lt_self 1 (inv_pos.mpr (zero_lt_one.trans hb))
  have hc0 : 0 ≤ (1 - b⁻¹) ^ n := (pow_pos hs0 n).le
  have hc1 : (1 - b⁻¹) ^ n ≤ 1 := pow_le_one₀ hs0.le hs1.le
  have hadm : ∀ᶠ i in F, 0 < diagonalPotentialMass θ (u i) (hu i) ∧
      IsAdmissibleWeight n (diagonalPotentialMass θ (u i) (hu i))
        (diagonalPotentialMass θ (v i) (hv i)) b :=
    eventually_positive_admissible_of_common_limit hL hLtop hulim hvlim hb
  filter_upwards [hadm] with i hi
  have hpos (a : Fin n) : 0 < diagonalPotentialMass θ (P i a) (hP i a) := by
    by_cases ha : a.val < j.val
    · simpa only [P, endpointMixedPotential, if_pos ha] using hi.1
    · simpa only [P, endpointMixedPotential, if_neg ha] using hV.positive_mass
  have hweights (a : Fin n) : IsAdmissibleWeight n
      (diagonalPotentialMass θ (P i a) (hP i a))
      (diagonalPotentialMass θ (Q i a) (hQ i a)) b := by
    by_cases ha : a.val < j.val
    · simpa only [P, Q, endpointMixedPotential, if_pos ha] using hi.2
    · simpa only [P, Q, endpointMixedPotential, if_neg ha] using
        isAdmissibleWeight_of_eq hV.positive_mass hb
  have hmass := globalMixedMass_le_of_admissibleWeights omega (hP i) (hQ i) (hPQ i)
    hpos hweights
  have hprod : (∏ _ : Fin n, (1 - b⁻¹)) = (1 - b⁻¹) ^ n := by simp
  have hbound : (1 - b⁻¹) ^ n * B i ≤ A i := by
    have h := ENNReal.toReal_mono (hfinite (hu i)) hmass
    simpa only [hprod, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0,
      A, B, Q, globalMixedMass, endpointMixedMass, endpointMixedMeasure] using h
  have hgap : B i - A i ≤ (1 - (1 - b⁻¹) ^ n) * M := by
    have h := mul_le_mul_of_nonneg_left (hBM i) (sub_nonneg.mpr hc1)
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sub_nonneg.mpr (hAB i))]
  exact hgap.trans_lt hbm

/-- Two genuine moving ordered potentials with actual diagonal masses
converging to the same finite positive scalar have true defining real
singularity distance tending to zero. All endpoint control is internal. -/
theorem tendsto_singularityDistance_toReal_zero_of_le_of_common_diagonal_limit
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {I : Type*} (F : Filter I)
    {u v : I → M → EReal} (hu : ∀ i, IsThetaPshPotential θ.val (u i))
    (hv : ∀ i, IsThetaPshPotential θ.val (v i)) (hle : ∀ i, u i ≤ v i)
    {L : ℝ≥0∞} (hL : 0 < L) (hLtop : L ≠ ⊤)
    (hulim : Tendsto (fun i => diagonalPotentialMass θ (u i) (hu i)) F (𝓝 L))
    (hvlim : Tendsto (fun i => diagonalPotentialMass θ (v i) (hv i)) F (𝓝 L)) :
    Tendsto (fun i => (singularityDistance omega θ hbig (u i) (v i)).toReal)
      F (𝓝 0) := by
  have hsum : Tendsto (fun i =>
      (∑ j : Fin (n + 1),
        ((endpointMixedMass θ (thetaPshSupremum θ.val) (v i)
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (hv i) j).toReal -
        (endpointMixedMass θ (thetaPshSupremum θ.val) (u i)
          (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic (hu i) j).toReal)) /
          (n + 1 : ℝ)) F (𝓝 0) := by
    simpa only [Finset.sum_const_zero, zero_div] using
      (tendsto_finsetSum Finset.univ fun j _ =>
        tendsto_endpoint_difference_of_common_diagonal_limit omega θ hbig F
          hu hv hle hL hLtop hulim hvlim j).div_const (n + 1 : ℝ)
  have heq (i : I) := singularityDistance_eq_mixedMass_sub_of_le omega θ hbig
    (hu i) (hv i) (hle i)
  simpa only [heq, EReal.toReal_coe] using hsum

end
end SGPT.Foundations.Analysis.Pending.ActualMovingOrderedSingularityDistance

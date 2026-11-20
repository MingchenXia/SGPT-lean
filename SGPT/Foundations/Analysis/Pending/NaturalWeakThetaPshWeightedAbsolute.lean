import SGPT.Foundations.Analysis.Pending.NaturalWeightedThetaPshMonotoneGaps

/-!
# Actual original-filter weighted absolute convergence from native weak chart reads

Only one genuine event is selected per tolerance. The original filter
receives neither an atTop-tail replacement nor a dominated-convergence
assumption; the real positive-part and signed-integral identities give
the absolute error after the actual new sequence DCT has been proved.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshWeightedAbsolute

open FirstPass NaturalWeightedThetaPshMonotoneGaps

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- Actual native weak chart reads imply nonnegative-test weighted absolute convergence on the same filter. -/
theorem tendsto_native_weighted_abs_of_chart_weak_tests
    {ι : Type*} [Countable ι] {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i y, u i y ≤ (C : EReal))
    (e : ComplexChart n M) (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ))
    (hφ : ∀ z, 0 ≤ φ z) :
    Tendsto (fun i => ∫ z, φ z *
      |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume) l (𝓝 0) := by
  obtain ⟨S, hS, _hSne, _hantiS, hg, _hantiW, heq, hgap⟩ :=
    exists_genuine_events_and_native_weighted_gap_tendsto hu hv hlim hC
  let W (k : ℕ) : M → EReal := uscRegularization (⨆ i : S k, u i.val)
  have hvlower (k : ℕ) : v ≤ W k := by
    rw [← heq]
    exact iInf_le _ k
  have hui (i : ι) : Integrable
      (fun z => φ z * (chartFunction (u i) e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        ((hu i).quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  have hvi : Integrable (fun z => φ z * (chartFunction v e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hv.quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  let F (i : ι) (z : ComplexModel n) : ℝ := φ z *
    ((chartFunction (u i) e z).toReal - (chartFunction v e z).toReal)
  let P (i : ι) (z : ComplexModel n) : ℝ := max (F i z) 0
  let G (k : ℕ) (z : ComplexModel n) : ℝ := φ z *
    ((chartFunction (W k) e z).toReal - (chartFunction v e z).toReal)
  have hFi (i : ι) : Integrable (F i) volume :=
    ((hui i).sub hvi).congr (Eventually.of_forall (fun z => by
      change φ z * (chartFunction (u i) e z).toReal - φ z * (chartFunction v e z).toReal = _
      dsimp only [F]
      ring))
  have hPi (i : ι) : Integrable (P i) volume := by
    have hz : Integrable (fun _ : ComplexModel n => (0 : ℝ)) volume := by simp
    exact (hFi i).sup hz
  have hGi (k : ℕ) : Integrable (G k) volume := by
    have hwi : Integrable (fun z => φ z * (chartFunction (W k) e z).toReal) volume := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
          ((hg k).quasiPshPotential.locallyIntegrableOn_chart_toReal e)
    exact (hwi.sub hvi).congr (Eventually.of_forall (fun z => by
      change φ z * (chartFunction (W k) e z).toReal - φ z * (chartFunction v e z).toReal = _
      dsimp only [G]
      ring))
  have hdom (k : ℕ) (i : ι) (hi : i ∈ S k) : P i ≤ᵐ[volume] G k := by
    have hraw : u i ≤ W k := by
      intro x
      have hsup : u i x ≤ (⨆ j : S k, u j.val) x := by
        simp only [iSup_apply]
        exact le_iSup (fun j : S k => u j.val x) ⟨i, hi⟩
      exact hsup.trans (le_uscRegularization _ x)
    have hgood : ∀ᵐ z ∂volume.restrict e.val.target,
        (chartFunction (u i) e z ≠ ⊤ ∧ chartFunction (u i) e z ≠ ⊥) ∧
        (chartFunction v e z ≠ ⊤ ∧ chartFunction v e z ≠ ⊥) ∧
        (chartFunction (W k) e z ≠ ⊤ ∧ chartFunction (W k) e z ≠ ⊥) := by
      filter_upwards [(hu i).quasiPshPotential.ae_finite_chart e,
        hv.quasiPshPotential.ae_finite_chart e, (hg k).quasiPshPotential.ae_finite_chart e]
        with z huz hvz hwz
      exact ⟨huz, hvz, hwz⟩
    have hgood' := (ae_restrict_iff' e.val.open_target.measurableSet).mp hgood
    filter_upwards [hgood'] with z hz
    by_cases hzt : z ∈ e.val.target
    · obtain ⟨huz, hvz, hwz⟩ := hz hzt
      have hreal : (chartFunction (u i) e z).toReal ≤ (chartFunction (W k) e z).toReal :=
        EReal.toReal_le_toReal (hraw (e.val.symm z)) huz.2 hwz.1
      have hlow : (chartFunction v e z).toReal ≤ (chartFunction (W k) e z).toReal :=
        EReal.toReal_le_toReal (hvlower k (e.val.symm z)) hvz.2 hwz.1
      exact max_le (mul_le_mul_of_nonneg_left (sub_le_sub_right hreal _) (hφ z))
        (mul_nonneg (hφ z) (sub_nonneg.mpr hlow))
    · have hzero : φ z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hzt (φ.tsupport_subset h))
      simp [P, F, G, hzero]
  have hPnonneg (i : ι) : 0 ≤ ∫ z, P i z ∂volume :=
    integral_nonneg (fun z => le_max_right _ _)
  have hPlim : Tendsto (fun i => ∫ z, P i z ∂volume) l (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall (fun i => ha.trans_le (hPnonneg i))
    · intro b hb
      obtain ⟨k, hk⟩ := ((hgap e φ hφ).eventually (Iio_mem_nhds hb)).exists
      filter_upwards [hS k] with i hi
      exact (integral_mono_ae (hPi i) (hGi k) (hdom k i hi)).trans_lt hk
  have hFread (i : ι) : (∫ z, F i z ∂volume) =
      (∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) -
        ∫ z, φ z * (chartFunction v e z).toReal ∂volume := by
    dsimp only [F]
    simp_rw [mul_sub]
    exact integral_sub (hui i) hvi
  have hFlim : Tendsto (fun i => ∫ z, F i z ∂volume) l (𝓝 0) := by
    have ht := (hlim e φ).sub
      (tendsto_const_nhds (x := ∫ z, φ z * (chartFunction v e z).toReal ∂volume))
    simpa only [← hFread, sub_self] using ht
  have hrealIdentity (t : ℝ) : |t| = 2 * max t 0 - t := by
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, abs_of_nonneg ht]
      ring
    · rw [max_eq_right ht, abs_of_nonpos ht]
      ring
  have hAbsRead (i : ι) : (∫ z, |F i z| ∂volume) =
      2 * (∫ z, P i z ∂volume) - ∫ z, F i z ∂volume := by
    simp_rw [hrealIdentity]
    change (∫ z, 2 * P i z - F i z ∂volume) = _
    rw [integral_sub ((hPi i).const_mul 2) (hFi i), integral_const_mul]
  have hAbsLim : Tendsto (fun i => ∫ z, |F i z| ∂volume) l (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x := (2 : ℝ))).mul hPlim).sub hFlim
    simpa only [← hAbsRead, mul_zero, sub_zero] using ht
  have hfunction : (fun i => ∫ z, |F i z| ∂volume) =
      fun i => ∫ z, φ z *
        |(chartFunction (u i) e z).toReal - (chartFunction v e z).toReal| ∂volume := by
    funext i
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      dsimp only [F]
      rw [abs_mul, abs_of_nonneg (hφ z)])
  rw [hfunction] at hAbsLim
  exact hAbsLim

end SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshWeightedAbsolute

import SGPT.Foundations.Analysis.Pending.NaturalGenuineWeakEventSuprema
import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual native weighted gaps of genuine original decreasing theta-PSH sequences

Dominated convergence is used only for the new natural-number sequence.
The original weak convergence filter is not assumed countably generated.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalWeightedThetaPshMonotoneGaps

open FirstPass NaturalGenuineWeakEventSuprema

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- A genuine decreasing sequence gives convergent actual native nonnegative-test real gaps. -/
theorem tendsto_native_weighted_gap_of_antitone_iInf
    {g : ℕ → M → EReal} {v : M → EReal}
    (hg : ∀ k, IsThetaPshPotential θ (g k)) (hv : IsThetaPshPotential θ v)
    (hanti : Antitone g) (heq : (⨅ k : ℕ, g k) = v)
    (e : ComplexChart n M) (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ))
    (hφ : ∀ z, 0 ≤ φ z) :
    Tendsto (fun k => ∫ z, φ z *
      ((chartFunction (g k) e z).toReal - (chartFunction v e z).toReal) ∂volume)
      atTop (𝓝 0) := by
  have hle (k : ℕ) : v ≤ g k := by
    rw [← heq]
    exact iInf_le _ k
  have hφg (k : ℕ) : Integrable
      (fun z => φ z * (chartFunction (g k) e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        ((hg k).quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  have hφv : Integrable (fun z => φ z * (chartFunction v e z).toReal) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
        (hv.quasiPshPotential.locallyIntegrableOn_chart_toReal e)
  let G : ℕ → ComplexModel n → ℝ := fun k z => φ z *
    ((chartFunction (g k) e z).toReal - (chartFunction v e z).toReal)
  have hGi (k : ℕ) : Integrable (G k) volume :=
    ((hφg k).sub hφv).congr (Eventually.of_forall (fun z => by
      change φ z * (chartFunction (g k) e z).toReal -
        φ z * (chartFunction v e z).toReal =
        φ z * ((chartFunction (g k) e z).toReal - (chartFunction v e z).toReal)
      ring))
  have hgfin : ∀ᵐ z ∂volume.restrict e.val.target,
      ∀ k : ℕ, chartFunction (g k) e z ≠ ⊤ ∧ chartFunction (g k) e z ≠ ⊥ := by
    rw [ae_all_iff]
    exact fun k => (hg k).quasiPshPotential.ae_finite_chart e
  have hgood : ∀ᵐ z ∂volume.restrict e.val.target,
      (chartFunction v e z ≠ ⊤ ∧ chartFunction v e z ≠ ⊥) ∧
      (∀ k : ℕ, chartFunction (g k) e z ≠ ⊤ ∧ chartFunction (g k) e z ≠ ⊥) := by
    filter_upwards [hv.quasiPshPotential.ae_finite_chart e, hgfin] with z hz hgz
    exact ⟨hz, hgz⟩
  have hgood' := (ae_restrict_iff' e.val.open_target.measurableSet).mp hgood
  have hbound (k : ℕ) : ∀ᵐ z ∂volume, ‖G k z‖ ≤ G 0 z := by
    filter_upwards [hgood'] with z hz
    by_cases hzt : z ∈ e.val.target
    · obtain ⟨hvz, hgz⟩ := hz hzt
      have hlo : (chartFunction v e z).toReal ≤ (chartFunction (g k) e z).toReal :=
        EReal.toReal_le_toReal (hle k (e.val.symm z)) hvz.2 (hgz k).1
      have hup : (chartFunction (g k) e z).toReal ≤ (chartFunction (g 0) e z).toReal :=
        EReal.toReal_le_toReal (hanti (Nat.zero_le k) (e.val.symm z)) (hgz k).2 (hgz 0).1
      have hnonneg : 0 ≤ G k z := mul_nonneg (hφ z) (sub_nonneg.mpr hlo)
      have hcmp : G k z ≤ G 0 z :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hup _) (hφ z)
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hcmp
    · have hzero : φ z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hzt (φ.tsupport_subset h))
      simp [G, hzero]
  have hpoint : ∀ᵐ z ∂volume, Tendsto (fun k => G k z) atTop (𝓝 0) := by
    filter_upwards [hgood'] with z hz
    by_cases hzt : z ∈ e.val.target
    · have hvz := (hz hzt).1
      have hinf : (⨅ k : ℕ, chartFunction (g k) e z) = chartFunction v e z := by
        simpa only [chartFunction, iInf_apply] using congrFun heq (e.val.symm z)
      have hE : Tendsto (fun k => chartFunction (g k) e z) atTop
          (𝓝 (chartFunction v e z)) := by
        rw [← hinf]
        exact tendsto_atTop_iInf (fun k m hkm => hanti hkm (e.val.symm z))
      have hR := (EReal.tendsto_toReal hvz.1 hvz.2).comp hE
      have hdiff : Tendsto (fun k => (chartFunction (g k) e z).toReal -
          (chartFunction v e z).toReal) atTop (𝓝 0) := by
        simpa using hR.sub (tendsto_const_nhds (x := (chartFunction v e z).toReal))
      simpa only [G, mul_zero] using (tendsto_const_nhds (x := φ z)).mul hdiff
    · have hzero : φ z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hzt (φ.tsupport_subset h))
      simpa only [G, hzero, zero_mul] using (tendsto_const_nhds (x := (0 : ℝ)))
  have hDCT := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := G) (f := fun _ => (0 : ℝ)) (G 0) (fun k => (hGi k).aestronglyMeasurable)
    (hGi 0) hbound hpoint
  simpa only [G, integral_zero] using hDCT

/-- The actual genuine weak-event supremum sequence internally yields all native weighted gaps. -/
theorem exists_genuine_events_and_native_weighted_gap_tendsto
    {ι : Type*} [Countable ι] {l : Filter ι} [NeBot l]
    {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i y, u i y ≤ (C : EReal)) :
    ∃ S : ℕ → Set ι,
      (∀ k, S k ∈ l) ∧ (∀ k, (S k).Nonempty) ∧ Antitone S ∧
      (∀ k, IsThetaPshPotential θ (uscRegularization (⨆ i : S k, u i.val))) ∧
      Antitone (fun k => uscRegularization (⨆ i : S k, u i.val)) ∧
      (⨅ k : ℕ, uscRegularization (⨆ i : S k, u i.val)) = v ∧
      (∀ (e : ComplexChart n M) (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
        (∀ z, 0 ≤ φ z) → Tendsto (fun k => ∫ z, φ z *
          ((chartFunction (uscRegularization (⨆ i : S k, u i.val)) e z).toReal -
            (chartFunction v e z).toReal) ∂volume) atTop (𝓝 0)) := by
  obtain ⟨S, hS, hSne, hantiS, hg, hantiW, heq, _hpoint⟩ :=
    exists_genuine_antitone_events_exact_inf_and_tendsto hu hv hlim hC
  exact ⟨S, hS, hSne, hantiS, hg, hantiW, heq,
    fun e φ hφ => tendsto_native_weighted_gap_of_antitone_iInf hg hv hantiW heq e φ hφ⟩

end SGPT.Foundations.Analysis.Pending.NaturalWeightedThetaPshMonotoneGaps

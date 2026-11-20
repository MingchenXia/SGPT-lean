import SGPT.Foundations.Analysis.FirstPass.OrderedL1Squeeze
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

set_option autoImplicit false

/-!
# Decreasing families of theta-PSH potentials converge in chart-local `L¹`

The local `L¹` topology of `FirstPass.PotentialL1` is compatible with a
pointwise decreasing sequence of theta-PSH potentials, provided that its
pointwise infimum is again a genuine theta-PSH potential.  This is the
decreasing counterpart to `Pending.IncreasingThetaPshChartL1`; unlike that
result, no upper-semicontinuous regularization is needed in the hypothesis,
because the specified infimum already supplies the pointwise limit.

The proof is chartwise dominated convergence.  On the full-measure set where
the potentials have finite values, the canonical extended-real distance is the
ordinary nonnegative difference `g_j - u`; antitonicity bounds it by the first
such difference.
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DecreasingThetaPshChartL1

open SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- For ordered real values, the canonical extended difference is their
ordinary nonnegative difference.  This local helper avoids importing the much
larger increasing-limit development. -/
private theorem canonicalERealAbsDiff_coe_coe_of_le {a b : ℝ} (hab : a ≤ b) :
    canonicalERealAbsDiff (b : EReal) (a : EReal) = ENNReal.ofReal (b - a) := by
  rw [canonicalERealAbsDiff_coe_coe, abs_of_nonneg (by linarith)]

/-- **Decreasing theta-PSH convergence in chart-local `L¹`.**  A pointwise
nonincreasing sequence of theta-PSH potentials converges in chart-local `L¹`
to its pointwise infimum whenever that infimum is a theta-PSH potential. -/
theorem manifoldL1LocallyTendsto_of_antitone_iInf
    {theta : ClosedRealOneOneForm n M} {g : ℕ → M → EReal} {u : M → EReal}
    (hg : ∀ j, IsThetaPshPotential theta.val (g j))
    (hanti : Antitone g)
    (hu : IsThetaPshPotential theta.val u)
    (heq : (⨅ j : ℕ, g j) = u) :
    ManifoldL1LocallyTendsto (n := n) g atTop u := by
  have hle : ∀ j, u ≤ g j := by
    intro j x
    rw [← heq]
    rw [iInf_apply]
    exact iInf_le (fun i : ℕ => g i x) j
  intro e K hK hKe
  set F : ℕ → ComplexModel n → ℝ≥0∞ := fun j z =>
    canonicalERealAbsDiff (chartFunction (g j) e z) (chartFunction u e z) with hF
  have hfinu : ∀ᵐ z ∂(volume.restrict K),
      chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe
      (hu.quasiPshPotential.ae_finite_chart e)
  have hfing : ∀ᵐ z ∂(volume.restrict K), ∀ j,
      chartFunction (g j) e z ≠ ⊤ ∧ chartFunction (g j) e z ≠ ⊥ := by
    rw [ae_all_iff]
    intro j
    exact ae_restrict_of_ae_restrict_of_subset hKe
      ((hg j).quasiPshPotential.ae_finite_chart e)
  have hgood : ∀ᵐ z ∂(volume.restrict K),
      (chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥) ∧
      (∀ j, chartFunction (g j) e z ≠ ⊤ ∧ chartFunction (g j) e z ≠ ⊥) := by
    filter_upwards [hfinu, hfing] with z h1 h2
    exact ⟨h1, h2⟩
  have hvalue : ∀ z, (chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥) →
      (∀ j, chartFunction (g j) e z ≠ ⊤ ∧ chartFunction (g j) e z ≠ ⊥) →
      ∀ j, F j z = ENNReal.ofReal
        ((chartFunction (g j) e z).toReal - (chartFunction u e z).toReal) := by
    intro z hu' hg' j
    have hle' : (chartFunction u e z).toReal ≤ (chartFunction (g j) e z).toReal :=
      EReal.toReal_le_toReal (hle j (e.val.symm z)) hu'.2 (hg' j).1
    have e1 : (((chartFunction u e z).toReal : ℝ) : EReal) =
        chartFunction u e z := EReal.coe_toReal hu'.1 hu'.2
    have e2 : (((chartFunction (g j) e z).toReal : ℝ) : EReal) =
        chartFunction (g j) e z := EReal.coe_toReal (hg' j).1 (hg' j).2
    have hcalc := canonicalERealAbsDiff_coe_coe_of_le hle'
    rw [e1, e2] at hcalc
    simpa [hF] using hcalc
  have hF_meas : ∀ j, AEMeasurable (F j) (volume.restrict K) := by
    intro j
    exact measurable_canonicalERealAbsDiff.comp_aemeasurable
      (((hg j).quasiPshPotential.aemeasurable_chart_restrict e hKe).prodMk
        (hu.quasiPshPotential.aemeasurable_chart_restrict e hKe))
  have hbound : ∀ j, F j ≤ᵐ[volume.restrict K] F 0 := by
    intro j
    filter_upwards [hgood] with z ⟨hu', hg'⟩
    rw [hvalue z hu' hg' j, hvalue z hu' hg' 0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hstep : (chartFunction (g j) e z).toReal ≤
        (chartFunction (g 0) e z).toReal :=
      EReal.toReal_le_toReal (hanti (Nat.zero_le j) (e.val.symm z))
        (hg' j).2 (hg' 0).1
    linarith
  have hfin : ∫⁻ z in K, F 0 z ∂volume ≠ ⊤ := by
    have heqint : ∫⁻ z in K, F 0 z ∂volume = chartEndpointRealL1 (g 0) u e K := by
      rw [chartEndpointRealL1]
      refine lintegral_congr_ae ?_
      filter_upwards [hgood] with z ⟨hu', hg'⟩
      have hle0 : (chartFunction u e z).toReal ≤ (chartFunction (g 0) e z).toReal :=
        EReal.toReal_le_toReal (hle 0 (e.val.symm z)) hu'.2 (hg' 0).1
      rw [hvalue z hu' hg' 0, abs_of_nonpos (by linarith)]
      congr 1
      ring
    rw [heqint]
    exact chartEndpointRealL1_ne_top (hg 0).quasiPshPotential hu.quasiPshPotential
      e hK hKe
  have hlim : ∀ᵐ z ∂(volume.restrict K),
      Tendsto (fun j => F j z) atTop (𝓝 0) := by
    filter_upwards [hgood] with z ⟨hu', hg'⟩
    have hinf : (⨅ j : ℕ, chartFunction (g j) e z) = chartFunction u e z := by
      change (⨅ j : ℕ, g j (e.val.symm z)) = u (e.val.symm z)
      simpa only [iInf_apply] using congrFun heq (e.val.symm z)
    have hEtend : Tendsto (fun j => chartFunction (g j) e z) atTop
        (𝓝 (chartFunction u e z)) := by
      rw [← hinf]
      exact tendsto_atTop_iInf fun j k hjk => hanti hjk (e.val.symm z)
    have hRtend : Tendsto (fun j => (chartFunction (g j) e z).toReal) atTop
        (𝓝 (chartFunction u e z).toReal) :=
      ((EReal.tendsto_toReal hu'.1 hu'.2).comp hEtend)
    have hdiff : Tendsto
        (fun j => (chartFunction (g j) e z).toReal -
          (chartFunction u e z).toReal) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => (chartFunction u e z).toReal) atTop
          (𝓝 (chartFunction u e z).toReal) := tendsto_const_nhds
      simpa using hRtend.sub hconst
    have hreal := ENNReal.tendsto_ofReal hdiff
    simp only [ENNReal.ofReal_zero] at hreal
    refine hreal.congr ?_
    intro j
    exact (hvalue z hu' hg' j).symm
  have hmain := tendsto_lintegral_of_dominated_convergence'
    (F := F) (f := fun _ => (0 : ℝ≥0∞)) (bound := F 0)
    (μ := volume.restrict K) hF_meas hbound hfin hlim
  simpa [chartL1EDistance, hF] using hmain

end

end SGPT.Foundations.Analysis.Pending.DecreasingThetaPshChartL1

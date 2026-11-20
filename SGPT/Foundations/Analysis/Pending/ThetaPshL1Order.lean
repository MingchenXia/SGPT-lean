import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison

/-!
# Order is preserved under genuine chart-local L1 convergence

A sequence of theta-PSH potentials below a fixed theta-PSH potential has
its chart-local L1 limit below the same potential everywhere. In each compact
chart ball, extract an almost-everywhere convergent subsequence in EReal and
then apply the local plurisubharmonic comparison principle.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaPshL1Order

open FirstPass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- Pointwise domination by a theta-PSH potential is closed under canonical
chart-local L1 convergence of actual theta-PSH potentials. -/
theorem le_of_manifoldL1LocallyTendsto {u : ℕ → M → EReal} {v w : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ (u j))
    (hv : IsThetaPshPotential θ v) (hw : IsThetaPshPotential θ w)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    (hle : ∀ j, u j ≤ w) : v ≤ w := by
  intro x
  let e : ComplexChart n M := complexChartAt (n := n) x
  let z : ComplexModel n := e.val x
  have hxsource : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : z ∈ e.val.target := e.val.map_source hxsource
  obtain ⟨W₁, ρ, hzW₁, hρ, hpv⟩ := hv.1 e z hz
  obtain ⟨W₂, σ, hzW₂, hσ, hpw⟩ := hw.1 e z hz
  let V : Set (ComplexModel n) := W₁ ∩ W₂
  have hV : IsOpen V := hρ.1.inter hσ.1
  have hzV : z ∈ V := ⟨hzW₁, hzW₂⟩
  have hρV := hρ.mono hV inter_subset_left
  have hσV := hσ.mono hV inter_subset_right
  have hpvV : PlurisubharmonicOn
      (fun y => chartFunction v e y + (σ y : EReal)) V :=
    (smoothLocalPotential_psh_iff θ e V ρ σ hρV hσV (chartFunction v e)).1
      (hpv.mono inter_subset_left)
  have hpwV := hpw.mono (inter_subset_right (s := W₁))
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV z hzV
  let K : Set (ComplexModel n) := closedBall z (ε / 2)
  let O : Set (ComplexModel n) := ball z (ε / 2)
  have hKV : K ⊆ V :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεV
  have hOV : O ⊆ V := ball_subset_closedBall.trans hKV
  have hKe : K ⊆ e.val.target := hKV.trans (inter_subset_left.trans hρ.2.1)
  have hfinite (f : M → EReal) (hf : IsThetaPshPotential θ f) :
      ∀ᵐ y ∂volume.restrict K,
        chartFunction f e y ≠ ⊤ ∧ chartFunction f e y ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hKe (hf.quasiPshPotential.ae_finite_chart e)
  obtain ⟨ns, _hns, hconv⟩ :=
    exists_strictMono_tendsto_ae_eReal_of_lintegral_canonicalERealAbsDiff
      (fun j => (hu j).quasiPshPotential.aemeasurable_chart_restrict e hKe)
      (hv.quasiPshPotential.aemeasurable_chart_restrict e hKe)
      (fun j => hfinite (u j) (hu j)) (hfinite v hv)
      (hlim e K (isCompact_closedBall z (ε / 2)) hKe)
  have haeK : ∀ᵐ y ∂volume.restrict K, chartFunction v e y ≤ chartFunction w e y := by
    filter_upwards [hconv] with y hy
    exact le_of_tendsto_of_tendsto hy tendsto_const_nhds
      (Eventually.of_forall fun k => hle (ns k) (e.val.symm y))
  have haeO : ∀ᵐ y ∂volume.restrict O,
      chartFunction v e y + (σ y : EReal) ≤ chartFunction w e y + (σ y : EReal) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall haeK]
      with y hy
    exact add_le_add_left hy _
  have hzO : z ∈ O := mem_ball_self (half_pos hε)
  have hlocal := (hpvV.mono hOV).le_of_ae_le isOpen_ball
    (hpwV.mono hOV).upperSemicontinuousOn volume haeO z hzO
  have hraw := (EReal.addLECancellable_coe (σ z)).add_le_add_iff_right.mp hlocal
  simpa [e, z, chartFunction, e.val.left_inv hxsource] using hraw

end SGPT.Foundations.Analysis.Pending.ThetaPshL1Order

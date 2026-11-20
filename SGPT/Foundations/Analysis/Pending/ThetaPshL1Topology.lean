import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

/-!
# The genuine chart-local L¹ topology on theta-PSH potentials

Each theta-PSH potential determines an element of L¹ on every compact chart
set. Its chart representative is almost everywhere finite and integrable;
therefore taking `EReal.toReal` does not alter its L¹ class. We induce the
topology from the product of these genuine L¹ spaces and prove that arbitrary
filter convergence is exactly `ManifoldL1LocallyTendsto`.

This topology is regular, so closures of compact families are compact. No
metric is postulated and no boundedness or positive-dimension hypothesis is
needed. On a compact manifold the global-volume equivalence is supplied
separately by `Pending.ChartwiseGlobalL1`.
-/

open Set Filter MeasureTheory Topology
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology

open FirstPass

noncomputable section

/-- A holomorphic chart together with a compact set inside its target. -/
def CompactChartSet (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] :=
  {q : ComplexChart n M × Set (ComplexModel n) //
    IsCompact q.2 ∧ q.2 ⊆ q.1.val.target}

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual theta-PSH potentials, carrying their chart-local L¹ topology. -/
def ThetaPshL1 (θ : SmoothRealForm n M 2) :=
  {u : M → EReal // IsThetaPshPotential θ u}

variable {θ : SmoothRealForm n M 2}

/-- The genuine L¹ class of a potential on a compact chart set. -/
def chartLp (u : ThetaPshL1 θ) (q : CompactChartSet n M) :
    Lp ℝ 1 (volume.restrict q.1.2) :=
  (memLp_one_iff_integrable.mpr
    (u.2.quasiPshPotential.integrableOn_chart_toReal q.1.1 q.2.1 q.2.2)).toLp
      (fun z => (chartFunction u.1 q.1.1 z).toReal)

/-- The L¹ distance of the chart classes is exactly the canonical extended-real
chart distance: the pole sets have zero Lebesgue measure. -/
@[simp] theorem edist_chartLp (u v : ThetaPshL1 θ) (q : CompactChartSet n M) :
    edist (chartLp u q) (chartLp v q) = chartL1EDistance u.1 v.1 q.1.1 q.1.2 := by
  rw [chartLp, chartLp, Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm,
    chartL1EDistance]
  apply lintegral_congr_ae
  have hu := ae_restrict_of_ae_restrict_of_subset q.2.2
    (u.2.quasiPshPotential.ae_finite_chart q.1.1)
  have hv := ae_restrict_of_ae_restrict_of_subset q.2.2
    (v.2.quasiPshPotential.ae_finite_chart q.1.1)
  filter_upwards [hu, hv] with z huz hvz
  conv_rhs =>
    rw [← EReal.coe_toReal huz.1 huz.2, ← EReal.coe_toReal hvz.1 hvz.2,
      canonicalERealAbsDiff_coe_coe]
  simp only [Pi.sub_apply, Real.enorm_eq_ofReal_abs]

/-- All compact-chart L¹ classes of a potential, as a point of a product of
actual L¹ spaces. -/
def chartLpFamily (u : ThetaPshL1 θ) :
    (q : CompactChartSet n M) → Lp ℝ 1 (volume.restrict q.1.2) :=
  chartLp u

instance : TopologicalSpace (ThetaPshL1 θ) :=
  TopologicalSpace.induced chartLpFamily inferInstance

/-- The chart-family map induces the L¹ topology on theta-PSH potentials. -/
theorem isInducing_chartLpFamily : IsInducing (chartLpFamily (θ := θ)) :=
  IsInducing.induced _

instance : RegularSpace (ThetaPshL1 θ) :=
  isInducing_chartLpFamily.regularSpace

/-- Topological convergence in the chart-local L¹ space is precisely the
project's canonical chartwise convergence, for every indexing filter. -/
theorem tendsto_iff_manifoldL1LocallyTendsto {α : Type*} {l : Filter α}
    {u : α → ThetaPshL1 θ} {v : ThetaPshL1 θ} :
    Tendsto u l (𝓝 v) ↔
      ManifoldL1LocallyTendsto (n := n) (fun i => (u i).1) l v.1 := by
  rw [isInducing_chartLpFamily.tendsto_nhds_iff, tendsto_pi_nhds]
  constructor
  · intro h e K hK hKe
    have hq := h (⟨(e, K), hK, hKe⟩ : CompactChartSet n M)
    exact (tendsto_iff_edist_tendsto_0.mp hq).congr
      (fun i => edist_chartLp (u i) v ⟨(e, K), hK, hKe⟩)
  · intro h q
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [Function.comp_apply, chartLpFamily, edist_chartLp] using
      h q.1.1 q.1.2 q.2.1 q.2.2

end

end SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology

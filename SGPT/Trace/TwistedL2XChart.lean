import SGPT.Trace.TwistedL2XFlat
import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood

/-!
# Atlas charts and chart densities on a complex manifold

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:charts`).  For two atlas charts
`c, c'` of a complex manifold `X` the coordinate change `chg c c' = c' ∘ c⁻¹` is holomorphic on the
overlap `ovl c c' = c(c.source ∩ c'.source)` (TN `differentiableOn_chartTransition`), its complex
derivatives satisfy the chain rule on triple overlaps (`fderiv_chg_comp`) and are invertible
(`isUnit_linMat_fderiv_chg`).  A smooth positive volume has a unique density in each chart
(`isChartDensity_eqOn`), chosen once and for all (`chartDensity`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff ComplexConjugate Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Coordinate changes -/

/-- The coordinate change `c' ∘ c⁻¹` from `c`-coordinates to `c'`-coordinates. -/
def chg (c c' : ComplexChart n X) (z : ComplexModel n) : ComplexModel n := c'.val (c.val.symm z)

/-- The overlap `c(c.source ∩ c'.source)` in `c`-coordinates. -/
def ovl (c c' : ComplexChart n X) : Set (ComplexModel n) :=
  c.val.target ∩ c.val.symm ⁻¹' c'.val.source

theorem ovl_eq_source (c c' : ComplexChart n X) : ovl c c' = (chartTransition c c').source := by
  simp [ovl, chartTransition]

theorem isOpen_ovl (c c' : ComplexChart n X) : IsOpen (ovl c c') := by
  rw [ovl_eq_source]; exact (chartTransition c c').open_source

theorem chg_eq (c c' : ComplexChart n X) : chg c c' = chartTransition c c' := by
  funext z; simp [chg, chartTransition]

theorem differentiableOn_chg (c c' : ComplexChart n X) :
    DifferentiableOn ℂ (chg c c') (ovl c c') := by
  rw [chg_eq, ovl_eq_source]; exact RegularPatchNeighborhood.differentiableOn_chartTransition c c'

theorem differentiableAt_chg {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    DifferentiableAt ℂ (chg c c') z :=
  (differentiableOn_chg c c').differentiableAt ((isOpen_ovl c c').mem_nhds hz)

theorem mem_ovl_iff {c c' : ComplexChart n X} {z : ComplexModel n} :
    z ∈ ovl c c' ↔ z ∈ c.val.target ∧ c.val.symm z ∈ c'.val.source := Iff.rfl

theorem chg_apply_chart {c c' : ComplexChart n X} {x : X} :
    chg c c' (c.val x) = c'.val (c.val.symm (c.val x)) := rfl

theorem chg_chart {c c' : ComplexChart n X} {x : X} (hx : x ∈ c.val.source) :
    chg c c' (c.val x) = c'.val x := by
  simp [chg, c.val.left_inv hx]

theorem chart_mem_ovl {c c' : ComplexChart n X} {x : X} (hx : x ∈ c.val.source)
    (hx' : x ∈ c'.val.source) : c.val x ∈ ovl c c' :=
  ⟨c.val.map_source hx, by simp only [mem_preimage]; rw [c.val.left_inv hx]; exact hx'⟩

theorem symm_chg {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    c'.val.symm (chg c c' z) = c.val.symm z :=
  c'.val.left_inv hz.2

theorem chg_mem_ovl {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    chg c c' z ∈ ovl c' c :=
  ⟨c'.val.map_source hz.2, by simp only [mem_preimage]; rw [symm_chg hz]; exact c.val.map_target hz.1⟩

theorem chg_chg {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    chg c' c (chg c c' z) = z := by
  simp only [chg]
  rw [c'.val.left_inv hz.2, c.val.right_inv hz.1]

/-- `chg c c''` is `chg c' c'' ∘ chg c c'` near a point of the triple overlap. -/
theorem chg_eventuallyEq_comp {c c' c'' : ComplexChart n X} {z : ComplexModel n}
    (hz : z ∈ ovl c c') : chg c c'' =ᶠ[𝓝 z] fun y => chg c' c'' (chg c c' y) := by
  filter_upwards [(isOpen_ovl c c').mem_nhds hz] with y hy
  simp only [chg]
  rw [c'.val.left_inv hy.2]

/-- **Chain rule on triple overlaps.** -/
theorem fderiv_chg_comp {c c' c'' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c')
    (hz' : c.val.symm z ∈ c''.val.source) :
    fderiv ℂ (chg c c'') z = (fderiv ℂ (chg c' c'') (chg c c' z)).comp (fderiv ℂ (chg c c') z) := by
  have h2 : chg c c' z ∈ ovl c' c'' :=
    ⟨c'.val.map_source hz.2, by simp only [mem_preimage]; rw [symm_chg hz]; exact hz'⟩
  rw [(chg_eventuallyEq_comp (c'' := c'') hz).fderiv_eq]
  exact fderiv_comp z (differentiableAt_chg h2) (differentiableAt_chg hz)

theorem chg_self_eventuallyEq {c : ComplexChart n X} {z : ComplexModel n}
    (hz : z ∈ c.val.target) : chg c c =ᶠ[𝓝 z] id := by
  filter_upwards [c.val.open_target.mem_nhds hz] with y hy
  exact c.val.right_inv hy

theorem fderiv_chg_self {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target) :
    fderiv ℂ (chg c c) z = ContinuousLinearMap.id ℂ (ComplexModel n) := by
  rw [(chg_self_eventuallyEq hz).fderiv_eq, fderiv_id]

theorem mem_ovl_self {c : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ c.val.target) :
    z ∈ ovl c c :=
  ⟨hz, c.val.map_target hz⟩

/-- The derivative of a coordinate change is invertible. -/
theorem isUnit_linMat_fderiv_chg {c c' : ComplexChart n X} {z : ComplexModel n}
    (hz : z ∈ ovl c c') : IsUnit (linMat (fderiv ℂ (chg c c') z)) := by
  have h := fderiv_chg_comp (c'' := c) hz (c.val.map_target hz.1)
  rw [fderiv_chg_self hz.1] at h
  have h1 := congrArg linMat h
  rw [linMat_id, linMat_comp] at h1
  exact (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_left_inverse h1.symm)

theorem fderiv_chg_inv_apply {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c')
    (v : ComplexModel n) :
    fderiv ℂ (chg c' c) (chg c c' z) (fderiv ℂ (chg c c') z v) = v := by
  have h := fderiv_chg_comp (c'' := c) hz (c.val.map_target hz.1)
  rw [fderiv_chg_self hz.1] at h
  have := congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L v) h
  simpa using this.symm

/-! ### Chart densities -/

section Density

variable [MeasurableSpace X] [BorelSpace X]

/-- **Uniqueness of chart densities**: two continuous densities of `μ` in the same chart agree on
the chart target. -/
theorem isChartDensity_eqOn {μ : Measure X} {c : ComplexChart n X} {ρ ρ' : ComplexModel n → ℝ}
    (h : IsChartDensity μ c ρ) (h' : IsChartDensity μ c ρ') : EqOn ρ ρ' c.val.target := by
  have hm : MeasurableSet c.val.target := c.val.open_target.measurableSet
  have hc := h.1.continuousOn
  have hc' := h'.1.continuousOn
  have heq : (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)) =
      (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ' z)) :=
    h.2.2.symm.trans h'.2.2
  have hae : (fun z => ENNReal.ofReal (ρ z)) =ᵐ[volume.restrict c.val.target]
      fun z => ENNReal.ofReal (ρ' z) :=
    (withDensity_eq_iff_of_sigmaFinite
      ((ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hm)
      ((ENNReal.continuous_ofReal.comp_continuousOn hc').aemeasurable hm)).mp heq
  have hae' : ρ =ᵐ[volume.restrict c.val.target] ρ' := by
    filter_upwards [hae, ae_restrict_mem hm] with z hz hzt
    exact (ENNReal.ofReal_eq_ofReal_iff (h.2.1 z hzt).le (h'.2.1 z hzt).le).mp hz
  exact Measure.eqOn_open_of_ae_eq hae' c.val.open_target hc hc'

variable (n) in
theorem exists_isChartDensity {μ : Measure X}
    (hμ : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := n) μ)
    (c : ComplexChart n X) : ∃ ρ : ComplexModel n → ℝ, IsChartDensity μ c ρ :=
  hμ c

end Density

end SGPT.Trace.TwistedL2

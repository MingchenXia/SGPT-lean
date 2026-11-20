import SGPT.Foundations.Analysis.Pending.KahlerPerturbation
import SGPT.Foundations.Analysis.Pending.ComplexGeometry

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The largest relative eigenvalue of two positive `(1,1)`-forms attains its maximum

For two real two-forms `a, b` on a complex manifold `Y`, strictly positive on complex lines in every
chart, the ratio `b(v, iv) / a(v, iv)` does not depend on the chart: along a chart change both forms
transform by the same `ℂ`-linear isomorphism (`ratio_chart_transfer`), and it is invariant under real
rescaling of `v`. Hence `η(x) = max_{v ≠ 0} b(v, iv)/a(v, iv)` (the largest eigenvalue of `b`
relative to `a`) is chart independent, and for a continuous `f` on a compact `Y` the function
`log η + f` attains its maximum (`exists_max_log_ratio_add`): there are `y` and `M` with
`log (b(v,iv)/a(v,iv)) + f(x) ≤ M` in every chart, every `x` and every `v ≠ 0`, and in every chart at
`y` a unit vector `ζ` realising `M`.

This is the first step of Błocki's proof of the second-derivative estimate
(`lnm2038-monge-ampere:page-0222`: "η ... is independent of holomorphic change of coordinates, and
thus η is a continuous, positive, globally defined function on M ... we can find y ∈ M where α
attains maximum"). Here the maximum is taken over the compact set of pairs (point, unit vector) in
finitely many chart balls, so no continuity of `η` itself is needed.

TN.4 B5, nonlinear track N3.
-/

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.RelativeEigenvalueMax

open FirstPass

noncomputable section

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The pair `![v, i v]`. -/
abbrev line (v : ComplexModel N) : Fin 2 → ComplexModel N := ![v, Complex.I • v]

theorem mem_chartTransition_source {e f : ComplexChart N Y} {x : Y} (hxe : x ∈ e.val.source)
    (hxf : x ∈ f.val.source) : e.val x ∈ (chartTransition e f).source := by
  refine ⟨e.val.map_source hxe, ?_⟩
  show e.val.symm (e.val x) ∈ f.val.source
  rw [e.val.left_inv hxe]
  exact hxf

theorem chartTransition_apply_chart {e f : ComplexChart N Y} {x : Y} (hxe : x ∈ e.val.source) :
    chartTransition e f (e.val x) = f.val x := by
  show f.val (e.val.symm (e.val x)) = f.val x
  rw [e.val.left_inv hxe]

/-- A two-form evaluated on a complex line, transported along a chart change. -/
theorem coeff_line_transfer (a : SmoothRealForm N Y 2) {e f : ComplexChart N Y} {x : Y}
    (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source) (v : ComplexModel N) :
    a.coeff e (e.val x) (line v) =
      a.coeff f (f.val x) (line (chartTransitionDerivative e f (e.val x) v)) := by
  have hz := mem_chartTransition_source hxe hxf
  rw [a.compatible e f (e.val x) hz, chartTransition_apply_chart hxe]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact chartTransitionDerivative_complex_smul e f (e.val x) hz Complex.I v

/-- The chart-transition derivative is bijective. -/
theorem chartTransitionDerivative_bijective {e f : ComplexChart N Y} {x : Y}
    (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source) :
    Function.Bijective (chartTransitionDerivative e f (e.val x)) := by
  have hinj := KahlerPerturbation.chartTransitionDerivative_injective e f
    (mem_chartTransition_source hxe hxf)
  refine ⟨hinj, ?_⟩
  have := LinearMap.injective_iff_surjective (f := (chartTransitionDerivative e f (e.val x) :
    ComplexModel N →ₗ[ℝ] ComplexModel N))
  exact this.mp hinj

/-- Real homogeneity of degree two on complex lines. -/
theorem coeff_line_smul (β : (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) (t : ℝ) (v : ComplexModel N) :
    β (line (t • v)) = t ^ 2 * β (line v) := by
  have h : line (t • v) = fun i => (fun _ : Fin 2 => t) i • (line v) i := by
    funext i
    fin_cases i
    · rfl
    · exact smul_comm Complex.I t v
  rw [h, β.map_smul_univ]
  simp [Finset.prod_const, smul_eq_mul]

/-- The ratio is invariant under nonzero real rescaling. -/
theorem ratio_smul (a b : (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) {t : ℝ} (ht : t ≠ 0)
    (v : ComplexModel N) : b (line (t • v)) / a (line (t • v)) = b (line v) / a (line v) := by
  rw [coeff_line_smul, coeff_line_smul, mul_div_mul_left _ _ (pow_ne_zero 2 ht)]

/-- Normalising a nonzero vector. -/
theorem ratio_normalize (a b : (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) {v : ComplexModel N}
    (hv : v ≠ 0) :
    ‖‖v‖⁻¹ • v‖ = 1 ∧ b (line (‖v‖⁻¹ • v)) / a (line (‖v‖⁻¹ • v)) = b (line v) / a (line v) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨?_, ratio_smul a b (inv_ne_zero hn) v⟩
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

/-- The value of the ratio at `x` in a chart is realised in any other chart at `x`. -/
theorem ratio_chart_transfer (a b : SmoothRealForm N Y 2) {e f : ComplexChart N Y} {x : Y}
    (hxe : x ∈ e.val.source) (hxf : x ∈ f.val.source) {v : ComplexModel N} (hv : v ≠ 0) :
    ∃ w : ComplexModel N, ‖w‖ = 1 ∧
      b.coeff f (f.val x) (line w) / a.coeff f (f.val x) (line w) =
        b.coeff e (e.val x) (line v) / a.coeff e (e.val x) (line v) := by
  set T := chartTransitionDerivative e f (e.val x)
  have hTv : T v ≠ 0 := fun h => hv ((chartTransitionDerivative_bijective hxe hxf).1
    (h.trans (map_zero T).symm))
  obtain ⟨hw1, hw⟩ := ratio_normalize (a.coeff f (f.val x)) (b.coeff f (f.val x)) hTv
  refine ⟨‖T v‖⁻¹ • T v, hw1, ?_⟩
  rw [hw, coeff_line_transfer a hxe hxf, coeff_line_transfer b hxe hxf]

/-- **The maximum of `log η + f`** (`lnm2038-monge-ampere:page-0222`). -/
theorem exists_max_log_ratio_add [CompactSpace Y] [Nonempty Y] (hN : 0 < N)
    (a b : SmoothRealForm N Y 2)
    (ha : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v, v ≠ 0 → 0 < a.coeff e z (line v))
    (hb : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v, v ≠ 0 → 0 < b.coeff e z (line v))
    {f : Y → ℝ} (hf : Continuous f) :
    ∃ (y : Y) (M : ℝ),
      (∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ v, v ≠ 0 →
        Real.log (b.coeff e z (line v) / a.coeff e z (line v)) + f (e.val.symm z) ≤ M) ∧
      (∀ e : ComplexChart N Y, y ∈ e.val.source → ∃ ζ : ComplexModel N, ‖ζ‖ = 1 ∧
        Real.log (b.coeff e (e.val y) (line ζ) / a.coeff e (e.val y) (line ζ)) + f y = M) := by
  classical
  have hsph : (sphere (0 : ComplexModel N) 1).Nonempty := by
    have : Nontrivial (ComplexModel N) := by
      have : 0 < Module.finrank ℂ (ComplexModel N) := by
        rw [finrank_euclideanSpace, Fintype.card_fin]; exact hN
      exact Module.nontrivial_of_finrank_pos this
    exact NormedSpace.sphere_nonempty.mpr zero_le_one
  -- chart balls around every point
  have hball : ∀ p : Y, ∃ r > 0, closedBall ((complexChartAt (n := N) p).val p) r ⊆
      (complexChartAt (n := N) p).val.target := fun p => by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (complexChartAt (n := N) p).val.open_target
      _ ((complexChartAt (n := N) p).val.map_source (mem_complexChartAt_source p))
    exact ⟨r / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hsub⟩
  choose r hr hrt using hball
  set e : Y → ComplexChart N Y := fun p => complexChartAt (n := N) p with hedef
  set O : Y → Set Y := fun p => (e p).val.source ∩ (e p).val ⁻¹' ball ((e p).val p) (r p)
    with hOdef
  have hO : ∀ p, IsOpen (O p) := fun p =>
    (e p).val.isOpen_inter_preimage isOpen_ball
  have hpO : ∀ p, p ∈ O p := fun p =>
    ⟨mem_complexChartAt_source p, mem_ball_self (hr p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion.mpr ⟨p, hpO p⟩)
  -- the function on each compact piece
  set Ψ : Y → ComplexModel N × ComplexModel N → ℝ := fun p q =>
    Real.log (b.coeff (e p) q.1 (line q.2) / a.coeff (e p) q.1 (line q.2)) +
      f ((e p).val.symm q.1) with hΨdef
  set S : Y → Set (ComplexModel N × ComplexModel N) := fun p =>
    closedBall ((e p).val p) (r p) ×ˢ sphere 0 1 with hSdef
  have hSc : ∀ p, IsCompact (S p) := fun p => (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hSne : ∀ p, (S p).Nonempty := fun p =>
    (nonempty_closedBall.mpr (hr p).le).prod hsph
  have hΨc : ∀ p, ContinuousOn (Ψ p) (S p) := by
    intro p
    have hline : Continuous fun q : ComplexModel N × ComplexModel N => line q.2 := by
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact continuous_snd
      · exact continuous_snd.const_smul Complex.I
    have hcoef : ∀ β : SmoothRealForm N Y 2, ContinuousOn
        (fun q : ComplexModel N × ComplexModel N => β.coeff (e p) q.1 (line q.2)) (S p) := by
      intro β
      have h1 : ContinuousOn (fun q : ComplexModel N × ComplexModel N => β.coeff (e p) q.1) (S p) :=
        (β.smooth (e p)).continuousOn.comp continuous_fst.continuousOn fun q hq => hrt p hq.1
      have hev : Continuous (fun p : ((ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ) ×
          (Fin 2 → ComplexModel N) => p.1 p.2) := continuous_eval
      exact hev.comp_continuousOn (h1.prodMk hline.continuousOn)
    have hpos : ∀ q ∈ S p, 0 < a.coeff (e p) q.1 (line q.2) := fun q hq =>
      ha (e p) q.1 (hrt p hq.1) q.2 (ne_zero_of_mem_sphere one_ne_zero ⟨q.2, hq.2⟩)
    have hposb : ∀ q ∈ S p, 0 < b.coeff (e p) q.1 (line q.2) := fun q hq =>
      hb (e p) q.1 (hrt p hq.1) q.2 (ne_zero_of_mem_sphere one_ne_zero ⟨q.2, hq.2⟩)
    refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.log ((hcoef b).div (hcoef a) fun q hq => (hpos q hq).ne') fun q hq =>
        (div_pos (hposb q hq) (hpos q hq)).ne'
    · refine hf.comp_continuousOn ?_
      exact ((e p).val.continuousOn_symm.comp continuous_fst.continuousOn
        fun q hq => hrt p hq.1)
  choose q hqS hqmax using fun p => (hSc p).exists_isMaxOn (hSne p) (hΨc p)
  -- the best piece
  have htne : t.Nonempty := by
    obtain ⟨y₀⟩ := ‹Nonempty Y›
    have := ht (mem_univ y₀)
    rw [mem_iUnion₂] at this
    obtain ⟨p, hp, -⟩ := this
    exact ⟨p, hp⟩
  obtain ⟨p₀, hp₀t, hp₀max⟩ := t.exists_max_image (fun p => Ψ p (q p)) htne
  set M := Ψ p₀ (q p₀) with hMdef
  -- the upper bound in every chart
  have hbound : ∀ (e' : ComplexChart N Y) z, z ∈ e'.val.target → ∀ v, v ≠ 0 →
      Real.log (b.coeff e' z (line v) / a.coeff e' z (line v)) + f (e'.val.symm z) ≤ M := by
    intro e' z hz v hv
    set x := e'.val.symm z with hxdef
    have hxe' : x ∈ e'.val.source := e'.val.map_target hz
    have hzx : e'.val x = z := e'.val.right_inv hz
    obtain ⟨p, hpt, hxp⟩ : ∃ p ∈ t, x ∈ O p := by
      have := ht (mem_univ x)
      rw [mem_iUnion₂] at this
      obtain ⟨p, hp, hxp⟩ := this
      exact ⟨p, hp, hxp⟩
    obtain ⟨w, hw1, hw⟩ := ratio_chart_transfer a b hxe' hxp.1 hv
    have hmem : ((e p).val x, w) ∈ S p :=
      ⟨ball_subset_closedBall hxp.2, mem_sphere_zero_iff_norm.mpr hw1⟩
    have h1 : Ψ p ((e p).val x, w) ≤ Ψ p (q p) := hqmax p hmem
    have h2 : Ψ p (q p) ≤ M := hp₀max p hpt
    have h3 : Ψ p ((e p).val x, w) = Real.log (b.coeff (e p) ((e p).val x) (line w) /
        a.coeff (e p) ((e p).val x) (line w)) + f ((e p).val.symm ((e p).val x)) := rfl
    rw [hzx] at hw
    rw [hw, (e p).val.left_inv hxp.1] at h3
    linarith
  set y := (e p₀).val.symm (q p₀).1 with hydef
  have hyt : (q p₀).1 ∈ (e p₀).val.target := hrt p₀ (hqS p₀).1
  have hy : y ∈ (e p₀).val.source := (e p₀).val.map_target hyt
  have hey : (e p₀).val y = (q p₀).1 := (e p₀).val.right_inv hyt
  refine ⟨y, M, hbound, fun e' hye' => ?_⟩
  have hq2 : (q p₀).2 ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨(q p₀).2, (hqS p₀).2⟩
  obtain ⟨ζ, hζ1, hζ⟩ := ratio_chart_transfer a b hy hye' hq2
  refine ⟨ζ, hζ1, ?_⟩
  rw [hζ, hey]

end

end SGPT.Foundations.Analysis.Pending.RelativeEigenvalueMax

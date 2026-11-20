import SGPT.Foundations.Analysis.Pending.RelativeEigenvalueMax

/-!
# Maxima of chart-compatible functions on the unit sphere bundle

Lane TOS-C11c (`claude-tos-c11c`, node `tos-c11c:maximum`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Step 2 ("by compactness of `X` it attains its
maximum at some point `x₀`"), for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

FPT maximizes `Q = log ℓ + η(s) - A a`, where `ℓ(x)` is the largest eigenvalue of the covariant Hessian
`∇²a` relative to the metric.  As in TN's `exists_max_log_ratio_add` (Błocki's eigenvalue method) one
does not need the continuity of `ℓ`: it suffices to maximize a function of a point and a tangent vector
which is read in charts, continuous on `target × sphere`, invariant under nonzero real rescaling of the
vector and compatible with the chart transitions.  `exists_max_of_chartCompatible` gives a point `y` and
a value `M` with `q_e(z, v) ≤ M` in every chart and every `v ≠ 0`, attained at `y` in every chart.
For the quotient `∇²a(v, v)/g(v, v)` the transition compatibility is the tensoriality of the covariant
Hessian (`TosC11b.covHess_comp`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace SGPT.Envelopes.TosC11c

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **The maximum of a chart-compatible function on the unit sphere bundle.**  Let `q_e(z, v)` be given
for every chart `e`, continuous on `target(e) × sphere(0, 1)`, invariant under `v ↦ t v` (`t ≠ 0`,
`z` in the target) and
compatible with the transitions: `q_e(e x, v) = q_f(f x, D(f ∘ e⁻¹)(e x) v)`.  On a compact nonempty
manifold of positive dimension there are `y` and `M` with `q_e(z, v) ≤ M` for every chart, every point
of its target and every `v ≠ 0`, and with `q_e(e y, ζ) = M` for a unit vector `ζ`, in every chart at
`y`. -/
theorem exists_max_of_chartCompatible [CompactSpace Y] [Nonempty Y] (hN : 0 < N)
    (q : ComplexChart N Y → ComplexModel N → ComplexModel N → ℝ)
    (hcont : ∀ e : ComplexChart N Y, ContinuousOn (fun p : ComplexModel N × ComplexModel N =>
      q e p.1 p.2) (e.val.target ×ˢ sphere 0 1))
    (hhom : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ (v : ComplexModel N) (t : ℝ), t ≠ 0 → q e z (t • v) = q e z v)
    (htr : ∀ (e f : ComplexChart N Y) (x : Y), x ∈ e.val.source → x ∈ f.val.source →
      ∀ v, q e (e.val x) v = q f (f.val x) (chartTransitionDerivative e f (e.val x) v)) :
    ∃ (y : Y) (M : ℝ),
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v, v ≠ 0 →
        q e z v ≤ M) ∧
      ∀ e : ComplexChart N Y, y ∈ e.val.source → ∃ ζ : ComplexModel N, ‖ζ‖ = 1 ∧
        q e (e.val y) ζ = M := by
  classical
  have hsph : (sphere (0 : ComplexModel N) 1).Nonempty := by
    have : Nontrivial (ComplexModel N) := by
      have : 0 < Module.finrank ℂ (ComplexModel N) := by
        rw [finrank_euclideanSpace, Fintype.card_fin]; exact hN
      exact Module.nontrivial_of_finrank_pos this
    exact NormedSpace.sphere_nonempty.mpr zero_le_one
  -- normalising a vector, and the transfer of values between charts
  have hnorm : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → ∀ (v : ComplexModel N), v ≠ 0 →
      ‖‖v‖⁻¹ • v‖ = 1 ∧ q e z (‖v‖⁻¹ • v) = q e z v := fun e z hz v hv => by
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨?_, hhom e z hz v _ (inv_ne_zero hn)⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have htransfer : ∀ (e f : ComplexChart N Y) (x : Y), x ∈ e.val.source → x ∈ f.val.source →
      ∀ v, v ≠ 0 → ∃ w : ComplexModel N, ‖w‖ = 1 ∧ q f (f.val x) w = q e (e.val x) v := by
    intro e f x hxe hxf v hv
    set T := chartTransitionDerivative e f (e.val x)
    have hTv : T v ≠ 0 := fun h => hv
      ((Pending.RelativeEigenvalueMax.chartTransitionDerivative_bijective hxe hxf).1
        (h.trans (map_zero T).symm))
    obtain ⟨hw1, hw⟩ := hnorm f (f.val x) (f.val.map_source hxf) (T v) hTv
    exact ⟨‖T v‖⁻¹ • T v, hw1, by rw [hw, htr e f x hxe hxf v]⟩
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
  have hO : ∀ p, IsOpen (O p) := fun p => (e p).val.isOpen_inter_preimage isOpen_ball
  have hpO : ∀ p, p ∈ O p := fun p => ⟨mem_complexChartAt_source p, mem_ball_self (hr p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion.mpr ⟨p, hpO p⟩)
  set Ψ : Y → ComplexModel N × ComplexModel N → ℝ := fun p w => q (e p) w.1 w.2 with hΨdef
  set S : Y → Set (ComplexModel N × ComplexModel N) := fun p =>
    closedBall ((e p).val p) (r p) ×ˢ sphere 0 1 with hSdef
  have hSc : ∀ p, IsCompact (S p) := fun p => (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hSne : ∀ p, (S p).Nonempty := fun p => (nonempty_closedBall.mpr (hr p).le).prod hsph
  have hΨc : ∀ p, ContinuousOn (Ψ p) (S p) := fun p =>
    (hcont (e p)).mono (prod_mono (hrt p) subset_rfl)
  choose w hwS hwmax using fun p => (hSc p).exists_isMaxOn (hSne p) (hΨc p)
  have htne : t.Nonempty := by
    obtain ⟨y₀⟩ := ‹Nonempty Y›
    have := ht (mem_univ y₀)
    rw [mem_iUnion₂] at this
    obtain ⟨p, hp, -⟩ := this
    exact ⟨p, hp⟩
  obtain ⟨p₀, hp₀t, hp₀max⟩ := t.exists_max_image (fun p => Ψ p (w p)) htne
  set M := Ψ p₀ (w p₀) with hMdef
  have hbound : ∀ (e' : ComplexChart N Y) (z : ComplexModel N), z ∈ e'.val.target → ∀ v, v ≠ 0 →
      q e' z v ≤ M := by
    intro e' z hz v hv
    set x := e'.val.symm z with hxdef
    have hxe' : x ∈ e'.val.source := e'.val.map_target hz
    have hzx : e'.val x = z := e'.val.right_inv hz
    obtain ⟨p, hpt, hxp⟩ : ∃ p ∈ t, x ∈ O p := by
      have := ht (mem_univ x)
      rw [mem_iUnion₂] at this
      obtain ⟨p, hp, hxp⟩ := this
      exact ⟨p, hp, hxp⟩
    obtain ⟨w', hw1, hw⟩ := htransfer e' (e p) x hxe' hxp.1 v hv
    have hmem : ((e p).val x, w') ∈ S p :=
      ⟨ball_subset_closedBall hxp.2, mem_sphere_zero_iff_norm.mpr hw1⟩
    have h1 : Ψ p ((e p).val x, w') ≤ Ψ p (w p) := hwmax p hmem
    have h2 : Ψ p (w p) ≤ M := hp₀max p hpt
    have h3 : Ψ p ((e p).val x, w') = q e' z v := by
      simp only [hΨdef]; rw [hw, hzx]
    linarith
  set y := (e p₀).val.symm (w p₀).1 with hydef
  have hyt : (w p₀).1 ∈ (e p₀).val.target := hrt p₀ (hwS p₀).1
  have hy : y ∈ (e p₀).val.source := (e p₀).val.map_target hyt
  have hey : (e p₀).val y = (w p₀).1 := (e p₀).val.right_inv hyt
  refine ⟨y, M, hbound, fun e' hye' => ?_⟩
  have hw2 : (w p₀).2 ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨(w p₀).2, (hwS p₀).2⟩
  obtain ⟨ζ, hζ1, hζ⟩ := htransfer (e p₀) e' y hy hye' (w p₀).2 hw2
  refine ⟨ζ, hζ1, ?_⟩
  rw [hζ, hey]

end SGPT.Envelopes.TosC11c

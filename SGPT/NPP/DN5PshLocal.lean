import SGPT.NPP.DN5PshLarge
import SGPT.NPP.DN5Interface

/-!
# The `psh` clauses at small radii, from the chart-level estimate

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Steps 2–6, "All bounds are uniform over the
centers, because the constructions are made in the charts of a fixed finite atlas").

Near every point `x` (chart `e` at `x`, a local potential `ρ` of `θ` on `W ∋ e x` with `u + ρ`
plurisubharmonic, compact balls `K ⊂ K' ⊂ W`, a tube `K' × B̄(0, R)` inside the domain where
`e ∘ F` is a local fibre map), the chart smoothing of `u` *is* the chart-level smoothing
`localSmoothing` of `u ∘ e⁻¹` along `Φ = e ∘ F` for radii `< r_b` (`bridge`).  The chart-level
estimate `SGPT.NPP.DN5.LocalJointEstimate` then gives the four `psh` clauses at the
points of a neighbourhood of `x` and radii `< r_s`, for all larger constants `K, A, C, C₁`
(`psh_local`); the joint Levi bound passes to every chart and potential by
`SGPT.NPP.DN5.jointLeviLowerBound_of_chart`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending IntegrationCurrent
open SGPT.NPP.DN2

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A tube around a compact part of the zero section inside the domain where `F` is good. -/
theorem exists_tube_goodSet (A : FibreAtlas N Y) {e : ComplexChart N Y}
    {Q : Set (ComplexModel N)} (hQ : IsCompact Q) (hQt : Q ⊆ e.val.target) :
    ∃ R > 0, Q ×ˢ closedBall (0 : ComplexModel N) R ⊆ goodSet A e := by
  have hsub : Q ×ˢ ({0} : Set (ComplexModel N)) ⊆ goodSet A e := by
    rintro ⟨z, ξ⟩ ⟨hz, hξ⟩
    rw [mem_singleton_iff] at hξ
    subst hξ
    exact mem_goodSet_of_mem_target A (hQt hz)
  obtain ⟨U, V, -, hV, hQU, h0V, hUV⟩ :=
    generalized_tube_lemma hQ isCompact_singleton (isOpen_goodSet A e) hsub
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV 0 (h0V rfl)
  refine ⟨R / 2, by linarith, fun q hq => hUV ⟨hQU hq.1, hRV ?_⟩⟩
  exact closedBall_subset_ball (by linarith) hq.2

/-- The support of the weight is bounded on a compact part of a chart. -/
theorem exists_fibreWeight_support_bound_compact (wY : KahlerBackground N Y)
    {e : ComplexChart N Y} {Q : Set (ComplexModel N)} (hQ : IsCompact Q)
    (hQt : Q ⊆ e.val.target) :
    ∃ Rw ≥ 0, ∀ z ∈ Q, ∀ ξ, fibreWeight wY e z ξ ≠ 0 → ‖ξ‖ ≤ Rw := by
  obtain ⟨m, hm, hmQ⟩ := exists_pos_le_chartNormSq wY e hQ hQt
  refine ⟨1 + (Real.pi * m)⁻¹, by positivity, fun z hz ξ hξ => ?_⟩
  have hlt : fibreNormSq wY e z ξ < 1 := by
    by_contra h
    exact hξ (DN3.chi_eq_zero_of_le N (not_lt.mp h))
  have hle := hmQ z hz ξ
  have hpm : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  have h2 : Real.pi * m * ‖ξ‖ ^ 2 < 1 := by
    unfold fibreNormSq at hlt
    nlinarith [Real.pi_pos]
  have h3 : ‖ξ‖ ^ 2 ≤ (Real.pi * m)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpm]
    linarith
  nlinarith [sq_nonneg (‖ξ‖ - 1)]

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

variable {wY : KahlerBackground N Y} {A : FibreAtlas N Y} {r₁ : ℝ}

/-- **The `psh` clauses at small radii near a point**, from the chart-level estimate. -/
theorem psh_local (hloc : LocalJointEstimate N) (hr : IsUniformRadius wY A r₁)
    (θ : ClosedRealOneOneForm N Y) {u : Y → EReal} (hu : IsThetaPshPotential θ.val u) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hr₀₁ : r₀ < r₁) (x : Y) :
    ∃ V : Set Y, IsOpen V ∧ x ∈ V ∧ ∃ rs K₀ A₀ C₀ C₁₀ : ℝ, 0 < rs ∧ rs ≤ r₀ ∧ 0 ≤ K₀ ∧
      0 ≤ A₀ ∧ 0 ≤ C₀ ∧ 0 < C₁₀ ∧
      1 ≤ C₁₀ ∧ ∀ K Ac C C₁ : ℝ, K₀ ≤ K → A₀ ≤ Ac → C₀ ≤ C → C₁₀ ≤ C₁ →
        let H := correctedSmoothing (smoothing wY A) u K
        ∀ y ∈ V,
          (∀ t : ℝ, 0 < t → t < rs → u y ≤ ((H y t : ℝ) : EReal)) ∧
          (∀ s : ℝ, s < Real.log rs →
            0 ≤ deriv (fun s => H y (Real.exp s)) s ∧
            0 < deriv (deriv (fun s => H y (Real.exp s))) s) ∧
          (∀ (e' : ComplexChart N Y) (z' : ComplexModel N), z' ∈ e'.val.target →
            e'.val.symm z' = y → ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < rs →
              JointLeviLowerBound θ wY H e' z' w (Ac * logSlope H y ‖w‖ + C * ‖w‖) C C) ∧
          (∀ a : ℝ, u y = (a : EReal) → ∀ L : ℝ, 0 ≤ L → ∀ r : ℝ, 0 < r → C₁ * r < rs →
            (∀ t : ℝ, 0 < t → t ≤ C₁ * r → H y t ≤ a + L * t) →
            ∀ (e' : ComplexChart N Y) (z' : ComplexModel N), z' ∈ e'.val.target →
              e'.val.symm z' = y → ∀ w : ℂ, ‖w‖ = r →
                JointLeviLowerBound θ wY H e' z' w
                  (Ac * logSlope H y r + C * (1 + L) * r ^ 2) (C * (1 + L) * r)
                  (C * (1 + L) * r)) := by
  set g : Y → ℝ := fun y => (u y).toReal with hgdef
  have hg : Integrable g (kahlerVolume wY) :=
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh (kahlerVolume wY)
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume wY) θ.val u hu
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ := e.val x
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hu.1 e z₀ hz₀
  have hWt : W ⊆ e.val.target := hρ.2.1
  obtain ⟨b3, hb3, hb3W⟩ := Metric.isOpen_iff.mp hρ.1 z₀ hz₀W
  set b := b3 / 4 with hbdef
  have hb : 0 < b := by positivity
  set Kc := closedBall z₀ b
  set Kc' := closedBall z₀ (2 * b)
  have hKc'W : Kc' ⊆ W := (closedBall_subset_ball (by linarith [hbdef])).trans hb3W
  have hKc't : Kc' ⊆ e.val.target := hKc'W.trans hWt
  have hKcKc' : Kc ⊆ interior Kc' :=
    (closedBall_subset_ball (by linarith)).trans ball_subset_interior_closedBall
  obtain ⟨R, hR, hRsub⟩ := exists_tube_goodSet A (isCompact_closedBall z₀ (2 * b)) hKc't
  obtain ⟨Rw, hRw0, hRw⟩ :=
    exists_fibreWeight_support_bound_compact wY (isCompact_closedBall z₀ (2 * b)) hKc't
  set rb := R / (Rw + 1)
  have hrb : 0 < rb := div_pos hR (by linarith)
  set Φ : ComplexModel N → ComplexModel N → ComplexModel N := fun z ξ => e.val (fibreMap A e z ξ)
  set α := wY.form.val.coeff e
  set ue : ComplexModel N → EReal := chartFunction u e
  -- the bridge
  have hbridge : ∀ z ∈ Kc', ∀ t : ℝ, 0 < t → t < rb →
      smoothing wY A g (e.val.symm z) t = localSmoothing Φ α (fun y => (ue y).toReal) z t := by
    intro z hz t ht htb
    rw [smoothing_eq_chartSmoothing_symm A (hKc't hz)]
    refine chartSmoothing_eq_localSmoothing A g t fun ξ hξ => ?_
    have hξR := hRw z hz ξ hξ
    have htξ : ‖t • ξ‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have h1 : t * (Rw + 1) < R := (lt_div_iff₀ (by linarith)).mp htb
      nlinarith [norm_nonneg ξ]
    have hmem : (z, t • ξ) ∈ goodSet A e :=
      hRsub ⟨hz, by rw [mem_closedBall, dist_zero_right]; exact htξ⟩
    exact (goodSet_target A hmem).2
  -- local nondegeneracy of `u ∘ e⁻¹` on `W` (from `LocallyNondegenerate u`; lane DN9)
  have hne : ∀ x ∈ W, ∀ V : Set (ComplexModel N), IsOpen V → x ∈ V → ∃ y ∈ V, ue y ≠ ⊥ := by
    intro x hx V hV hxV
    obtain ⟨y', hy', hy'u⟩ := hu.2 (e.val.symm x) (e.val.source ∩ e.val ⁻¹' V)
      (e.val.isOpen_inter_preimage hV) ⟨e.val.map_target (hWt hx), by
        simp only [mem_preimage]; rw [e.val.right_inv (hWt hx)]; exact hxV⟩
    refine ⟨e.val y', hy'.2, ?_⟩
    change u (e.val.symm (e.val y')) ≠ ⊥
    rw [e.val.left_inv hy'.1]
    exact hy'u
  -- the chart-level estimate
  obtain ⟨r₁', K₀', A₀', C₀', C₁', hr₁', hK₀', hA₀', hC₀', hC₁', hcl⟩ :=
    hloc Φ (goodSet A e) α W Kc Kc' R ρ ue (isLocalFibreMap_goodSet A e) hρ.1
      (isCompact_closedBall _ _) hKcKc' hKc'W hR hRsub ((wY.form.val.smooth e).mono hWt)
      (fun z hz => wY.isKahler.2 e z (hWt hz)) (fun z hz => wY.isKahler.1 e z (hWt hz))
      hρ.2.2.1 hpsh hne
  set rs := min (min r₁' rb) r₀
  have hrs : 0 < rs := lt_min (lt_min hr₁' hrb) hr₀
  have hrs₁ : rs ≤ r₁' := (min_le_left _ _).trans (min_le_left _ _)
  have hrsb : rs ≤ rb := (min_le_left _ _).trans (min_le_right _ _)
  have hrs₀ : rs ≤ r₀ := min_le_right _ _
  refine ⟨e.val.source ∩ e.val ⁻¹' ball z₀ b, e.val.isOpen_inter_preimage isOpen_ball,
    ⟨hx, mem_ball_self hb⟩, rs, K₀', A₀', C₀', max C₁' 1, hrs, hrs₀, hK₀', hA₀', hC₀',
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_max_right _ _, ?_⟩
  intro K Ac C C₁ hK hA hC hC₁ H y hy
  set z := e.val y
  have hzb : z ∈ ball z₀ b := hy.2
  have hzK : z ∈ Kc := ball_subset_closedBall hzb
  have hzK' : z ∈ Kc' := closedBall_subset_closedBall (by linarith) hzK
  have hzt : z ∈ e.val.target := hKc't hzK'
  have hyz : e.val.symm z = y := e.val.left_inv hy.1
  have huy : ue z = u y := by simp only [ue, chartFunction, hyz]
  obtain ⟨cla, clb, clc, cld⟩ := hcl z hzK
  have hKK : 0 ≤ K - K₀' := by linarith
  -- the identity between the global and the chart-level corrected smoothings
  have hident : ∀ z' ∈ Kc', ∀ t : ℝ, 0 < t → t < rb →
      H (e.val.symm z') t = localCorrected Φ α ue K₀' z' t + (K - K₀') * t ^ 2 := by
    intro z' hz' t ht htb
    change smoothing wY A g (e.val.symm z') t + K * t ^ 2 = _
    rw [hbridge z' hz' t ht htb, localCorrected]
    ring
  have hidenty : ∀ t : ℝ, 0 < t → t < rb →
      H y t = localCorrected Φ α ue K₀' z t + (K - K₀') * t ^ 2 := by
    intro t ht htb
    rw [← hyz]
    exact hident z hzK' t ht htb
  -- log-radius calculus
  set φ := fun s => smoothing wY A g y (Real.exp s)
  have hφ : ContDiffOn ℝ ∞ φ (Iio (Real.log r₁)) := contDiffOn_smoothing_logRadius hr hg y
  have hlogrs : Real.log rs < Real.log r₁ :=
    Real.log_lt_log hrs (hrs₀.trans_lt hr₀₁)
  have hHexp : ∀ K' : ℝ, (fun s => correctedSmoothing (smoothing wY A) u K' y (Real.exp s)) =
      fun s => φ s + K' * Real.exp s ^ 2 := fun K' => rfl
  -- the log-radius clause
  have hlocφ : ∀ s : ℝ, s < Real.log rs →
      localCorrected Φ α ue K₀' z (Real.exp s) = φ s + K₀' * Real.exp s ^ 2 := by
    intro s hs
    have hexp : Real.exp s < rs := by
      calc Real.exp s < Real.exp (Real.log rs) := Real.exp_lt_exp.mpr hs
        _ = rs := Real.exp_log hrs
    have h := hidenty (Real.exp s) (Real.exp_pos s) (hexp.trans_le hrsb)
    have h2 : H y (Real.exp s) = φ s + K * Real.exp s ^ 2 := rfl
    linarith
  have hevloc : ∀ s : ℝ, s < Real.log rs →
      (fun s => localCorrected Φ α ue K₀' z (Real.exp s)) =ᶠ[𝓝 s]
        fun s => φ s + K₀' * Real.exp s ^ 2 := by
    intro s hs
    filter_upwards [isOpen_Iio.mem_nhds hs] with s' hs'
    exact hlocφ s' hs'
  have hb_all : ∀ s : ℝ, s < Real.log rs →
      0 ≤ deriv (fun s => H y (Real.exp s)) s ∧
        0 < deriv (deriv (fun s => H y (Real.exp s))) s := by
    intro s hs
    have hsS : s ∈ Iio (Real.log r₁) := lt_trans hs hlogrs
    obtain ⟨d1K, d2K⟩ := deriv_add_sq_exp isOpen_Iio hφ hsS K
    obtain ⟨d1K0, d2K0⟩ := deriv_add_sq_exp isOpen_Iio hφ hsS K₀'
    obtain ⟨lb1, lb2⟩ := clb s (lt_of_lt_of_le hs (Real.log_le_log hrs hrs₁))
    have hev := hevloc s hs
    rw [hev.deriv_eq, d1K0] at lb1
    rw [hev.deriv.deriv_eq, d2K0] at lb2
    have he : 0 ≤ Real.exp s ^ 2 := sq_nonneg _
    have hKe : 0 ≤ (K - K₀') * Real.exp s ^ 2 := mul_nonneg hKK he
    refine ⟨?_, ?_⟩
    · change 0 ≤ deriv (fun s => φ s + K * Real.exp s ^ 2) s
      rw [d1K]
      linarith
    · change 0 < deriv (deriv (fun s => φ s + K * Real.exp s ^ 2)) s
      rw [d2K]
      linarith
  -- slopes
  have hslope : ∀ t : ℝ, 0 < t → t < rs →
      logSlope H y t = t * deriv (localCorrected Φ α ue K₀' z) t + 2 * (K - K₀') * t ^ 2 ∧
        0 ≤ logSlope H y t := by
    intro t ht htrs
    have hev : localCorrected Φ α ue K₀' z =ᶠ[𝓝 t] fun t' => H y t' - (K - K₀') * t' ^ 2 := by
      filter_upwards [Ioo_mem_nhds ht (htrs.trans_le hrsb)] with t' ht'
      rw [hidenty t' ht'.1 ht'.2]
      ring
    have hdH : DifferentiableAt ℝ (H y) t :=
      differentiableAt_correctedSmoothing hr hg K y ht ((htrs.trans_le hrs₀).trans hr₀₁)
    have hsq : HasDerivAt (fun t' : ℝ => t' ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hd : HasDerivAt (fun t' => H y t' - (K - K₀') * t' ^ 2)
        (deriv (H y) t - (K - K₀') * (2 * t)) t :=
      hdH.hasDerivAt.sub (hsq.const_mul _)
    have hloc_d : deriv (localCorrected Φ α ue K₀' z) t =
        deriv (H y) t - (K - K₀') * (2 * t) := by
      rw [hev.deriv_eq]
      exact hd.deriv
    refine ⟨?_, ?_⟩
    · rw [logSlope, hloc_d]
      ring
    · rw [logSlope_eq_deriv_exp ht hdH]
      exact (hb_all (Real.log t) (Real.log_lt_log ht htrs)).1
  -- the joint Levi form in the chart `e`, against the chart-level one
  have hJH : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < rs → ContDiffAt ℝ 2 (jointFun H e) (z, w) := by
    intro w hw0 hwrs
    have h1 := (contDiffAt_jointFun hr hg hzt hw0 ((hwrs.trans_le hrs₀).trans hr₀₁)).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have h2 : ContDiffAt ℝ 2 (fun p : ComplexModel N × ℂ => K * ‖p.2‖ ^ 2) (z, w) :=
      contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp (z, w) contDiffAt_snd)
    have heq : jointFun H e = fun p => jointFun (smoothing wY A g) e p + K * ‖p.2‖ ^ 2 := rfl
    rw [heq]
    exact h1.add h2
  have hρz : ContDiffAt ℝ 2 ρ z :=
    (hρ.2.2.1.contDiffAt (hρ.1.mem_nhds (hKc'W hzK'))).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
  have hlevi : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < rs → ∀ (v : ComplexModel N) (η : ℂ),
      leviForm (chartJoint H e ρ) (z, w) (v, η) =
        leviForm (fun p : ComplexModel N × ℂ => localCorrected Φ α ue K₀' p.1 ‖p.2‖ + ρ p.1)
          (z, w) (v, η) + (K - K₀') * ‖η‖ ^ 2 := by
    intro w hw0 hwrs v η
    have hnb : ∀ᶠ p : ComplexModel N × ℂ in 𝓝 (z, w),
        p.1 ∈ ball z₀ (2 * b) ∧ 0 < ‖p.2‖ ∧ ‖p.2‖ < rb := by
      have h1 : ∀ᶠ p : ComplexModel N × ℂ in 𝓝 (z, w), p.1 ∈ ball z₀ (2 * b) :=
        continuous_fst.continuousAt.preimage_mem_nhds
          (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hzb))
      have h2 : ∀ᶠ p : ComplexModel N × ℂ in 𝓝 (z, w), ‖p.2‖ ∈ Ioo 0 rb :=
        (continuous_norm.comp continuous_snd).continuousAt.preimage_mem_nhds
          (Ioo_mem_nhds hw0 (hwrs.trans_le hrsb))
      filter_upwards [h1, h2] with p hp1 hp2
      exact ⟨hp1, hp2.1, hp2.2⟩
    set Lj := fun p : ComplexModel N × ℂ => localCorrected Φ α ue K₀' p.1 ‖p.2‖ + ρ p.1
    set Sq := fun p : ComplexModel N × ℂ => (K - K₀') * ‖p.2‖ ^ 2
    have hev : chartJoint H e ρ =ᶠ[𝓝 (z, w)] Lj + Sq := by
      filter_upwards [hnb] with p hp
      simp only [chartJoint, Pi.add_apply, Lj, Sq]
      rw [hident p.1 (ball_subset_closedBall hp.1) ‖p.2‖ hp.2.1 hp.2.2]
      ring
    have hSq : ContDiffAt ℝ 2 Sq (z, w) :=
      contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp (z, w) contDiffAt_snd)
    have hCJ : ContDiffAt ℝ 2 (chartJoint H e ρ) (z, w) := by
      rw [chartJoint_eq]
      exact (hJH w hw0 hwrs).add (hρz.comp (z, w) contDiffAt_fst)
    have hLj : ContDiffAt ℝ 2 Lj (z, w) := by
      have hev2 : Lj =ᶠ[𝓝 (z, w)] fun p => chartJoint H e ρ p - Sq p := by
        filter_upwards [hev] with p hp
        rw [hp]
        simp only [Pi.add_apply]
        ring
      exact (hCJ.sub hSq).congr_of_eventuallyEq hev2
    rw [leviForm_congr hev, leviForm_add hLj hSq]
    congr 1
    have h := leviForm_smul (u := fun p : ComplexModel N × ℂ => ‖p.2‖ ^ 2)
      ((contDiff_norm_sq ℝ).contDiffAt.comp (z, w) contDiffAt_snd) (K - K₀') (v, η)
    rw [leviForm_normSq_snd] at h
    exact h
  -- transfer to an arbitrary chart
  have htransfer : ∀ (e' : ComplexChart N Y) (z' : ComplexModel N), z' ∈ e'.val.target →
      e'.val.symm z' = y → ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < rs → ∀ a₁ a₂ a₃ : ℝ,
      (∀ (v : ComplexModel N) (η : ℂ),
        -(a₁ * chartNormSq wY e z v) - a₂ * Real.sqrt (chartNormSq wY e z v) * ‖η‖ -
          a₃ * ‖η‖ ^ 2 ≤ leviForm (chartJoint H e ρ) (z, w) (v, η)) →
      JointLeviLowerBound θ wY H e' z' w a₁ a₂ a₃ := by
    intro e' z' hz' hz'y w hw0 hwrs a₁ a₂ a₃ hbd
    have hzs : z' ∈ (chartTransition e' e).source :=
      mem_transition_source_iff.mpr ⟨hz', by rw [hz'y]; exact hy.1⟩
    have hτ : chartTransition e' e z' = z := by rw [transition_apply, hz'y]
    refine jointLeviLowerBound_of_chart θ wY H hzs (by rw [hτ]; exact hJH w hw0 hwrs)
      (by rw [hτ]; exact hKc'W hzK') hρ ?_
    intro v η
    rw [hτ]
    exact hbd v η
  refine ⟨fun t ht htrs => ?_, hb_all, ?_, ?_⟩
  · -- clause (a)
    have h := cla t ht (htrs.trans_le hrs₁)
    rw [huy] at h
    refine h.trans ?_
    rw [EReal.coe_le_coe_iff, hidenty t ht (htrs.trans_le hrsb)]
    nlinarith [sq_nonneg t]
  · -- clause (c)
    intro e' z' hz' hz'y w hw0 hwrs
    refine htransfer e' z' hz' hz'y w hw0 hwrs _ _ _ fun v η => ?_
    obtain ⟨hsl, hsl0⟩ := hslope ‖w‖ hw0 hwrs
    have hloc := clc w hw0 (hwrs.trans_le hrs₁) v η
    rw [hlevi w hw0 hwrs v η]
    set Nv := chartNormSq wY e z v
    have hNv : α z ![v, Complex.I • v] = Nv := rfl
    rw [hNv] at hloc
    have hN := chartNormSq_nonneg wY e hzt v
    set dl := deriv (localCorrected Φ α ue K₀' z) ‖w‖
    set lg := logSlope H y ‖w‖
    have hll : ‖w‖ * dl ≤ lg := by
      rw [hsl]
      have : 0 ≤ 2 * (K - K₀') * ‖w‖ ^ 2 := by positivity
      linarith
    have hA1 : A₀' * (‖w‖ * dl) ≤ Ac * lg :=
      (mul_le_mul_of_nonneg_left hll hA₀').trans (mul_le_mul_of_nonneg_right hA hsl0)
    have h1 : A₀' * (‖w‖ * dl) * Nv ≤ Ac * lg * Nv := mul_le_mul_of_nonneg_right hA1 hN
    have h2 : C₀' * ‖w‖ * Nv ≤ C * ‖w‖ * Nv :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hw0.le) hN
    have h3 : C₀' * Real.sqrt Nv * ‖η‖ ≤ C * Real.sqrt Nv * ‖η‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))
        (norm_nonneg _)
    have h4 : C₀' * ‖η‖ ^ 2 ≤ C * ‖η‖ ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    have h5 : 0 ≤ (K - K₀') * ‖η‖ ^ 2 := mul_nonneg hKK (sq_nonneg _)
    have e1 : (A₀' * (‖w‖ * dl) + C₀' * ‖w‖) * Nv = A₀' * (‖w‖ * dl) * Nv + C₀' * ‖w‖ * Nv := by
      ring
    have e2 : (Ac * lg + C * ‖w‖) * Nv = Ac * lg * Nv + C * ‖w‖ * Nv := by ring
    linarith
  · -- clause (d)
    intro a ha L hL r hr hC₁r hHlin e' z' hz' hz'y w hw
    have hw0 : 0 < ‖w‖ := hw ▸ hr
    have hC₁'le : C₁' ≤ C₁ := (le_max_left _ _).trans hC₁
    have h1C₁ : 1 ≤ C₁ := (le_max_right _ _).trans hC₁
    have hC₁'r : C₁' * r ≤ C₁ * r := mul_le_mul_of_nonneg_right hC₁'le hr.le
    have hrC : r ≤ C₁ * r := by nlinarith
    have hrrs : r < rs := lt_of_le_of_lt hrC hC₁r
    have hwrs : ‖w‖ < rs := hw ▸ hrrs
    have hloclin : ∀ t : ℝ, 0 < t → t ≤ C₁' * r →
        localCorrected Φ α ue K₀' z t ≤ a + L * t := by
      intro t ht htr
      have htrs : t < rs := lt_of_le_of_lt (htr.trans hC₁'r) hC₁r
      have h1 := hHlin t ht (htr.trans hC₁'r)
      have h2 := hidenty t ht (htrs.trans_le hrsb)
      have : 0 ≤ (K - K₀') * t ^ 2 := mul_nonneg hKK (sq_nonneg t)
      linarith
    have hua : ue z = (a : EReal) := by rw [huy]; exact ha
    refine htransfer e' z' hz' hz'y w hw0 hwrs _ _ _ fun v η => ?_
    have hloc := cld a L r hua hL hr (lt_of_le_of_lt hC₁'r (hC₁r.trans_le hrs₁)) hloclin w hw v η
    obtain ⟨hsl, hsl0⟩ := hslope r hr hrrs
    rw [hlevi w hw0 hwrs v η]
    set Nv := chartNormSq wY e z v
    have hNv : α z ![v, Complex.I • v] = Nv := rfl
    rw [hNv] at hloc
    have hN := chartNormSq_nonneg wY e hzt v
    set dl := deriv (localCorrected Φ α ue K₀' z) r
    set lg := logSlope H y r
    have hll : r * dl ≤ lg := by
      rw [hsl]
      have : 0 ≤ 2 * (K - K₀') * r ^ 2 := by positivity
      linarith
    have hA1 : A₀' * (r * dl) ≤ Ac * lg :=
      (mul_le_mul_of_nonneg_left hll hA₀').trans (mul_le_mul_of_nonneg_right hA hsl0)
    have hL1 : 0 ≤ 1 + L := by linarith
    have hCL : C₀' * (1 + L) ≤ C * (1 + L) := mul_le_mul_of_nonneg_right hC hL1
    have h1 : A₀' * (r * dl) * Nv ≤ Ac * lg * Nv := mul_le_mul_of_nonneg_right hA1 hN
    have h2 : C₀' * (1 + L) * r ^ 2 * Nv ≤ C * (1 + L) * r ^ 2 * Nv :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCL (sq_nonneg r)) hN
    have h3 : C₀' * (1 + L) * r * Real.sqrt Nv * ‖η‖ ≤ C * (1 + L) * r * Real.sqrt Nv * ‖η‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCL hr.le) (Real.sqrt_nonneg _)) (norm_nonneg _)
    have h4 : C₀' * (1 + L) * r * ‖η‖ ^ 2 ≤ C * (1 + L) * r * ‖η‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCL hr.le) (sq_nonneg _)
    have h5 : 0 ≤ (K - K₀') * ‖η‖ ^ 2 := mul_nonneg hKK (sq_nonneg _)
    have e1 : (A₀' * (r * dl) + C₀' * (1 + L) * r ^ 2) * Nv =
        A₀' * (r * dl) * Nv + C₀' * (1 + L) * r ^ 2 * Nv := by ring
    have e2 : (Ac * lg + C * (1 + L) * r ^ 2) * Nv = Ac * lg * Nv + C * (1 + L) * r ^ 2 * Nv := by
      ring
    linarith

end SGPT.NPP.DN5

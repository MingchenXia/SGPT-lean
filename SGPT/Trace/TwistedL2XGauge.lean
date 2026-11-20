import SGPT.Trace.TwistedL2XForms

/-!
# Gauge forms on a complex manifold

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:forms`).  A *gauge form*
(`TwistedDatum.IsGaugeFormX`) is a chart-frame-indexed local sesquilinear integrand `F c e u w z`,
a density with respect to the volume `μ` read in the coordinates of `c` (all weights are
`|e|²_h e^{-φ}`, not `e^{-p} = |e|²_h e^{-φ} ρ`), which depends only on germs, is additive in `w`,
and is invariant under a simultaneous change of chart and frame of `L`:

`F c' e' u' w' (c' x) = F c e u w (c x)`  whenever `u', w'` are the transports of `u, w`.

The six integrands of the twisted Bochner--Kodaira argument are gauge forms:
`isGaugeFormX_theta`, `isGaugeFormX_levi`, `isGaugeFormX_tr`, `isGaugeFormX_tstar`,
`isGaugeFormX_curv`, `isGaugeFormX_data`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-! ### Chart data -/

/-- `a` read in the chart `c`. -/
def aC (c : ComplexChart n X) (z : ComplexModel n) : ℝ := T.a (c.val.symm z)

/-- `b` read in the chart `c`. -/
def bC (c : ComplexChart n X) (z : ComplexModel n) : ℝ := T.b (c.val.symm z)

/-- The twisted local weight `p - log a` (the weight of the metric `a h e^{-φ}`). -/
def pTX (c : ComplexChart n X) (e : AtlasFrame T.L) (z : ComplexModel n) : ℝ :=
  T.pX c e z - Real.log (T.aC c z)

/-- `∂a(v)` in the chart `c`. -/
def dAX (c : ComplexChart n X) (z v : ComplexModel n) : ℂ := dDir v (fun y => (T.aC c y : ℂ)) z

/-- The sesquilinear twisted curvature `a Levi(p)(v, w) - Levi(a)(v, w) - ∂a(v) conj ∂a(w) / b`. -/
def HsX (c : ComplexChart n X) (e : AtlasFrame T.L) (z v w : ComplexModel n) : ℂ :=
  (T.aC c z : ℂ) * leviS (T.pX c e) z v w - leviS (T.aC c) z v w -
    T.dAX c z v * conj (T.dAX c z w) / (T.bC c z : ℂ)

/-! ### The six integrands -/

/-- The twisted adjoint form `ϑ' u conj(ϑ' w) a |e|² e^{-φ}`. -/
def FθX (c : ComplexChart n X) (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  chartTheta (T.pTX c e) u z * conj (chartTheta (T.pTX c e) w z) *
    ((T.aC c z * T.wX c e z : ℝ) : ℂ)

/-- The twisted Levi form. -/
def FLX (c : ComplexChart n X) (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  leviS (T.pTX c e) z (u z) (w z) * ((T.aC c z * T.wX c e z : ℝ) : ℂ)

/-- The twisted `tr(A Ā)` form. -/
def FTX (c : ComplexChart n X) (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  trS u w z * ((T.aC c z * T.wX c e z : ℝ) : ℂ)

/-- The form of `‖T* τ‖²`. -/
def FAX (c : ComplexChart n X) (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  ((T.aC c z + T.bC c z : ℝ) : ℂ) * chartTheta (T.pX c e) u z *
    conj (chartTheta (T.pX c e) w z) * ((T.wX c e z : ℝ) : ℂ)

/-- The twisted curvature form. -/
def FHX (c : ComplexChart n X) (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  T.HsX c e z (u z) (w z) * ((T.wX c e z : ℝ) : ℂ)

/-- The data form `⟨∂̄G_e, w⟩ |e|² e^{-φ}`. -/
def FDX (c : ComplexChart n X) (e : AtlasFrame T.L) (_u w : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) : ℂ :=
  dbarPairing (chartCoeff T.L c e T.G) z (w z) * ((T.wX c e z : ℝ) : ℂ)

/-- **Gauge forms on a manifold.** -/
structure IsGaugeFormX (F : ComplexChart n X → AtlasFrame T.L →
    (ComplexModel n → ComplexModel n) → (ComplexModel n → ComplexModel n) →
      ComplexModel n → ℂ) : Prop where
  congr : ∀ c e u u' w w' z, u =ᶠ[𝓝 z] u' → w =ᶠ[𝓝 z] w' → F c e u w z = F c e u' w' z
  zero : ∀ c e u w z, w =ᶠ[𝓝 z] 0 → F c e u w z = 0
  add : ∀ c e (u : ComplexModel n → ComplexModel n) {ι : Type} (s : Finset ι)
    (w : ι → ComplexModel n → ComplexModel n) z, z ∈ T.pieceDomain c e →
    ContDiffAt ℝ ∞ u z → (∀ i ∈ s, ContDiffAt ℝ ∞ (w i) z) →
    F c e u (fun y => ∑ i ∈ s, w i y) z = ∑ i ∈ s, F c e u (w i) z
  gauge : ∀ c e c' e' u u' w w' z, z ∈ T.pieceDomain c e →
    c.val.symm z ∈ c'.val.source ∩ e'.val.baseSet →
    ContDiffOn ℝ ∞ u (T.pieceDomain c e) → ContDiffOn ℝ ∞ w (T.pieceDomain c e) →
    ContDiffOn ℝ ∞ u' (T.pieceDomain c' e') → ContDiffOn ℝ ∞ w' (T.pieceDomain c' e') →
    IsTransp T.L c e c' e' u u' z → IsTransp T.L c e c' e' w w' z →
    F c' e' u' w' (chg c c' z) = F c e u w z
  contOn : ∀ c e u w, ContDiffOn ℝ ∞ u (T.pieceDomain c e) →
    ContDiffOn ℝ ∞ w (T.pieceDomain c e) → ContinuousOn (F c e u w) (T.pieceDomain c e)

variable {T}

/-! ### Smoothness and transport of the chart data -/

theorem contDiffOn_aC {e : AtlasFrame T.L} (c : ComplexChart n X) : ContDiffOn ℝ ∞ (T.aC c) (T.pieceDomain c e) :=
  (T.a_smooth c).mono (T.pieceDomain_subset_chartSmooth c e)

theorem contDiffOn_bC {e : AtlasFrame T.L} (c : ComplexChart n X) : ContDiffOn ℝ ∞ (T.bC c) (T.pieceDomain c e) :=
  (T.b_smooth c).mono (T.pieceDomain_subset_chartSmooth c e)

theorem aC_pos {c : ComplexChart n X} {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) : 0 < T.aC c z := by
  obtain ⟨m, M, hm, hb⟩ := T.bounds
  exact hm.trans_le (hb _ hz.2).1

theorem bC_pos {c : ComplexChart n X} {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) : 0 < T.bC c z := by
  obtain ⟨m, M, hm, hb⟩ := T.bounds
  exact hm.trans_le (hb _ hz.2).2.2.1

theorem contDiffOn_logaC (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContDiffOn ℝ ∞ (fun z => Real.log (T.aC c z)) (T.pieceDomain c e) :=
  (contDiffOn_aC (e := e) c).log fun _ hz => (aC_pos hz).ne'

theorem contDiffOn_pTX (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContDiffOn ℝ ∞ (T.pTX c e) (T.pieceDomain c e) :=
  (T.contDiffOn_pX c e).sub (contDiffOn_logaC c e)

theorem aC_chg {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    T.aC c' (chg c c' z) = T.aC c z := by
  simp [aC, symm_chg hz]

theorem bC_chg {c c' : ComplexChart n X} {z : ComplexModel n} (hz : z ∈ ovl c c') :
    T.bC c' (chg c c' z) = T.bC c z := by
  simp [bC, symm_chg hz]

theorem aC_comp_eventuallyEq {c c' : ComplexChart n X} {z : ComplexModel n}
    (hz : z ∈ ovl c c') : (fun y => T.aC c' (chg c c' y)) =ᶠ[𝓝 z] T.aC c := by
  filter_upwards [(isOpen_ovl c c').mem_nhds hz] with y hy
  exact aC_chg hy

theorem differentiableAt_of_pieceDomain {c : ComplexChart n X} {e : AtlasFrame T.L}
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f (T.pieceDomain c e)) {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) : DifferentiableAt ℝ f z :=
  ((hf.contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz)).differentiableAt (by simp))

/-- The transport of `∂f(v)` for a function read in two charts. -/
theorem dDir_comp_transport {c c' : ComplexChart n X}
    {f f' : ComplexModel n → ℝ} {z : ComplexModel n} (hzo : z ∈ ovl c c')
    (hf' : DifferentiableAt ℝ f' (chg c c' z)) (hff : (fun y => f' (chg c c' y)) =ᶠ[𝓝 z] f)
    (τ : ℂ) (v : ComplexModel n) :
    dDir (τ • fderiv ℂ (chg c c') z v) (fun y => (f' y : ℂ)) (chg c c' z) =
      τ * dDir v (fun y => (f y : ℂ)) z := by
  have hev : (fun y => ((f' (chg c c' y) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun y => ((f y : ℝ) : ℂ) :=
    hff.mono fun y hy => congrArg (fun r : ℝ => (r : ℂ)) hy
  rw [dDir_smul_dir, ← dDir_comp_holo (differentiableAt_chg hzo)
    (differentiableAt_ofReal_comp hf'), dDir_congr_of_eventuallyEq hev]

/-- **Chart invariance of the twisted adjoint.** -/
theorem chartTheta_pTX_transport {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {u u' : ComplexModel n → ComplexModel n} (hu : ContDiffOn ℝ ∞ u (T.pieceDomain c e))
    (hu' : ContDiffOn ℝ ∞ u' (T.pieceDomain c' e')) {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) (hz' : c.val.symm z ∈ c'.val.source ∩ e'.val.baseSet)
    (hrel : IsTransp T.L c e c' e' u u' z) :
    chartTheta (T.pTX c' e') u' (chg c c' z) =
      frameTrans T.L e e' (c.val.symm z) * chartTheta (T.pTX c e) u z := by
  have hzo : z ∈ ovl c c' := ⟨hz.1.1, hz'.1⟩
  have hzd' := chg_mem_pieceDomain hz hz'
  have hθ := T.chartTheta_transport (T.isOpen_pieceDomain c e) (T.isOpen_pieceDomain c' e')
    subset_rfl subset_rfl hu hu' hz hz' hzd' hrel
  have hl : (fun y => Real.log (T.aC c' (chg c c' y))) =ᶠ[𝓝 z]
      fun y => Real.log (T.aC c y) :=
    (aC_comp_eventuallyEq (T := T) hzo).mono fun y hy => congrArg Real.log hy
  have hu0 := hrel.self_of_nhds
  simp only at hu0
  change chartTheta (fun y => T.pX c' e' y - Real.log (T.aC c' y)) u' (chg c c' z) =
    _ * chartTheta (fun y => T.pX c e y - Real.log (T.aC c y)) u z
  rw [chartTheta_sub_weight (differentiableAt_of_pieceDomain (T.contDiffOn_pX c' e') hzd')
      (differentiableAt_of_pieceDomain (contDiffOn_logaC c' e') hzd'),
    chartTheta_sub_weight (differentiableAt_of_pieceDomain (T.contDiffOn_pX c e) hz)
      (differentiableAt_of_pieceDomain (contDiffOn_logaC c e) hz),
    hu0, dDir_comp_transport hzo
      (differentiableAt_of_pieceDomain (contDiffOn_logaC c' e') hzd') hl, hθ]
  ring

/-- **Chart invariance of the Levi form of the twisted weight.** -/
theorem leviS_pTX_transport {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {z : ComplexModel n} (hz : z ∈ T.ovlD c c' e e') (a b : ComplexModel n) :
    leviS (T.pTX c' e') (chg c c' z) (fderiv ℂ (chg c c') z a) (fderiv ℂ (chg c c') z b) =
      leviS (T.pTX c e) z a b := by
  rw [leviS_transport_of_smooth hz (contDiffOn_pTX c' e')]
  refine leviS_eq_of_dDir_eq_add_holo
    (((contDiffOn_pTX c e).contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds
      (ovlD_spec hz).1)).of_le (WithTop.coe_le_coe.mpr le_top)) (fun j => ?_) a b
  obtain ⟨g, hg, hev⟩ := dDir_pX_transport hz (coordVec j)
  refine ⟨g, hg, ?_⟩
  filter_upwards [hev, (T.isOpen_ovlD c c' e e').mem_nhds hz] with y hy hyD
  obtain ⟨hyd, hy'⟩ := ovlD_spec hyD
  have hyo : y ∈ ovl c c' := ⟨hyd.1.1, hy'.1⟩
  have hyd' := chg_mem_pieceDomain hyd hy'
  have hS : IsOpen (T.ovlD c c' e e') := T.isOpen_ovlD c c' e e'
  -- the twisted weights differ from the untwisted ones by the same function
  have e1 : (fun x => (T.pTX c' e' (chg c c' x) : ℂ)) =ᶠ[𝓝 y]
      fun x => (T.pX c' e' (chg c c' x) : ℂ) - (Real.log (T.aC c x) : ℂ) := by
    filter_upwards [(isOpen_ovl c c').mem_nhds hyo] with x hx
    simp only [pTX, aC_chg hx]
    push_cast; ring
  have e2 : (fun x => (T.pTX c e x : ℂ)) =
      fun x => (T.pX c e x : ℂ) - (Real.log (T.aC c x) : ℂ) := by
    funext x; simp only [pTX]; push_cast; ring
  have hchgy : DifferentiableAt ℂ (chg c c') y := differentiableAt_chg hyo
  have d1 : DifferentiableAt ℝ (fun x => (T.pX c' e' (chg c c' x) : ℂ)) y :=
    differentiableAt_ofReal_comp ((differentiableAt_of_pieceDomain (T.contDiffOn_pX c' e')
      hyd').comp y (hchgy.restrictScalars ℝ))
  have d2 : DifferentiableAt ℝ (fun x => (Real.log (T.aC c x) : ℂ)) y :=
    differentiableAt_ofReal_comp (differentiableAt_of_pieceDomain (contDiffOn_logaC c e) hyd)
  have d3 : DifferentiableAt ℝ (fun x => (T.pX c e x : ℂ)) y :=
    differentiableAt_ofReal_comp (differentiableAt_of_pieceDomain (T.contDiffOn_pX c e) hyd)
  rw [dDir_congr_of_eventuallyEq e1, e2, dDir_sub d1 d2, dDir_sub d3 d2, hy]
  ring

/-! ### The six gauge forms -/

theorem continuousOn_wXc (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContinuousOn (fun z => ((T.wX c e z : ℝ) : ℂ)) (T.pieceDomain c e) :=
  Complex.continuous_ofReal.comp_continuousOn (continuousOn_wX c e)

theorem continuousOn_awX (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContinuousOn (fun z => ((T.aC c z * T.wX c e z : ℝ) : ℂ)) (T.pieceDomain c e) :=
  Complex.continuous_ofReal.comp_continuousOn
    ((contDiffOn_aC (e := e) c).continuousOn.mul (continuousOn_wX c e))

/-- The data common to all gauge computations at a point of an overlap. -/
theorem gauge_setup {c c' : ComplexChart n X} {e e' : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) (hz' : c.val.symm z ∈ c'.val.source ∩ e'.val.baseSet) :
    z ∈ ovl c c' ∧ z ∈ T.ovlD c c' e e' ∧
      T.wX c' e' (chg c c' z) * (frameTrans T.L e e' (c.val.symm z) *
        conj (frameTrans T.L e e' (c.val.symm z))) = T.wX c e z := by
  have hzo : z ∈ ovl c c' := ⟨hz.1.1, hz'.1⟩
  exact ⟨hzo, mem_ovlD hz hz', wX_chg hzo ⟨hz.1.2, hz'.2⟩⟩

theorem isGaugeFormX_theta : T.IsGaugeFormX T.FθX where
  congr c e u u' w w' z hu hw := by simp only [FθX, chartTheta_congr hu, chartTheta_congr hw]
  zero c e u w z hw := by simp [FθX, chartTheta_eq_zero_of_eventuallyEq hw]
  add c e u ι s w z _ _ hw := by
    simp only [FθX, chartTheta_finset_sum s fun i hi => (hw i hi).differentiableAt (by simp),
      map_sum, Finset.mul_sum, Finset.sum_mul]
  gauge c e c' e' u u' w w' z hz hz' hu hw hu' hw' hru hrw := by
    obtain ⟨hzo, -, hW⟩ := gauge_setup hz hz'
    simp only [FθX]
    rw [chartTheta_pTX_transport hu hu' hz hz' hru, chartTheta_pTX_transport hw hw' hz hz' hrw,
      aC_chg hzo]
    push_cast
    rw [← hW]
    simp only [map_mul]
    ring
  contOn c e u w hu hw := by
    have hO := T.isOpen_pieceDomain c e
    exact ((continuousOn_chartTheta' hO (contDiffOn_pTX c e) hu).mul
      (Complex.continuous_conj.comp_continuousOn
        (continuousOn_chartTheta' hO (contDiffOn_pTX c e) hw))).mul (continuousOn_awX c e)

theorem isGaugeFormX_levi : T.IsGaugeFormX T.FLX where
  congr c e u u' w w' z hu hw := by simp only [FLX, hu.self_of_nhds, hw.self_of_nhds]
  zero c e u w z hw := by simp [FLX, hw.self_of_nhds, leviS_zero_right]
  add c e u ι s w z _ _ _ := by
    simp only [FLX]
    rw [leviS_finset_sum_right, Finset.sum_mul]
  gauge c e c' e' u u' w w' z hz hz' _ _ _ _ hru hrw := by
    obtain ⟨hzo, hzD, hW⟩ := gauge_setup hz hz'
    simp only [FLX]
    have hu0 := hru.self_of_nhds
    have hw0 := hrw.self_of_nhds
    simp only at hu0 hw0
    rw [hu0, hw0, leviS_smul, leviS_pTX_transport hzD, aC_chg hzo]
    push_cast
    rw [← hW]
    ring
  contOn c e u w hu hw :=
    (continuousOn_leviS (T.isOpen_pieceDomain c e) (contDiffOn_pTX c e) hu.continuousOn
      hw.continuousOn).mul (continuousOn_awX c e)

theorem isGaugeFormX_tr : T.IsGaugeFormX T.FTX where
  congr c e u u' w w' z hu hw := by simp only [FTX, trS_congr hu hw]
  zero c e u w z hw := by simp [FTX, trS_eq_zero_of_right hw]
  add c e u ι s w z _ _ hw := by
    simp only [FTX]
    rw [trS_finset_sum_right u s fun i hi => (hw i hi).differentiableAt (by simp), Finset.sum_mul]
  gauge c e c' e' u u' w w' z hz hz' hu hw hu' hw' hru hrw := by
    obtain ⟨hzo, hzD, hW⟩ := gauge_setup hz hz'
    have hzd' := chg_mem_pieceDomain hz hz'
    set S := T.ovlD c c' e e'
    have hSo : IsOpen S := T.isOpen_ovlD c c' e e'
    have hψ : DifferentiableOn ℂ (chg c c') S :=
      (differentiableOn_chg c c').mono fun y hy => hy.1.2
    have ht : DifferentiableOn ℂ (fun y => frameTrans T.L e e' (c.val.symm y)) S :=
      (differentiableOn_frameTrans c e e').mono fun y hy => ⟨hy.1.1.1.1, hy.1.1.1.2, hy.2⟩
    simp only [FTX]
    rw [trS_transport hSo hψ ht hzD (isUnit_linMat_fderiv_chg hzo)
      ((hu.contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz)).differentiableAt (by simp))
      ((hu'.contDiffAt ((T.isOpen_pieceDomain c' e').mem_nhds hzd')).differentiableAt (by simp))
      ((hw.contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz)).differentiableAt (by simp))
      ((hw'.contDiffAt ((T.isOpen_pieceDomain c' e').mem_nhds hzd')).differentiableAt (by simp))
      hru hrw, aC_chg hzo]
    push_cast
    rw [← hW]
    ring
  contOn c e u w hu hw :=
    (continuousOn_trS (T.isOpen_pieceDomain c e) hu hw).mul (continuousOn_awX c e)

theorem continuousOn_abC (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContinuousOn (fun z => ((T.aC c z + T.bC c z : ℝ) : ℂ)) (T.pieceDomain c e) :=
  Complex.continuous_ofReal.comp_continuousOn
    ((contDiffOn_aC (e := e) c).continuousOn.add (contDiffOn_bC (e := e) c).continuousOn)

theorem isGaugeFormX_tstar : T.IsGaugeFormX T.FAX where
  congr c e u u' w w' z hu hw := by simp only [FAX, chartTheta_congr hu, chartTheta_congr hw]
  zero c e u w z hw := by simp [FAX, chartTheta_eq_zero_of_eventuallyEq hw]
  add c e u ι s w z _ _ hw := by
    simp only [FAX, chartTheta_finset_sum s fun i hi => (hw i hi).differentiableAt (by simp),
      map_sum, Finset.mul_sum, Finset.sum_mul]
  gauge c e c' e' u u' w w' z hz hz' hu hw hu' hw' hru hrw := by
    obtain ⟨hzo, -, hW⟩ := gauge_setup hz hz'
    have hzd' := chg_mem_pieceDomain hz hz'
    have hO := T.isOpen_pieceDomain c e
    have hO' := T.isOpen_pieceDomain c' e'
    simp only [FAX]
    rw [T.chartTheta_transport hO hO' subset_rfl subset_rfl hu hu' hz hz' hzd' hru,
      T.chartTheta_transport hO hO' subset_rfl subset_rfl hw hw' hz hz' hzd' hrw,
      aC_chg hzo, bC_chg hzo]
    push_cast
    rw [← hW]
    simp only [map_mul]
    ring
  contOn c e u w hu hw := by
    have hO := T.isOpen_pieceDomain c e
    exact (((continuousOn_abC c e).mul (continuousOn_chartTheta' hO (T.contDiffOn_pX c e) hu)).mul
      (Complex.continuous_conj.comp_continuousOn
        (continuousOn_chartTheta' hO (T.contDiffOn_pX c e) hw))).mul (continuousOn_wXc c e)

theorem dAX_smul (c : ComplexChart n X) (z v : ComplexModel n) (τ : ℂ) :
    T.dAX c z (τ • v) = τ * T.dAX c z v := dDir_smul_dir τ v _ z

theorem dAX_add (c : ComplexChart n X) (z v w : ComplexModel n) :
    T.dAX c z (v + w) = T.dAX c z v + T.dAX c z w := dDir_add_dir v w _ z

theorem dAX_sum (c : ComplexChart n X) (z : ComplexModel n) {ι : Type*} (s : Finset ι)
    (w : ι → ComplexModel n) : T.dAX c z (∑ i ∈ s, w i) = ∑ i ∈ s, T.dAX c z (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dAX, dDir]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dAX_add, ih]

theorem dAX_zero (c : ComplexChart n X) (z : ComplexModel n) : T.dAX c z 0 = 0 := by
  simp [dAX, dDir]

theorem HsX_smul (c : ComplexChart n X) (e : AtlasFrame T.L) (z v w : ComplexModel n) (τ : ℂ) :
    T.HsX c e z (τ • v) (τ • w) = (τ * conj τ) * T.HsX c e z v w := by
  simp only [HsX, leviS_smul, dAX_smul, map_mul]
  ring

theorem HsX_sum (c : ComplexChart n X) (e : AtlasFrame T.L) (z v : ComplexModel n) {ι : Type*}
    (s : Finset ι) (w : ι → ComplexModel n) :
    T.HsX c e z v (∑ i ∈ s, w i) = ∑ i ∈ s, T.HsX c e z v (w i) := by
  simp only [HsX, leviS_finset_sum_right, dAX_sum, map_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]

theorem HsX_zero (c : ComplexChart n X) (e : AtlasFrame T.L) (z v : ComplexModel n) :
    T.HsX c e z v 0 = 0 := by
  simp [HsX, leviS_zero_right, dAX_zero]

theorem HsX_transport {c c' : ComplexChart n X} {e e' : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) (hz' : c.val.symm z ∈ c'.val.source ∩ e'.val.baseSet)
    (v w : ComplexModel n) (τ : ℂ) :
    T.HsX c' e' (chg c c' z) (τ • fderiv ℂ (chg c c') z v) (τ • fderiv ℂ (chg c c') z w) =
      (τ * conj τ) * T.HsX c e z v w := by
  obtain ⟨hzo, hzD, -⟩ := gauge_setup hz hz'
  have hzd' := chg_mem_pieceDomain hz hz'
  rw [HsX_smul]
  congr 1
  have hla : leviS (T.aC c') (chg c c' z) (fderiv ℂ (chg c c') z v) (fderiv ℂ (chg c c') z w) =
      leviS (T.aC c) z v w := by
    rw [leviS_transport_of_smooth hzD (contDiffOn_aC (e := e') c')]
    exact leviS_congr_weight (aC_comp_eventuallyEq hzo) v w
  have hda : ∀ v : ComplexModel n,
      T.dAX c' (chg c c' z) (fderiv ℂ (chg c c') z v) = T.dAX c z v := by
    intro v
    have := dDir_comp_transport hzo
      (differentiableAt_of_pieceDomain (contDiffOn_aC (e := e') c') hzd')
      (aC_comp_eventuallyEq hzo) 1 v
    simpa [dAX] using this
  simp only [HsX, leviS_pX_transport hzD, hla, hda, aC_chg hzo, bC_chg hzo]

theorem continuousOn_dAX (c : ComplexChart n X) (e : AtlasFrame T.L)
    {w : ComplexModel n → ComplexModel n} (hw : ContinuousOn w (T.pieceDomain c e)) :
    ContinuousOn (fun z => T.dAX c z (w z)) (T.pieceDomain c e) := by
  have hO := T.isOpen_pieceDomain c e
  have h : (fun z => T.dAX c z (w z)) =
      fun z => ∑ j, w z j * dDir (coordVec j) (fun y => (T.aC c y : ℂ)) z := by
    funext z; exact dDir_vec_eq_sum _ _ _
  rw [h]
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.comp_continuousOn hw).mul
    (contDiffOn_dDir hO (contDiffOn_ofReal' (contDiffOn_aC (e := e) c)) _).continuousOn

theorem isGaugeFormX_curv : T.IsGaugeFormX T.FHX where
  congr c e u u' w w' z hu hw := by simp only [FHX, hu.self_of_nhds, hw.self_of_nhds]
  zero c e u w z hw := by simp [FHX, hw.self_of_nhds, HsX_zero]
  add c e u ι s w z _ _ _ := by
    simp only [FHX]
    rw [HsX_sum, Finset.sum_mul]
  gauge c e c' e' u u' w w' z hz hz' _ _ _ _ hru hrw := by
    obtain ⟨-, -, hW⟩ := gauge_setup hz hz'
    simp only [FHX]
    have hu0 := hru.self_of_nhds
    have hw0 := hrw.self_of_nhds
    simp only at hu0 hw0
    rw [hu0, hw0, HsX_transport hz hz', ← hW]
    ring
  contOn c e u w hu hw := by
    have hO := T.isOpen_pieceDomain c e
    have hb : ContinuousOn (fun z => (T.bC c z : ℂ)) (T.pieceDomain c e) :=
      Complex.continuous_ofReal.comp_continuousOn (contDiffOn_bC (e := e) c).continuousOn
    have hb0 : ∀ z ∈ T.pieceDomain c e, (T.bC c z : ℂ) ≠ 0 := fun z hz => by
      exact_mod_cast (bC_pos hz).ne'
    unfold FHX HsX
    refine ContinuousOn.mul ?_ (continuousOn_wXc c e)
    refine ((((Complex.continuous_ofReal.comp_continuousOn
      (contDiffOn_aC (e := e) c).continuousOn).mul
      (continuousOn_leviS hO (T.contDiffOn_pX c e) hu.continuousOn hw.continuousOn)).sub
      (continuousOn_leviS hO (contDiffOn_aC (e := e) c) hu.continuousOn hw.continuousOn)).sub ?_)
    exact ((continuousOn_dAX c e hu.continuousOn).mul (Complex.continuous_conj.comp_continuousOn
      (continuousOn_dAX c e hw.continuousOn))).div hb hb0

theorem contDiffOn_chartCoeff (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContDiffOn ℝ ∞ (chartCoeff T.L c e T.G) (T.pieceDomain c e) :=
  T.G_smooth c e

theorem chartCoeff_transport {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {z : ComplexModel n} (hzD : z ∈ T.ovlD c c' e e') :
    (fun y => chartCoeff T.L c' e' T.G (chg c c' y)) =ᶠ[𝓝 z]
      fun y => frameTrans T.L e e' (c.val.symm y) * chartCoeff T.L c e T.G y := by
  filter_upwards [(T.isOpen_ovlD c c' e e').mem_nhds hzD] with y hy
  obtain ⟨hyd, hy'⟩ := ovlD_spec hy
  simp only [chartCoeff, symm_chg (⟨hyd.1.1, hy'.1⟩ : y ∈ ovl c c')]
  exact frameCoeff_eq_frameTrans_mul e e' T.G ⟨hyd.1.2, hy'.2⟩

theorem isGaugeFormX_data : T.IsGaugeFormX T.FDX where
  congr c e u u' w w' z _ hw := by simp only [FDX, hw.self_of_nhds]
  zero c e u w z hw := by simp [FDX, hw.self_of_nhds, dbarPairing_zero]
  add c e u ι s w z _ _ _ := by
    simp only [FDX]
    rw [dbarPairing_finset_sum, Finset.sum_mul]
  gauge c e c' e' u u' w w' z hz hz' _ _ _ _ _ hrw := by
    obtain ⟨hzo, hzD, hW⟩ := gauge_setup hz hz'
    have hzd' := chg_mem_pieceDomain hz hz'
    set S := T.ovlD c c' e e'
    have hSo : IsOpen S := T.isOpen_ovlD c c' e e'
    have hψ : DifferentiableOn ℂ (chg c c') S :=
      (differentiableOn_chg c c').mono fun y hy => hy.1.2
    have ht : DifferentiableOn ℂ (fun y => frameTrans T.L e e' (c.val.symm y)) S :=
      (differentiableOn_frameTrans c e e').mono fun y hy => ⟨hy.1.1.1.1, hy.1.1.1.2, hy.2⟩
    have hG : DifferentiableAt ℝ (chartCoeff T.L c e T.G) z :=
      ((contDiffOn_chartCoeff c e).contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz))
        |>.differentiableAt (by simp)
    have hG' : DifferentiableAt ℝ (chartCoeff T.L c' e' T.G) (chg c c' z) :=
      ((contDiffOn_chartCoeff c' e').contDiffAt ((T.isOpen_pieceDomain c' e').mem_nhds hzd'))
        |>.differentiableAt (by simp)
    simp only [FDX]
    have hw0 := hrw.self_of_nhds
    simp only at hw0
    rw [hw0, dbarPairing_transport hSo hψ ht hzD hG hG' (chartCoeff_transport hzD), ← hW]
    ring
  contOn c e u w _ hw := by
    have hO := T.isOpen_pieceDomain c e
    unfold FDX dbarPairing
    refine ContinuousOn.mul (continuousOn_finsetSum _ fun j _ => ?_) (continuousOn_wXc c e)
    exact (Complex.continuous_conj.comp_continuousOn
      ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.comp_continuousOn
        hw.continuousOn)).mul (contDiffOn_dbarDir hO (contDiffOn_chartCoeff c e) _).continuousOn

end TwistedDatum

end SGPT.Trace.TwistedL2

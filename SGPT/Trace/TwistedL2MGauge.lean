import SGPT.Trace.TwistedL2MFrame

/-!
# Gauge calculus for the twisted Bochner--Kodaira identity on `ℂⁿ`

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:gauge`).  A change of holomorphic frame
`e = t e'` of `L` multiplies coefficient fields by the holomorphic nonvanishing function `t` and
changes the local weight by `p' = p + log |t|²`.  Every integrand of the Bochner--Kodaira identity is
invariant:

* `chartTheta_gauge`: `ϑ_{p'}(t u) = t ϑ_p u` (the formal adjoint of `∂̄`);
* `leviS_gauge`: `Levi(p') = Levi(p)` (`log |t|²` is pluriharmonic), for the sesquilinear
  Levi form `leviS`;
* `trS_gauge`: `tr(A_{tu} Ā_{tw}) = |t|² tr(A_u Ā_w)` for `A_u = ∂̄u` (`trS`);
* `dbarPairing_gauge`: `⟨∂̄(tG), t v⟩ = |t|² ⟨∂̄G, v⟩`;
* `cweight_gauge`: `e^{-p'} |t|² = e^{-p}`.

Together with the linearity lemmas below these are the only analytic inputs of the
globalization of the flat Morrey--Kohn--Hörmander identity over a finite family of frames.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending.CauchyGreen
  SGPT.Foundations.Analysis.Pending.Hormander

variable {n : ℕ}

/-! ### Linearity of the Wirtinger derivatives -/

theorem dDir_add' {v x : ComplexModel n} {f g : ComplexModel n → ℂ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dDir v (fun y => f y + g y) x = dDir v f x + dDir v g x := by
  simp only [dDir, fderiv_fun_add hf hg, add_apply]
  ring

theorem dDir_finset_sum_fun' {ι : Type*} (s : Finset ι) {g : ι → ComplexModel n → ℂ}
    {v x : ComplexModel n} (hg : ∀ j ∈ s, DifferentiableAt ℝ (g j) x) :
    dDir v (fun y => ∑ j ∈ s, g j y) x = ∑ j ∈ s, dDir v (g j) x := by
  have h : fderiv ℝ (fun y => ∑ j ∈ s, g j y) x = ∑ j ∈ s, fderiv ℝ (g j) x :=
    fderiv_fun_sum hg
  simp only [dDir, h, sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_div]

theorem euclid_sum_apply {ι : Type*} (s : Finset ι) (w : ι → ComplexModel n) (j : Fin n) :
    (∑ i ∈ s, w i) j = ∑ i ∈ s, w i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

theorem differentiableAt_coord {u : ComplexModel n → ComplexModel n} {x : ComplexModel n}
    (hu : DifferentiableAt ℝ u x) (j : Fin n) : DifferentiableAt ℝ (fun y => u y j) x :=
  ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ).differentiableAt.comp x hu

theorem differentiableAt_dDir {v x : ComplexModel n} {f : ComplexModel n → ℂ}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (dDir v f) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x := hD.clm_apply (differentiableAt_const v)
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Complex.I • v)) x :=
    hD.clm_apply (differentiableAt_const _)
  have hfun : dDir v f = fun y => (2 : ℂ)⁻¹ *
      (fderiv ℝ f y v - Complex.I * fderiv ℝ f y (Complex.I • v)) := by
    funext y; simp only [dDir]; ring
  rw [hfun]
  exact (h1.sub (h2.const_mul _)).const_mul _

theorem differentiableAt_dbarDir {v x : ComplexModel n} {f : ComplexModel n → ℂ}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (dbarDir v f) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x := hD.clm_apply (differentiableAt_const v)
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Complex.I • v)) x :=
    hD.clm_apply (differentiableAt_const _)
  have hfun : dbarDir v f = fun y => (2 : ℂ)⁻¹ *
      (fderiv ℝ f y v + Complex.I * fderiv ℝ f y (Complex.I • v)) := by
    funext y; simp only [dbarDir]; ring
  rw [hfun]
  exact (h1.add (h2.const_mul _)).const_mul _

/-! ### Holomorphic functions -/

theorem dDir_eq_fderiv_complex {t : ComplexModel n → ℂ} {y : ComplexModel n}
    (ht : DifferentiableAt ℂ t y) (v : ComplexModel n) : dDir v t y = fderiv ℂ t y v := by
  have h : fderiv ℝ t y = (fderiv ℂ t y).restrictScalars ℝ := ht.fderiv_restrictScalars ℝ
  simp only [dDir, h, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem differentiableOn_dDir_of_holomorphic {t : ComplexModel n → ℂ} {S : Set (ComplexModel n)}
    (hS : IsOpen S) (ht : DifferentiableOn ℂ t S) (v : ComplexModel n) :
    DifferentiableOn ℂ (dDir v t) S :=
  (differentiableOn_fderiv_apply_of_isOpen ht hS v).congr fun _y hy =>
    dDir_eq_fderiv_complex (ht.differentiableAt (hS.mem_nhds hy)) v

theorem dbarDir_holomorphic {t : ComplexModel n → ℂ} {y : ComplexModel n}
    (ht : DifferentiableAt ℂ t y) (v : ComplexModel n) : dbarDir v t y = 0 :=
  SGPT.Foundations.Analysis.Pending.OTChen.dbarDir_eq_zero_of_differentiableAt ht v

theorem ofReal_norm_sq_eq_mul_conj (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem dDir_ofReal_norm_sq {t : ComplexModel n → ℂ} {z : ComplexModel n}
    (ht : DifferentiableAt ℂ t z) (v : ComplexModel n) :
    dDir v (fun y => ((‖t y‖ ^ 2 : ℝ) : ℂ)) z = dDir v t z * conj (t z) := by
  have htR : DifferentiableAt ℝ t z := ht.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun y => conj (t y)) z :=
    (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp z htR
  have hfun : (fun y => ((‖t y‖ ^ 2 : ℝ) : ℂ)) = fun y => t y * conj (t y) := by
    funext y; exact ofReal_norm_sq_eq_mul_conj _
  rw [hfun, dDir_mul htR hc, dDir_conj htR, dbarDir_holomorphic ht, map_zero, mul_zero, add_zero]

/-- `∂_v log |t|² = ∂_v t / t` for a holomorphic nonvanishing `t`. -/
theorem dDir_ofReal_log_norm_sq {t : ComplexModel n → ℂ} {z : ComplexModel n}
    (ht : DifferentiableAt ℂ t z) (ht0 : t z ≠ 0) (v : ComplexModel n) :
    dDir v (fun y => ((Real.log (‖t y‖ ^ 2) : ℝ) : ℂ)) z = dDir v t z / t z := by
  have htR : DifferentiableAt ℝ t z := ht.restrictScalars ℝ
  have hn : DifferentiableAt ℝ (fun y => ‖t y‖ ^ 2) z := htR.norm_sq ℝ
  have hpos : 0 < ‖t z‖ ^ 2 := by positivity
  rw [FunctionalTwistedAdjointYoungDraft.dDir_ofReal_log hn hpos v, dDir_ofReal_norm_sq ht v]
  rw [ofReal_norm_sq_eq_mul_conj]
  have hconj : conj (t z) ≠ 0 := by simpa using ht0
  field_simp

/-- **The weight change of a frame change.**  Hypotheses used by all gauge lemmas: on an open
`S ∋ z`, `t` is holomorphic and nonvanishing and `p' = p + log |t|²`. -/
structure GaugeData (S : Set (ComplexModel n)) (t : ComplexModel n → ℂ)
    (p p' : ComplexModel n → ℝ) : Prop where
  isOpen : IsOpen S
  holo : DifferentiableOn ℂ t S
  ne_zero : ∀ y ∈ S, t y ≠ 0
  weight : ∀ y ∈ S, p' y = p y + Real.log (‖t y‖ ^ 2)

namespace GaugeData

variable {S : Set (ComplexModel n)} {t : ComplexModel n → ℂ} {p p' : ComplexModel n → ℝ}
  (g : GaugeData S t p p')

include g

theorem differentiableAt {y : ComplexModel n} (hy : y ∈ S) : DifferentiableAt ℂ t y :=
  g.holo.differentiableAt (g.isOpen.mem_nhds hy)

theorem weight_eventuallyEq {y : ComplexModel n} (hy : y ∈ S) :
    (fun y' => (p' y' : ℂ)) =ᶠ[𝓝 y] fun y' => (p y' : ℂ) + ((Real.log (‖t y'‖ ^ 2) : ℝ) : ℂ) := by
  filter_upwards [g.isOpen.mem_nhds hy] with y' hy'
  rw [g.weight y' hy', Complex.ofReal_add]

theorem differentiableAt_log {y : ComplexModel n} (hy : y ∈ S) :
    DifferentiableAt ℝ (fun y' => ((Real.log (‖t y'‖ ^ 2) : ℝ) : ℂ)) y := by
  have htR : DifferentiableAt ℝ t y := (g.differentiableAt hy).restrictScalars ℝ
  have hn : DifferentiableAt ℝ (fun y => ‖t y‖ ^ 2) y := htR.norm_sq ℝ
  have hpos : ‖t y‖ ^ 2 ≠ 0 := by have := g.ne_zero y hy; positivity
  exact differentiableAt_ofReal_comp (hn.log hpos)

/-- `∂_v p' = ∂_v p + ∂_v t / t` at points of `S`. -/
theorem dDir_weight {y : ComplexModel n} (hy : y ∈ S) (hp : DifferentiableAt ℝ p y)
    (v : ComplexModel n) :
    dDir v (fun y' => (p' y' : ℂ)) y = dDir v (fun y' => (p y' : ℂ)) y + dDir v t y / t y := by
  rw [dDir_congr_of_eventuallyEq (g.weight_eventuallyEq hy),
    dDir_add' (differentiableAt_ofReal_comp hp) (g.differentiableAt_log hy),
    dDir_ofReal_log_norm_sq (g.differentiableAt hy) (g.ne_zero y hy)]

theorem cweight_mul {y : ComplexModel n} (hy : y ∈ S) :
    cweight p' y * (t y * conj (t y)) = cweight p y := by
  have hpos : 0 < ‖t y‖ ^ 2 := by have := g.ne_zero y hy; positivity
  have hn0 : ((‖t y‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr (g.ne_zero y hy)).ne'
  rw [← ofReal_norm_sq_eq_mul_conj]
  simp only [cweight, g.weight y hy, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
    Real.exp_log hpos]
  push_cast
  field_simp

end GaugeData

/-! ### The weighted adjoint `ϑ` -/

theorem chartTheta_gauge {S : Set (ComplexModel n)} {t : ComplexModel n → ℂ}
    {p p' : ComplexModel n → ℝ} (g : GaugeData S t p p') {z : ComplexModel n} (hz : z ∈ S)
    (hp : DifferentiableAt ℝ p z) {u : ComplexModel n → ComplexModel n}
    (hu : DifferentiableAt ℝ u z) :
    chartTheta p' (fun y => t y • u y) z = t z * chartTheta p u z := by
  have htR : DifferentiableAt ℝ t z := (g.differentiableAt hz).restrictScalars ℝ
  have ht0 := g.ne_zero z hz
  simp only [chartTheta, deltaDir, PiLp.smul_apply, smul_eq_mul]
  have hj : ∀ j : Fin n, dDir (coordVec j) (fun y => t y * u y j) z =
      dDir (coordVec j) t z * u z j + t z * dDir (coordVec j) (fun y => u y j) z :=
    fun j => dDir_mul htR (differentiableAt_coord hu j)
  simp only [hj, g.dDir_weight hz hp, Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp
  ring

theorem chartTheta_finset_sum {p : ComplexModel n → ℝ} {ι : Type*} (s : Finset ι)
    {w : ι → ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hw : ∀ i ∈ s, DifferentiableAt ℝ (w i) z) :
    chartTheta p (fun y => ∑ i ∈ s, w i y) z = ∑ i ∈ s, chartTheta p (w i) z := by
  have hj : ∀ j : Fin n, dDir (coordVec j) (fun y => ∑ i ∈ s, w i y j) z =
      ∑ i ∈ s, dDir (coordVec j) (fun y => w i y j) z := fun j =>
    dDir_finset_sum_fun' s fun i hi => differentiableAt_coord (hw i hi) j
  simp only [chartTheta, deltaDir, euclid_sum_apply, hj, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

theorem chartTheta_eq_zero_of_eventuallyEq {p : ComplexModel n → ℝ}
    {u : ComplexModel n → ComplexModel n} {z : ComplexModel n} (hu : u =ᶠ[𝓝 z] 0) :
    chartTheta p u z = 0 := by
  simp only [chartTheta, deltaDir]
  have hj : ∀ j : Fin n, (fun y => u y j) =ᶠ[𝓝 z] fun _ => 0 := fun j =>
    hu.mono fun y hy => by simp [hy]
  simp [dDir_eq_zero_of_eventuallyEq_zero (hj _), (hj _).self_of_nhds]

theorem chartTheta_congr {p : ComplexModel n → ℝ} {u u' : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hu : u =ᶠ[𝓝 z] u') : chartTheta p u z = chartTheta p u' z := by
  have hj : ∀ j : Fin n, (fun y => u y j) =ᶠ[𝓝 z] fun y => u' y j := fun j =>
    hu.mono fun y hy => by simp [hy]
  simp only [chartTheta, deltaDir, dDir_congr_of_eventuallyEq (hj _), (hj _).self_of_nhds]

/-! ### The sesquilinear Levi form -/

/-- The sesquilinear Levi form `Levi(p)(u, w) = ∑_{j,k} ∂_{k̄} ∂_j p · u_j · conj w_k`. -/
def leviS (p : ComplexModel n → ℝ) (z u w : ComplexModel n) : ℂ :=
  ∑ j, ∑ k, dbarDir (coordVec k) (dDir (coordVec j) fun y => (p y : ℂ)) z * u j * conj (w k)

theorem leviS_gauge {S : Set (ComplexModel n)} {t : ComplexModel n → ℂ}
    {p p' : ComplexModel n → ℝ} (g : GaugeData S t p p') {z : ComplexModel n} (hz : z ∈ S)
    (hp : ContDiffAt ℝ 2 p z) (u w : ComplexModel n) : leviS p' z u w = leviS p z u w := by
  have hev : ∀ᶠ y in 𝓝 z, y ∈ S ∧ ContDiffAt ℝ 2 p y :=
    (g.isOpen.eventually_mem hz).and (hp.eventually (by simp))
  have hkey : ∀ j k : Fin n,
      dbarDir (coordVec k) (dDir (coordVec j) fun y => (p' y : ℂ)) z =
        dbarDir (coordVec k) (dDir (coordVec j) fun y => (p y : ℂ)) z := by
    intro j k
    have he : dDir (coordVec j) (fun y => (p' y : ℂ)) =ᶠ[𝓝 z]
        fun y => dDir (coordVec j) (fun y => (p y : ℂ)) y + dDir (coordVec j) t y / t y :=
      hev.mono fun y hy => g.dDir_weight hy.1 (hy.2.differentiableAt (by norm_num)) _
    have hd1 : DifferentiableOn ℂ (dDir (coordVec j) t) S :=
      differentiableOn_dDir_of_holomorphic g.isOpen g.holo (coordVec j)
    have hd2 : DifferentiableOn ℂ (fun y => dDir (coordVec j) t y / t y) S :=
      (hd1.mul (g.holo.inv g.ne_zero)).congr fun y _ => by simp [div_eq_mul_inv]
    have hh : DifferentiableAt ℂ (fun y => dDir (coordVec j) t y / t y) z :=
      hd2.differentiableAt (g.isOpen.mem_nhds hz)
    have hpc : ContDiffAt ℝ 2 (fun y => (p y : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp z hp
    rw [dbarDir_congr he, dbarDir_add (differentiableAt_dDir hpc) (hh.restrictScalars ℝ),
      dbarDir_holomorphic hh, add_zero]
  simp only [leviS, hkey]

theorem leviS_smul (p : ComplexModel n → ℝ) (z u w : ComplexModel n) (c : ℂ) :
    leviS p z (c • u) (c • w) = (c * conj c) * leviS p z u w := by
  unfold leviS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul]
  ring

theorem leviS_finset_sum_right (p : ComplexModel n → ℝ) (z u : ComplexModel n) {ι : Type*}
    (s : Finset ι) (w : ι → ComplexModel n) :
    leviS p z u (∑ i ∈ s, w i) = ∑ i ∈ s, leviS p z u (w i) := by
  simp only [leviS, euclid_sum_apply, map_sum, Finset.mul_sum]
  exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm

theorem leviS_zero_right (p : ComplexModel n → ℝ) (z u : ComplexModel n) :
    leviS p z u 0 = 0 := by
  simp [leviS]

/-- On the diagonal the sesquilinear Levi form is TN's Levi form. -/
theorem leviS_self {p : ComplexModel n → ℝ} {z : ComplexModel n} (hp : ContDiffAt ℝ 2 p z)
    (u : ComplexModel n) : leviS p z u u = (leviForm p z u : ℂ) := by
  have hpc : ContDiffAt ℝ 2 (fun y => (p y : ℂ)) z :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp z hp
  have hd : ∀ j, DifferentiableAt ℝ (dDir (coordVec j) fun y => (p y : ℂ)) z := fun j =>
    differentiableAt_dDir hpc
  have hu : (∑ j : Fin n, u j • coordVec j : ComplexModel n) = u := by
    ext i
    simp [coordVec, euclid_sum_apply]
  have hfun : dDir u (fun y => (p y : ℂ)) =
      fun y => ∑ j, u j * dDir (coordVec j) (fun y => (p y : ℂ)) y := by
    funext y
    have := dDir_sum_dir Finset.univ (fun j => u j) (fun j => (coordVec j : ComplexModel n))
      (fun y => (p y : ℂ)) y
    rwa [hu] at this
  have hdir : ∀ F : ComplexModel n → ℂ,
      dbarDir u F z = ∑ k, conj (u k) * dbarDir (coordVec k) F z := by
    intro F
    have := dbarDir_sum_dir Finset.univ (fun j => u j) (fun j => (coordVec j : ComplexModel n)) F z
    rwa [hu] at this
  rw [← dbarDir_dDir_ofReal_eq_leviForm hp, hfun, hdir]
  have hk : ∀ k, dbarDir (coordVec k)
      (fun y => ∑ j, u j * dDir (coordVec j) (fun y => (p y : ℂ)) y) z =
        ∑ j, u j * dbarDir (coordVec k) (dDir (coordVec j) fun y => (p y : ℂ)) z := by
    intro k
    rw [dbarDir_finset_sum_fun Finset.univ (fun j _ => (hd j).const_mul (u j))]
    simp_rw [dbarDir_const_mul_fun _ (hd _)]
  simp only [hk, leviS, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### `tr(A_u Ā_w)` -/

/-- `tr(A_u Ā_w) = ∑_{j,k} ∂_{k̄} u_j · conj(∂_{j̄} w_k)` for `A_u = ∂̄u`. -/
def trS (u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  ∑ j, ∑ k, dbarDir (coordVec k) (fun y => u y j) z * conj (dbarDir (coordVec j) (fun y => w y k) z)

theorem dbarDir_holo_mul {t f : ComplexModel n → ℂ} {z v : ComplexModel n}
    (ht : DifferentiableAt ℂ t z) (hf : DifferentiableAt ℝ f z) :
    dbarDir v (fun y => t y * f y) z = t z * dbarDir v f z := by
  rw [dbarDir_mul (ht.restrictScalars ℝ) hf, dbarDir_holomorphic ht, zero_mul, zero_add]

theorem trS_gauge {t : ComplexModel n → ℂ} {z : ComplexModel n} (ht : DifferentiableAt ℂ t z)
    {u w : ComplexModel n → ComplexModel n} (hu : DifferentiableAt ℝ u z)
    (hw : DifferentiableAt ℝ w z) :
    trS (fun y => t y • u y) (fun y => t y • w y) z = (t z * conj (t z)) * trS u w z := by
  unfold trS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [dbarDir_holo_mul ht (differentiableAt_coord hu j),
    dbarDir_holo_mul ht (differentiableAt_coord hw k), map_mul]
  ring

theorem trS_finset_sum_right (u : ComplexModel n → ComplexModel n) {ι : Type*} (s : Finset ι)
    {w : ι → ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hw : ∀ i ∈ s, DifferentiableAt ℝ (w i) z) :
    trS u (fun y => ∑ i ∈ s, w i y) z = ∑ i ∈ s, trS u (w i) z := by
  simp only [trS, euclid_sum_apply]
  have hk : ∀ j k : Fin n, dbarDir (coordVec j) (fun y => ∑ i ∈ s, w i y k) z =
      ∑ i ∈ s, dbarDir (coordVec j) (fun y => w i y k) z := fun j k =>
    dbarDir_finset_sum_fun s fun i hi => differentiableAt_coord (hw i hi) k
  simp only [hk, map_sum, Finset.mul_sum]
  exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm

theorem trS_congr {u u' w w' : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hu : u =ᶠ[𝓝 z] u') (hw : w =ᶠ[𝓝 z] w') : trS u w z = trS u' w' z := by
  have hu' : ∀ j : Fin n, (fun y => u y j) =ᶠ[𝓝 z] fun y => u' y j := fun j =>
    hu.mono fun y hy => by simp [hy]
  have hw' : ∀ j : Fin n, (fun y => w y j) =ᶠ[𝓝 z] fun y => w' y j := fun j =>
    hw.mono fun y hy => by simp [hy]
  simp only [trS, dbarDir_congr_of_eventuallyEq (hu' _), dbarDir_congr_of_eventuallyEq (hw' _)]

theorem trS_eq_zero_of_right {u w : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hw : w =ᶠ[𝓝 z] 0) : trS u w z = 0 := by
  have hw' : ∀ j : Fin n, (fun y => w y j) =ᶠ[𝓝 z] fun _ => 0 := fun j =>
    hw.mono fun y hy => by simp [hy]
  simp [trS, dbarDir_eq_zero_of_eventuallyEq_zero (hw' _)]

/-! ### The data pairing -/

theorem dbarPairing_gauge {t G : ComplexModel n → ℂ} {z : ComplexModel n}
    (ht : DifferentiableAt ℂ t z) (hG : DifferentiableAt ℝ G z) (v : ComplexModel n) :
    dbarPairing (fun y => t y * G y) z (t z • v) = (t z * conj (t z)) * dbarPairing G z v := by
  simp only [dbarPairing, PiLp.smul_apply, smul_eq_mul, dbarDir_holo_mul ht hG, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dbarPairing_finset_sum (G : ComplexModel n → ℂ) (z : ComplexModel n) {ι : Type*}
    (s : Finset ι) (w : ι → ComplexModel n) :
    dbarPairing G z (∑ i ∈ s, w i) = ∑ i ∈ s, dbarPairing G z (w i) := by
  simp only [dbarPairing, euclid_sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem dbarPairing_zero (G : ComplexModel n → ℂ) (z : ComplexModel n) :
    dbarPairing G z 0 = 0 := by
  simp [dbarPairing]

end SGPT.Trace.TwistedL2

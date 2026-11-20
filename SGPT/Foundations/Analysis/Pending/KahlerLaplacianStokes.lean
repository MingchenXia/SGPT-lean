import SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
import SGPT.Foundations.Analysis.Pending.SmoothCurrentClosedness
import SGPT.Foundations.Analysis.Pending.MixedCoefficientCongruence
import SGPT.Foundations.Analysis.Pending.ClosedTopCurrents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Stokes for the Kähler Laplacian; harmonic functions are constant

Let `(M, ω)` be a compact Kähler manifold of dimension `N` (`w : KahlerBackground N M`), with Kähler
volume `ω^N` (`IntegrationCurrent.kahlerVolume`), and let `Δ_ω u = Re tr(H⁻¹ ∂∂̄u)` be the Laplacian
of `ω` (`KahlerLaplacianChart.laplacian`, `H` the coefficient matrix of `ω` in a chart).

* `chartDensity_mul_chartLaplacian`: in a chart, `Δ_ω u · ω^N = N ddᶜu ∧ ω^{N-1}` at the level
  of densities, i.e. `ω^N-density · Δ_ω u = N Re C(∂∂̄u, H, …, H) / π^N`. This comes from the
  algebraic identity `C(K, H, …, H) = (N - 1)! det H · tr(H⁻¹K)`
  (`mixedCoefficient_cons_const`, `re_mixedCoefficient_const_mul_re_trace`).
* `integral_mixedCoefficient_cons_eq_zero` is the integration by parts for a `C²` first slot in
  `ℂ^N`. The cofactor field of smooth slots is divergence free (`MixedHessian`), so
  `C(∂∂̄a, ∂∂̄g₁, …) = ∑ ∂ⱼ(∂̄ₖa · cofⱼₖ)` (`mixedCoefficient_cons_eq_sum_wirt`) integrates to `0`.
* **`integral_laplacian_eq_zero`** (Stokes): `∫_M Δ_ω u ω^N = 0` for every `u` that is `C²` in
  every chart. The proof uses a partition of unity subordinate to slot charts (where `ω = ddᶜρ`)
  and the chart identity above (`integral_laplacian_eq_zero_of_slotChart`).
* `kahlerVolume_pos_of_isOpen`: `ω^N` charges every nonempty open set
  (`isOpenPosMeasure_kahlerVolume`).
* **`exists_eq_const_of_laplacian_eq_zero`**: a `C²` function with `Δ_ω u = 0` on a compact
  connected Kähler manifold is constant. This is item (1) of blueprint
  `bou:kahler-laplacian-solvability`. The proof uses `Δ(u²) - 2uΔu = 2⟪a∇v, ∇v⟫ ≥ 0`
  (`laplacian_mul_self_sub`) and Stokes for `u²`.

TN.5, blueprint `bou:kahler-laplacian-solvability`. The solvability statement (2) is in
`Pending.KahlerLaplacianSolvability`.
-/

noncomputable section

open Set Filter Topology MeasureTheory Function Complex
open scoped ContDiff ComplexOrder Matrix RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere MixedHessian

/-! ### Integration by parts for a `C²` slot in `ℂ^{m+1}` -/

section Euclidean

/-- A directional Wirtinger operator lowers the order of differentiability by one. -/
theorem contDiff_wirt_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : ℂ} {v : E}
    {f : E → ℂ} {k k' : WithTop ℕ∞} (hf : ContDiff ℝ k f) (hk : k' + 1 ≤ k) :
    ContDiff ℝ k' (wirt c v f) := by
  have hD : ContDiff ℝ k' (fderiv ℝ f) := hf.fderiv_right hk
  unfold wirt
  fun_prop

variable {m : ℕ}

/-- **Divergence form of a mixed coefficient with a `C²` first slot**: with the cofactor field of
smooth slots `g₁, …, gₘ`, `C(∂∂̄a, ∂∂̄g₁, …) = ∑ⱼₖ ∂ⱼ(∂̄ₖa · cofⱼₖ)`, because the cofactor field is
`∂`-divergence free (`MixedHessian.sum_dDir_cofactorField`). -/
theorem mixedCoefficient_cons_eq_sum_wirt {g : Fin m → ComplexModel (m + 1) → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {a : ComplexModel (m + 1) → ℝ} (ha : ContDiff ℝ 2 a)
    (z : ComplexModel (m + 1)) :
    mixedCoefficient (Fin.cons (complexHessian a z) (fun i ↦ complexHessian (g i) z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      ∑ j, ∑ k, wirt (-I) (coordinateVector j) (fun y ↦ wirt I (coordinateVector k)
        (fun y ↦ (a y : ℂ)) y * cofactorField g j k y) z := by
  have hA : ContDiff ℝ 2 (fun y ↦ (a y : ℂ)) := ofRealCLM.contDiff.comp ha
  have hF : ∀ k : Fin (m + 1), ContDiff ℝ 1 (wirt I (coordinateVector k) (fun y ↦ (a y : ℂ))) :=
    fun k => contDiff_wirt_of_le hA (by norm_num)
  have hC := contDiff_cofactorField hg
  have hterm : ∀ j k, wirt (-I) (coordinateVector j) (fun y ↦ wirt I (coordinateVector k)
      (fun y ↦ (a y : ℂ)) y * cofactorField g j k y) z =
      complexHessian a z j k * cofactorField g j k z +
        wirt I (coordinateVector k) (fun y ↦ (a y : ℂ)) z *
          wirt (-I) (coordinateVector j) (cofactorField g j k) z := by
    intro j k
    rw [wirt_mul ((hF k).differentiable one_ne_zero z) ((hC j k).differentiable (by simp) z),
      complexHessian_eq_wirt ha.contDiffAt j k]
  simp only [hterm, Finset.sum_add_distrib, mixedCoefficient_cons]
  have e1 : ∑ j, ∑ k, wirt I (coordinateVector k) (fun y ↦ (a y : ℂ)) z *
      wirt (-I) (coordinateVector j) (cofactorField g j k) z = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [← Finset.mul_sum, sum_dDir_cofactorField hg, mul_zero]
  rw [e1, add_zero]
  rfl

/-- **Stokes for a `C²` slot**: for `a` of class `C²` with compact support and smooth `g₁, …, gₘ`,
`z ↦ C(∂∂̄a, ∂∂̄g₁, …, ∂∂̄gₘ)` is integrable with integral `0`. -/
theorem integral_mixedCoefficient_cons_eq_zero {g : Fin m → ComplexModel (m + 1) → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {a : ComplexModel (m + 1) → ℝ} (ha : ContDiff ℝ 2 a)
    (hac : HasCompactSupport a) :
    Integrable (fun z ↦ mixedCoefficient (Fin.cons (complexHessian a z)
      (fun i ↦ complexHessian (g i) z) : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) ∧
    ∫ z, mixedCoefficient (Fin.cons (complexHessian a z) (fun i ↦ complexHessian (g i) z) :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = 0 := by
  have hA : ContDiff ℝ 2 (fun y ↦ (a y : ℂ)) := ofRealCLM.contDiff.comp ha
  have hAc : HasCompactSupport (fun y ↦ (a y : ℂ)) := hac.comp_left Complex.ofReal_zero
  obtain ⟨P, hP⟩ : ∃ P : Fin (m + 1) → Fin (m + 1) → ComplexModel (m + 1) → ℂ,
      P = fun j k y ↦ wirt I (coordinateVector k) (fun y ↦ (a y : ℂ)) y * cofactorField g j k y :=
    ⟨_, rfl⟩
  have hPs : ∀ j k, ContDiff ℝ 1 (P j k) := fun j k => by
    rw [hP]
    exact (contDiff_wirt_of_le hA (by norm_num)).mul
      ((contDiff_cofactorField hg j k).of_le (by simp))
  have hPc : ∀ j k, HasCompactSupport (P j k) := fun j k => by
    rw [hP]
    exact (HasCompactSupport.wirt hAc _ _).mul_right
  have hi : ∀ j k, Integrable (wirt (-I) (coordinateVector j) (P j k)) := fun j k =>
    (contDiff_wirt_of_le (k' := 0) (hPs j k) (by simp)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.wirt (hPc j k) _ _)
  have heq : (fun z ↦ mixedCoefficient (Fin.cons (complexHessian a z)
      (fun i ↦ complexHessian (g i) z) : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) =
      fun z => ∑ j, ∑ k, wirt (-I) (coordinateVector j) (P j k) z := by
    funext z
    rw [mixedCoefficient_cons_eq_sum_wirt hg ha z, hP]
  rw [heq]
  refine ⟨integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi j k, ?_⟩
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi j k]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hi j k]
  exact Finset.sum_eq_zero fun k _ => integral_wirt_eq_zero _ (hPs j k) (hPc j k) _ _

end Euclidean

/-! ### The trace identity `N C(K, H, …, H) = N! det H · tr(H⁻¹K)` -/

section Algebra

variable {m : ℕ}

/-- `C(K, H, …, H) = m! det H · tr(H⁻¹ K)` for `H` invertible (`m + 1` slots). -/
theorem mixedCoefficient_cons_const {H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hH : IsUnit H.det) (K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    mixedCoefficient (Fin.cons K (fun _ : Fin m => H) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      (m.factorial : ℂ) * H.det * (H⁻¹ * K).trace := by
  have hfun : (Fin.cons K (fun _ : Fin m => H) :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = fun i => H *
        (Fin.cons (H⁻¹ * K) (fun _ : Fin m => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i * 1 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH]
    · simp
  rw [hfun, MixedMongeAmpere.mixedCoefficient_mul_mul, Matrix.det_one, mul_one,
    ClosedTopCurrents.mixedCoefficient_cons_one]
  ring

/-- **The density identity behind `Δ_ω u = N ddᶜu ∧ ω^{N-1} / ω^N`**: for a positive definite
`H` and any `K`, `Re C(H, …, H) · Re tr(H⁻¹K) = (m + 1) Re C(K, H, …, H)` (`m + 1` slots). -/
theorem re_mixedCoefficient_const_mul_re_trace {H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hH : H.PosDef) (K : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    (mixedCoefficient (fun _ : Fin (m + 1) => H)).re * (H⁻¹ * K).trace.re =
      (m + 1) * (mixedCoefficient (Fin.cons K (fun _ : Fin m => H) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re := by
  have hdet := hH.det_pos
  have him : H.det.im = 0 := (Complex.pos_iff.mp hdet).2.symm
  rw [mixedCoefficient_cons_const (isUnit_iff_ne_zero.mpr hdet.ne') K,
    mixedCoefficient_diagonal]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, him, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, zero_mul, sub_zero, mul_zero, Complex.mul_im,
    Complex.add_re, Complex.one_re]
  ring

end Algebra

/-! ### The Laplacian of a Hermitian form: sums, locality, continuity -/

section Laplacian

open KahlerLaplacianChart

/-- Second derivatives of finite sums of `C²` functions. -/
theorem fderiv_fderiv_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) {v : ι → E → ℝ} {z : E} (hv : ∀ i ∈ s, ContDiffAt ℝ 2 (v i) z) :
    fderiv ℝ (fderiv ℝ (fun w => ∑ i ∈ s, v i w)) z = ∑ i ∈ s, fderiv ℝ (fderiv ℝ (v i)) z := by
  have hev : ∀ᶠ w in 𝓝 z, ∀ i ∈ s, DifferentiableAt ℝ (v i) w :=
    (Filter.eventually_all_finset s).2 fun i hi =>
      ((hv i hi).eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have h1 : fderiv ℝ (fun w => ∑ i ∈ s, v i w) =ᶠ[𝓝 z] fun w => ∑ i ∈ s, fderiv ℝ (v i) w := by
    filter_upwards [hev] with w hw
    exact fderiv_fun_sum hw
  rw [h1.fderiv_eq]
  exact fderiv_fun_sum fun i hi =>
    ((hv i hi).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The Laplacian is additive** on functions that are `C²` in every chart. -/
theorem laplacian_sum (g : SmoothRealForm n M 2) {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ∀ e : ComplexChart n M,
      ContDiffOn ℝ 2 (fun z => f i (e.val.symm z)) e.val.target) (y : M) :
    laplacian g (fun x => ∑ i ∈ s, f i x) y = ∑ i ∈ s, laplacian g (f i) y := by
  set e := complexChartAt (n := n) y with he
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  have hd : ∀ i ∈ s, ContDiffAt ℝ 2 (fun z => f i (e.val.symm z)) (e.val y) := fun i hi =>
    (hf i hi e).contDiffAt (e.val.open_target.mem_nhds hz)
  have hsum := fderiv_fderiv_sum s hd
  simp only [laplacian, chartLaplacian_eq_hessTrace realBasis, ← he]
  rw [hsum]
  unfold EllipticMeanValue.hessTrace
  simp only [FunLike.coe_sum, Finset.sum_apply]
  exact Finset.sum_comm

/-- **Locality**: the Laplacian vanishes where the function vanishes near the point. -/
theorem laplacian_eq_zero_of_notMem_tsupport (g : SmoothRealForm n M 2) {f : M → ℝ} {y : M}
    (hy : y ∉ tsupport f) : laplacian g f y = 0 := by
  have h0 := SmoothCurrentClosedness.chart_eventuallyEq_zero hy
    (mem_complexChartAt_source (n := n) y)
  simp only [laplacian, chartLaplacian]
  rw [complexHessian_congr' h0, complexHessian_eq_zero_of_notMem_tsupport (by simp)]
  simp

/-- The chart Laplacian of a `C²` function is continuous on the chart target. -/
theorem continuousOn_chartLaplacian {g : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (e : ComplexChart n M) {v : ComplexModel n → ℝ} (hv : ContDiffOn ℝ 2 v e.val.target) :
    ContinuousOn (chartLaplacian g e v) e.val.target := by
  have ha : ContinuousOn (fun z => lapCoeff (normalizedHermitianMatrix (g.coeff e z)))
      e.val.target :=
    (contDiffOn_lapCoeff e.val.open_target (g.smooth e) fun z hz =>
      isUnit_iff_ne_zero.mpr (posDef_coeff hg hz).det_pos.ne').continuousOn
  have hD2 : ContinuousOn (fun z => fderiv ℝ (fderiv ℝ v) z) e.val.target :=
    (hv.fderiv_of_isOpen e.val.open_target (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
      e.val.open_target le_rfl
  have heq : chartLaplacian g e v = fun z => EllipticMeanValue.hessTrace realBasis
      (lapCoeff (normalizedHermitianMatrix (g.coeff e z))) (fderiv ℝ (fderiv ℝ v) z) :=
    funext fun z => chartLaplacian_eq_hessTrace realBasis g e v z
  rw [heq]
  unfold EllipticMeanValue.hessTrace
  exact continuousOn_finsetSum _ fun i _ =>
    (hD2.clm_apply continuousOn_const).clm_apply (ha.clm_apply continuousOn_const)

/-- **The Laplacian of a `C²` function is continuous** on `M`. -/
theorem continuous_laplacian {g : SmoothRealForm n M 2} (hg : g.IsHermitian) {u : M → ℝ}
    (hu : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun w => u (e.val.symm w)) e.val.target) :
    Continuous (laplacian g u) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  set e := complexChartAt (n := n) y with he
  have hy : y ∈ e.val.source := mem_complexChartAt_source y
  have hev : (fun y' => chartLaplacian g e (fun w => u (e.val.symm w)) (e.val y')) =ᶠ[𝓝 y]
      laplacian g u := by
    filter_upwards [e.val.open_source.mem_nhds hy] with y' hy'
    exact (laplacian_eq hg hu hy').symm
  refine ContinuousAt.congr ?_ hev
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  exact ((continuousOn_chartLaplacian hg e (hu e)).continuousAt
    (e.val.open_target.mem_nhds hz)).comp (e.val.continuousAt hy)

/-- The chart representative of a function that is `C²` in a chart, supported in a compact subset
of the chart source, extended by zero: a `C²` function with compact support inside the image of
the support. -/
theorem contDiff_indicator_comp_symm_two (e : ComplexChart n M) {f : M → ℝ}
    (hf : ContDiffOn ℝ 2 (fun z => f (e.val.symm z)) e.val.target) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) :
    ContDiff ℝ 2 (e.val.target.indicator (fun z => f (e.val.symm z))) ∧
      HasCompactSupport (e.val.target.indicator (fun z => f (e.val.symm z))) ∧
      tsupport (e.val.target.indicator (fun z => f (e.val.symm z))) ⊆ e.val '' tsupport f := by
  set L := e.val '' tsupport f with hL
  have hLc : IsCompact L := hc.image_of_continuousOn (e.val.continuousOn.mono hs)
  have hLt : L ⊆ e.val.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.val.map_source (hs hy)
  have hzero : ∀ z ∉ L, e.val.target.indicator (fun z => f (e.val.symm z)) z = 0 := fun z hz => by
    by_cases hzt : z ∈ e.val.target
    · rw [indicator_of_mem hzt]
      exact image_eq_zero_of_notMem_tsupport fun h => hz ⟨_, h, e.val.right_inv hzt⟩
    · exact indicator_of_notMem hzt _
  have hsupp : support (e.val.target.indicator (fun z => f (e.val.symm z))) ⊆ L := fun z hz => by
    by_contra h
    exact hz (hzero z h)
  refine ⟨contDiff_iff_contDiffAt.2 fun z => ?_,
    HasCompactSupport.of_support_subset_isCompact hLc hsupp,
    closure_minimal hsupp hLc.isClosed⟩
  by_cases hzt : z ∈ e.val.target
  · have heq : e.val.target.indicator (fun z => f (e.val.symm z)) =ᶠ[𝓝 z]
        fun z => f (e.val.symm z) := by
      filter_upwards [e.val.open_target.mem_nhds hzt] with w hw using indicator_of_mem hw _
    exact (hf.contDiffAt (e.val.open_target.mem_nhds hzt)).congr_of_eventuallyEq heq
  · have hzL : z ∉ L := fun h => hzt (hLt h)
    have heq : e.val.target.indicator (fun z => f (e.val.symm z)) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hLc.isClosed.isOpen_compl.mem_nhds hzL] with w hw using hzero w hw
    exact contDiffAt_const.congr_of_eventuallyEq heq

end Laplacian

/-! ### Stokes: `∫_M Δ_ω u ω^N = 0` for `u` of class `C²` -/

section Stokes

open KahlerLaplacianChart FirstPass.PositiveClasses ProductTestForms IntegrationCurrent
  TopDegreeDensity SmoothMixedMeasureDensity GlobalNonPluripolar GlobalSlotStokes ChartPartition
  SmoothCurrentClosedness

/-- **`Δ_ω u · ω^N = N ddᶜu ∧ ω^{N-1}` in a chart**: the density of the Kähler volume times the
chart Laplacian is `(m + 1) Re C(∂∂̄v, H, …, H) / π^{m+1}`, `H` the coefficient matrix of `ω`. -/
theorem chartDensity_mul_chartLaplacian {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (w : KahlerBackground (m + 1) M) (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)}
    (hz : z ∈ e.val.target) (v : ComplexModel (m + 1) → ℝ) :
    (chartDensity (fun _ : Fin (m + 1) => w.form) e z).toReal * chartLaplacian w.form.val e v z =
      (m + 1) * (mixedCoefficient (Fin.cons (complexHessian v z)
        (fun _ : Fin m => normalizedHermitianMatrix (w.form.val.coeff e z)) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re / Real.pi ^ (m + 1) := by
  have hH := posDef_coeff w.isKahler.1 hz
  have h11 : IsOneOne (w.form.val.coeff e z) := (w.isKahler.1 e z hz).1
  have hden : actualMixedTopDensity (fun _ : Fin (m + 1) => w.form.val.coeff e z) =
      (mixedCoefficient (fun _ : Fin (m + 1) =>
        normalizedHermitianMatrix (w.form.val.coeff e z))).re / Real.pi ^ (m + 1) := by
    rw [actualMixedTopDensity_eq_normalizedMixedTopDensity _ fun _ => h11]
    rfl
  have hpos : 0 < (mixedCoefficient (fun _ : Fin (m + 1) =>
      normalizedHermitianMatrix (w.form.val.coeff e z))).re := by
    rw [mixedCoefficient_diagonal]
    have hd := hH.det_pos
    have him : (normalizedHermitianMatrix (w.form.val.coeff e z)).det.im = 0 :=
      (Complex.pos_iff.mp hd).2.symm
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, him, mul_zero, sub_zero]
    exact mul_pos (by exact_mod_cast Nat.factorial_pos _) (Complex.pos_iff.mp hd).1
  have hc : (chartDensity (fun _ : Fin (m + 1) => w.form) e z).toReal =
      (mixedCoefficient (fun _ : Fin (m + 1) =>
        normalizedHermitianMatrix (w.form.val.coeff e z))).re / Real.pi ^ (m + 1) := by
    rw [chartDensity, ENNReal.toReal_ofReal (by rw [hden]; positivity), hden]
  rw [hc, chartLaplacian, div_mul_eq_mul_div, re_mixedCoefficient_const_mul_re_trace hH]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Stokes in a slot chart**: `∫_M Δ_ω f ω^N = 0` for `f` of class `C²`, supported in a compact
subset of the source of a slot chart. -/
theorem integral_laplacian_eq_zero_of_slotChart {m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M] [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] (w : KahlerBackground (m + 1) M)
    (J : SlotChart (fun _ : Fin (m + 1) => w.form) w.form) {f : M → ℝ}
    (hf : ∀ e : ComplexChart (m + 1) M, ContDiffOn ℝ 2 (fun z => f (e.val.symm z)) e.val.target)
    (hfJ : tsupport f ⊆ (J.source : Set M)) (hfK : IsCompact (tsupport f)) :
    ∫ x, laplacian w.form.val f x ∂(kahlerVolume w) = 0 := by
  classical
  have hg : w.form.val.IsHermitian := w.isKahler.1
  set e := J.chart with he
  set D := J.domain with hD
  have hDt : (D : Set (ComplexModel (m + 1))) ⊆ e.val.target := J.domain_le_target
  have hzero : ∀ x, x ∉ (J.source : Set M) → laplacian w.form.val f x = 0 := fun x hx =>
    laplacian_eq_zero_of_notMem_tsupport _ fun h => hx (hfJ h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have himage : (J.source : Set M) = e.val.symm '' D := by
    rw [e.val.symm_image_eq_source_inter_preimage hDt]
    rfl
  have hω : ∀ _ : Fin (m + 1), ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin (m + 1) => w.form) (fun _ _ => 0) hω := rfl
  rw [himage, hvol, setIntegral_image_eq hω e D.isOpen.measurableSet hDt
    (continuous_laplacian hg hf)]
  -- the chart representative `V` of `f`
  have hfe : tsupport f ⊆ e.val.source := hfJ.trans fun x hx => hx.1
  obtain ⟨hVs, hVc, hVt⟩ := contDiff_indicator_comp_symm_two e (hf e) hfK hfe
  set V := e.val.target.indicator (fun z => f (e.val.symm z)) with hV
  have hVD : tsupport V ⊆ D := hVt.trans (by rintro _ ⟨x, hx, rfl⟩; exact (hfJ hx).2)
  -- a cut-off of the local potential of `ω`
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact (Ω := D) hVc hVD
  set ψ : ComplexModel (m + 1) → ℝ := ⇑χ with hψ
  have hψs : ContDiff ℝ ∞ ψ := χ.contDiff
  have hψD : tsupport ψ ⊆ (D : Set (ComplexModel (m + 1))) := χ.tsupport_subset
  set ρt : ComplexModel (m + 1) → ℝ := fun z => ψ z * J.potential 0 z with hρt
  have hρts : ContDiff ℝ ∞ ρt :=
    contDiff_mul_of_tsupport_subset D.isOpen hψs hψD (J.localPotential 0).2.2.1
  obtain ⟨hXi, hX0⟩ := integral_mixedCoefficient_cons_eq_zero (g := fun _ : Fin m => ρt)
    (fun _ => hρts) hVs hVc
  set X : ComplexModel (m + 1) → ℂ := fun z => mixedCoefficient (Fin.cons (complexHessian V z)
    (fun _ : Fin m => complexHessian ρt z) : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    with hX
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hpt : ∀ z ∈ (D : Set (ComplexModel (m + 1))),
      (chartDensity (fun _ : Fin (m + 1) => w.form) e z).toReal *
          laplacian w.form.val f (e.val.symm z) = (m + 1) * (X z).re / Real.pi ^ (m + 1) := by
    intro z hz
    have hzt := hDt hz
    have hl : laplacian w.form.val f (e.val.symm z) = chartLaplacian w.form.val e V z := by
      rw [laplacian_eq hg hf (e.val.map_target hzt), e.val.right_inv hzt]
      unfold chartLaplacian
      congr 3
      refine complexHessian_congr' ?_
      filter_upwards [e.val.open_target.mem_nhds hzt] with y hy
      rw [hV, indicator_of_mem hy]
    rw [hl, chartDensity_mul_chartLaplacian w e hzt V]
    congr 3
    by_cases hzV : z ∈ tsupport V
    · have hψ1 : ∀ᶠ y in 𝓝 z, ψ y = 1 := hχ1.filter_mono (nhds_le_nhdsSet hzV)
      have hloc : J.potential 0 =ᶠ[𝓝 z] ρt := by
        filter_upwards [hψ1] with y hy
        simp [hρt, hy]
      have hρC : ContDiffAt ℝ 2 (J.potential 0) z :=
        ((J.localPotential 0).2.2.1.contDiffAt (D.isOpen.mem_nhds hz)).of_le h2
      have hH : normalizedHermitianMatrix (w.form.val.coeff e z) = complexHessian ρt z := by
        rw [← complexHessian_congr' hloc, ← normalizedHermitianMatrix_smoothDDC hρC,
          (J.localPotential 0).2.2.2 hz]
      simp only [hX, hH]
    · rw [complexHessian_eq_zero_of_notMem_tsupport hzV]
      simp [hX, MixedHessian.mixedCoefficient_cons, complexHessian_eq_zero_of_notMem_tsupport hzV]
  rw [setIntegral_congr_fun D.isOpen.measurableSet hpt]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    rw [hX]
    simp only
    rw [mixedCoefficient_cons_eq_zero_of_notMem_tsupport fun h => hz (hVD h), Complex.zero_re,
      mul_zero, zero_div]]
  have hre : ∫ z, (X z).re = (∫ z, X z).re := integral_re (𝕜 := ℂ) hXi
  rw [integral_div, integral_const_mul, hre, hX0]
  simp

/-- **Stokes on a compact Kähler manifold for `C²` functions**: `∫_M Δ_ω u ω^N = 0`. -/
theorem integral_laplacian_eq_zero (w : KahlerBackground n M) {u : M → ℝ}
    (hu : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun z => u (e.val.symm z)) e.val.target) :
    ∫ x, laplacian w.form.val u x ∂(kahlerVolume w) = 0 := by
  classical
  rcases n with _ | m
  · have h0 : ∀ x, laplacian w.form.val u x = 0 := fun x => by
      simp [laplacian, chartLaplacian, Matrix.trace]
    simp [h0]
  · have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    obtain ⟨r, χ, idx, hχs, -, hχS, hχK, hsum⟩ :=
      exists_chartSmooth_partitionOfUnity (n := m + 1)
        (fun J : SlotChart (fun _ : Fin (m + 1) => w.form) w.form => J.source)
        fun x => SlotChart.exists_mem_source _ w.form x
    have hpiece : ∀ a, ∀ e : ComplexChart (m + 1) M, ContDiffOn ℝ 2
        (fun z => (fun y => χ a y * u y) (e.val.symm z)) e.val.target :=
      fun a e => (((hχs a) e).of_le h2).mul (hu e)
    have hsplit : ∀ x, laplacian w.form.val u x =
        ∑ a, laplacian w.form.val (fun y => χ a y * u y) x := by
      intro x
      have hfun : u = fun y => ∑ a, χ a y * u y := funext fun y => by
        rw [← Finset.sum_mul, hsum, one_mul]
      conv_lhs => rw [hfun]
      exact laplacian_sum _ _ (fun a _ => hpiece a) x
    simp_rw [hsplit]
    have hint : ∀ a, Integrable (laplacian w.form.val (fun y => χ a y * u y)) (kahlerVolume w) :=
      fun a => (continuous_laplacian w.isKahler.1 (hpiece a)).integrable_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
    rw [integral_finsetSum _ fun a _ => hint a]
    refine Finset.sum_eq_zero fun a _ => ?_
    exact integral_laplacian_eq_zero_of_slotChart w (idx a) (hpiece a)
      (tsupport_mul_subset_left.trans (hχS a))
      ((hχK a).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)

end Stokes

/-! ### The Kähler volume charges every nonempty open set -/

section Volume

open KahlerLaplacianChart FirstPass.PositiveClasses ProductTestForms IntegrationCurrent
  TopDegreeDensity SmoothMixedMeasureDensity GlobalNonPluripolar SmoothCurrentClosedness

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The Kähler volume of a nonempty open set is positive.** -/
theorem kahlerVolume_pos_of_isOpen (w : KahlerBackground n M) {U : Set M} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < kahlerVolume w U := by
  obtain ⟨x, hx⟩ := hne
  set e := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hz0 : e.val x ∈ e.val.target := e.val.map_source hxs
  have hVo : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) := e.val.isOpen_inter_preimage_symm hU
  have hz0V : e.val x ∈ e.val.target ∩ e.val.symm ⁻¹' U :=
    ⟨hz0, by simp [e.val.left_inv hxs, hx]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hVo _ hz0V
  set K := Metric.closedBall (e.val x) (δ / 2) with hK
  have hKV : K ⊆ e.val.target ∩ e.val.symm ⁻¹' U :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  have hKt : K ⊆ e.val.target := fun z hz => (hKV hz).1
  have hKU : e.val.symm '' K ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hKV hz).2
  have hω : ∀ _ : Fin n, ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin n => w.form) (fun _ _ => 0) hω := rfl
  have h1 := setIntegral_image_eq hω e Metric.isClosed_closedBall.measurableSet hKt
    (continuous_const (y := (1 : ℝ)))
  rw [← hvol, setIntegral_const, smul_eq_mul, mul_one] at h1
  -- the density is continuous and positive on the chart target
  obtain ⟨F, hF⟩ : ∃ F : ComplexModel n → ℝ,
      F = fun z => actualMixedTopDensity (fun _ : Fin n => w.form.val.coeff e z) := ⟨_, rfl⟩
  have hFpos : ∀ z ∈ e.val.target, 0 < F z := fun z hz => by
    have hden : topDensity ((formPow w.form.val n).coeff e z) = F z := by
      rw [formPow_coeff, topDensity_formPower, ← actualMixedTopDensity_const, hF]
    rw [← hden]
    exact topDensity_formPow_pos w.isKahler.1 hz
  have hFc : ContinuousOn F e.val.target := by
    rw [hF]
    exact continuous_actualMixedTopDensity.comp_continuousOn
      (continuousOn_pi.mpr fun _ => (w.form.val.smooth e).continuousOn)
  have hcongr : ∀ z ∈ K, (chartDensity (fun _ : Fin n => w.form) e z).toReal * 1 = F z :=
    fun z hz => by
      have hFz : F z = actualMixedTopDensity (fun _ : Fin n => w.form.val.coeff e z) := by rw [hF]
      rw [mul_one, chartDensity, ENNReal.toReal_ofReal (hFz ▸ (hFpos z (hKt hz)).le), hFz]
  rw [setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet hcongr] at h1
  have hKc : IsCompact K := isCompact_closedBall _ _
  obtain ⟨z1, hz1K, hz1⟩ := hKc.exists_isMinOn
    ⟨e.val x, Metric.mem_closedBall_self (by positivity)⟩ (hFc.mono hKt)
  have hvolK : 0 < volume.real K := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (half_pos hδ)).ne'
      measure_closedBall_lt_top.ne
  have hint : 0 < ∫ z in K, F z := by
    have hle : ∫ _ in K, F z1 ≤ ∫ z in K, F z :=
      setIntegral_mono_on (continuousOn_const.integrableOn_compact hKc)
        ((hFc.mono hKt).integrableOn_compact hKc) Metric.isClosed_closedBall.measurableSet
        fun z hz => hz1 hz
    rw [setIntegral_const, smul_eq_mul] at hle
    exact lt_of_lt_of_le (mul_pos hvolK (hFpos z1 (hKt hz1K))) hle
  rw [← h1, measureReal_def] at hint
  exact lt_of_lt_of_le (ENNReal.toReal_pos_iff.1 hint).1 (measure_mono hKU)

instance isOpenPosMeasure_kahlerVolume (w : KahlerBackground n M) :
    (kahlerVolume w).IsOpenPosMeasure :=
  ⟨fun _ hU hne => (kahlerVolume_pos_of_isOpen w hU hne).ne'⟩

end Volume

/-! ### A harmonic `C²` function on a compact connected Kähler manifold is constant -/

section Harmonic

open KahlerLaplacianChart FirstPass.PositiveClasses IntegrationCurrent

/-- `D²(v²) = 2 (v D²v + Dv ⊗ Dv)`. -/
theorem fderiv_fderiv_mul_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E → ℝ}
    {z : E} (hv : ContDiffAt ℝ 2 v z) :
    fderiv ℝ (fderiv ℝ (fun w => v w * v w)) z =
      (2 : ℝ) • (v z • fderiv ℝ (fderiv ℝ v) z + (fderiv ℝ v z).smulRight (fderiv ℝ v z)) := by
  have hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ v w :=
    (hv.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
  have h1 : fderiv ℝ (fun w => v w * v w) =ᶠ[𝓝 z] fun w => (2 : ℝ) • (v w • fderiv ℝ v w) := by
    filter_upwards [hd] with w hw
    rw [fderiv_fun_mul hw hw, two_smul]
  rw [h1.fderiv_eq]
  have hD : HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) z) z :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hvz : HasFDerivAt v (fderiv ℝ v z) z := (hv.differentiableAt (by simp)).hasFDerivAt
  exact ((hvz.smul hD).const_smul (2 : ℝ)).fderiv

/-- `A : (L ⊗ L) = ⟪A ∇L, ∇L⟫`, `∇L` the vector representing the linear form `L`. -/
theorem hessTrace_smulRight_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (L : E →L[ℝ] ℝ) :
    EllipticMeanValue.hessTrace b A (L.smulRight L) =
      ⟪A ((InnerProductSpace.toDual ℝ E).symm L), (InnerProductSpace.toDual ℝ E).symm L⟫ := by
  set g := (InnerProductSpace.toDual ℝ E).symm L with hg
  have hL : ∀ x, L x = ⟪g, x⟫ := fun x => InnerProductSpace.toDual_symm_apply.symm
  have hgsum : g = ∑ i, L (b i) • b i := by
    conv_lhs => rw [← b.sum_repr' g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hL, real_inner_comm]
  have hR : ⟪A g, g⟫ = L (A g) := by rw [hL, real_inner_comm]
  rw [hR]
  conv_rhs => rw [hgsum]
  unfold EllipticMeanValue.hessTrace
  simp [map_sum, map_smul, smul_eq_mul]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`Δ(u²) - 2uΔu = 2|∂u|²_ω`** in any chart: `2 ⟪a ∇v, ∇v⟫` with `v = u ∘ e⁻¹` and
`a = ¼ conj(H⁻¹)` the real coefficient of the Laplacian. -/
theorem laplacian_mul_self_sub {g : SmoothRealForm n M 2} (hg : g.IsHermitian) {u : M → ℝ}
    (hu : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun z => u (e.val.symm z)) e.val.target)
    {e : ComplexChart n M} {y : M} (hy : y ∈ e.val.source) :
    laplacian g (fun x => u x * u x) y - 2 * u y * laplacian g u y =
      2 * ⟪lapCoeff (normalizedHermitianMatrix (g.coeff e (e.val y)))
          ((InnerProductSpace.toDual ℝ (ComplexModel n)).symm
            (fderiv ℝ (fun z => u (e.val.symm z)) (e.val y))),
        (InnerProductSpace.toDual ℝ (ComplexModel n)).symm
          (fderiv ℝ (fun z => u (e.val.symm z)) (e.val y))⟫ := by
  have hu2 : ∀ e : ComplexChart n M,
      ContDiffOn ℝ 2 (fun z => (fun x => u x * u x) (e.val.symm z)) e.val.target :=
    fun e => (hu e).mul (hu e)
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  have hv : ContDiffAt ℝ 2 (fun z => u (e.val.symm z)) (e.val y) :=
    (hu e).contDiffAt (e.val.open_target.mem_nhds hz)
  have hD := fderiv_fderiv_mul_self hv
  have huy : u (e.val.symm (e.val y)) = u y := by rw [e.val.left_inv hy]
  rw [laplacian_eq hg hu2 hy, laplacian_eq hg hu hy, chartLaplacian_eq_hessTrace realBasis,
    chartLaplacian_eq_hessTrace realBasis, ← hessTrace_smulRight_self realBasis]
  beta_reduce at hD ⊢
  rw [hD, SchauderBlowup.hessTrace_smul_right, WholeSpaceSolvability.hessTrace_add_right,
    SchauderBlowup.hessTrace_smul_right, huy]
  ring

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **A harmonic `C²` function on a compact connected Kähler manifold is constant**
(blueprint `bou:kahler-laplacian-solvability` (1)): by Stokes, `∫ Δ(u²) ω^N = 0`, while
`Δ(u²) = 2|∂u|²_ω ≥ 0` is continuous and `ω^N` charges open sets; so `du = 0`. -/
theorem exists_eq_const_of_laplacian_eq_zero [ConnectedSpace M] (w : KahlerBackground n M)
    {u : M → ℝ}
    (hu : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun z => u (e.val.symm z)) e.val.target)
    (h : ∀ y, laplacian w.form.val u y = 0) : ∃ c, ∀ y, u y = c := by
  have hg := w.isKahler.1
  have hu2 : ∀ e : ComplexChart n M,
      ContDiffOn ℝ 2 (fun z => (fun x => u x * u x) (e.val.symm z)) e.val.target :=
    fun e => (hu e).mul (hu e)
  have hform : ∀ (e : ComplexChart n M) (y : M), y ∈ e.val.source →
      laplacian w.form.val (fun x => u x * u x) y =
        2 * ⟪lapCoeff (normalizedHermitianMatrix (w.form.val.coeff e (e.val y)))
            ((InnerProductSpace.toDual ℝ (ComplexModel n)).symm
              (fderiv ℝ (fun z => u (e.val.symm z)) (e.val y))),
          (InnerProductSpace.toDual ℝ (ComplexModel n)).symm
            (fderiv ℝ (fun z => u (e.val.symm z)) (e.val y))⟫ := by
    intro e y hy
    have := laplacian_mul_self_sub hg hu hy
    rwa [h y, mul_zero, sub_zero] at this
  have hpos : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, v ≠ 0 →
        0 < ⟪lapCoeff (normalizedHermitianMatrix (w.form.val.coeff e z)) v, v⟫ :=
    fun e z hz v hv => lapCoeff_pos (posDef_coeff hg hz) hv
  have hnn : 0 ≤ laplacian w.form.val (fun x => u x * u x) := fun y => by
    have hys := mem_complexChartAt_source (n := n) y
    rw [hform _ y hys]
    by_cases h0 : (InnerProductSpace.toDual ℝ (ComplexModel n)).symm
        (fderiv ℝ (fun z => u ((complexChartAt (n := n) y).val.symm z))
          ((complexChartAt (n := n) y).val y)) = 0
    · rw [h0]
      simp
    · exact (mul_pos two_pos (hpos _ _ ((complexChartAt (n := n) y).val.map_source hys) _ h0)).le
  have hcont := continuous_laplacian hg (u := fun x => u x * u x) hu2
  have hint := KahlerLaplacianStokes.integral_laplacian_eq_zero w (u := fun x => u x * u x) hu2
  have hzero : laplacian w.form.val (fun x => u x * u x) = 0 := by
    have hae := (integral_eq_zero_iff_of_nonneg hnn (hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)))).1 hint
    exact (Continuous.ae_eq_iff_eq (kahlerVolume w) hcont continuous_const).1 hae
  have hgrad : ∀ (e : ComplexChart n M), ∀ z ∈ e.val.target,
      fderiv ℝ (fun w => u (e.val.symm w)) z = 0 := by
    intro e z hz
    have hy : e.val.symm z ∈ e.val.source := e.val.map_target hz
    have h1 := hform e _ hy
    rw [congrFun hzero, e.val.right_inv hz, Pi.zero_apply] at h1
    by_contra hne
    have hgv : (InnerProductSpace.toDual ℝ (ComplexModel n)).symm
        (fderiv ℝ (fun w => u (e.val.symm w)) z) ≠ 0 := fun h0 =>
      hne ((LinearIsometryEquiv.map_eq_zero_iff _).1 h0)
    have := hpos e z hz _ hgv
    linarith
  have hloc : IsLocallyConstant u := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    set e := complexChartAt (n := n) x with he
    have hxs : x ∈ e.val.source := mem_complexChartAt_source x
    have hz : e.val x ∈ e.val.target := e.val.map_source hxs
    have hdiff : DifferentiableOn ℝ (fun w => u (e.val.symm w)) e.val.target :=
      (hu e).differentiableOn (by simp)
    have hO := e.val.open_target.isOpen_inter_preimage_of_fderiv_eq_zero hdiff
      (fun z hz => hgrad e z hz) {u x}
    have hmem : e.val x ∈ e.val.target ∩ (fun w => u (e.val.symm w)) ⁻¹' {u x} :=
      ⟨hz, by simp [e.val.left_inv hxs]⟩
    filter_upwards [e.val.open_source.mem_nhds hxs,
      (e.val.continuousAt hxs).preimage_mem_nhds (hO.mem_nhds hmem)] with y hys hy
    have : u (e.val.symm (e.val y)) = u x := hy.2
    rwa [e.val.left_inv hys] at this
  obtain ⟨y0⟩ : Nonempty M := inferInstance
  exact ⟨u y0, fun y => hloc.apply_eq_of_preconnectedSpace y y0⟩

end Harmonic

end SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes

import SGPT.Envelopes.TosC11dLineCalc
import SGPT.Okounkov.TranscendentalWNRegBeta
import SGPT.Foundations.Analysis.Pending.AubinYauEstimate
import SGPT.Foundations.Analysis.Pending.HolomorphicHessianTwo

/-!
# Transfer of the chart quantities to holomorphic coordinates

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:transfer`).  Source: Xia, *Foundations of
pluripotential theory*, `sec:real-hessian-envelopes` (the covariant Hessian is a tensor) and
`lem:penalized-real-hessian`, Step 2 (normal coordinates at the maximum point), for SGPT
`thm:Tos_C11` (Tosatti, Chu–Zhou).

Let `e` be a chart, `ρ` a local potential of the Kähler form `A` on an open set `W` of the chart
target, `u` chart-smooth and `Φ` a holomorphic map of `ℂⁿ` (e.g. normal coordinates).  For `ψ = ρ ∘ Φ`
and `a = u ∘ e⁻¹ ∘ Φ` (up to germs) at a point `x` with `Φ x ∈ W`:

* `metricOf_eq_chartMetric` — `metricOf ψ x (Y, Z) = π · g_e(Φ x)(DΦ Y, DΦ Z)` (`g_e = chartMetric A e`);
* `hessQuot_eq_quot`, `gradNormSq_eq_sFun` — `hessQuot A u e (Φ x) (DΦ Y) = π · quot ψ a x Y` and
  `gradNormSq A u e (Φ x) = π · sFun ψ a x` when `DΦ(x)` is invertible (tensoriality of the covariant
  Hessian, `TosC11b.covHess_comp`, and its invariance under constant rescaling of the metric);
* `leviForm_eq_coeff` — `leviForm (u ∘ e⁻¹ ∘ Φ) x v = π · (ddᶜu)_e(Φ x)(DΦ v, i DΦ v)`;
* `re_det_complexHessian_eq_exp_comp` — the penalized equation in the coordinates `Φ`.
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps need deeper pending instance synthesis, as in
-- Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

variable {n : ℕ}

/-! ### The metric of a potential through `smoothDDC`, and rescaling -/

theorem smoothDDC_I_eq_metricOf {ψ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hψ : ContDiffAt ℝ 2 ψ z) (Y Z : ComplexModel n) :
    smoothDDC ψ z ![Y, Complex.I • Z] = metricOf ψ z Y Z / Real.pi := by
  have hs : ∀ U V, fderiv ℝ (fderiv ℝ ψ) z U V = fderiv ℝ (fderiv ℝ ψ) z V U :=
    hψ.isSymmSndFDerivAt (by simp)
  rw [smoothDDC_apply_eq_realHessian hψ, realHessian_eq_fderiv, realHessian_eq_fderiv,
    metricOf_apply, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, hs]
  ring

theorem gradVec_smul {g : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hg : ∀ v, v ≠ 0 → 0 < g v v) {c : ℝ} (hc : 0 < c) (L : ComplexModel n →L[ℝ] ℝ) :
    TosC11c.gradVec (c • g) L = c⁻¹ • TosC11c.gradVec g L := by
  have hcg : ∀ v, v ≠ 0 → 0 < (c • g) v v := fun v hv => by
    simp only [smul_apply, smul_eq_mul]; exact mul_pos hc (hg v hv)
  refine (TosC11c.eq_gradVec hcg fun V => ?_).symm
  simp only [smul_apply, smul_eq_mul, map_smul]
  rw [TosC11c.apply_gradVec hg]
  field_simp

/-- The covariant Hessian is invariant under a constant rescaling of the metric. -/
theorem covHess_smul_metric {g : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {a : ComplexModel n → ℝ} {z : ComplexModel n} (hg : DifferentiableAt ℝ g z) {c : ℝ}
    (hc : c ≠ 0) (Y Z G : ComplexModel n) :
    TosC11b.covHess (fun x => c • g x) a z Y Z (c⁻¹ • G) = TosC11b.covHess g a z Y Z G := by
  have hcg : DifferentiableAt ℝ (fun x => c • g x) z := hg.const_smul c
  have hd : fderiv ℝ (fun x => c • g x) z = c • fderiv ℝ g z := (hg.hasFDerivAt.const_smul c).fderiv
  simp only [TosC11b.covHess, TosC11c.koszul_eq hcg, TosC11c.koszul_eq hg, hd]
  simp only [smul_apply, map_smul, smul_eq_mul]
  field_simp

/-! ### Coordinates `Φ` -/

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The real derivative of a holomorphic map is complex linear. -/
theorem fderiv_I_smul {Φ : ComplexModel N → ComplexModel N} (hΦ : ContDiff ℂ ∞ Φ)
    (x v : ComplexModel N) :
    fderiv ℝ Φ x (Complex.I • v) = Complex.I • fderiv ℝ Φ x v := by
  have hd : DifferentiableAt ℂ Φ x := hΦ.differentiable (by simp) x
  rw [hd.fderiv_restrictScalars ℝ]
  exact (fderiv ℂ Φ x).map_smul Complex.I v

/-- **The metric in the coordinates `Φ`**: `metricOf ψ x (Y, Z) = π g_e(Φ x)(DΦ Y, DΦ Z)` for
`ψ = ρ ∘ Φ` near `x`, `ρ` a local potential of `A` on `W ∋ Φ x`. -/
theorem metricOf_eq_chartMetric (A : KahlerBackground N Y) {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {Φ : ComplexModel N → ComplexModel N}
    (hΦ : ContDiff ℂ ∞ Φ) {ψ : ComplexModel N → ℝ} {x : ComplexModel N}
    (hψ : ψ =ᶠ[𝓝 x] fun y => ρ (Φ y)) (hx : Φ x ∈ W) (Yv Zv : ComplexModel N) :
    metricOf ψ x Yv Zv =
      Real.pi * TosC11c.chartMetric A e (Φ x) (fderiv ℝ Φ x Yv) (fderiv ℝ Φ x Zv) := by
  have hO : IsOpen (Φ ⁻¹' W) := hpot.1.preimage hΦ.continuous
  have hρΦ : ContDiffAt ℝ 2 (fun y => ρ (Φ y)) x := by
    have h1 : ContDiffAt ℝ ∞ ρ (Φ x) := hpot.2.2.1.contDiffAt (hpot.1.mem_nhds hx)
    exact (h1.comp x (hΦ.restrict_scalars ℝ).contDiffAt).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcomp := HolomorphicDDC.smoothDDC_comp hO hpot.1 hΦ.contDiffOn hpot.2.2.1
    (fun y hy => hy) (show x ∈ Φ ⁻¹' W from hx)
  have h1 : metricOf ψ x Yv Zv = metricOf (fun y => ρ (Φ y)) x Yv Zv := by
    rw [metricOf, metricOf, hψ.fderiv.fderiv_eq]
  have h2 := smoothDDC_I_eq_metricOf hρΦ Yv Zv
  rw [hcomp, SGPT.Analysis.KahlerNormal.compContinuousLinearMap_apply_two, fderiv_I_smul hΦ,
    hpot.2.2.2 hx] at h2
  rw [h1]
  simp only [TosC11c.chartMetric, TosC11c.twoFormMetric_apply]
  rw [h2]
  field_simp

/-- **The covariant Hessian quotient and the gradient length in the coordinates `Φ`**:
`hessQuot A u e (Φ x) (DΦ Y) = π · quot ψ a x Y` and `gradNormSq A u e (Φ x) = π · sFun ψ a x`. -/
theorem hessQuot_eq_quot (A : KahlerBackground N Y) {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {Φ : ComplexModel N → ComplexModel N}
    (hΦ : ContDiff ℂ ∞ Φ) {u : Y → ℝ} (hu : ChartSmooth (n := N) u)
    {ψ a : ComplexModel N → ℝ} (hψs : ContDiff ℝ ∞ ψ) {x : ComplexModel N}
    (hψ : ψ =ᶠ[𝓝 x] fun y => ρ (Φ y)) (ha : a =ᶠ[𝓝 x] fun y => u (e.val.symm (Φ y)))
    (hx : Φ x ∈ W) (hinv : Function.Bijective (fderiv ℝ Φ x)) :
    (∀ Yv, TosC11c.hessQuot A u e (Φ x) (fderiv ℝ Φ x Yv) = Real.pi * quot ψ a x Yv) ∧
      TosC11c.gradNormSq A u e (Φ x) = Real.pi * sFun ψ a x := by
  set g := TosC11c.chartMetric A e with hgdef
  have hzt : Φ x ∈ e.val.target := hpot.2.1 hx
  have hU := e.val.open_target
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hΦR : ContDiff ℝ ∞ Φ := hΦ.restrict_scalars ℝ
  -- the metric germ
  have hWx : ∀ᶠ y in 𝓝 x, Φ y ∈ W :=
    hΦR.continuous.continuousAt.eventually (hpot.1.mem_nhds hx)
  have hmet : metricOf ψ =ᶠ[𝓝 x] fun y => Real.pi • TosC11b.pullbackBilin g Φ y := by
    filter_upwards [hWx, hψ.eventually_nhds] with y hy hψy
    ext Yv Zv
    rw [metricOf_eq_chartMetric A hpot hΦ hψy hy]
    rfl
  have hmet' : TosC11b.pullbackBilin g Φ =ᶠ[𝓝 x] fun y => Real.pi⁻¹ • metricOf ψ y := by
    filter_upwards [hmet] with y hy
    rw [hy, smul_smul, inv_mul_cancel₀ Real.pi_ne_zero, one_smul]
  have hmx : ∀ Yv Zv, metricOf ψ x Yv Zv = Real.pi * g (Φ x) (fderiv ℝ Φ x Yv) (fderiv ℝ Φ x Zv) :=
    fun Yv Zv => by rw [hmet.self_of_nhds]; rfl
  -- positivity of the metric of `ψ` at `x`
  have hpos : ∀ v, v ≠ 0 → 0 < metricOf ψ x v v := fun v hv => by
    rw [hmx]
    refine mul_pos Real.pi_pos (TosC11c.chartMetric_pos A e hzt _ fun h => hv ?_)
    exact hinv.1 (by rw [h, map_zero])
  -- the gradient vectors
  set G := TosC11c.chartGrad A u e (Φ x) with hGdef
  obtain ⟨G'', hG''⟩ := hinv.2 G
  have hgd : DifferentiableAt ℝ g (Φ x) :=
    ((TosC11c.contDiffOn_chartMetric A e).contDiffAt (hU.mem_nhds hzt)).differentiableAt (by simp)
  have hue : ContDiffAt ℝ 2 (fun z => u (e.val.symm z)) (Φ x) :=
    ((hu e).contDiffAt (hU.mem_nhds hzt)).of_le h2
  have hGg : ∀ V, g (Φ x) V G = fderiv ℝ (fun z => u (e.val.symm z)) (Φ x) V :=
    TosC11c.apply_gradVec (TosC11c.chartMetric_pos A e hzt) _
  obtain ⟨hgrad, hcov⟩ := TosC11b.covHess_comp (g := g) (φ := Φ)
    (a := fun z => u (e.val.symm z)) hgd (TosC11c.chartMetric_symm A e hzt)
    (hΦR.contDiffAt.of_le h2) hue hGg hG''
  have hDa : fderiv ℝ a x = fderiv ℝ ((fun z => u (e.val.symm z)) ∘ Φ) x := ha.fderiv_eq
  have hG''eq : G'' = Real.pi • grad ψ a x := by
    have hgv : Real.pi⁻¹ • G'' = grad ψ a x := by
      refine TosC11c.eq_gradVec hpos fun V => ?_
      rw [map_smul, hmx, hDa, ← hgrad V]
      simp only [TosC11b.pullbackBilin_apply]
      rw [smul_eq_mul]
      field_simp
    rw [← hgv, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]
  have hcovx : ∀ Yv, TosC11b.covHess (metricOf ψ) a x Yv Yv (grad ψ a x) =
      TosC11b.covHess g (fun z => u (e.val.symm z)) (Φ x) (fderiv ℝ Φ x Yv) (fderiv ℝ Φ x Yv) G := by
    intro Yv
    have ha' : ((fun z => u (e.val.symm z)) ∘ Φ) =ᶠ[𝓝 x] a := by exact ha.symm
    rw [← hcov Yv Yv, TosC11c.covHess_congr hmet' ha', hG''eq]
    have hmd : DifferentiableAt ℝ (metricOf ψ) x :=
      (contDiff_metricOf hψs).contDiffAt.differentiableAt (by simp)
    have := covHess_smul_metric (g := metricOf ψ) (a := a) hmd (c := Real.pi⁻¹)
      (inv_ne_zero Real.pi_ne_zero) Yv Yv (grad ψ a x)
    rw [inv_inv] at this
    rw [this]
  refine ⟨fun Yv => ?_, ?_⟩
  · show TosC11b.covHess g (fun z => u (e.val.symm z)) (Φ x) (fderiv ℝ Φ x Yv) (fderiv ℝ Φ x Yv) G /
        g (Φ x) (fderiv ℝ Φ x Yv) (fderiv ℝ Φ x Yv) = Real.pi *
          (TosC11b.covHess (metricOf ψ) a x Yv Yv (grad ψ a x) / metricOf ψ x Yv Yv)
    rw [hcovx, hmx, mul_div_assoc', mul_div_mul_left _ _ Real.pi_ne_zero]
  · simp only [TosC11c.gradNormSq, sFun]
    rw [← hGdef, ← hG'', hDa, fderiv_comp x (hue.differentiableAt (by norm_num))
      (hΦR.differentiable (by simp) x), ContinuousLinearMap.comp_apply, hG''eq]
    simp only [map_smul, smul_eq_mul]

/-- **The Levi form in the coordinates `Φ`**: for `g = f ∘ Φ` near `x`, `f` smooth near `Φ x`,
`leviForm g x v = π · ddᶜf(Φ x)(DΦ v, i DΦ v)`. -/
theorem leviForm_comp_eq {Φ : ComplexModel N → ComplexModel N} (hΦ : ContDiff ℂ ∞ Φ)
    {f : ComplexModel N → ℝ} {V : Set (ComplexModel N)} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {x : ComplexModel N} (hx : Φ x ∈ V) {g : ComplexModel N → ℝ}
    (hg : g =ᶠ[𝓝 x] fun y => f (Φ y)) (v : ComplexModel N) :
    leviForm g x v = Real.pi *
      smoothDDC f (Φ x) ![fderiv ℝ Φ x v, Complex.I • fderiv ℝ Φ x v] := by
  have hO : IsOpen (Φ ⁻¹' V) := hV.preimage (hΦ.restrict_scalars ℝ).continuous
  have hfΦ : ContDiffAt ℝ 2 (fun y => f (Φ y)) x := by
    have h1 : ContDiffAt ℝ ∞ f (Φ x) := hf.contDiffAt (hV.mem_nhds hx)
    exact (h1.comp x (hΦ.restrict_scalars ℝ).contDiffAt).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcomp := HolomorphicDDC.smoothDDC_comp hO hV hΦ.contDiffOn hf (fun y hy => hy)
    (show x ∈ Φ ⁻¹' V from hx)
  have h1 := smoothDDC_complexDiagonal_eq_leviForm hfΦ v
  rw [hcomp, SGPT.Analysis.KahlerNormal.compContinuousLinearMap_apply_two,
    fderiv_I_smul hΦ] at h1
  rw [AubinYauUniformConstants.leviForm_congr hg, h1]
  field_simp

/-- The complex Hessian matrix in the coordinates `Φ`. -/
theorem complexHessian_comp_eq {Φ : ComplexModel N → ComplexModel N} (hΦ : ContDiff ℂ ∞ Φ)
    {f : ComplexModel N → ℝ} {V : Set (ComplexModel N)} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {x : ComplexModel N} (hx : Φ x ∈ V) {g : ComplexModel N → ℝ}
    (hg : g =ᶠ[𝓝 x] fun y => f (Φ y)) :
    complexHessian g x = (Pending.HolomorphicMixedDensity.jacobianMatrix Φ x).transpose *
      complexHessian f (Φ x) *
        (Pending.HolomorphicMixedDensity.jacobianMatrix Φ x).map (starRingEnd ℂ) := by
  have hO : IsOpen (Φ ⁻¹' V) := hV.preimage (hΦ.restrict_scalars ℝ).continuous
  rw [AubinYauUniformConstants.complexHessian_congr hg]
  exact Pending.HolomorphicHessianTwo.complexHessian_comp_holomorphic_two hO hV hΦ.contDiffOn
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (fun y hy => hy) (show x ∈ Φ ⁻¹' V from hx)

theorem re_det_congr (J M : Matrix (Fin N) (Fin N) ℂ) :
    (J.transpose * M * J.map (starRingEnd ℂ)).det.re = Complex.normSq J.det * M.det.re := by
  have hc : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det _ _).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc, mul_comm J.det, mul_assoc,
    Complex.mul_conj, mul_comm, Complex.re_ofReal_mul]

/-- **The penalized equation in the coordinates `Φ`**. -/
theorem re_det_complexHessian_comp_eq (A : KahlerBackground N Y) {e : ComplexChart N Y}
    {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hpot : IsSmoothLocalPotential A.form.val e W ρ) {Φ : ComplexModel N → ComplexModel N}
    (hΦ : ContDiff ℂ ∞ Φ) {u G : Y → ℝ} (hu : ChartSmooth (n := N) u)
    (hdens : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm u hu).val.coeff e z) =
        Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z))
    {ψ a : ComplexModel N → ℝ} {x : ComplexModel N}
    (hψ : ψ =ᶠ[𝓝 x] fun y => ρ (Φ y)) (ha : a =ᶠ[𝓝 x] fun y => u (e.val.symm (Φ y)))
    (hx : Φ x ∈ W) :
    (complexHessian (fun y => ψ y + a y) x).det.re =
      Real.exp (G (e.val.symm (Φ x))) * (complexHessian ψ x).det.re := by
  have hρ : ContDiffOn ℝ ∞ ρ W := hpot.2.2.1
  have hue : ContDiffOn ℝ ∞ (fun z => u (e.val.symm z)) W := (hu e).mono hpot.2.1
  have hsum : (fun y => ψ y + a y) =ᶠ[𝓝 x] fun y => (fun z => ρ z + u (e.val.symm z)) (Φ y) := by
    filter_upwards [hψ, ha] with y h1 h2
    rw [h1, h2]
  rw [complexHessian_comp_eq hΦ hpot.1 (hρ.add hue) hx hsum, complexHessian_comp_eq hΦ hpot.1 hρ hx hψ,
    re_det_congr, re_det_congr, AubinYauEstimate.re_det_complexHessian_eq_exp A hu hdens hpot hx]
  ring

end Manifold

end SGPT.Envelopes.TosC11d

import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import SGPT.Foundations.Analysis.Pending.GramDeterminant
import SGPT.Foundations.Analysis.Pending.HessianLocalExtremum

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Alexandrov--Bakelman--Pucci estimate (measure form)

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ` and an
orthonormal basis `b`, `U ⊆ E` open, `v` of class `C²` on `U`, `K ⊆ U` compact, `x₀ ∈ K` with
`v x₀ ≤ -a`, `v ≥ 0` on `K \ interior K`, and `‖x - x₀‖ ≤ d` on `K`.  Then
(`addHaar_ball_le_lintegral_det`)

`μ (B(0, a/d)) ≤ ∫_Γ det D²v dμ`,  `Γ = {x ∈ interior K : v x < 0, D²v(x) ≥ 0}`,

with `det D²v(x)` the Gram determinant of `D²v(x)` in `b` (independent of `b`,
`GramDeterminant.det_riesz_comp`).

This is Gilbarg--Trudinger, Lemma 9.2, in the form used by Błocki for the `L²`-stability of the
complex Monge--Ampère equation (`blocki05-uniform-estimate:page-0002`, Theorem 1;
`lnm2038-monge-ampere:page-0219`--`page-0220`, Theorem 5.10): the inequality
`‖u‖_∞ ≤ diam Ω · λ_m^{-1/m} (∫_Γ det D²u)^{1/m}` is `μ (B(0, a/d)) = (a/d)^m λ_m ≤ ∫_Γ det D²u`.
The set `Γ` here contains the lower contact set of the source (only the inclusion
`Γ_source ⊆ {D²u ≥ 0}` is used there).

## Proof

For `‖p‖ < a/d`, the function `w = v - ⟪p, ·⟫` attains its minimum on `K` at some `x`; on
`K \ interior K`, `w ≥ -⟪p, x⟫ > -a - ⟪p, x₀⟫ ≥ w x₀`, so `x ∈ interior K`, `v x < 0`,
`Dv(x) = ⟪p, ·⟫` and `D²v(x) ≥ 0` (`IsLocalMin.fderiv_fderiv_nonneg`).  Hence `B(0, a/d)` lies in the
image of `Γ` under the gradient map `x ↦ riesz b (Dv(x))`, whose derivative is
`riesz b ∘ D²v(x)`, and mathlib's area inequality `addHaar_image_le_lintegral_abs_det_fderiv`
bounds the measure of the image.  TN.4 B5, nonlinear track N2.
-/

open Set Filter MeasureTheory Metric
open scoped Topology InnerProductSpace RealInnerProductSpace ENNReal

namespace SGPT.Foundations.Analysis.Pending.AlexandrovBakelmanPucci

open GramDeterminant

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The set `{B | ∀ h, 0 ≤ B h h}` of positive semidefinite bilinear forms is closed. -/
theorem isClosed_setOf_nonneg :
    IsClosed {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ h, 0 ≤ B h h} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun h => isClosed_le continuous_const
    ((ContinuousLinearMap.apply ℝ ℝ h).continuous.comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) h).continuous)

/-- The set `Γ` is measurable. -/
theorem measurableSet_contact [MeasurableSpace E] [BorelSpace E] {U K : Set E}
    {v : E → ℝ} (hKU : K ⊆ U) (hv : ContDiffOn ℝ 2 v U) :
    MeasurableSet {x | x ∈ interior K ∧ v x < 0 ∧ ∀ h, 0 ≤ fderiv ℝ (fderiv ℝ v) x h h} := by
  have hopen : IsOpen (interior K ∩ v ⁻¹' Iio 0) :=
    (hv.continuousOn.mono (interior_subset.trans hKU)).isOpen_inter_preimage isOpen_interior
      isOpen_Iio
  have hmeas : MeasurableSet
      (fderiv ℝ (fderiv ℝ v) ⁻¹' {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ h, 0 ≤ B h h}) :=
    measurable_fderiv ℝ (fderiv ℝ v) isClosed_setOf_nonneg.measurableSet
  have : {x | x ∈ interior K ∧ v x < 0 ∧ ∀ h, 0 ≤ fderiv ℝ (fderiv ℝ v) x h h} =
      (interior K ∩ v ⁻¹' Iio 0) ∩
        fderiv ℝ (fderiv ℝ v) ⁻¹' {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ h, 0 ≤ B h h} := by
    ext x; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio]; tauto
  rw [this]
  exact hopen.measurableSet.inter hmeas

/-- **The ball of slopes lies in the gradient image of `Γ`.** -/
theorem exists_mem_contact_riesz_eq (b : OrthonormalBasis ι ℝ E) {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {v : E → ℝ} (hv : ContDiffOn ℝ 2 v U) {x₀ : E}
    (hx₀ : x₀ ∈ K) {a d : ℝ} (hv₀ : v x₀ ≤ -a) (hfr : ∀ x ∈ K, x ∉ interior K → 0 ≤ v x)
    (hd : ∀ x ∈ K, ‖x - x₀‖ ≤ d) {p : E} (hp : ‖p‖ < a / d) :
    ∃ x, (x ∈ interior K ∧ v x < 0 ∧ ∀ h, 0 ≤ fderiv ℝ (fderiv ℝ v) x h h) ∧
      riesz b (fderiv ℝ v x) = p := by
  have hd0 : 0 ≤ d := by simpa using hd x₀ hx₀
  have hdpos : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at hp; exact absurd hp (not_lt.mpr (norm_nonneg p))
  have hpa : ‖p‖ * d < a := by rwa [lt_div_iff₀ hdpos] at hp
  have hinner : ∀ x ∈ K, ⟪p, x - x₀⟫ < a := fun x hx =>
    (real_inner_le_norm p (x - x₀)).trans_lt
      ((mul_le_mul_of_nonneg_left (hd x hx) (norm_nonneg p)).trans_lt hpa)
  set w : E → ℝ := fun y => v y - innerSL ℝ p y with hwdef
  have hwc : ContinuousOn w K :=
    (hv.continuousOn.mono hKU).sub (innerSL ℝ p).continuous.continuousOn
  obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn ⟨x₀, hx₀⟩ hwc
  have hwx : w x ≤ w x₀ := hxmin hx₀
  simp only [hwdef, innerSL_apply_apply] at hwx
  have hxint : x ∈ interior K := by
    by_contra hx
    have h0 := hfr x hxK hx
    have := hinner x hxK
    rw [inner_sub_right] at this
    linarith
  have hvneg : v x < 0 := by
    have := hinner x hxK
    rw [inner_sub_right] at this
    linarith
  have hlm : IsLocalMin w x := hxmin.isLocalMin (mem_interior_iff_mem_nhds.mp hxint)
  have hvx : ContDiffAt ℝ 2 v x := hv.contDiffAt (hU.mem_nhds (hKU (interior_subset hxint)))
  have hwx2 : ContDiffAt ℝ 2 w x := hvx.sub (innerSL ℝ p).contDiff.contDiffAt
  have hvd : DifferentiableAt ℝ v x := hvx.differentiableAt (by norm_num)
  -- first order: `Dv(x) = ⟪p, ·⟫`
  have hfd : fderiv ℝ v x = innerSL ℝ p := by
    have h1 := hlm.fderiv_eq_zero
    have h2 : fderiv ℝ w x = fderiv ℝ v x - innerSL ℝ p := by
      exact (hvd.hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt).fderiv
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  -- second order: `D²w(x) = D²v(x) ≥ 0`
  have hD2 : fderiv ℝ (fderiv ℝ w) x = fderiv ℝ (fderiv ℝ v) x := by
    have hev : fderiv ℝ w =ᶠ[𝓝 x] fun y => fderiv ℝ v y - innerSL ℝ p := by
      filter_upwards [hvx.eventually (by simp)] with y hy
      exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.sub
        (innerSL ℝ p).hasFDerivAt).fderiv
    rw [hev.fderiv_eq, fderiv_sub_const]
  refine ⟨x, ⟨hxint, hvneg, fun h => ?_⟩, by rw [hfd, riesz_innerSL]⟩
  rw [← hD2]
  exact hlm.fderiv_fderiv_nonneg hwx2 h

/-- **Alexandrov--Bakelman--Pucci, measure form** (Gilbarg--Trudinger, Lemma 9.2; Błocki,
`blocki05-uniform-estimate:page-0002`). -/
theorem addHaar_ball_le_lintegral_det [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (b : OrthonormalBasis ι ℝ E) {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {v : E → ℝ} (hv : ContDiffOn ℝ 2 v U) {x₀ : E}
    (hx₀ : x₀ ∈ K) {a d : ℝ} (hv₀ : v x₀ ≤ -a) (hfr : ∀ x ∈ K, x ∉ interior K → 0 ≤ v x)
    (hd : ∀ x ∈ K, ‖x - x₀‖ ≤ d) :
    μ (ball 0 (a / d)) ≤
      ∫⁻ x in {x | x ∈ interior K ∧ v x < 0 ∧ ∀ h, 0 ≤ fderiv ℝ (fderiv ℝ v) x h h},
        ENNReal.ofReal (Matrix.of fun i j => fderiv ℝ (fderiv ℝ v) x (b i) (b j)).det ∂μ := by
  set Γ := {x | x ∈ interior K ∧ v x < 0 ∧ ∀ h, 0 ≤ fderiv ℝ (fderiv ℝ v) x h h} with hΓ
  have hΓm : MeasurableSet Γ := measurableSet_contact hKU hv
  have hvx : ∀ x ∈ Γ, ContDiffAt ℝ 2 v x := fun x hx =>
    hv.contDiffAt (hU.mem_nhds (hKU (interior_subset hx.1)))
  have hder : ∀ x ∈ Γ, HasFDerivWithinAt (fun y => riesz b (fderiv ℝ v y))
      ((riesz b).comp (fderiv ℝ (fderiv ℝ v) x)) Γ x := by
    intro x hx
    have hD : DifferentiableAt ℝ (fderiv ℝ v) x :=
      ((hvx x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact ((riesz b).hasFDerivAt.comp x hD.hasFDerivAt).hasFDerivWithinAt
  calc μ (ball 0 (a / d))
      ≤ μ ((fun y => riesz b (fderiv ℝ v y)) '' Γ) := by
        refine measure_mono fun p hp => ?_
        rw [mem_ball_zero_iff] at hp
        obtain ⟨x, hx, hxp⟩ :=
          exists_mem_contact_riesz_eq b hU hK hKU hv hx₀ hv₀ hfr hd hp
        exact ⟨x, hx, hxp⟩
    _ ≤ ∫⁻ x in Γ, ENNReal.ofReal |((riesz b).comp (fderiv ℝ (fderiv ℝ v) x)).det| ∂μ :=
        addHaar_image_le_lintegral_abs_det_fderiv μ hΓm hder
    _ = ∫⁻ x in Γ, ENNReal.ofReal
          (Matrix.of fun i j => fderiv ℝ (fderiv ℝ v) x (b i) (b j)).det ∂μ := by
        refine setLIntegral_congr_fun hΓm fun x hx => ?_
        have hsymm : ∀ h k, fderiv ℝ (fderiv ℝ v) x h k = fderiv ℝ (fderiv ℝ v) x k h :=
          fun h k => (hvx x hx).isSymmSndFDerivAt (by simp) h k
        rw [det_riesz_comp b b, abs_of_nonneg (det_gram_nonneg b hsymm hx.2.2)]

end SGPT.Foundations.Analysis.Pending.AlexandrovBakelmanPucci

import SGPT.Projective.Basic
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import SGPT.Foundations.Analysis.FirstPass.CoordinateDensityGeometry
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization
import SGPT.Foundations.Analysis.Pending.FubiniStudyLineLevi

/-!
# The Fubini–Study Kähler form on `ℙᴺ`

In every affine chart `U_i ≅ ℂᴺ` of `ℙᴺ` the Fubini–Study form is
`ω_FS = ddᶜ log(1 + ‖z‖²)`, i.e. `ω_FS = ddᶜ log ‖Z‖²` in homogeneous coordinates, with the
normalisation `dᶜ = -(1/4π) d ∘ J` of `SGPT.Foundations.Analysis` (so that `∫_{ℙ¹} ω_FS = 1`,
`ω_FS ∈ c₁(O(1))`).  Since the coefficient `smoothDDC log(1 + ‖z‖²)` is the same in every chart,
the content of the construction is the transformation law on overlaps: on `U_i ∩ U_j`,
`log(1 + ‖z'‖²) = log(1 + ‖z‖²) - log |w_j|²` with `w = insertNth i 1 z` and `w_j` holomorphic and
nonvanishing, and `ddᶜ log |w_j|² = 0`.

Main definitions and results:

* `SGPT.Projective.ComplexProjectiveSpace.homNormSq`: the Hermitian norm `‖v‖² = ∑ |v_m|²`;
* `fsPotential`: the affine potential `log(1 + ‖z‖²)`;
* `fsForm`, `fsClosedForm`, `fsBackground`: `ω_FS` as a smooth real form, a closed real
  `(1,1)`-form and a Kähler background (`fsForm_isKahler`: strictly positive in every chart);
* `isSmoothLocalPotential_fsPotential`: `log(1 + ‖z‖²)` is a global potential of `ω_FS` on
  every chart.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Manifold ContDiff

namespace SGPT.Projective.ComplexProjectiveSpace

variable {N : ℕ}

/-! ### The Hermitian norm of homogeneous coordinates -/

/-- The Hermitian norm `‖v‖² = ∑_m |v_m|²` of homogeneous coordinates (not the sup norm of
the Pi type). -/
def homNormSq (v : Fin (N + 1) → ℂ) : ℝ := ∑ m, ‖v m‖ ^ 2

theorem homNormSq_nonneg (v : Fin (N + 1) → ℂ) : 0 ≤ homNormSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem homNormSq_pos {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) : 0 < homNormSq v := by
  obtain ⟨m, hm⟩ : ∃ m', v m' ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hm) 2)
    (Finset.single_le_sum (f := fun m => ‖v m‖ ^ 2) (fun m _ => sq_nonneg _)
      (Finset.mem_univ m))

theorem homNormSq_smul (c : ℂ) (v : Fin (N + 1) → ℂ) :
    homNormSq (c • v) = ‖c‖ ^ 2 * homNormSq v := by
  simp only [homNormSq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem homNormSq_eq_norm_sq (v : Fin (N + 1) → ℂ) :
    homNormSq v = ‖(WithLp.toLp 2 v : ComplexModel (N + 1))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

theorem homNormSq_succAbove (j : Fin (N + 1)) (v : Fin (N + 1) → ℂ) :
    homNormSq v = ‖v j‖ ^ 2 + ∑ k : Fin N, ‖v (j.succAbove k)‖ ^ 2 :=
  Fin.sum_univ_succAbove (fun m => ‖v m‖ ^ 2) j

/-- `‖insertNth i 1 z‖² = 1 + ‖z‖²`. -/
theorem homNormSq_affineLift (i : Fin (N + 1)) (z : ComplexModel N) :
    homNormSq (affineLift i z) = 1 + ‖z‖ ^ 2 := by
  rw [homNormSq_succAbove i, EuclideanSpace.norm_sq_eq]
  simp

/-- `1 + ‖(v_{j.succAbove k}/v_j)_k‖² = ‖v‖² / |v_j|²`. -/
theorem one_add_norm_sq_affineRatio (j : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hvj : v j ≠ 0) :
    1 + ‖affineRatio j v‖ ^ 2 = homNormSq v / ‖v j‖ ^ 2 := by
  have hpos : 0 < ‖v j‖ ^ 2 := pow_pos (norm_pos_iff.mpr hvj) 2
  rw [homNormSq_succAbove j, EuclideanSpace.norm_sq_eq]
  simp only [affineRatio_apply, norm_div, div_pow]
  rw [add_div, div_self hpos.ne', Finset.sum_div]

/-! ### The Fubini–Study potential -/

/-- The Fubini–Study potential `log(1 + ‖z‖²)` of an affine chart. -/
def fsPotential (z : ComplexModel N) : ℝ := Real.log (1 + ‖z‖ ^ 2)

theorem fsPotential_nonneg (z : ComplexModel N) : 0 ≤ fsPotential z :=
  Real.log_nonneg (by nlinarith [sq_nonneg ‖z‖])

theorem fsPotential_eq_log_homNormSq (i : Fin (N + 1)) (z : ComplexModel N) :
    fsPotential z = Real.log (homNormSq (affineLift i z)) := by
  rw [homNormSq_affineLift, fsPotential]

theorem contDiff_fsPotential : ContDiff ℝ ∞ (fsPotential (N := N)) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).log fun z => by positivity

/-- On `U_i ∩ U_j`: `log(1 + ‖z'‖²) = log(1 + ‖z‖²) - log |w_j|²`, `w = insertNth i 1 z`. -/
theorem fsPotential_transition (i j : Fin (N + 1)) {z : ComplexModel N}
    (hz : affineLift i z j ≠ 0) :
    fsPotential (affineRatio j (affineLift i z)) =
      fsPotential z - Real.log (Complex.normSq (affineLift i z j)) := by
  rw [fsPotential, one_add_norm_sq_affineRatio j hz, Real.log_div
    (homNormSq_pos (affineLift_ne_zero i z)).ne' (pow_pos (norm_pos_iff.mpr hz) 2).ne',
    homNormSq_affineLift, Complex.normSq_eq_norm_sq]
  rfl

/-- The normalised `ddᶜ` of the Fubini–Study potential is invariant under every transition. -/
theorem smoothDDC_fsPotential_transition (i j : Fin (N + 1)) {z : ComplexModel N}
    (hz : z ∈ ((affineChart (N := N) i).symm.trans (affineChart j)).source) :
    smoothDDC (fun y => fsPotential (((affineChart (N := N) i).symm.trans (affineChart j)) y)) z =
      smoothDDC fsPotential z := by
  set T := (affineChart (N := N) i).symm.trans (affineChart j)
  have hU : IsOpen T.source := T.open_source
  have heq : (fun y => fsPotential (T y)) =ᶠ[𝓝 z]
      (fun y => fsPotential y - Real.log (Complex.normSq (affineLift i y j))) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    have hy' := (mem_transition_source_iff i j y).mp hy
    rw [transition_apply i j hy', fsPotential_transition i j hy']
  have hlog : ContDiffOn ℝ ∞ (fun y => Real.log (Complex.normSq (affineLift i y j))) T.source := by
    have hn : ContDiff ℝ ∞ (fun y : ComplexModel N => Complex.normSq (affineLift i y j)) := by
      have hc : ContDiff ℂ ∞ (fun y : ComplexModel N => affineLift i y j) :=
        contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex
          (differentiable_affineLift_apply i j).differentiableOn isOpen_univ)
      simp only [← Complex.sq_norm]
      exact (contDiff_norm_sq ℝ).comp (hc.restrict_scalars ℝ)
    refine hn.contDiffOn.log fun y hy => ?_
    exact (Complex.normSq_pos.mpr ((mem_transition_source_iff i j y).mp hy)).ne'
  have hzero : smoothDDC (fun y => Real.log (Complex.normSq (affineLift i y j))) z = 0 :=
    Pending.PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
      (Eventually.of_forall fun y => (differentiable_affineLift_apply i j) y)
      ((mem_transition_source_iff i j z).mp hz)
  rw [smoothDDC_congr heq, smoothDDC_sub hU contDiff_fsPotential.contDiffOn hlog hz, hzero,
    sub_zero]

/-! ### The Fubini–Study form -/

theorem chart_target_eq_univ (e : ComplexChart N (ComplexProjectiveSpace N)) :
    e.val.target = univ := by
  obtain ⟨i, hi⟩ := (mem_atlas_iff e.val).mp e.property
  rw [hi, affineChart_target]

/-- The Fubini–Study form `ω_FS`, given in every affine chart by `ddᶜ log(1 + ‖z‖²)`. -/
def fsForm : SmoothRealForm N (ComplexProjectiveSpace N) 2 where
  coeff := fun _ => smoothDDC fsPotential
  smooth := fun _ => (Pending.LogWeightFactorization.smoothDDC_contDiffOn isOpen_univ
    contDiff_fsPotential.contDiffOn).mono (subset_univ _)
  compatible := by
    intro e f z hz v
    obtain ⟨i, hi⟩ := (mem_atlas_iff e.val).mp e.property
    obtain ⟨j, hj⟩ := (mem_atlas_iff f.val).mp f.property
    change z ∈ (e.val.symm.trans f.val).source at hz
    rw [hi, hj] at hz
    change smoothDDC fsPotential z v = smoothDDC fsPotential ((e.val.symm.trans f.val) z)
      (fun a => fderiv ℝ (e.val.symm.trans f.val) z (v a))
    rw [hi, hj]
    set T := (affineChart (N := N) i).symm.trans (affineChart j)
    have hT : ContDiffOn ℂ ∞ T T.source :=
      contDiffOn_of_differentiableOn_complex (differentiableOn_transition i j) T.open_source
    have h := HolomorphicDDC.smoothDDC_comp T.open_source isOpen_univ hT
      contDiff_fsPotential.contDiffOn (mapsTo_univ _ _) hz
    rw [smoothDDC_fsPotential_transition i j hz] at h
    exact congrArg (fun A => A v) h

@[simp] theorem fsForm_coeff (e : ComplexChart N (ComplexProjectiveSpace N)) (z : ComplexModel N) :
    fsForm.coeff e z = smoothDDC fsPotential z := rfl

theorem fsForm_closed : (fsForm (N := N)).IsClosed := by
  intro e z _
  change extDeriv (extDeriv (smoothDc fsPotential)) z = 0
  exact extDeriv_extDeriv_apply
    ((smoothDc_contDiffOn isOpen_univ contDiff_fsPotential.contDiffOn).contDiffAt
      (isOpen_univ.mem_nhds (mem_univ z)))
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

theorem fsForm_typeOneOne : (fsForm (N := N)).IsTypeOneOne := by
  intro e z _ v w
  exact MongeAmpere.smoothDDC_isOneOne
    (contDiff_fsPotential.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v w

/-! ### Strict positivity -/

/-- The homogeneous lift `(1, z)` in `ℂ^{N+1}` (Euclidean). -/
def homLift (z : ComplexModel N) : ComplexModel (N + 1) := WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp z))

/-- The tangent lift `(0, v)`. -/
def homTangent (v : ComplexModel N) : ComplexModel (N + 1) := WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))

theorem homLift_line (z v : ComplexModel N) (t : ℂ) :
    homLift (z + t • v) = homLift z + t • homTangent v := by
  ext m
  refine Fin.cases ?_ (fun k => ?_) m
  · simp [homLift, homTangent]
  · simp [homLift, homTangent]

theorem norm_sq_homLift (z : ComplexModel N) : ‖homLift z‖ ^ 2 = 1 + ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, EuclideanSpace.norm_sq_eq]
  simp [homLift]

theorem homLift_ne_zero (z : ComplexModel N) : homLift z ≠ 0 := by
  intro h
  have := congrArg (fun w : ComplexModel (N + 1) => w 0) h
  simp [homLift] at this

theorem homTangent_not_span (z : ComplexModel N) {v : ComplexModel N} (hv : v ≠ 0) :
    ∀ r : ℂ, homTangent v ≠ r • homLift z := by
  intro r h
  have h0 := congrArg (fun w : ComplexModel (N + 1) => w 0) h
  have hr : r = 0 := by simpa [homLift, homTangent] using h0.symm
  apply hv
  ext k
  have hk := congrArg (fun w : ComplexModel (N + 1) => w k.succ) h
  simpa [homLift, homTangent, hr] using hk

theorem fsPotential_line (z v : ComplexModel N) (t : ℂ) :
    fsPotential (z + t • v) = Real.log (‖homLift z + t • homTangent v‖ ^ 2) := by
  rw [fsPotential, ← homLift_line, norm_sq_homLift]

/-- `ω_FS` is strictly positive: `ddᶜ log(1 + ‖z‖²)(v, iv) > 0` for `v ≠ 0`. -/
theorem fsPotential_strictlyPositive (z : ComplexModel N) {v : ComplexModel N} (hv : v ≠ 0) :
    0 < smoothDDC fsPotential z ![v, Complex.I • v] := by
  have hρ : ContDiffAt ℝ 2 (fsPotential (N := N)) z :=
    contDiff_fsPotential.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [Pending.FubiniStudyLineLevi.quad_smoothDDC_eq_leviForm hρ v,
    Pending.FubiniStudyLineLevi.leviForm_eq_line hρ v]
  have heq : (fun t : ℂ => fsPotential (z + t • v)) =
      (fun t : ℂ => Real.log (‖homLift z + t • homTangent v‖ ^ 2)) :=
    funext (fsPotential_line z v)
  rw [heq]
  exact div_pos
    (Pending.FubiniStudyLineLevi.leviForm_log_normSq_line_pos
      (homTangent_not_span z hv) (homLift_ne_zero z))
    Real.pi_pos

theorem fsForm_isKahler : (fsForm (N := N)).IsKahler := by
  refine ⟨?_, fsForm_closed⟩
  intro e z hz
  exact ⟨fsForm_typeOneOne e z hz, fun v hv => fsPotential_strictlyPositive z hv⟩

/-- `ω_FS` as a closed real `(1,1)`-form. -/
def fsClosedForm : ClosedRealOneOneForm N (ComplexProjectiveSpace N) :=
  ⟨fsForm, fsForm_closed, fsForm_typeOneOne⟩

/-- The Fubini–Study Kähler background `ω_FS` of `ℙᴺ`. -/
def fsBackground : KahlerBackground N (ComplexProjectiveSpace N) :=
  ⟨fsClosedForm, fsForm_isKahler⟩

@[simp] theorem fsBackground_coeff (e : ComplexChart N (ComplexProjectiveSpace N))
    (z : ComplexModel N) :
    (fsBackground (N := N)).form.val.coeff e z = smoothDDC fsPotential z := rfl

/-- `log(1 + ‖z‖²)` is a global smooth potential of `ω_FS` on every affine chart. -/
theorem isSmoothLocalPotential_fsPotential (e : ComplexChart N (ComplexProjectiveSpace N)) :
    IsSmoothLocalPotential (fsBackground (N := N)).form.val e univ fsPotential :=
  ⟨isOpen_univ, (chart_target_eq_univ e).symm.subset, contDiff_fsPotential.contDiffOn,
    fun _ _ => rfl⟩

end SGPT.Projective.ComplexProjectiveSpace

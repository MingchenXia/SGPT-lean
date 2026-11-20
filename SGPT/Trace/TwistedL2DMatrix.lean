import SGPT.Trace.TwistedL2MSigmaDensity

/-!
# Linear algebra of the Kähler form `σ` for the density lemma

Blueprint `claude-tl2-dens.tex` (`claude-tl2-dens:matrix`).  On an open `U ⊆ ℂⁿ` where
`σ = ω + ddᶜr` is Kähler, write `σᵀ(z)` for the transposed matrix of `σ` (positive definite,
`TwistedL2MSigma.lean`).  This file provides

* `mv M x`: a matrix acting on a vector of `ℂⁿ` (`EuclideanSpace`), with its adjoint rule;
* `Bm z = √(σᵀ(z))` (continuous functional calculus) and its inverse `Bi z`: Hermitian,
  `Bm² = σᵀ`, continuous on `U`; `σ(v) = ‖Bm v‖²` (`sigmaQ_eq_norm_sq`), and the inverse metric
  of `(0,2)`-covectors is `Bi²` (`sigmaInv_eq`);
* the dual-norm bound `norm_mv_Bi_sq_le`: if `|⟨v, a⟩|² ≤ c σ(v)` for all `v` then
  `‖Bi a‖² ≤ c`;
* the wedge bound `zeroTwoNormSq_wedge_le`: `|a ∧ σ^♭W|²_σ ≤ ‖Bi a‖² ‖Bm W‖²`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter Matrix
open scoped Topology ContDiff ComplexConjugate ComplexOrder InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ}

/-! ### Matrices acting on `ℂⁿ` -/

/-- A matrix acting on a vector of `ℂⁿ`. -/
def mv (M : Matrix (Fin n) (Fin n) ℂ) (x : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (M *ᵥ WithLp.ofLp x)

@[simp] theorem mv_apply (M : Matrix (Fin n) (Fin n) ℂ) (x : ComplexModel n) (i : Fin n) :
    mv M x i = ∑ j, M i j * x j := rfl

theorem mv_mul (M N : Matrix (Fin n) (Fin n) ℂ) (x : ComplexModel n) :
    mv (M * N) x = mv M (mv N x) := by
  simp only [mv, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

@[simp] theorem mv_one (x : ComplexModel n) : mv 1 x = x := by
  simp [mv]

theorem mv_add (M : Matrix (Fin n) (Fin n) ℂ) (x y : ComplexModel n) :
    mv M (x + y) = mv M x + mv M y := by
  ext i; simp [mv, Matrix.mulVec_add]

theorem mv_sub (M : Matrix (Fin n) (Fin n) ℂ) (x y : ComplexModel n) :
    mv M (x - y) = mv M x - mv M y := by
  ext i; simp [mv, Matrix.mulVec_sub]

theorem mv_smul (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x : ComplexModel n) :
    mv M (c • x) = c • mv M x := by
  ext i; simp [mv, Matrix.mulVec_smul]

@[simp] theorem mv_zero (M : Matrix (Fin n) (Fin n) ℂ) : mv M 0 = 0 := by
  ext i; simp [mv]

theorem mv_sum (M : Matrix (Fin n) (Fin n) ℂ) {ι : Type*} (s : Finset ι) (x : ι → ComplexModel n) :
    mv M (∑ i ∈ s, x i) = ∑ i ∈ s, mv M (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mv_add, ih]

/-- The adjoint rule `⟪M x, y⟫ = ⟪x, Mᴴ y⟫`. -/
theorem inner_mv_left (M : Matrix (Fin n) (Fin n) ℂ) (x y : ComplexModel n) :
    ⟪mv M x, y⟫_ℂ = ⟪x, mv Mᴴ y⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, mv]
  rw [Matrix.star_mulVec, dotProduct_comm (Mᴴ *ᵥ _), Matrix.dotProduct_mulVec, dotProduct_comm]

theorem inner_mv_right (M : Matrix (Fin n) (Fin n) ℂ) (x y : ComplexModel n) :
    ⟪x, mv M y⟫_ℂ = ⟪mv Mᴴ x, y⟫_ℂ := by
  rw [inner_mv_left, conjTranspose_conjTranspose]

/-- A crude bound for the operator norm. -/
def mnorm (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

theorem mnorm_nonneg (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_le_sum_norm_coord (x : ComplexModel n) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  have h : x = ∑ i, x i • (EuclideanSpace.single i (1 : ℂ) : ComplexModel n) := by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one]

theorem norm_coord_le (x : ComplexModel n) (i : Fin n) : ‖x i‖ ≤ ‖x‖ := by
  exact PiLp.norm_apply_le x i

theorem norm_mv_le (M : Matrix (Fin n) (Fin n) ℂ) (x : ComplexModel n) :
    ‖mv M x‖ ≤ mnorm M * ‖x‖ := by
  refine (norm_le_sum_norm_coord _).trans ?_
  unfold mnorm
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mv_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_coord_le x j) (norm_nonneg _)

theorem continuous_mnorm : Continuous (mnorm (n := n)) := by
  unfold mnorm
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_apply j |>.comp (continuous_apply i)).norm

theorem continuous_mv : Continuous fun p : Matrix (Fin n) (Fin n) ℂ × ComplexModel n => mv p.1 p.2 := by
  have h : Continuous fun p : Matrix (Fin n) (Fin n) ℂ × ComplexModel n =>
      p.1 *ᵥ WithLp.ofLp p.2 :=
    (continuous_fst.matrix_mulVec ((PiLp.continuous_ofLp 2 _).comp continuous_snd))
  exact (PiLp.continuous_toLp 2 _).comp h

/-! ### The matrix square root -/

section Sqrt

open scoped Matrix.Norms.L2Operator MatrixOrder

/-- The positive square root of a matrix (continuous functional calculus). -/
def msqrt (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt A

theorem msqrt_mul_self {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) :
    msqrt A * msqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem msqrt_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) : (msqrt A)ᴴ = msqrt A :=
  (CFC.sqrt_nonneg A).isSelfAdjoint

theorem continuousOn_msqrt {X : Type*} [TopologicalSpace X] {f : X → Matrix (Fin n) (Fin n) ℂ}
    {S : Set X} (hf : ContinuousOn f S) (hp : ∀ x ∈ S, (f x).PosSemidef) :
    ContinuousOn (fun x => msqrt (f x)) S :=
  CFC.continuousOn_sqrt.comp hf fun x hx => (hp x hx).nonneg

end Sqrt

/-! ### The square root of `σᵀ` -/

variable {omega : KahlerBackground n (ComplexModel n)} {r : ComplexModel n → ℝ}
  {U : Set (ComplexModel n)}

variable (omega r) in
/-- `σᵀ(z)`. -/
def sT (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ := (sigmaMat omega r z)ᵀ

variable (omega r) in
/-- `Bm z = √(σᵀ(z))`. -/
def Bm (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ := msqrt (sT omega r z)

variable (omega r) in
/-- `Bi z = (Bm z)⁻¹`. -/
def Bi (z : ComplexModel n) : Matrix (Fin n) (Fin n) ℂ := (Bm omega r z)⁻¹

theorem Bm_conjTranspose (z : ComplexModel n) : (Bm omega r z)ᴴ = Bm omega r z :=
  msqrt_conjTranspose _

section OnU

variable (hU : IsOpen U) (hr : IsKahlerModificationOn omega r U)
include hU hr

theorem posDef_sT {z : ComplexModel n} (hz : z ∈ U) : (sT omega r z).PosDef :=
  posDef_sigmaMat_transpose hU hr hz

theorem Bm_mul_Bm {z : ComplexModel n} (hz : z ∈ U) : Bm omega r z * Bm omega r z = sT omega r z :=
  msqrt_mul_self (posDef_sT hU hr hz).posSemidef

theorem isUnit_det_Bm {z : ComplexModel n} (hz : z ∈ U) : IsUnit (Bm omega r z).det := by
  have h := (posDef_sT hU hr hz).det_pos.ne'
  rw [← Bm_mul_Bm hU hr hz, det_mul] at h
  exact isUnit_iff_ne_zero.mpr fun h0 => h (by rw [h0, zero_mul])

theorem Bi_mul_Bm {z : ComplexModel n} (hz : z ∈ U) : Bi omega r z * Bm omega r z = 1 :=
  nonsing_inv_mul _ (isUnit_det_Bm hU hr hz)

theorem Bm_mul_Bi {z : ComplexModel n} (hz : z ∈ U) : Bm omega r z * Bi omega r z = 1 :=
  mul_nonsing_inv _ (isUnit_det_Bm hU hr hz)

omit hU hr in
theorem Bi_conjTranspose (z : ComplexModel n) : (Bi omega r z)ᴴ = Bi omega r z := by
  rw [Bi, conjTranspose_nonsing_inv, Bm_conjTranspose]

theorem sigmaInv_eq {z : ComplexModel n} (hz : z ∈ U) :
    sigmaInv omega r z = Bi omega r z * Bi omega r z := by
  rw [sigmaInv, ← sT, ← Bm_mul_Bm hU hr hz, Bi, Matrix.mul_inv_rev]

theorem mv_Bm_Bi {z : ComplexModel n} (hz : z ∈ U) (x : ComplexModel n) :
    mv (Bm omega r z) (mv (Bi omega r z) x) = x := by
  rw [← mv_mul, Bm_mul_Bi hU hr hz, mv_one]

theorem mv_Bi_Bm {z : ComplexModel n} (hz : z ∈ U) (x : ComplexModel n) :
    mv (Bi omega r z) (mv (Bm omega r z) x) = x := by
  rw [← mv_mul, Bi_mul_Bm hU hr hz, mv_one]

theorem mv_Bm_Bm {z : ComplexModel n} (hz : z ∈ U) (x : ComplexModel n) :
    mv (Bm omega r z) (mv (Bm omega r z) x) = mv (sT omega r z) x := by
  rw [← mv_mul, Bm_mul_Bm hU hr hz]

theorem continuousOn_sT : ContinuousOn (sT omega r) U := by
  refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => ?_
  exact (contDiffOn_sigmaMat hU hr l k).continuousOn

theorem continuousOn_Bm : ContinuousOn (Bm omega r) U :=
  continuousOn_msqrt (continuousOn_sT hU hr) fun _ hz => (posDef_sT hU hr hz).posSemidef

theorem continuousOn_Bi : ContinuousOn (Bi omega r) U := by
  intro z hz
  have hinv : ContinuousAt Ring.inverse (Bm omega r z).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_det_Bm hU hr hz).ne_zero
  exact (ContinuousAt.comp (f := Bm omega r) (continuousAt_matrix_inv _ hinv)
    ((continuousOn_Bm hU hr).continuousAt (hU.mem_nhds hz))).continuousWithinAt

/-- `σ(v) = ⟪v, σᵀ v⟫` (as a complex number). -/
theorem sigmaQ_eq_inner {z : ComplexModel n} (hz : z ∈ U) (v : ComplexModel n) :
    (sigmaQ omega r z v : ℂ) = ⟪v, mv (sT omega r z) v⟫_ℂ := by
  obtain ⟨V, R, hV, hzV, -, hR, hσ⟩ := exists_sigma_potential hU hr hz
  have hRz : ContDiffAt ℝ 2 R z :=
    (hR.contDiffAt (hV.mem_nhds hzV)).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hσ z hzV, ← leviS_self hRz, ← sum_sigmaMat_mul hV hR hσ hzV]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, mv, dotProduct,
    mulVec, sT, transpose_apply, Pi.star_apply, RCLike.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sigmaQ_eq_norm_sq {z : ComplexModel n} (hz : z ∈ U) (v : ComplexModel n) :
    sigmaQ omega r z v = ‖mv (Bm omega r z) v‖ ^ 2 := by
  have h := sigmaQ_eq_inner hU hr hz v
  rw [← mv_Bm_Bm hU hr hz, inner_mv_right, Bm_conjTranspose, inner_self_eq_norm_sq_to_K] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re] at this
  rw [this]
  first
  | (rw [← RCLike.ofReal_pow, RCLike.ofReal_re])
  | norm_cast

/-- **The dual-norm bound**: if `|⟪v, a⟫|² ≤ c σ(v)` for every `v`, then `‖Bi a‖² ≤ c`. -/
theorem norm_mv_Bi_sq_le {z : ComplexModel n} (hz : z ∈ U) {a : ComplexModel n} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ v, ‖⟪v, a⟫_ℂ‖ ^ 2 ≤ c * sigmaQ omega r z v) :
    ‖mv (Bi omega r z) a‖ ^ 2 ≤ c := by
  set y := mv (Bi omega r z) a with hy
  have hv := h (mv (Bi omega r z) y)
  rw [inner_mv_left, Bi_conjTranspose, ← hy, inner_self_eq_norm_sq_to_K,
    sigmaQ_eq_norm_sq hU hr hz, mv_Bm_Bi hU hr hz] at hv
  have hv' : (‖y‖ ^ 2) ^ 2 ≤ c * ‖y‖ ^ 2 := by simpa [norm_pow] using hv
  by_cases hy0 : ‖y‖ = 0
  · rw [hy0]
    simpa using hc
  · have hp : 0 < ‖y‖ ^ 2 := by positivity
    nlinarith

end OnU

/-! ### The `(0,2)`-norm and the wedge bound -/

/-- The entrywise representation of `Bi β Biᵀ` (for the `σ`-norm of `(0,2)`-covectors). -/
def flat2 (M : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 fun p => M p.1 p.2

theorem norm_flat2_sq (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖flat2 M‖ ^ 2 = ∑ j, ∑ k, ‖M j k‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem re_trace_conjTranspose_mul_self (M : Matrix (Fin n) (Fin n) ℂ) :
    (trace (Mᴴ * M)).re = ∑ j, ∑ k, ‖M j k‖ ^ 2 := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, RCLike.star_def, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem transpose_conjTranspose_of_herm {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Qᴴ = Q) :
    (Qᵀ)ᴴ = Qᵀ := by
  ext i j
  have := congrFun (congrFun hQ j) i
  simp only [conjTranspose_apply, transpose_apply] at this ⊢
  exact this

/-- `|β|²_σ = ½ ‖Q β Qᵀ‖²` for `N = Q Q`, `Q` Hermitian. -/
theorem zeroTwoNormSq_eq_of_inv {N Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Qᴴ = Q) (hN : N = Q * Q)
    (β : Matrix (Fin n) (Fin n) ℂ) :
    zeroTwoNormSq N β = (1 / 2 : ℝ) * ‖flat2 (Q * β * Qᵀ)‖ ^ 2 := by
  rw [norm_flat2_sq, zeroTwoNormSq, hN, ← re_trace_conjTranspose_mul_self]
  congr 2
  rw [conjTranspose_mul, conjTranspose_mul, hQ, transpose_conjTranspose_of_herm hQ,
    transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm Qᵀ]
  simp only [Matrix.mul_assoc]

end SGPT.Trace.TwistedL2

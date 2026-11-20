import SGPT.GAGA.H0SConeGraph

/-!
# The Łojasiewicz inequality for the cone over a projective submanifold


* `exists_local_lojasiewicz` (**Jacobian criterion ⇒ local Łojasiewicz**): let `V ⊆ ℂᴺ` be,
  near `y₀ ∈ V`, the graph `{(L₀ y)₂ = g (L₀ y)₁}` of a continuous map in linear coordinates
  `L₀ : ℂᴺ ≅ ℂᵏ × ℂʳ`, and let `h_1, …, h_s` be `C¹` functions vanishing on `V` whose
  differentials at `y₀` have no common zero in the normal directions `L₀⁻¹(0 × ℂʳ)`.  Then
  `∑_j |h_j(y)|² ≥ c dist(y, V)²` near `y₀`.  (Proof: with `y' = L₀⁻¹((L₀ y)₁, g (L₀ y)₁) ∈ V`
  we have `y - y' = L₀⁻¹(0, u)`, and the strict derivative of `h = (h_j)` at `y₀` gives
  `|h(y)| = |h(y) - h(y')| ≥ |Dh(y₀)(y - y')| - η|y - y'| ≥ c'|u|`.)
* `homogenize i d g`: the homogenization `Z_i^d g(Z'/Z_i)` (with `Z'` the other coordinates) of a
  polynomial `g` on the affine chart `U_i`, for `d > deg g`; it vanishes on `{Z_i = 0}`
  (`eval_homogenize`).
* `exists_cone_lojasiewicz` (**global Łojasiewicz inequality on the cone**): if, in each affine
  chart, the common zeros of the polynomials `g_{i,j}` lie in `S ∩ U_i` and the local
  Łojasiewicz inequality holds at the points of `S ∩ U_i`, then their
  homogenizations `G_{i,j}` satisfy
  `∑_{i,j} |G_{i,j}(Z)|² ≥ c |Z|^{2(d-1)} dist(Z, Ŝ)²` on `ℂ^{N+1}`, `Ŝ` the affine cone over
  `S`: the hypothesis `hLoj` of the extension theorem.  (Proof: both sides are
  homogeneous of degree `2d`; on the unit sphere one uses the local inequality near points of
  the cone and positivity of `∑ |G|²` away from it, then compactness.)
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0S

open Set Filter Metric
open scoped Topology ContDiff NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.GAGA.H0

/-! ### The local inequality -/

/-- **Jacobian criterion ⇒ local Łojasiewicz inequality.** -/
theorem exists_local_lojasiewicz {N k r s : ℕ} {V : Set (ComplexModel N)} {y₀ : ComplexModel N}
    (hy₀ : y₀ ∈ V) (L0 : ComplexModel N ≃L[ℂ] ComplexModel k × ComplexModel r) {ε : ℝ}
    (hε : 0 < ε) {g : ComplexModel k → ComplexModel r} (hgc : ContinuousAt g (L0 y₀).1)
    (hgraph : ∀ y ∈ ball y₀ ε, y ∈ V ↔ (L0 y).2 = g (L0 y).1)
    (h : Fin s → ComplexModel N → ℂ) (hh : ∀ j, ContDiffAt ℂ 1 (h j) y₀)
    (hV : ∀ j, ∀ y ∈ V, h j y = 0)
    (hjac : ∀ u : ComplexModel r, (∀ j, fderiv ℂ (h j) y₀ (L0.symm (0, u)) = 0) → u = 0) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ y ∈ ball y₀ δ, c * infDist y V ^ 2 ≤ ∑ j, ‖h j y‖ ^ 2 := by
  set H : ComplexModel N → (Fin s → ℂ) := fun y j => h j y with hHdef
  set H' : ComplexModel N →L[ℂ] (Fin s → ℂ) := ContinuousLinearMap.pi fun j => fderiv ℂ (h j) y₀
  have hHs : HasStrictFDerivAt H H' y₀ :=
    hasStrictFDerivAt_pi.mpr fun j => (hh j).hasStrictFDerivAt (by simp)
  set P : ComplexModel r →L[ℂ] ComplexModel N :=
    (L0.symm : ComplexModel k × ComplexModel r →L[ℂ] ComplexModel N).comp
      (ContinuousLinearMap.inr ℂ (ComplexModel k) (ComplexModel r)) with hPdef
  have hP : ∀ u, P u = L0.symm (0, u) := fun u => rfl
  set B : ComplexModel r →L[ℂ] (Fin s → ℂ) := H'.comp P with hBdef
  have hBinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).mpr fun u hu => ?_
    refine hjac u fun j => ?_
    have := congrFun hu j
    simpa [hBdef, hP, H'] using this
  obtain ⟨K, hK0, hK⟩ :=
    (B : ComplexModel r →ₗ[ℂ] (Fin s → ℂ)).injective_iff_antilipschitz.mp hBinj
  have hKB : ∀ u, ‖u‖ ≤ K * ‖B u‖ := fun u => ZeroHomClass.bound_of_antilipschitz
    (B : ComplexModel r →ₗ[ℂ] (Fin s → ℂ)) hK u
  set A : ℝ := ‖P‖ with hAdef
  have hA0 : 0 ≤ A := norm_nonneg _
  have hK0' : (0 : ℝ) < K := hK0
  set η : ℝ≥0 := ⟨1 / (2 * K * (A + 1)), by positivity⟩ with hηdef
  have hη : (0 : ℝ≥0) < η := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_zero]
    change (0 : ℝ) < 1 / (2 * K * (A + 1))
    positivity
  obtain ⟨T, hT, happrox⟩ := hHs.approximates_deriv_on_nhds (Or.inr hη)
  obtain ⟨δ₁, hδ₁, hδ₁T⟩ := Metric.mem_nhds_iff.mp hT
  -- the projection to the graph
  set π : ComplexModel N → ComplexModel N := fun y => L0.symm ((L0 y).1, g (L0 y).1) with hπdef
  have hπ₀ : π y₀ = y₀ := by
    have h1 := (hgraph y₀ (mem_ball_self hε)).mp hy₀
    simp only [hπdef, ← h1, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  have hπc : ContinuousAt π y₀ := by
    have h1 : ContinuousAt (fun y : ComplexModel N => (L0 y).1) y₀ :=
      (L0.continuous.fst).continuousAt
    exact L0.symm.continuous.continuousAt.comp
      (h1.prodMk (ContinuousAt.comp (f := fun y : ComplexModel N => (L0 y).1) hgc h1))
  obtain ⟨δ₂, hδ₂, hδ₂π⟩ := Metric.eventually_nhds_iff.mp
    (hπc.eventually (ball_mem_nhds (π y₀) (lt_min hε hδ₁)))
  refine ⟨min δ₁ δ₂, 1 / (2 * K * (A + 1)) ^ 2, lt_min hδ₁ hδ₂, by positivity, fun y hy => ?_⟩
  have hyT : y ∈ T := hδ₁T (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hy) (min_le_left _ _)))
  have hπy := hδ₂π (lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _))
  rw [hπ₀] at hπy
  have hπyT : π y ∈ T := hδ₁T (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hπy) (min_le_right _ _)))
  have hLπ : L0 (π y) = ((L0 y).1, g (L0 y).1) := by
    simp only [hπdef, ContinuousLinearEquiv.apply_symm_apply]
  have hπV : π y ∈ V := by
    rw [hgraph _ (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hπy) (min_le_left _ _))), hLπ]
  set u : ComplexModel r := (L0 y).2 - g (L0 y).1 with hudef
  have hdiff : y - π y = P u := by
    rw [hP]
    apply L0.injective
    rw [map_sub, hLπ, ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext (by simp) (by simp [hudef])
  have hHπ : H (π y) = 0 := funext fun j => hV j _ hπV
  have happ := happrox y hyT (π y) hπyT
  rw [hHπ, sub_zero, hdiff] at happ
  have hPu : ‖P u‖ ≤ A * ‖u‖ := P.le_opNorm u
  -- `‖H y‖ ≥ ‖u‖ / (2K)`
  have hHy : ‖u‖ ≤ 2 * K * ‖H y‖ := by
    have h1 : ‖B u‖ ≤ ‖H y‖ + η * ‖P u‖ := by
      calc ‖B u‖ = ‖H y - (H y - H' (P u))‖ := by rw [sub_sub_cancel]; rfl
        _ ≤ ‖H y‖ + ‖H y - H' (P u)‖ := norm_sub_le _ _
        _ ≤ ‖H y‖ + η * ‖P u‖ := by gcongr
    have h2 : (η : ℝ) * ‖P u‖ ≤ ‖u‖ / (2 * K) := by
      calc (η : ℝ) * ‖P u‖ ≤ 1 / (2 * K * (A + 1)) * (A * ‖u‖) := by
            gcongr
            · exact le_of_eq rfl
        _ ≤ ‖u‖ / (2 * K) := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [norm_nonneg u, mul_nonneg hK0'.le (norm_nonneg u)]
    have h3 := hKB u
    have h4 : ‖u‖ ≤ K * (‖H y‖ + ‖u‖ / (2 * K)) := by
      calc ‖u‖ ≤ K * ‖B u‖ := h3
        _ ≤ K * (‖H y‖ + ‖u‖ / (2 * K)) := by gcongr; linarith
    have h5 : K * (‖u‖ / (2 * K)) = ‖u‖ / 2 := by field_simp
    nlinarith [h4, h5]
  -- `dist(y, V) ≤ (A + 1) ‖u‖`
  have hdist : infDist y V ≤ (A + 1) * ‖u‖ := by
    calc infDist y V ≤ dist y (π y) := infDist_le_dist_of_mem hπV
      _ = ‖P u‖ := by rw [dist_eq_norm, hdiff]
      _ ≤ A * ‖u‖ := hPu
      _ ≤ (A + 1) * ‖u‖ := by nlinarith [norm_nonneg u]
  -- `‖H y‖² ≤ ∑ ‖h_j y‖²`
  have hsum : ‖H y‖ ^ 2 ≤ ∑ j, ‖h j y‖ ^ 2 := by
    have hle : ‖H y‖ ≤ Real.sqrt (∑ j, ‖h j y‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
      rw [Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact Finset.single_le_sum (f := fun j => ‖h j y‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    calc ‖H y‖ ^ 2 ≤ Real.sqrt (∑ j, ‖h j y‖ ^ 2) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hfin : infDist y V ≤ 2 * K * (A + 1) * ‖H y‖ := by
    calc infDist y V ≤ (A + 1) * ‖u‖ := hdist
      _ ≤ (A + 1) * (2 * K * ‖H y‖) := by gcongr
      _ = 2 * K * (A + 1) * ‖H y‖ := by ring
  have hpos : 0 < 2 * K * (A + 1) := by positivity
  have hsq : infDist y V ^ 2 ≤ (2 * K * (A + 1)) ^ 2 * ‖H y‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ infDist_nonneg hfin 2
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  nlinarith [hsq, mul_le_mul_of_nonneg_left hsum (sq_nonneg (2 * K * (A + 1)))]

end SGPT.GAGA.H0S

namespace SGPT.GAGA.H0S

open Set Filter Metric
open scoped Topology ContDiff NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.GAGA.H0

/-! ### Homogenization -/

variable {N : ℕ}

/-- The homogenization `Z_i^d g(Z'/Z_i)` (`Z'` the coordinates other than `Z_i`) of a polynomial
`g` on the affine chart `U_i`: `∑_m g_m Z_i^{d - |m|} ∏_k Z_{i.succAbove k}^{m_k}`. -/
def homogenize (i : Fin (N + 1)) (d : ℕ) (g : MvPolynomial (Fin N) ℂ) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ m ∈ g.support, MvPolynomial.C (g.coeff m) *
    MvPolynomial.X i ^ (d - m.sum fun _ e => e) * ∏ k, MvPolynomial.X (i.succAbove k) ^ m k

/-- For `d > deg g`: `G(Z) = Z_i^d g(Z'/Z_i)` if `Z_i ≠ 0`, and `G(Z) = 0` if `Z_i = 0`. -/
theorem eval_homogenize (i : Fin (N + 1)) {d : ℕ} {g : MvPolynomial (Fin N) ℂ}
    (hd : g.totalDegree < d) (Z : Fin (N + 1) → ℂ) :
    MvPolynomial.eval Z (homogenize i d g) =
      if Z i = 0 then 0 else Z i ^ d * MvPolynomial.eval (fun k => Z (i.succAbove k) / Z i) g := by
  classical
  have hsum : ∀ m : Fin N →₀ ℕ, (m.sum fun _ e => e) = ∑ k, m k := fun m =>
    Finsupp.sum_fintype m _ (fun _ => rfl)
  have hdeg : ∀ m ∈ g.support, ∑ k, m k < d := fun m hm => by
    rw [← hsum]; exact lt_of_le_of_lt (MvPolynomial.le_totalDegree hm) hd
  unfold homogenize
  rw [map_sum]
  split_ifs with hZ
  · refine Finset.sum_eq_zero fun m hm => ?_
    simp only [map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X, hZ, hsum]
    rw [zero_pow (by have := hdeg m hm; omega)]
    ring
  · rw [MvPolynomial.eval_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X, map_prod, hsum]
    have h1 : ∏ k, (Z (i.succAbove k) / Z i) ^ m k =
        (∏ k, Z (i.succAbove k) ^ m k) / Z i ^ (∑ k, m k) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ => div_pow _ _ _
    have h2 : Z i ^ d = Z i ^ (d - ∑ k, m k) * Z i ^ (∑ k, m k) := by
      rw [← pow_add]
      congr 1
      have := hdeg m hm
      omega
    rw [h1, h2]
    have hne : Z i ^ (∑ k, m k) ≠ 0 := pow_ne_zero _ hZ
    field_simp

/-- Homogeneity: `G(c Z) = c^d G(Z)` (for `0 < d`, `d > deg g`). -/
theorem eval_homogenize_smul (i : Fin (N + 1)) {d : ℕ} {g : MvPolynomial (Fin N) ℂ}
    (hd : g.totalDegree < d) (c : ℂ) (Z : Fin (N + 1) → ℂ) :
    MvPolynomial.eval (c • Z) (homogenize i d g) = c ^ d * MvPolynomial.eval Z (homogenize i d g) := by
  rw [eval_homogenize i hd, eval_homogenize i hd]
  by_cases hZ : Z i = 0
  · simp [hZ]
  by_cases hc : c = 0
  · subst hc
    simp [zero_pow (show d ≠ 0 by omega)]
  have hcZ : (c • Z) i ≠ 0 := by simp [hc, hZ]
  rw [if_neg hcZ, if_neg hZ]
  simp only [Pi.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hc]
  ring

/-- On the chart `U_i`, `∑_j |G_{i,j}(Z)|² = |Z_i|^{2d} ∑_j |g_{i,j}(Z'/Z_i)|²`. -/
theorem sum_norm_eval_homogenize_sq (i : Fin (N + 1)) {q d : ℕ}
    (g : Fin q → MvPolynomial (Fin N) ℂ) (hd : ∀ j, (g j).totalDegree < d)
    {Z : ComplexModel (N + 1)} (hZ : Z i ≠ 0) :
    ∑ j, ‖MvPolynomial.eval (fun k => Z k) (homogenize i d (g j))‖ ^ 2 =
      ‖Z i‖ ^ (2 * d) * ∑ j, ‖MvPolynomial.eval (fun k => affineRatio i (WithLp.ofLp Z) k) (g j)‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_homogenize i (hd j), if_neg hZ, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm d 2]
  rfl

/-! ### Distance to the cone -/

theorem norm_affineLift_sub (i : Fin (N + 1)) (y v : ComplexModel N) :
    ‖WithLp.toLp 2 (affineLift i y) - WithLp.toLp 2 (affineLift i v)‖ = ‖y - v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succAbove _ i]
  simp

theorem affineLift_mem_affineCone {S : Set (ComplexProjectiveSpace N)} (i : Fin (N + 1))
    {v : ComplexModel N} (hv : affinePoint i v ∈ S) :
    WithLp.toLp 2 (affineLift i v) ∈ affineCone S := fun _ => hv

/-- `dist(Z, Ŝ) ≤ |Z_i| dist(Z'/Z_i, S ∩ U_i)` on `{Z_i ≠ 0}`. -/
theorem infDist_affineCone_le {S : Set (ComplexProjectiveSpace N)} (i : Fin (N + 1))
    {Z : ComplexModel (N + 1)} (hZ : Z i ≠ 0) (hV : {y | affinePoint i y ∈ S}.Nonempty) :
    infDist Z (affineCone S) ≤
      ‖Z i‖ * infDist (affineRatio i (WithLp.ofLp Z)) {y | affinePoint i y ∈ S} := by
  have hpos : 0 < ‖Z i‖ := norm_pos_iff.mpr hZ
  have hZeq : Z = Z i • WithLp.toLp 2 (affineLift i (affineRatio i (WithLp.ofLp Z))) := by
    rw [affineLift_affineRatio i hZ]
    ext m
    simp [hZ]
  have key : infDist Z (affineCone S) / ‖Z i‖ ≤
      infDist (affineRatio i (WithLp.ofLp Z)) {y | affinePoint i y ∈ S} := by
    refine (le_infDist hV).mpr fun v hv => ?_
    rw [div_le_iff₀ hpos]
    have hW : Z i • WithLp.toLp 2 (affineLift i v) ∈ affineCone S :=
      smul_mem_affineCone _ (affineLift_mem_affineCone i hv)
    calc infDist Z (affineCone S) ≤ dist Z (Z i • WithLp.toLp 2 (affineLift i v)) :=
          infDist_le_dist_of_mem hW
      _ = dist (affineRatio i (WithLp.ofLp Z)) v * ‖Z i‖ := by
        have hsub : Z - Z i • WithLp.toLp 2 (affineLift i v) = Z i •
            (WithLp.toLp 2 (affineLift i (affineRatio i (WithLp.ofLp Z))) -
              WithLp.toLp 2 (affineLift i v)) := by
          rw [smul_sub, ← hZeq]
        rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul, norm_affineLift_sub, mul_comm]
  rwa [div_le_iff₀ hpos, mul_comm] at key

/-! ### The global inequality -/

/-- **The Łojasiewicz inequality on the affine cone.**  Let `S ⊆ ℙᴺ` and `g_{i,j}`
(`i ∈ {0, …, N}`, `j < q`) polynomials of degree `< d` (`d ≥ 1`) on the affine charts such that
their common zeros in `U_i` lie in `S` and the local Łojasiewicz inequality
`c dist(y, S ∩ U_i)² ≤ ∑_j |g_{i,j}(y)|²` holds near every point of `S ∩ U_i`.  Then the homogenizations
`G_{i,j} = Z_i^d g_{i,j}(Z'/Z_i)` satisfy
`c |Z|^{2(d-1)} dist(Z, Ŝ)² ≤ ∑_{i,j} |G_{i,j}(Z)|²` on `ℂ^{N+1}`. -/
theorem exists_cone_lojasiewicz {q d : ℕ} {S : Set (ComplexProjectiveSpace N)}
    (g : Fin (N + 1) → Fin q → MvPolynomial (Fin N) ℂ) (hd1 : 1 ≤ d)
    (hd : ∀ i j, (g i j).totalDegree < d)
    (hzero : ∀ i (y : ComplexModel N), (∀ j, MvPolynomial.eval (fun k => y k) (g i j) = 0) →
      affinePoint i y ∈ S)
    (hloc : ∀ i (y₀ : ComplexModel N), affinePoint i y₀ ∈ S → ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ y ∈ ball y₀ δ, c * infDist y {y | affinePoint i y ∈ S} ^ 2 ≤
        ∑ j, ‖MvPolynomial.eval (fun k => y k) (g i j)‖ ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ Z : ComplexModel (N + 1),
      c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z (affineCone S) ^ 2 ≤
        ∑ ij : Fin (N + 1) × Fin q,
          ‖MvPolynomial.eval (fun k => Z k) (homogenize ij.1 d (g ij.1 ij.2))‖ ^ 2 := by
  set C := affineCone S with hCdef
  have hCcone : ∀ (c : ℂ) (Z : ComplexModel (N + 1)), Z ∈ C → c • Z ∈ C :=
    fun c _ hZ => smul_mem_affineCone c hZ
  set Gf : ComplexModel (N + 1) → ℝ := fun Z => ∑ ij : Fin (N + 1) × Fin q,
    ‖MvPolynomial.eval (fun k => Z k) (homogenize ij.1 d (g ij.1 ij.2))‖ ^ 2 with hGfdef
  have hGf0 : ∀ Z, 0 ≤ Gf Z := fun Z => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hGfc : Continuous Gf := by
    refine continuous_finsetSum _ fun ij _ => ?_
    exact ((differentiable_polyFun (fun _ : Fin 1 => homogenize ij.1 d (g ij.1 ij.2)) 0).continuous.norm.pow 2)
  -- the chart part of `Gf`
  have hGfi : ∀ (i : Fin (N + 1)) Z, ∑ j, ‖MvPolynomial.eval (fun k => Z k) (homogenize i d (g i j))‖ ^ 2
      ≤ Gf Z := by
    intro i Z
    rw [hGfdef]
    beta_reduce
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun i' => ∑ j, ‖MvPolynomial.eval (fun k => Z k)
      (homogenize i' d (g i' j))‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  -- homogeneity of `Gf`
  have hGfsmul : ∀ (c : ℂ) Z, Gf (c • Z) = ‖c‖ ^ (2 * d) * Gf Z := by
    intro c Z
    rw [hGfdef]
    beta_reduce
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    have h := eval_homogenize_smul ij.1 (hd ij.1 ij.2) c (fun k => Z k)
    change ‖MvPolynomial.eval (c • fun k => Z k) _‖ ^ 2 = _
    rw [h, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm d 2]
  -- the inequality on the unit sphere
  have hsphere : ∃ c : ℝ, 0 < c ∧ ∀ Z ∈ sphere (0 : ComplexModel (N + 1)) 1,
      c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z C ^ 2 ≤ Gf Z := by
    refine (isCompact_sphere (0 : ComplexModel (N + 1)) 1).induction_on
      (p := fun T => ∃ c : ℝ, 0 < c ∧ ∀ Z ∈ T, c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z C ^ 2 ≤ Gf Z)
      ⟨1, one_pos, fun _ h => absurd h (Set.notMem_empty _)⟩
      (fun _ _ hst ⟨c, hc, h⟩ => ⟨c, hc, fun Z hZ => h Z (hst hZ)⟩)
      (fun _ _ ⟨c, hc, h⟩ ⟨c', hc', h'⟩ => ⟨min c c', lt_min hc hc', fun Z hZ => by
        rcases hZ with hZ | hZ
        · exact le_trans (by gcongr; exact min_le_left _ _) (h Z hZ)
        · exact le_trans (by gcongr; exact min_le_right _ _) (h' Z hZ)⟩) ?_
    intro Z hZ
    have hZn : ‖Z‖ = 1 := by simpa using hZ
    have hZ0 : Z ≠ 0 := by rintro rfl; simp at hZn
    obtain ⟨i, hZi⟩ : ∃ i, Z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hZ0 (by ext j; simpa using h j)
    have hZ2 : ‖Z‖ < 2 := by rw [hZn]; norm_num
    have hnorm2 : ∀ᶠ Z' in 𝓝 Z, ‖Z'‖ < 2 := continuous_norm.continuousAt.eventually (gt_mem_nhds hZ2)
    by_cases hZC : Z ∈ C
    · -- near the cone: the local inequality in the chart `U_i`
      set y₀ := affineRatio i (WithLp.ofLp Z) with hy₀def
      have hy₀ : affinePoint i y₀ ∈ S := (mem_affineCone_iff hZi).mp hZC
      obtain ⟨δ, c, hδ, hc, hlocal⟩ := hloc i y₀ hy₀
      set a := ‖Z i‖ / 2 with hadef
      have ha : 0 < a := by positivity
      have hev : ∀ᶠ Z' in 𝓝 Z, a < ‖Z' i‖ ∧ affineRatio i (WithLp.ofLp Z') ∈ ball y₀ δ ∧
          ‖Z'‖ < 2 := by
        have h1 : ∀ᶠ Z' in 𝓝 Z, a < ‖Z' i‖ :=
          (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.norm.continuousAt.eventually
            (lt_mem_nhds (half_lt_self (norm_pos_iff.mpr hZi)))
        have hcont : ContinuousAt (fun Z' : ComplexModel (N + 1) =>
            affineRatio i (WithLp.ofLp Z')) Z := by
          have : (fun Z' : ComplexModel (N + 1) => affineRatio i (WithLp.ofLp Z')) =
              fun Z' => (Z' i)⁻¹ • numer i Z' := funext (affineRatio_eq_smul_numer i)
          rw [this]
          exact (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt).inv₀ hZi).smul
            (numer i).continuous.continuousAt
        exact h1.and ((hcont.eventually (ball_mem_nhds y₀ hδ)).and hnorm2)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds hev, c * a ^ (2 * (d - 1)) / 2 ^ (2 * (d - 1)),
        by positivity, fun Z' hZ' => ?_⟩
      obtain ⟨haZ', hZ'b, hZ'2⟩ := hZ'
      have hZ'i : Z' i ≠ 0 := by
        intro h; rw [h, norm_zero] at haZ'; linarith
      have hloc' := hlocal _ hZ'b
      have hdist := infDist_affineCone_le i hZ'i ⟨y₀, hy₀⟩
      have hGi := hGfi i Z'
      rw [sum_norm_eval_homogenize_sq i (g i) (hd i) hZ'i] at hGi
      set D := infDist (affineRatio i (WithLp.ofLp Z')) {y | affinePoint i y ∈ S}
      have hD0 : 0 ≤ D := infDist_nonneg
      have hCD : infDist Z' C ^ 2 ≤ ‖Z' i‖ ^ 2 * D ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ infDist_nonneg hdist 2
      have hpow : ‖Z' i‖ ^ (2 * d) = ‖Z' i‖ ^ (2 * (d - 1)) * ‖Z' i‖ ^ 2 := by
        rw [← pow_add]; congr 1; omega
      have hZ'n : ‖Z'‖ ^ (2 * (d - 1)) ≤ 2 ^ (2 * (d - 1)) := by
        gcongr
      have haZ'p : a ^ (2 * (d - 1)) ≤ ‖Z' i‖ ^ (2 * (d - 1)) := by
        gcongr
      have h2pos : (0 : ℝ) < 2 ^ (2 * (d - 1)) := by positivity
      calc c * a ^ (2 * (d - 1)) / 2 ^ (2 * (d - 1)) * ‖Z'‖ ^ (2 * (d - 1)) * infDist Z' C ^ 2
          ≤ c * a ^ (2 * (d - 1)) * infDist Z' C ^ 2 := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ h2pos]
            have : 0 ≤ c * a ^ (2 * (d - 1)) * infDist Z' C ^ 2 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hZ'n this]
        _ ≤ c * ‖Z' i‖ ^ (2 * (d - 1)) * (‖Z' i‖ ^ 2 * D ^ 2) := by
            gcongr
        _ = ‖Z' i‖ ^ (2 * d) * (c * D ^ 2) := by rw [hpow]; ring
        _ ≤ ‖Z' i‖ ^ (2 * d) * ∑ j, ‖MvPolynomial.eval (fun k =>
              affineRatio i (WithLp.ofLp Z') k) (g i j)‖ ^ 2 := by gcongr
        _ ≤ Gf Z' := hGi
    · -- away from the cone: `Gf` is positive
      have hy : affinePoint i (affineRatio i (WithLp.ofLp Z)) ∉ S := fun h =>
        hZC ((mem_affineCone_iff hZi).mpr h)
      obtain ⟨j, hj⟩ : ∃ j, MvPolynomial.eval (fun k => affineRatio i (WithLp.ofLp Z) k)
          (g i j) ≠ 0 := by
        by_contra h
        push Not at h
        exact hy (hzero i _ h)
      have hGpos : 0 < Gf Z := by
        refine lt_of_lt_of_le ?_ (hGfi i Z)
        rw [sum_norm_eval_homogenize_sq i (g i) (hd i) hZi]
        refine mul_pos (pow_pos (norm_pos_iff.mpr hZi) _) ?_
        exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hj) 2)
          (Finset.single_le_sum (f := fun j => ‖MvPolynomial.eval (fun k =>
            affineRatio i (WithLp.ofLp Z) k) (g i j)‖ ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j))
      have hev : ∀ᶠ Z' in 𝓝 Z, Gf Z / 2 < Gf Z' ∧ ‖Z'‖ < 2 :=
        (hGfc.continuousAt.eventually (lt_mem_nhds (half_lt_self hGpos))).and hnorm2
      refine ⟨_, mem_nhdsWithin_of_mem_nhds hev, Gf Z / 2 / (2 ^ (2 * (d - 1)) * 4),
        by positivity, fun Z' hZ' => ?_⟩
      obtain ⟨hG', hZ'2⟩ := hZ'
      have hdist : infDist Z' C ≤ ‖Z'‖ := by
        simpa using infDist_le_dist_of_mem (x := Z') (zero_mem_affineCone S)
      have h1 : ‖Z'‖ ^ (2 * (d - 1)) * infDist Z' C ^ 2 ≤ 2 ^ (2 * (d - 1)) * 4 := by
        have h2 : infDist Z' C ^ 2 ≤ 4 := by
          have := pow_le_pow_left₀ infDist_nonneg (hdist.trans hZ'2.le) 2
          linarith
        have h3 : ‖Z'‖ ^ (2 * (d - 1)) ≤ 2 ^ (2 * (d - 1)) := by gcongr
        exact mul_le_mul h3 h2 (sq_nonneg _) (by positivity)
      have h4 : (0 : ℝ) < 2 ^ (2 * (d - 1)) * 4 := by positivity
      calc Gf Z / 2 / (2 ^ (2 * (d - 1)) * 4) * ‖Z'‖ ^ (2 * (d - 1)) * infDist Z' C ^ 2
          = Gf Z / 2 / (2 ^ (2 * (d - 1)) * 4) * (‖Z'‖ ^ (2 * (d - 1)) * infDist Z' C ^ 2) := by
            ring
        _ ≤ Gf Z / 2 / (2 ^ (2 * (d - 1)) * 4) * (2 ^ (2 * (d - 1)) * 4) := by
            gcongr
        _ = Gf Z / 2 := by field_simp
        _ ≤ Gf Z' := hG'.le
  -- homogeneity
  obtain ⟨c, hc, hcS⟩ := hsphere
  have key : ∀ (t : ℝ) (W : ComplexModel (N + 1)), 0 < t → ‖W‖ = 1 →
      c * ‖(t : ℂ) • W‖ ^ (2 * (d - 1)) * infDist ((t : ℂ) • W) C ^ 2 ≤ Gf ((t : ℂ) • W) := by
    intro t W ht hW
    have h1 := hcS W (by simpa using hW)
    have htn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    rw [hGfsmul, infDist_smul_cone hCcone (by exact_mod_cast ht.ne'), norm_smul, htn, hW,
      mul_one]
    rw [hW, one_pow, mul_one] at h1
    have hpow : t ^ (2 * d) = t ^ (2 * (d - 1)) * t ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, mul_pow]
    have ht' : 0 ≤ t ^ (2 * (d - 1)) * t ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 ht']
  refine ⟨c, hc, fun Z => ?_⟩
  by_cases hZ0 : Z = 0
  · subst hZ0
    rw [infDist_zero_of_mem (zero_mem_affineCone S)]
    exact (le_of_eq (by ring)).trans (hGf0 0)
  · have ht : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
    have hW : ‖((‖Z‖⁻¹ : ℝ) : ℂ) • Z‖ = 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
        inv_mul_cancel₀ ht.ne']
    have hZW : ((‖Z‖ : ℝ) : ℂ) • ((((‖Z‖⁻¹ : ℝ)) : ℂ) • Z) = Z := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
    have := key ‖Z‖ _ ht hW
    rwa [hZW] at this

end SGPT.GAGA.H0S

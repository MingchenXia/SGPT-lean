import SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
import SGPT.Foundations.Analysis.Pending.HolderNemytskii
import SGPT.Foundations.Analysis.Pending.WirtingerLogDet

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The complex Monge–Ampère operator on `C^{2,r}(M)`: chart representation and remainder estimate

For a Hermitian background form `a` on a complex manifold `M` (e.g. a Kähler form `A`) the
Monge–Ampère operator is `ma a ψ = log det(H_a + complexHessian ψ) - log det H_a`, read in charts
(`maChart`, `ma`); it is `log((a + ddᶜψ)^N / a^N)`, chart independent where the determinant does not
vanish (`maChart_eq_of_mem`: both matrices transform by `Jᵀ (·) J̄`, `re_det_congr`).

Locally, `maChart` is the function `maLocal H (z, K) = log det(H(z) + herm K) - log det H(z)` of the
point and of the array `K = (∂²ψ/∂z_j∂z̄_k)` (`kfun`), smooth on the open set `maDomain` where the
determinants are positive (`contDiffOn_maLocal`), with derivative in `K` given by Jacobi's formula
(`hasDerivAt_det_add_smul`): `D F(z, K)(0, L) = Re tr((H + herm K)⁻¹ herm L)`
(`fderiv_maLocal_apply`) — the Laplacian of `a + ddᶜψ` (`KahlerLaplacianChart`).
`exists_cutoffModel` replaces `maLocal` near a compact graph by a smooth compactly supported `Γ`.

**Main result** `exists_chart_estimates` (one chart `e_i` of a Hölder atlas, base point
`Φ₀ ∈ C^{2,r}(M)` with `g = a + ddᶜΦ₀` Hermitian): there are `ρ, C` such that for `‖ψ - Φ₀‖ < ρ`
the local representative of `ma a ψ` lies in `C^{0,r}_b`, and for `‖ψ_j - Φ₀‖ < ρ` that of the
remainder `ma a ψ₁ - ma a ψ₂ - Δ_g (ψ₁ - ψ₂)` has `C^{0,r}_b` norm
`≤ C (‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) ‖ψ₁ - ψ₂‖` (`HolderNemytskii.abs_remainder_sub_le` applied to
`P_j(z) = (z, K_{ψ_j}(z))`).  Summed over the atlas this is the strict differentiability of
`ψ ↦ ma a ψ : C^{2,r}(M) → C^{0,r}(M)` at `Φ₀` with derivative `Δ_g` (consumer: the openness step of
the `ε`-continuity path of Yau's theorem, blueprint `bou:yau-openness`; TN.4 B5, N1).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff InnerProductSpace Manifold ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.MongeAmpereHolder

open FirstPass FirstPass.MongeAmpere KahlerLaplacianChart

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Transformation laws along chart transitions -/

/-- The complex Hessian of a function that is `C²` in every chart transforms by `Jᵀ (·) J̄`. -/
theorem complexHessian_transition {u : M → ℝ}
    (hu : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun w => u (e.val.symm w)) e.val.target)
    {e f : ComplexChart n M} {y : M} (hye : y ∈ e.val.source) (hyf : y ∈ f.val.source) :
    complexHessian (fun w => u (e.val.symm w)) (e.val y) =
      (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y))ᵀ *
        complexHessian (fun w => u (f.val.symm w)) (f.val y) *
          (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y)).map
            (starRingEnd ℂ) := by
  set τ := chartTransition e f with hτ
  have hz : e.val y ∈ τ.source := RelativeEigenvalueMax.mem_chartTransition_source hye hyf
  have hτz : τ (e.val y) = f.val y := RelativeEigenvalueMax.chartTransition_apply_chart hye
  have hev : (fun w => u (e.val.symm w)) =ᶠ[𝓝 (e.val y)]
      (fun w => (fun x => u (f.val.symm x)) (τ w)) := by
    filter_upwards [τ.open_source.mem_nhds hz] with w hw
    have hw2 : e.val.symm w ∈ f.val.source := hw.2
    show u (e.val.symm w) = u (f.val.symm (f.val (e.val.symm w)))
    rw [f.val.left_inv hw2]
  have hτhol : ContDiffOn ℂ ∞ τ τ.source := fun w hw =>
    (HolomorphicMaps.chartTransition_contDiffAt e f hw).contDiffWithinAt
  have hmaps : MapsTo τ τ.source f.val.target := fun w hw => (τ.map_source hw).1
  rw [complexHessian_congr' hev, HolomorphicHessianTwo.complexHessian_comp_holomorphic_two
    τ.open_source f.val.open_target hτhol (hu f) hmaps hz, hτz]

/-- The coefficient matrix of a `(1,1)`-form transforms by `Jᵀ (·) J̄`. -/
theorem coeffMatrix_transition (g : SmoothRealForm n M 2)
    (hg : ∀ f : ComplexChart n M, ∀ z ∈ f.val.target, IsOneOne (g.coeff f z))
    {e f : ComplexChart n M} {y : M} (hye : y ∈ e.val.source) (hyf : y ∈ f.val.source) :
    normalizedHermitianMatrix (g.coeff e (e.val y)) =
      (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y))ᵀ *
        normalizedHermitianMatrix (g.coeff f (f.val y)) *
          (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y)).map
            (starRingEnd ℂ) := by
  have hz := RelativeEigenvalueMax.mem_chartTransition_source hye hyf
  have hτz := RelativeEigenvalueMax.chartTransition_apply_chart (f := f) hye
  have hf11 : IsOneOne (g.coeff f (chartTransition e f (e.val y))) := by
    rw [hτz]; exact hg f _ (f.val.map_source hyf)
  rw [coeff_eq_compLinearMap g e f hz, normalizedHermitianMatrix_compLinearMap hf11,
    standardMatrix_transitionLinear, hτz]

theorem re_det_congr (J X : Matrix (Fin n) (Fin n) ℂ) :
    (Jᵀ * X * J.map (starRingEnd ℂ)).det.re = Complex.normSq J.det * X.det.re := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  have : J.det * X.det * (starRingEnd ℂ) J.det = ((Complex.normSq J.det : ℝ) : ℂ) * X.det := by
    rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [this, Complex.re_ofReal_mul]

/-! ### The Monge–Ampère operator -/

/-- The Monge–Ampère operator of the background `a` in the chart `e`:
`log det(H_e + complexHessian v) - log det H_e` (real parts). -/
def maChart (a : SmoothRealForm n M 2) (e : ComplexChart n M) (v : ComplexModel n → ℝ)
    (z : ComplexModel n) : ℝ :=
  Real.log (normalizedHermitianMatrix (a.coeff e z) + complexHessian v z).det.re -
    Real.log (normalizedHermitianMatrix (a.coeff e z)).det.re

/-- The Monge–Ampère operator `log ((a + ddᶜψ)^N / a^N)` on `M`, read in the preferred chart. -/
def ma (a : SmoothRealForm n M 2) (ψ : M → ℝ) (y : M) : ℝ :=
  maChart a (complexChartAt (n := n) y) (fun w => ψ ((complexChartAt (n := n) y).val.symm w))
    ((complexChartAt (n := n) y).val y)

/-- **Chart independence** of the Monge–Ampère operator, at a point where the determinants are
nonzero in the chart `f`. -/
theorem maChart_eq_of_mem {a : SmoothRealForm n M 2} (ha : a.IsHermitian) {ψ : M → ℝ}
    (hψ : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun w => ψ (e.val.symm w)) e.val.target)
    {e f : ComplexChart n M} {y : M} (hye : y ∈ e.val.source) (hyf : y ∈ f.val.source)
    (hdet : (normalizedHermitianMatrix (a.coeff f (f.val y)) +
      complexHessian (fun w => ψ (f.val.symm w)) (f.val y)).det.re ≠ 0) :
    maChart a e (fun w => ψ (e.val.symm w)) (e.val y) =
      maChart a f (fun w => ψ (f.val.symm w)) (f.val y) := by
  have ha11 : ∀ f : ComplexChart n M, ∀ z ∈ f.val.target, IsOneOne (a.coeff f z) :=
    fun f z hz => (ha f z hz).1
  have hJ := isUnit_det_jacobianMatrix e f hye hyf
  have hJ0 : 0 < Complex.normSq (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f)
      (e.val y)).det := Complex.normSq_pos.mpr hJ.ne_zero
  have hH0 : (normalizedHermitianMatrix (a.coeff f (f.val y))).det.re ≠ 0 :=
    (posDef_coeff ha (f.val.map_source hyf)).det_pos.ne' |> fun h => by
      have h' := (posDef_coeff ha (f.val.map_source hyf)).det_pos
      exact (Complex.pos_iff.mp h').1.ne'
  simp only [maChart]
  rw [complexHessian_transition hψ hye hyf, coeffMatrix_transition a ha11 hye hyf,
    ← Matrix.add_mul, ← Matrix.mul_add, re_det_congr, re_det_congr,
    Real.log_mul hJ0.ne' hdet, Real.log_mul hJ0.ne' hH0]
  ring

/-- The Monge–Ampère operator on `M` is computed in any chart (where the determinant of the
coefficient matrix of `a + ddᶜψ` is nonzero). -/
theorem ma_eq {a : SmoothRealForm n M 2} (ha : a.IsHermitian) {ψ : M → ℝ}
    (hψ : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun w => ψ (e.val.symm w)) e.val.target)
    {e : ComplexChart n M} {y : M} (hye : y ∈ e.val.source)
    (hdet : (normalizedHermitianMatrix (a.coeff e (e.val y)) +
      complexHessian (fun w => ψ (e.val.symm w)) (e.val y)).det.re ≠ 0) :
    ma a ψ y = maChart a e (fun w => ψ (e.val.symm w)) (e.val y) :=
  maChart_eq_of_mem ha hψ (mem_complexChartAt_source y) hye hdet

/-! ### Jacobi's formula along a real line -/

/-- **Jacobi's formula**: `d/ds det(P + s K) = tr(adj P · K)` at `s = 0`. -/
theorem hasDerivAt_det_add_smul (P K : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => (P + (s : ℂ) • K).det) (P.adjugate * K).trace 0 := by
  classical
  have hentry : ∀ i j : Fin n, HasDerivAt (fun s : ℝ => (P + (s : ℂ) • K) i j) (K i j) 0 := by
    intro i j
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have := (h1.mul_const (K i j)).const_add (P i j)
    simpa using this
  simp_rw [WirtingerLogDet.det_eq_sum]
  have hσ : ∀ σ : Equiv.Perm (Fin n), HasDerivAt
      (fun s : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (P + (s : ℂ) • K) (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ l, (∏ j ∈ Finset.univ.erase l, (P + ((0 : ℝ) : ℂ) • K) (σ j) j) • K (σ l) l) 0 := by
    intro σ
    exact (HasDerivAt.fun_finsetProd fun i _ => hentry (σ i) i).const_mul _
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun σ _ => hσ σ
  refine h.congr_deriv ?_
  symm
  -- the derivative
  have hR : (P.adjugate * K).trace = ∑ l, (P.updateCol l (fun k => K k l)).det := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, ← Matrix.cramer_apply,
      Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec, dotProduct]
  rw [hR]
  simp_rw [WirtingerLogDet.det_updateCol_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Complex.ofReal_zero, zero_smul, add_zero, smul_eq_mul]
  ring

/-! ### The local Monge–Ampère function -/

/-- The Hermitian part of an array of complex numbers, as a matrix. -/
def hermPart (K : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => (K j k + star (K k j)) / 2

/-- A matrix as an element of the normed space `Fin n → Fin n → ℂ`. -/
def kmat (M : Matrix (Fin n) (Fin n) ℂ) : Fin n → Fin n → ℂ := fun j k => M j k

theorem hermPart_kmat {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    hermPart (kmat M) = M := by
  ext j k
  have := congrFun (congrFun hM.eq j) k
  simp only [Matrix.conjTranspose_apply] at this
  simp only [hermPart, kmat, Matrix.of_apply, this]
  ring

theorem hermPart_add (K L : Fin n → Fin n → ℂ) : hermPart (K + L) = hermPart K + hermPart L := by
  ext j k
  simp only [hermPart, Matrix.of_apply, Pi.add_apply, star_add, Matrix.add_apply]
  ring

theorem hermPart_smul (c : ℝ) (K : Fin n → Fin n → ℂ) :
    hermPart (c • K) = (c : ℂ) • hermPart K := by
  ext j k
  simp only [hermPart, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Complex.real_smul, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

theorem isHermitian_hermPart (K : Fin n → Fin n → ℂ) : (hermPart K).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, hermPart, Matrix.of_apply, star_div₀, star_add,
    star_star]
  rw [show star (2 : ℂ) = 2 by simp]
  ring

/-- The local Monge–Ampère function `F_H(z, K) = log det(H(z) + herm K) - log det H(z)`. -/
def maLocal (H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ)
    (p : ComplexModel n × (Fin n → Fin n → ℂ)) : ℝ :=
  Real.log (H p.1 + hermPart p.2).det.re - Real.log (H p.1).det.re

section LocalSmooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The determinant of a matrix with smooth entries is smooth (Leibniz expansion). -/
theorem contDiffOn_det {F : X → Matrix (Fin n) (Fin n) ℂ} {s : Set X} {m : WithTop ℕ∞}
    (hF : ∀ i j, ContDiffOn ℝ m (fun x => F x i j) s) : ContDiffOn ℝ m (fun x => (F x).det) s := by
  simp_rw [WirtingerLogDet.det_eq_sum]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hF _ _)

variable {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}

/-- The domain where the local Monge–Ampère function is smooth. -/
def maDomain (H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (U : Set (ComplexModel n)) :
    Set (ComplexModel n × (Fin n → Fin n → ℂ)) :=
  {p | p.1 ∈ U ∧ 0 < (H p.1 + hermPart p.2).det.re ∧ 0 < (H p.1).det.re}

theorem contDiffOn_entries {m : WithTop ℕ∞} (hH : ∀ i j, ContDiffOn ℝ m (fun z => H z i j) U)
    (i j : Fin n) :
    ContDiffOn ℝ m (fun p : ComplexModel n × (Fin n → Fin n → ℂ) => (H p.1 + hermPart p.2) i j)
      (Prod.fst ⁻¹' U) := by
  simp only [Matrix.add_apply, hermPart, Matrix.of_apply]
  refine ((hH i j).comp contDiffOn_fst (fun p hp => hp)).add ?_
  have h1 : ContDiff ℝ m (fun p : ComplexModel n × (Fin n → Fin n → ℂ) => p.2 i j) :=
    (contDiff_apply_apply (𝕜 := ℝ) (n := m) (E := ℂ) i j).comp contDiff_snd
  have h2 : ContDiff ℝ m (fun p : ComplexModel n × (Fin n → Fin n → ℂ) => star (p.2 j i)) :=
    Complex.conjCLE.contDiff.comp ((contDiff_apply_apply (𝕜 := ℝ) (n := m) (E := ℂ) j i).comp contDiff_snd)
  exact ((h1.add h2).div_const 2).contDiffOn

theorem isOpen_maDomain (hU : IsOpen U) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U) :
    IsOpen (maDomain H U) := by
  have hc1 : ContinuousOn (fun p : ComplexModel n × (Fin n → Fin n → ℂ) =>
      (H p.1 + hermPart p.2).det.re) (Prod.fst ⁻¹' U) :=
    Complex.continuous_re.comp_continuousOn (contDiffOn_det (contDiffOn_entries hH)).continuousOn
  have hc2 : ContinuousOn (fun p : ComplexModel n × (Fin n → Fin n → ℂ) => (H p.1).det.re)
      (Prod.fst ⁻¹' U) :=
    Complex.continuous_re.comp_continuousOn ((contDiffOn_det (m := ∞) fun i j =>
      (hH i j).comp contDiffOn_fst (fun p hp => hp)).continuousOn)
  have hU' : IsOpen (Prod.fst ⁻¹' U : Set (ComplexModel n × (Fin n → Fin n → ℂ))) :=
    hU.preimage continuous_fst
  have h1 := hc1.isOpen_inter_preimage hU' (isOpen_Ioi (a := (0 : ℝ)))
  have h2 := (hc2.mono inter_subset_left).isOpen_inter_preimage h1 (isOpen_Ioi (a := (0 : ℝ)))
  convert h2 using 1
  ext p
  simp only [maDomain, mem_inter_iff, mem_preimage, mem_Ioi]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem contDiffOn_maLocal (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U) :
    ContDiffOn ℝ ∞ (maLocal H) (maDomain H U) := by
  have hsub : maDomain H U ⊆ Prod.fst ⁻¹' U := fun p hp => hp.1
  have hd1 : ContDiffOn ℝ ∞ (fun p : ComplexModel n × (Fin n → Fin n → ℂ) =>
      (H p.1 + hermPart p.2).det.re) (maDomain H U) :=
    (Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_det (contDiffOn_entries hH))).mono hsub
  have hd2 : ContDiffOn ℝ ∞ (fun p : ComplexModel n × (Fin n → Fin n → ℂ) => (H p.1).det.re)
      (maDomain H U) :=
    (Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_det (m := ∞) fun i j =>
      (hH i j).comp contDiffOn_fst (fun p hp => hp))).mono hsub
  exact (hd1.log fun p hp => hp.2.1.ne').sub (hd2.log fun p hp => hp.2.2.ne')

/-- **The derivative of the local Monge–Ampère function** in the `K`-direction:
`D F_H(z, K)(0, L) = Re tr((H(z) + herm K)⁻¹ · herm L)`. -/
theorem fderiv_maLocal_apply (hU : IsOpen U) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    {p : ComplexModel n × (Fin n → Fin n → ℂ)} (hp : p ∈ maDomain H U)
    (hP : (H p.1 + hermPart p.2).IsHermitian) (L : Fin n → Fin n → ℂ) :
    fderiv ℝ (maLocal H) p (0, L) = (((H p.1 + hermPart p.2)⁻¹ * hermPart L).trace).re := by
  set P := H p.1 + hermPart p.2 with hPdef
  have hD : HasFDerivAt (maLocal H) (fderiv ℝ (maLocal H) p) p :=
    (((contDiffOn_maLocal hH).contDiffAt ((isOpen_maDomain hU hH).mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => p + s • ((0 : ComplexModel n), L)) ((0 : ComplexModel n), L) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ComplexModel n), L)).const_add p
  have h1 := hD.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hc (by simp)
  -- the same derivative computed by Jacobi's formula
  have hfun : (maLocal H ∘ fun s : ℝ => p + s • ((0 : ComplexModel n), L)) =
      fun s : ℝ => Real.log (P + (s : ℂ) • hermPart L).det.re - Real.log (H p.1).det.re := by
    funext s
    simp only [comp_apply, maLocal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_zero, add_zero, hermPart_add, hermPart_smul, hPdef, add_assoc]
  rw [hfun] at h1
  have hre : P.det.re ≠ 0 := hp.2.1.ne'
  have hdet0 : (P + ((0 : ℝ) : ℂ) • hermPart L).det.re ≠ 0 := by simpa using hre
  have hJ := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_det_add_smul P (hermPart L))).log hdet0).sub_const (Real.log (H p.1).det.re)
  have huniq := h1.unique hJ
  rw [huniq]
  simp only [comp_apply, Complex.reCLM_apply, Complex.ofReal_zero, zero_smul, add_zero]
  have hP0 : P.det ≠ 0 := fun h => hre (by rw [h]; simp)
  have htr : (P.adjugate * hermPart L).trace = (P.det.re : ℂ) * (P⁻¹ * hermPart L).trace := by
    rw [WirtingerLogDet.adjugate_eq_det_smul_inv' hP0, smul_mul_assoc, Matrix.trace_smul,
      smul_eq_mul, WirtingerLogDet.ofReal_re_det_of_isHermitian hP]
  rw [htr, Complex.re_ofReal_mul]
  field_simp

end LocalSmooth

/-! ### The array of second derivatives -/

theorem norm_kmat_le {M : Matrix (Fin n) (Fin n) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j k, ‖M j k‖ ≤ C) : ‖kmat M‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).mpr fun j => (pi_norm_le_iff_of_nonneg hC).mpr fun k => h j k

theorem norm_coordinateVector (j : Fin n) : ‖coordinateVector (n := n) j‖ = 1 := by
  simp [coordinateVector]

theorem norm_I_smul_coordinateVector (j : Fin n) :
    ‖Complex.I • coordinateVector (n := n) j‖ = 1 := by
  rw [norm_smul, Complex.norm_I, one_mul, norm_coordinateVector]

theorem norm_kmat_complexHessianOfBilin_le (Q : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    ‖kmat (SemiconcaveHessian.complexHessianOfBilin Q)‖ ≤ ‖Q‖ := by
  refine norm_kmat_le (norm_nonneg Q) fun j k => ?_
  have hb : ∀ x y : ComplexModel n, ‖x‖ = 1 → ‖y‖ = 1 → |Q x y| ≤ ‖Q‖ := by
    intro x y hx hy
    have := Q.le_opNorm₂ x y
    rw [hx, hy, mul_one, mul_one, Real.norm_eq_abs] at this
    exact this
  have h1 := hb _ _ (norm_coordinateVector j) (norm_coordinateVector k)
  have h2 := hb _ _ (norm_I_smul_coordinateVector j) (norm_I_smul_coordinateVector k)
  have h3 := hb _ _ (norm_coordinateVector j) (norm_I_smul_coordinateVector k)
  have h4 := hb _ _ (norm_I_smul_coordinateVector j) (norm_coordinateVector k)
  simp only [SemiconcaveHessian.complexHessianOfBilin]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, show ‖(4 : ℂ)‖ = 4 by simp]
  have e1 := abs_add_le (Q (coordinateVector j) (coordinateVector k))
    (Q (Complex.I • coordinateVector j) (Complex.I • coordinateVector k))
  have e2 := abs_sub (Q (coordinateVector j) (Complex.I • coordinateVector k))
    (Q (Complex.I • coordinateVector j) (coordinateVector k))
  linarith

theorem complexHessianOfBilin_sub (Q Q' : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    SemiconcaveHessian.complexHessianOfBilin (Q - Q') =
      SemiconcaveHessian.complexHessianOfBilin Q - SemiconcaveHessian.complexHessianOfBilin Q' := by
  ext j k
  simp only [SemiconcaveHessian.complexHessianOfBilin, sub_apply, Matrix.sub_apply]
  push_cast
  ring

theorem kmat_sub (M M' : Matrix (Fin n) (Fin n) ℂ) : kmat (M - M') = kmat M - kmat M' := rfl

/-- `K w z = (∂²w/∂z_j∂z̄_k)(z)` as an element of `Fin n → Fin n → ℂ`. -/
def kfun (w : ComplexModel n → ℝ) (z : ComplexModel n) : Fin n → Fin n → ℂ :=
  kmat (complexHessian w z)

theorem kfun_sub_kfun (w w' : ComplexModel n → ℝ) (z z' : ComplexModel n) :
    ‖kfun w z - kfun w' z'‖ ≤ ‖fderiv ℝ (fderiv ℝ w) z - fderiv ℝ (fderiv ℝ w') z'‖ := by
  simp only [kfun, ComplexHessianDeterminant.complexHessian_eq_complexHessianOfBilin, ← kmat_sub,
    ← complexHessianOfBilin_sub]
  exact norm_kmat_complexHessianOfBilin_le _

theorem norm_kfun_le (w : ComplexModel n → ℝ) (z : ComplexModel n) :
    ‖kfun w z‖ ≤ ‖fderiv ℝ (fderiv ℝ w) z‖ := by
  simp only [kfun, ComplexHessianDeterminant.complexHessian_eq_complexHessianOfBilin]
  exact norm_kmat_complexHessianOfBilin_le _

theorem kfun_sub (w w' : ComplexModel n → ℝ) (z : ComplexModel n) (hw : ContDiffAt ℝ 2 w z)
    (hw' : ContDiffAt ℝ 2 w' z) : kfun (fun x => w x - w' x) z = kfun w z - kfun w' z := by
  have hd : fderiv ℝ (fun x => w x - w' x) =ᶠ[𝓝 z] fun x => fderiv ℝ w x - fderiv ℝ w' x := by
    filter_upwards [hw.eventually (by simp), hw'.eventually (by simp)] with x hx hx'
    exact fderiv_sub (hx.differentiableAt (by simp)) (hx'.differentiableAt (by simp))
  have h2 : fderiv ℝ (fderiv ℝ (fun x => w x - w' x)) z =
      fderiv ℝ (fderiv ℝ w) z - fderiv ℝ (fderiv ℝ w') z := by
    rw [hd.fderiv_eq]
    exact fderiv_sub ((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
      ((hw'.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  simp only [kfun, ComplexHessianDeterminant.complexHessian_eq_complexHessianOfBilin, h2,
    complexHessianOfBilin_sub, kmat_sub]

/-! ### A compactly supported model of the local Monge–Ampère function -/

/-- **The cut-off model.**  Near the compact graph `{(z, K₀ z) : z ∈ K}` inside the smoothness
domain, `maLocal H` agrees with a smooth compactly supported `Γ`; uniformly, on the `η`-neighbourhoods
`{(z, L) : z ∈ K, ‖L - K₀ z‖ ≤ η}`. -/
theorem exists_cutoffModel {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    {K : Set (ComplexModel n)} (hK : IsCompact K) {K₀ : ComplexModel n → Fin n → Fin n → ℂ}
    (hK₀ : Continuous K₀) (hdom : ∀ z ∈ K, (z, K₀ z) ∈ maDomain H U) :
    ∃ (Γ : ComplexModel n × (Fin n → Fin n → ℂ) → ℝ) (η : ℝ), 0 < η ∧ ContDiff ℝ ∞ Γ ∧
      HasCompactSupport Γ ∧ ∀ z ∈ K, ∀ L, ‖L - K₀ z‖ ≤ η →
        (z, L) ∈ maDomain H U ∧ Γ =ᶠ[𝓝 (z, L)] maLocal H := by
  set C₀ := (fun z => (z, K₀ z)) '' K with hC₀def
  have hC₀c : IsCompact C₀ := hK.image (continuous_id.prodMk hK₀)
  have hO := isOpen_maDomain hU hH
  have hC₀O : C₀ ⊆ maDomain H U := by
    rintro _ ⟨z, hz, rfl⟩; exact hdom z hz
  obtain ⟨K₁, hK₁c, hC₀K₁, hK₁O⟩ := exists_compact_between hC₀c hO hC₀O
  obtain ⟨ξ, hξs, hξc, hξt, hξ1, -⟩ := exists_cutoff hK₁c hO hK₁O
  obtain ⟨η, hη, hηsub⟩ := hC₀c.exists_cthickening_subset_open isOpen_interior hC₀K₁
  refine ⟨fun p => ξ p • maLocal H p, η, hη,
    contDiff_smul_of_tsupport hO hξs hξt (contDiffOn_maLocal hH), ?_, fun z hz L hL => ?_⟩
  · refine hξc.mono' fun p hp => subset_tsupport _ fun h0 => hp ?_
    simp [h0]
  · have hmem : (z, L) ∈ interior K₁ := by
      refine hηsub (Metric.mem_cthickening_of_dist_le _ (z, K₀ z) _ _ ⟨z, hz, rfl⟩ ?_)
      rw [Prod.dist_eq, dist_self, dist_eq_norm]
      exact max_le hη.le hL
    refine ⟨hK₁O (interior_subset hmem), ?_⟩
    filter_upwards [isOpen_interior.mem_nhds hmem] with p hp
    simp [hξ1 p (interior_subset hp)]

/-! ### Helpers -/

theorem isHermitian_complexHessian_of_contDiffAt {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) : (complexHessian u z).IsHermitian := by
  rw [ComplexHessianDeterminant.complexHessian_eq_complexHessianOfBilin]
  exact ComplexHessianDeterminant.isHermitian_complexHessianOfBilin fun x y =>
    hu.isSymmSndFDerivAt (by simp) x y

theorem le_rpow_self_of_le_one {x r : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hr1 : r ≤ 1) :
    x ≤ x ^ r := by
  rcases hx0.eq_or_lt with h0 | h0
  · rw [← h0]; exact Real.rpow_nonneg le_rfl _
  · calc x = x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ x ^ r := Real.rpow_le_rpow_of_exponent_ge h0 hx1 hr1

/-- Local Hölder bounds plus a sup bound give a global Hölder bound. -/
theorem abs_sub_le_of_local {f : ComplexModel n → ℝ} {B L r : ℝ} (hr : 0 ≤ r) (hL0 : 0 ≤ L)
    (hB : ∀ z, |f z| ≤ B) (hL : ∀ z z', ‖z - z'‖ ≤ 1 → |f z - f z'| ≤ L * ‖z - z'‖ ^ r)
    (z z' : ComplexModel n) : |f z - f z'| ≤ (L + 2 * B) * ‖z - z'‖ ^ r := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB z)
  rcases le_or_gt ‖z - z'‖ 1 with h | h
  · exact (hL z z' h).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg
      (norm_nonneg _) _))
  · have hρ : 1 ≤ ‖z - z'‖ ^ r := Real.one_le_rpow h.le hr
    calc |f z - f z'| ≤ |f z| + |f z'| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB z, hB z']
      _ ≤ 2 * B * ‖z - z'‖ ^ r := le_mul_of_one_le_right (by positivity) hρ
      _ ≤ (L + 2 * B) * ‖z - z'‖ ^ r := by
          gcongr
          linarith

section BCDH

variable {r : ℝ≥0}

theorem fderiv_fderiv_sub (f f' : BoundedContDiffHolderMap 2 r (ComplexModel n) ℝ)
    (z : ComplexModel n) :
    fderiv ℝ (fderiv ℝ ⇑(f - f')) z = fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f') z := by
  have hf := WholeSpaceSolvability.contDiff_two f
  have hf' := WholeSpaceSolvability.contDiff_two f'
  have h1 : fderiv ℝ ⇑(f - f') = fun x => fderiv ℝ f x - fderiv ℝ f' x := by
    funext x
    rw [BoundedContDiffHolderMap.coe_sub]
    exact fderiv_sub ((hf.differentiable (by simp)) x) ((hf'.differentiable (by simp)) x)
  rw [h1]
  exact fderiv_sub (((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z)
    (((hf'.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z)

theorem kfun_sub' (f f' : BoundedContDiffHolderMap 2 r (ComplexModel n) ℝ) (z : ComplexModel n) :
    kfun ⇑(f - f') z = kfun f z - kfun f' z := by
  simp only [kfun, ComplexHessianDeterminant.complexHessian_eq_complexHessianOfBilin,
    fderiv_fderiv_sub, complexHessianOfBilin_sub, kmat_sub]

theorem norm_kfun_sub_le' (f f' : BoundedContDiffHolderMap 2 r (ComplexModel n) ℝ)
    (z : ComplexModel n) : ‖kfun f z - kfun f' z‖ ≤ ‖f - f'‖ := by
  rw [← kfun_sub']
  exact (norm_kfun_le _ z).trans (WholeSpaceSolvability.norm_fderiv_fderiv_le _ z)

theorem norm_kfun_holder (f : BoundedContDiffHolderMap 2 r (ComplexModel n) ℝ)
    (z z' : ComplexModel n) : ‖kfun f z - kfun f z'‖ ≤ ‖f‖ * ‖z - z'‖ ^ (r : ℝ) :=
  (kfun_sub_kfun _ _ z z').trans (WholeSpaceSolvability.norm_fderiv_fderiv_sub_le f z z')

theorem lipschitzWith_kmat_complexHessianOfBilin :
    LipschitzWith 1 (fun Q : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ =>
      kmat (SemiconcaveHessian.complexHessianOfBilin Q)) := by
  refine LipschitzWith.of_dist_le_mul fun Q Q' => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← kmat_sub, ← complexHessianOfBilin_sub]
  exact norm_kmat_complexHessianOfBilin_le _

theorem continuous_kfun (f : BoundedContDiffHolderMap 2 r (ComplexModel n) ℝ) :
    Continuous (kfun f) := by
  have hD : Continuous (fun z => fderiv ℝ (fderiv ℝ f) z) :=
    ((WholeSpaceSolvability.contDiff_two f).fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      one_ne_zero
  have : kfun ⇑f = (fun Q => kmat (SemiconcaveHessian.complexHessianOfBilin Q)) ∘
      (fun z => fderiv ℝ (fderiv ℝ f) z) := by
    funext z
    simp only [kfun, comp_apply, ComplexHessianDeterminant.complexHessian_eq_complexHessianOfBilin]
  rw [this]
  exact lipschitzWith_kmat_complexHessianOfBilin.continuous.comp hD

/-- A `C¹` map with compact support on a normed space is bounded and Lipschitz. -/
theorem exists_lipschitz_of_hasCompactSupport' {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x, ‖f x‖ ≤ K) ∧ ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K₀, hK₀⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨K₁, hK₁⟩ :=
    (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  have hK₀0 : 0 ≤ K₀ := (norm_nonneg _).trans (hK₀ 0)
  refine ⟨max K₀ K₁, hK₀0.trans (le_max_left _ _), fun x => (hK₀ x).trans (le_max_left _ _),
    fun x y => ?_⟩
  exact (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.differentiable one_ne_zero) z) (fun z _ => (hK₁ z).trans (le_max_right K₀ K₁))
    (mem_univ y) (mem_univ x)

end BCDH

/-! ### Estimates in one chart of a Hölder atlas -/

/-- **Per-chart estimates of the Monge–Ampère operator** near `Φ₀ ∈ C^{2,r}(M)` (with
`g = a + ddᶜΦ₀` Hermitian): on a `C^{2,r}`-ball around `Φ₀` the local representative of `ma a ψ` is
in `C^{0,r}_b`, and that of the remainder `ma ψ₁ - ma ψ₂ - Δ_g(ψ₁ - ψ₂)` has `C^{0,r}_b` norm
`≤ C (‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) ‖ψ₁ - ψ₂‖`. -/
theorem exists_chart_estimates {a g : SmoothRealForm n M 2} (ha : a.IsHermitian)
    (hg : g.IsHermitian) {A : HolderAtlas n M} {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1)
    (Φ₀ : A.HolderMap 2 r ℝ)
    (hgφ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      normalizedHermitianMatrix (g.coeff e z) =
        normalizedHermitianMatrix (a.coeff e z) + complexHessian (fun x => Φ₀ (e.val.symm x)) z)
    (i : Fin A.m) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (∀ ψ : A.HolderMap 2 r ℝ, ‖ψ - Φ₀‖ < ρ →
        ∃ h : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ, ⇑h = A.localRep i (ma a ⇑ψ)) ∧
      (∀ ψ₁ ψ₂ : A.HolderMap 2 r ℝ, ‖ψ₁ - Φ₀‖ < ρ → ‖ψ₂ - Φ₀‖ < ρ →
        ∃ h : BoundedContDiffHolderMap 0 r (ComplexModel n) ℝ,
          ⇑h = A.localRep i (fun y => ma a ⇑ψ₁ y - ma a ⇑ψ₂ y - laplacian g ⇑(ψ₁ - ψ₂) y) ∧
          ‖h‖ ≤ C * (‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) * ‖ψ₁ - ψ₂‖) := by
  classical
  have hr1' : r ≤ 1 := hr1.le
  have hr0' : (0 : ℝ) ≤ r := r.2
  set e := A.chart i with he
  have hKc : IsCompact (e.val '' tsupport (A.χ i)) := A.isCompact_image_tsupport i
  have hKt : e.val '' tsupport (A.χ i) ⊆ e.val.target := image_tsupport_subset_target A i
  set K := e.val '' tsupport (A.χ i) with hK
  obtain ⟨K', hK'c, hKK', hK't⟩ := exists_compact_between hKc e.val.open_target hKt
  obtain ⟨σ, hσs, hσc, hσt, hσ1, -⟩ := exists_cutoff hK'c e.val.open_target hK't
  obtain ⟨Cσ, hCσ⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (k := 2) (F := ℝ) hr1' e
    (contDiff_infty.1 hσs (2 + 1)) hσc hσt
  choose w hw hwn using hCσ
  set Cs := max Cσ 0 with hCs
  have hCs0 : 0 ≤ Cs := le_max_right _ _
  have hwn' : ∀ ψ, ‖w ψ‖ ≤ Cs * ‖ψ‖ := fun ψ =>
    (hwn ψ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hwsub : ∀ ψ₁ ψ₂, w (ψ₁ - ψ₂) = w ψ₁ - w ψ₂ := by
    intro ψ₁ ψ₂
    ext x
    simp only [hw, BoundedContDiffHolderMap.coe_sub, Pi.sub_apply, HolderAtlas.HolderMap.coe_sub,
      smul_eq_mul]
    ring
  have hwloc : ∀ ψ : A.HolderMap 2 r ℝ, ∀ z ∈ interior K',
      (⇑(w ψ)) =ᶠ[𝓝 z] fun x => ψ (e.val.symm x) := by
    intro ψ z hz
    filter_upwards [isOpen_interior.mem_nhds hz] with x hx
    rw [hw ψ x, hσ1 x (interior_subset hx), smul_eq_mul, one_mul]
  have hC2 : ∀ ψ : A.HolderMap 2 r ℝ, ∀ f : ComplexChart n M,
      ContDiffOn ℝ 2 (fun x => ψ (f.val.symm x)) f.val.target :=
    fun ψ f z hz => (ManifoldContinuity.contDiffAt_comp_symm hr1' ψ f hz).contDiffWithinAt
  have hkfun : ∀ ψ : A.HolderMap 2 r ℝ, ∀ z ∈ K,
      kfun (w ψ) z = kmat (complexHessian (fun x => ψ (e.val.symm x)) z) := by
    intro ψ z hz
    simp only [kfun, complexHessian_congr' (hwloc ψ z (hKK' hz))]
  have hherm : ∀ ψ : A.HolderMap 2 r ℝ, ∀ z ∈ K,
      hermPart (kfun (w ψ) z) = complexHessian (fun x => ψ (e.val.symm x)) z := by
    intro ψ z hz
    rw [hkfun ψ z hz, hermPart_kmat (isHermitian_complexHessian_of_contDiffAt
      (ManifoldContinuity.contDiffAt_comp_symm hr1' ψ e (hKt hz)))]
  -- the coefficient matrix of `a`
  set H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ :=
    fun z => normalizedHermitianMatrix (a.coeff e z) with hHdef
  have hH : ∀ j k, ContDiffOn ℝ ∞ (fun z => H z j k) e.val.target := by
    intro j k
    have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (KahlerLaplacianChart.contDiffOn_apply (a.smooth e) ![coordinateVector j, Complex.I • coordinateVector k])
    have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (KahlerLaplacianChart.contDiffOn_apply (a.smooth e) ![coordinateVector j, coordinateVector k])
    exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul h2))
  -- the base point and the domain
  set W₀ := w Φ₀ with hW₀
  have hdom : ∀ z ∈ K, (z, kfun W₀ z) ∈ maDomain H e.val.target := by
    intro z hz
    refine ⟨hKt hz, ?_, ?_⟩
    · show 0 < (H z + hermPart (kfun W₀ z)).det.re
      rw [hherm Φ₀ z hz, hHdef]
      dsimp only
      rw [← hgφ e z (hKt hz)]
      exact (Complex.pos_iff.mp (posDef_coeff hg (hKt hz)).det_pos).1
    · exact (Complex.pos_iff.mp (posDef_coeff ha (hKt hz)).det_pos).1
  obtain ⟨Γ, η, hη, hΓs, hΓc, hΓeq⟩ :=
    exists_cutoffModel e.val.open_target hH hKc (continuous_kfun W₀) hdom
  -- bounds for `Γ` and its derivatives
  have hΓ3 : ContDiff ℝ (3 : ℕ) Γ := contDiff_infty.1 hΓs 3
  obtain ⟨B₀, hB₀0, hB₀, hB₀l⟩ :=
    exists_lipschitz_of_hasCompactSupport' (hΓ3.of_le (by norm_num)) hΓc
  have hΓ2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ Γ)) :=
    (hΓ3.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  obtain ⟨B₂, hB₂0, hB₂, hB₂l⟩ := exists_lipschitz_of_hasCompactSupport' hΓ2
    ((hΓc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  have hΓd : ∀ p, HasFDerivAt Γ (fderiv ℝ Γ p) p :=
    fun p => ((hΓ3.differentiable (by norm_num)) p).hasFDerivAt
  have hgd : ∀ p, HasFDerivAt (fderiv ℝ Γ) (fderiv ℝ (fderiv ℝ Γ) p) p := fun p =>
    (((hΓ3.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) p).hasFDerivAt
  -- the cut-off `χ̃` of the chart
  obtain ⟨hχs, hχc, -⟩ := HolderAtlas.HolderMap.contDiff_indicator_comp_symm e (A.chartSmooth i)
    (A.isCompact_tsupport i) (A.tsupport_subset i)
  set χt := e.val.target.indicator ((A.χ i) ∘ e.val.symm) with hχt
  obtain ⟨Kχ, hKχ0, hKχ, hKχl⟩ :=
    ManifoldSchauder.exists_lipschitz_of_hasCompactSupport (hχs.of_le (by simp)) hχc
  have hχ0 : ∀ z, |χt z| ≤ Kχ := fun z => by rw [← Real.norm_eq_abs]; exact hKχ z
  have hχ1 : ∀ z z', |χt z - χt z'| ≤ Kχ * ‖z - z'‖ := fun z z' => by
    rw [← Real.norm_eq_abs]; exact hKχl z z'
  have hχK : ∀ z, χt z ≠ 0 → z ∈ K := by
    intro z hz
    by_cases hzt : z ∈ e.val.target
    · rw [hχt, indicator_of_mem hzt, comp_apply] at hz
      exact ⟨e.val.symm z, subset_tsupport _ hz, e.val.right_inv hzt⟩
    · exact absurd (indicator_of_notMem hzt _) hz
  have hloc : ∀ (F : M → ℝ) z, A.localRep i F z = χt z * F (e.val.symm z) := by
    intro F z
    by_cases hzt : z ∈ e.val.target
    · rw [HolderAtlas.localRep_of_mem F hzt, hχt, indicator_of_mem hzt, comp_apply, smul_eq_mul]
    · rw [HolderAtlas.localRep_of_notMem F hzt, hχt, indicator_of_notMem hzt, zero_mul]
  -- the radius
  set ρ := η / (2 * Cs + 1) with hρ
  have hρ0 : 0 < ρ := div_pos hη (by linarith)
  have hCsρ : Cs * ρ ≤ η := by
    rw [hρ, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hwdiff : ∀ ψ : A.HolderMap 2 r ℝ, ‖w ψ - W₀‖ ≤ Cs * ‖ψ - Φ₀‖ := fun ψ => by
    rw [← hwsub]; exact hwn' _
  have hnear : ∀ ψ : A.HolderMap 2 r ℝ, ‖ψ - Φ₀‖ < ρ → ∀ z, ‖kfun (w ψ) z - kfun W₀ z‖ ≤ η :=
    fun ψ hψ z => ((norm_kfun_sub_le' _ _ z).trans (hwdiff ψ)).trans
      ((mul_le_mul_of_nonneg_left hψ.le hCs0).trans hCsρ)
  -- the Monge–Ampère operator on `K` through `Γ`
  have hma : ∀ ψ : A.HolderMap 2 r ℝ, ‖ψ - Φ₀‖ < ρ → ∀ z ∈ K,
      ma a ψ (e.val.symm z) = Γ (z, kfun (w ψ) z) := by
    intro ψ hψ z hz
    obtain ⟨hdomψ, hΓψ⟩ := hΓeq z hz (kfun (w ψ) z) (hnear ψ hψ z)
    have hzt := hKt hz
    have hys : e.val.symm z ∈ e.val.source := e.val.map_target hzt
    have hdet : (normalizedHermitianMatrix (a.coeff e (e.val (e.val.symm z))) +
        complexHessian (fun x => ψ (e.val.symm x)) (e.val (e.val.symm z))).det.re ≠ 0 := by
      rw [e.val.right_inv hzt, ← hherm ψ z hz]
      exact hdomψ.2.1.ne'
    rw [ma_eq ha (hC2 ψ) hys hdet, e.val.right_inv hzt, hΓψ.eq_of_nhds]
    simp only [maLocal, maChart, hherm ψ z hz, hHdef]
  set M₀ := 1 + ‖W₀‖ with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  set C := Kχ * (6 * B₂ + B₂ * (M₀ + 2 * η)) * Cs ^ 2 with hCdef
  refine ⟨ρ, C, hρ0, by positivity, fun ψ hψ => ?_, fun ψ₁ ψ₂ hψ₁ hψ₂ => ?_⟩
  · -- membership
    set f : ComplexModel n → ℝ := fun z => Γ (z, kfun (w ψ) z) with hf
    have hrep : A.localRep i (ma a ⇑ψ) = fun z => χt z * f z := by
      funext z
      rw [hloc]
      by_cases h0 : χt z = 0
      · rw [h0, zero_mul, zero_mul]
      · rw [hma ψ hψ z (hχK z h0)]
    have hf0 : ∀ z, |f z| ≤ B₀ := fun z => by rw [← Real.norm_eq_abs]; exact hB₀ _
    have hfl : ∀ z z', ‖z - z'‖ ≤ 1 →
        |f z - f z'| ≤ (B₀ * (1 + ‖w ψ‖)) * ‖z - z'‖ ^ (r : ℝ) := by
      intro z z' hzz
      rw [← Real.norm_eq_abs, mul_assoc]
      refine (hB₀l _ _).trans (mul_le_mul_of_nonneg_left ?_ hB₀0)
      rw [Prod.mk_sub_mk]
      have hρz : 0 ≤ ‖z - z'‖ ^ (r : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
      · exact (le_rpow_self_of_le_one (norm_nonneg _) hzz hr1').trans
          (le_mul_of_one_le_left hρz (by linarith [norm_nonneg (w ψ)]))
      · exact (norm_kfun_holder _ z z').trans
          (mul_le_mul_of_nonneg_right (by linarith) hρz)
    have hf1 := abs_sub_le_of_local hr0' (by positivity) hf0 hfl
    have hHol := HolderNemytskii.abs_mul_sub_le hr0' hr1' hKχ0 hχ0 hχ1 hf0 hf1
    refine ⟨ManifoldParametrix.ofHolderZero hr0 (fun z => χt z * f z) (F := Kχ * B₀)
      (fun z => ?_) (by positivity) hHol, ?_⟩
    · rw [abs_mul]; exact mul_le_mul (hχ0 z) (hf0 z) (abs_nonneg _) hKχ0
    · rw [ManifoldParametrix.coe_ofHolderZero, hrep]
  · -- the remainder
    set P₀ : ComplexModel n → ComplexModel n × (Fin n → Fin n → ℂ) := fun z => (z, kfun W₀ z)
      with hP₀
    set P₁ : ComplexModel n → ComplexModel n × (Fin n → Fin n → ℂ) :=
      fun z => (z, kfun (w ψ₁) z) with hP₁
    set P₂ : ComplexModel n → ComplexModel n × (Fin n → Fin n → ℂ) :=
      fun z => (z, kfun (w ψ₂) z) with hP₂
    set R : ComplexModel n → ℝ :=
      fun z => Γ (P₁ z) - Γ (P₂ z) - fderiv ℝ Γ (P₀ z) (P₁ z - P₂ z) with hRdef
    have hlap : ∀ z ∈ K,
        laplacian g ⇑(ψ₁ - ψ₂) (e.val.symm z) = fderiv ℝ Γ (P₀ z) (P₁ z - P₂ z) := by
      intro z hz
      have hzt := hKt hz
      rw [KahlerLaplacianChart.laplacian_eq hg (hC2 (ψ₁ - ψ₂)) (e.val.map_target hzt),
        e.val.right_inv hzt]
      obtain ⟨-, hΓ0⟩ := hΓeq z hz (kfun W₀ z) (by rw [sub_self, norm_zero]; exact hη.le)
      rw [hΓ0.fderiv_eq]
      have hP : P₁ z - P₂ z =
          (0, kmat (complexHessian (fun x => (ψ₁ - ψ₂) (e.val.symm x)) z)) := by
        simp only [hP₁, hP₂, Prod.mk_sub_mk, sub_self]
        rw [← kfun_sub', ← hwsub, hkfun _ z hz]
      have hgz : H z + hermPart (kfun W₀ z) = normalizedHermitianMatrix (g.coeff e z) := by
        rw [hherm Φ₀ z hz, hgφ e z hzt]
      have hPherm : (H (P₀ z).1 + hermPart (P₀ z).2).IsHermitian := by
        show (H z + hermPart (kfun W₀ z)).IsHermitian
        rw [hgz]; exact (posDef_coeff hg hzt).isHermitian
      rw [hP, fderiv_maLocal_apply e.val.open_target hH (hdom z hz) hPherm,
        hermPart_kmat (isHermitian_complexHessian_of_contDiffAt
          (ManifoldContinuity.contDiffAt_comp_symm hr1' (ψ₁ - ψ₂) e hzt))]
      show _ = ((H z + hermPart (kfun W₀ z))⁻¹ * _).trace.re
      rw [hgz]
      rfl
    have hrep : A.localRep i (fun y => ma a ⇑ψ₁ y - ma a ⇑ψ₂ y - laplacian g ⇑(ψ₁ - ψ₂) y) =
        fun z => χt z * R z := by
      funext z
      rw [hloc]
      by_cases h0 : χt z = 0
      · rw [h0, zero_mul, zero_mul]
      · have hz := hχK z h0
        rw [hma ψ₁ hψ₁ z hz, hma ψ₂ hψ₂ z hz, hlap z hz]
    -- the hypotheses of the Nemytskii estimate
    set δ := Cs * (‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) with hδ
    set d := Cs * ‖ψ₁ - ψ₂‖ with hd
    have hδ0 : 0 ≤ δ := by positivity
    have hd0 : 0 ≤ d := by positivity
    have hδη : δ ≤ 2 * η := by
      have : ‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖ ≤ 2 * ρ := by linarith
      calc δ ≤ Cs * (2 * ρ) := mul_le_mul_of_nonneg_left this hCs0
        _ = 2 * (Cs * ρ) := by ring
        _ ≤ 2 * η := by linarith
    have hj1 : ∀ z, ‖P₁ z - P₀ z‖ ≤ δ := by
      intro z
      simp only [hP₁, hP₀, Prod.mk_sub_mk, sub_self]
      refine norm_prod_le_iff.mpr ⟨by simpa using hδ0, ?_⟩
      refine ((norm_kfun_sub_le' _ _ z).trans (hwdiff ψ₁)).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (ψ₂ - Φ₀)]) hCs0
    have hj2 : ∀ z, ‖P₂ z - P₀ z‖ ≤ δ := by
      intro z
      simp only [hP₂, hP₀, Prod.mk_sub_mk, sub_self]
      refine norm_prod_le_iff.mpr ⟨by simpa using hδ0, ?_⟩
      refine ((norm_kfun_sub_le' _ _ z).trans (hwdiff ψ₂)).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (ψ₁ - Φ₀)]) hCs0
    have hj1' : ∀ z z', ‖P₁ z - P₀ z - (P₁ z' - P₀ z')‖ ≤ δ * ‖z - z'‖ ^ (r : ℝ) := by
      intro z z'
      simp only [hP₁, hP₀, Prod.mk_sub_mk, sub_self]
      refine norm_prod_le_iff.mpr ⟨by simpa using mul_nonneg hδ0 (Real.rpow_nonneg
        (norm_nonneg _) _), ?_⟩
      rw [← kfun_sub', ← kfun_sub']
      refine (norm_kfun_holder _ z z').trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg
        (norm_nonneg _) _))
      exact (hwdiff ψ₁).trans
        (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (ψ₂ - Φ₀)]) hCs0)
    have hj2' : ∀ z z', ‖P₂ z - P₀ z - (P₂ z' - P₀ z')‖ ≤ δ * ‖z - z'‖ ^ (r : ℝ) := by
      intro z z'
      simp only [hP₂, hP₀, Prod.mk_sub_mk, sub_self]
      refine norm_prod_le_iff.mpr ⟨by simpa using mul_nonneg hδ0 (Real.rpow_nonneg
        (norm_nonneg _) _), ?_⟩
      rw [← kfun_sub', ← kfun_sub']
      refine (norm_kfun_holder _ z z').trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg
        (norm_nonneg _) _))
      exact (hwdiff ψ₂).trans
        (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (ψ₁ - Φ₀)]) hCs0)
    have hj0 : ∀ z z', ‖z - z'‖ ≤ 1 → ‖P₀ z - P₀ z'‖ ≤ M₀ * ‖z - z'‖ ^ (r : ℝ) := by
      intro z z' hzz
      simp only [hP₀, Prod.mk_sub_mk]
      have hρz : 0 ≤ ‖z - z'‖ ^ (r : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
      · exact (le_rpow_self_of_le_one (norm_nonneg _) hzz hr1').trans
          (le_mul_of_one_le_left hρz (by linarith [norm_nonneg W₀]))
      · exact (norm_kfun_holder _ z z').trans (mul_le_mul_of_nonneg_right (by linarith) hρz)
    have hjd : ∀ z, ‖P₁ z - P₂ z‖ ≤ d := by
      intro z
      simp only [hP₁, hP₂, Prod.mk_sub_mk, sub_self]
      refine norm_prod_le_iff.mpr ⟨by simpa using hd0, ?_⟩
      refine (norm_kfun_sub_le' _ _ z).trans ?_
      rw [← hwsub]; exact hwn' _
    have hjd' : ∀ z z', ‖P₁ z - P₂ z - (P₁ z' - P₂ z')‖ ≤ d * ‖z - z'‖ ^ (r : ℝ) := by
      intro z z'
      simp only [hP₁, hP₂, Prod.mk_sub_mk, sub_self]
      refine norm_prod_le_iff.mpr ⟨by simpa using mul_nonneg hd0 (Real.rpow_nonneg
        (norm_nonneg _) _), ?_⟩
      rw [← kfun_sub', ← kfun_sub']
      refine (norm_kfun_holder _ z z').trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg
        (norm_nonneg _) _))
      rw [← hwsub]; exact hwn' _
    have hRb : ∀ z, |R z| ≤ B₂ * δ * d := fun z =>
      (HolderNemytskii.abs_remainder_le hΓd hgd hB₂ hj1 hj2 z).trans
        (mul_le_mul_of_nonneg_left (hjd z) (by positivity))
    have hRh : ∀ z z', |R z - R z'| ≤ ((2 * B₂ + B₂ * (M₀ + δ)) * δ * d) * ‖z - z'‖ ^ (r : ℝ) :=
      fun z z' => HolderNemytskii.abs_remainder_sub_le hΓd hgd hB₂ hB₂l hB₂0 hr0' hM₀0 hj1 hj2
        hj1' hj2' hj0 hjd hjd' z z'
    have hHol := HolderNemytskii.abs_mul_sub_le hr0' hr1' hKχ0 hχ0 hχ1 hRb hRh
    refine ⟨ManifoldParametrix.ofHolderZero hr0 (fun z => χt z * R z) (F := Kχ * (B₂ * δ * d))
      (fun z => ?_) (by positivity) hHol, ?_, ?_⟩
    · rw [abs_mul]; exact mul_le_mul (hχ0 z) (hRb z) (abs_nonneg _) hKχ0
    · rw [ManifoldParametrix.coe_ofHolderZero, hrep]
    · refine (ManifoldParametrix.norm_ofHolderZero_le hr0 _ _ _ _).trans ?_
      have hδd : δ * d = Cs ^ 2 * ((‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) * ‖ψ₁ - ψ₂‖) := by
        rw [hδ, hd]; ring
      have hB : Kχ * (B₂ * δ * d) + (Kχ * ((2 * B₂ + B₂ * (M₀ + δ)) * δ * d) +
          (Kχ + 2 * Kχ) * (B₂ * δ * d)) = Kχ * (6 * B₂ + B₂ * (M₀ + δ)) * (δ * d) := by ring
      rw [hB, hδd, hCdef]
      have hst : 0 ≤ (‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) * ‖ψ₁ - ψ₂‖ := by positivity
      have hmono : Kχ * (6 * B₂ + B₂ * (M₀ + δ)) ≤ Kχ * (6 * B₂ + B₂ * (M₀ + 2 * η)) := by
        gcongr
      calc Kχ * (6 * B₂ + B₂ * (M₀ + δ)) * (Cs ^ 2 * ((‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) * ‖ψ₁ - ψ₂‖))
          ≤ Kχ * (6 * B₂ + B₂ * (M₀ + 2 * η)) * (Cs ^ 2 * ((‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) *
            ‖ψ₁ - ψ₂‖)) := mul_le_mul_of_nonneg_right hmono (by positivity)
        _ = Kχ * (6 * B₂ + B₂ * (M₀ + 2 * η)) * Cs ^ 2 * (‖ψ₁ - Φ₀‖ + ‖ψ₂ - Φ₀‖) *
            ‖ψ₁ - ψ₂‖ := by ring

end SGPT.Foundations.Analysis.Pending.MongeAmpereHolder

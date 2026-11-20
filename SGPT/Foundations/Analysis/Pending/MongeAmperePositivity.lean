import SGPT.Foundations.Analysis.Pending.YauOpenness

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Positivity of `a + ddᶜψ` for `ψ` close to `Φ₀` in `C^{2,r}(M)`

If `g = a + ddᶜΦ₀` is Hermitian (positive definite in every chart) and `ψ ∈ C^{2,r}(M)` is close
enough to `Φ₀`, then `H_a + complexHessian ψ` is positive definite in **every** chart
(`exists_posDef_near`): in the charts of a Hölder atlas on the compact pieces
`e_i(tsupport χ_i)` by a uniform margin (compactness, `exists_inner_ge_of_isCompact`) and a
perturbation bound `‖matCLM D‖ ≤ c ‖kmat D‖` (`norm_matCLM_le`); in an arbitrary chart by the
congruence `H_e + K_e = Jᵀ (H_i + K_i) J̄` along the chart transition.

Consumer: the openness step of the `ε`-continuity path of Yau's theorem: the solutions produced by
`YauOpenness.exists_ma_eq_near_of_smooth` are `C^{2,r}`-close to the smooth solution `φ₀`, hence
`H_A + complexHessian ψ > 0` in every chart (`exists_ma_eq_near_posDef`).  TN.4 B5, N1; blueprint
`bou:yau-openness`.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff InnerProductSpace Manifold ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.MongeAmperePositivity

open FirstPass FirstPass.MongeAmpere KahlerLaplacianChart MongeAmpereHolder ComplexHessianDeterminant

variable {n : ℕ}

/-- The real part of the Hermitian form of a matrix, as a real inner product. -/
theorem re_star_dotProduct_mulVec (P : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (P *ᵥ x)).re = ⟪matCLM P (WithLp.toLp 2 x), WithLp.toLp 2 x⟫_ℝ := by
  rw [real_inner_eq_re, EuclideanSpace.inner_eq_star_dotProduct]
  have h2 : x ⬝ᵥ star (WithLp.ofLp (matCLM P (WithLp.toLp 2 x))) = star (star x ⬝ᵥ (P *ᵥ x)) := by
    rw [← Matrix.star_dotProduct, dotProduct_comm]
    simp [matCLM_apply]
  rw [h2, Complex.star_def, Complex.conj_re]

/-- `‖matCLM D‖ ≤ c ‖D‖_sup`. -/
theorem norm_matCLM_le (D : Matrix (Fin n) (Fin n) ℂ) :
    ‖matCLM D‖ ≤ (∑ j : Fin n, ∑ k : Fin n, (‖matCLM (Matrix.single j k (1 : ℂ))‖ +
      ‖matCLM (Matrix.single j k Complex.I)‖)) * ‖kmat D‖ := by
  rw [matCLM_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hjk : ‖D j k‖ ≤ ‖kmat D‖ :=
    (norm_le_pi_norm (kmat D j) k).trans (norm_le_pi_norm (kmat D) j)
  have hre : |(D j k).re| ≤ ‖kmat D‖ := (Complex.abs_re_le_norm _).trans hjk
  have him : |(D j k).im| ≤ ‖kmat D‖ := (Complex.abs_im_le_norm _).trans hjk
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, add_mul]
  exact add_le_add (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hre (norm_nonneg _))
    (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left him (norm_nonneg _))

/-- **A uniform margin by compactness**: a continuous family of real operators, positive on nonzero
vectors at every point of a compact set, is uniformly positive there. -/
theorem exists_inner_ge_of_isCompact {T : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hT : ContinuousOn T K)
    (hpos : ∀ z ∈ K, ∀ u : ComplexModel n, u ≠ 0 → 0 < ⟪T z u, u⟫_ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ K, ∀ u : ComplexModel n, m * ‖u‖ ^ 2 ≤ ⟪T z u, u⟫_ℝ := by
  set S := K ×ˢ sphere (0 : ComplexModel n) 1 with hSdef
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun p : ComplexModel n × ComplexModel n => ⟪T p.1 p.2, p.2⟫_ℝ) S :=
    ((hT.comp continuousOn_fst fun p hp => hp.1).clm_apply continuousOn_snd).inner continuousOn_snd
  have hscale : ∀ z u, u ≠ 0 → ⟪T z u, u⟫_ℝ = ‖u‖ ^ 2 * ⟪T z (‖u‖⁻¹ • u), ‖u‖⁻¹ • u⟫_ℝ := by
    intro z u hu
    have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    field_simp
  have hmem : ∀ z ∈ K, ∀ u : ComplexModel n, u ≠ 0 → (z, ‖u‖⁻¹ • u) ∈ S := by
    intro z hz u hu
    refine ⟨hz, ?_⟩
    simp [norm_smul, norm_ne_zero_iff.mpr hu]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun z hz u => ?_⟩
    by_cases hu : u = 0
    · simp [hu]
    · have := hmem z hz u hu
      rw [hSe] at this
      exact this.elim
  · obtain ⟨p, hpS, hpmin⟩ := hS.exists_isMinOn hSne hcont
    have hp2 : p.2 ≠ 0 := by
      intro h0
      have := hpS.2
      rw [h0] at this
      simp at this
    refine ⟨⟪T p.1 p.2, p.2⟫_ℝ, hpos p.1 hpS.1 p.2 hp2, fun z hz u => ?_⟩
    by_cases hu : u = 0
    · simp [hu]
    · have h := hpmin (hmem z hz u hu)
      simp only [Set.mem_ofPred_eq] at h
      rw [hscale z u hu, mul_comm]
      exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

theorem re_normalizedHermitianMatrix (A : CoordinateRealTwoForm n) (j k : Fin n) :
    (normalizedHermitianMatrix A j k).re =
      Real.pi * A ![coordinateVector j, Complex.I • coordinateVector k] := by
  simp [normalizedHermitianMatrix, Complex.mul_re]

theorem im_normalizedHermitianMatrix (A : CoordinateRealTwoForm n) (j k : Fin n) :
    (normalizedHermitianMatrix A j k).im =
      -(Real.pi * A ![coordinateVector j, coordinateVector k]) := by
  simp [normalizedHermitianMatrix, Complex.mul_im]

/-- The real operator of the coefficient matrix of a smooth field of two-forms is continuous. -/
theorem continuousOn_matCLM {F : ComplexModel n → CoordinateRealTwoForm n} {U : Set (ComplexModel n)}
    (hF : ContinuousOn F U) :
    ContinuousOn (fun z => matCLM (normalizedHermitianMatrix (F z))) U := by
  have h : (fun z => matCLM (normalizedHermitianMatrix (F z))) = fun z =>
      ∑ j, ∑ k, ((Real.pi * F z ![coordinateVector j, Complex.I • coordinateVector k]) •
        matCLM (Matrix.single j k 1) + (-(Real.pi * F z ![coordinateVector j, coordinateVector k])) •
          matCLM (Matrix.single j k Complex.I)) := by
    funext z
    rw [matCLM_eq_sum]
    simp only [re_normalizedHermitianMatrix, im_normalizedHermitianMatrix]
  rw [h]
  have hev : ∀ w : Fin 2 → ComplexModel n, ContinuousOn (fun z => F z w) U := fun w =>
    (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ w).continuous.comp_continuousOn hF
  refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
  exact ((continuousOn_const.mul (hev _)).smul continuousOn_const).add
    ((continuousOn_const.mul (hev _)).neg.smul continuousOn_const)

theorem matCLM_add (P P' : Matrix (Fin n) (Fin n) ℂ) : matCLM (P + P') = matCLM P + matCLM P' :=
  matCLMₗ.map_add P P'

theorem conjTranspose_map_conj (J : Matrix (Fin n) (Fin n) ℂ) :
    (J.map (starRingEnd ℂ))ᴴ = Jᵀ := by
  ext j k
  simp [Matrix.conjTranspose_apply]

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Positivity on the compact pieces of one chart** for `ψ` close to `Φ₀`. -/
theorem exists_chart_posDef {a g : SmoothRealForm n M 2} (ha : a.IsHermitian)
    (hg : g.IsHermitian) {A : HolderAtlas n M} {r : ℝ≥0} (hr1 : r ≤ 1) (Φ₀ : A.HolderMap 2 r ℝ)
    (hgφ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      normalizedHermitianMatrix (g.coeff e z) =
        normalizedHermitianMatrix (a.coeff e z) + complexHessian (fun x => Φ₀ (e.val.symm x)) z)
    (i : Fin A.m) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ψ : A.HolderMap 2 r ℝ, ‖ψ - Φ₀‖ < ρ →
      ∀ z ∈ (A.chart i).val '' tsupport (A.χ i),
        (normalizedHermitianMatrix (a.coeff (A.chart i) z) +
          complexHessian (fun x => ψ ((A.chart i).val.symm x)) z).PosDef := by
  classical
  set e := A.chart i with he
  have hKc : IsCompact (e.val '' tsupport (A.χ i)) := A.isCompact_image_tsupport i
  have hKt : e.val '' tsupport (A.χ i) ⊆ e.val.target := image_tsupport_subset_target A i
  set K := e.val '' tsupport (A.χ i) with hK
  obtain ⟨K', hK'c, hKK', hK't⟩ := exists_compact_between hKc e.val.open_target hKt
  obtain ⟨σ, hσs, hσc, hσt, hσ1, -⟩ := exists_cutoff hK'c e.val.open_target hK't
  obtain ⟨Cσ, hCσ⟩ := HolderAtlas.HolderMap.exists_smul_comp_symm (A := A) (k := 2) (F := ℝ) hr1 e
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
  have hkfun : ∀ ψ : A.HolderMap 2 r ℝ, ∀ z ∈ K,
      kfun (w ψ) z = kmat (complexHessian (fun x => ψ (e.val.symm x)) z) := by
    intro ψ z hz
    have hloc : (⇑(w ψ)) =ᶠ[𝓝 z] fun x => ψ (e.val.symm x) := by
      filter_upwards [isOpen_interior.mem_nhds (hKK' hz)] with x hx
      rw [hw ψ x, hσ1 x (interior_subset hx), smul_eq_mul, one_mul]
    simp only [kfun, complexHessian_congr' hloc]
  -- the margin of `g` on `K`
  have hT : ContinuousOn (fun z => matCLM (normalizedHermitianMatrix (g.coeff e z))) K :=
    (continuousOn_matCLM (g.smooth e).continuousOn).mono hKt
  obtain ⟨m, hm, hmle⟩ := exists_inner_ge_of_isCompact hKc hT fun z hz u hu => by
    have hx : WithLp.ofLp u ≠ 0 := by
      intro h; apply hu; ext j; simpa using congrFun h j
    have h := (posDef_coeff hg (hKt hz)).dotProduct_mulVec_pos hx
    have h2 := re_star_dotProduct_mulVec (normalizedHermitianMatrix (g.coeff e z)) (WithLp.ofLp u)
    simp only [WithLp.toLp_ofLp] at h2
    rw [← h2]
    exact (Complex.pos_iff.mp h).1
  set c : ℝ := ∑ j : Fin n, ∑ k : Fin n, (‖matCLM (Matrix.single j k (1 : ℂ))‖ +
      ‖matCLM (Matrix.single j k Complex.I)‖) with hcdef
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  refine ⟨m / (2 * (c * Cs + 1)), div_pos hm (by positivity), fun ψ hψ z hz => ?_⟩
  have hzt := hKt hz
  have hherm : (normalizedHermitianMatrix (a.coeff e z) +
      complexHessian (fun x => ψ (e.val.symm x)) z).IsHermitian :=
    (posDef_coeff ha hzt).isHermitian.add (isHermitian_complexHessian_of_contDiffAt
      (ManifoldContinuity.contDiffAt_comp_symm hr1 ψ e hzt))
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hherm, fun x hx => Complex.pos_iff.mpr ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩⟩
  rw [re_star_dotProduct_mulVec]
  set D := complexHessian (fun x => ψ (e.val.symm x)) z - complexHessian (fun x => Φ₀ (e.val.symm x)) z
    with hDdef
  have hdecomp : normalizedHermitianMatrix (a.coeff e z) +
      complexHessian (fun x => ψ (e.val.symm x)) z = normalizedHermitianMatrix (g.coeff e z) + D := by
    rw [hgφ e z hzt, hDdef]; abel
  have hD : ‖kmat D‖ ≤ Cs * ‖ψ - Φ₀‖ := by
    have : kmat D = kfun (w ψ) z - kfun (w Φ₀) z := by
      rw [hkfun ψ z hz, hkfun Φ₀ z hz, hDdef]; rfl
    rw [this]
    exact (norm_kfun_sub_le' _ _ z).trans (by rw [← hwsub]; exact hwn' _)
  set u : ComplexModel n := WithLp.toLp 2 x with hu
  have hu0 : u ≠ 0 := by
    intro h; apply hx; funext j; simpa [hu] using congrArg (fun v : ComplexModel n => v j) h
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  rw [hdecomp, matCLM_add, add_apply, inner_add_left]
  have h1 := hmle z hz u
  have h2 : |⟪matCLM D u, u⟫_ℝ| ≤ c * (Cs * ‖ψ - Φ₀‖) * ‖u‖ ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖matCLM D u‖ * ‖u‖ ≤ ‖matCLM D‖ * ‖u‖ * ‖u‖ :=
          mul_le_mul_of_nonneg_right ((matCLM D).le_opNorm u) (norm_nonneg _)
      _ ≤ (c * (Cs * ‖ψ - Φ₀‖)) * ‖u‖ * ‖u‖ := by
          gcongr
          exact (norm_matCLM_le D).trans (mul_le_mul_of_nonneg_left hD hc0)
      _ = c * (Cs * ‖ψ - Φ₀‖) * ‖u‖ ^ 2 := by ring
  have h3 : c * (Cs * ‖ψ - Φ₀‖) ≤ m / 2 := by
    have hρ : ‖ψ - Φ₀‖ ≤ m / (2 * (c * Cs + 1)) := hψ.le
    have hcs : c * (Cs * ‖ψ - Φ₀‖) ≤ (c * Cs + 1) * ‖ψ - Φ₀‖ := by
      nlinarith [norm_nonneg (ψ - Φ₀)]
    calc c * (Cs * ‖ψ - Φ₀‖) ≤ (c * Cs + 1) * ‖ψ - Φ₀‖ := hcs
      _ ≤ (c * Cs + 1) * (m / (2 * (c * Cs + 1))) :=
          mul_le_mul_of_nonneg_left hρ (by positivity)
      _ = m / 2 := by field_simp
  have hu2 : 0 < ‖u‖ ^ 2 := by positivity
  have := neg_abs_le ⟪matCLM D u, u⟫_ℝ
  nlinarith

/-- **Positivity near `Φ₀` in every chart**: for `ψ` close enough to `Φ₀` in `C^{2,r}(M)`,
`H_a + complexHessian ψ` is positive definite in every chart. -/
theorem exists_posDef_near {a g : SmoothRealForm n M 2} (ha : a.IsHermitian)
    (hg : g.IsHermitian) {A : HolderAtlas n M} {r : ℝ≥0} (hr1 : r ≤ 1) (Φ₀ : A.HolderMap 2 r ℝ)
    (hgφ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      normalizedHermitianMatrix (g.coeff e z) =
        normalizedHermitianMatrix (a.coeff e z) + complexHessian (fun x => Φ₀ (e.val.symm x)) z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ψ : A.HolderMap 2 r ℝ, ‖ψ - Φ₀‖ < ρ →
      ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
        (normalizedHermitianMatrix (a.coeff e z) +
          complexHessian (fun x => ψ (e.val.symm x)) z).PosDef := by
  choose ρs hρs hpd using fun i => exists_chart_posDef ha hg hr1 Φ₀ hgφ i
  set ρ : ℝ := 1 / (1 + ∑ i, 1 / ρs i) with hρdef
  have hsum0 : 0 ≤ ∑ i, 1 / ρs i := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hρs i)).le
  have hρ0 : 0 < ρ := one_div_pos.mpr (by linarith)
  have hρle : ∀ i, ρ ≤ ρs i := by
    intro i
    have h1 : 1 / ρs i ≤ 1 + ∑ j, 1 / ρs j := by
      have := Finset.single_le_sum (f := fun j => 1 / ρs j)
        (fun j _ => (one_div_pos.mpr (hρs j)).le) (Finset.mem_univ i)
      linarith
    rw [hρdef, div_le_iff₀ (by linarith)]
    have := (div_le_iff₀ (hρs i)).mp h1
    linarith [mul_comm (ρs i) (1 + ∑ j, 1 / ρs j)]
  refine ⟨ρ, hρ0, fun ψ hψ e z hz => ?_⟩
  have hψC2 : ∀ f : ComplexChart n M, ContDiffOn ℝ 2 (fun x => ψ (f.val.symm x)) f.val.target :=
    fun f w hw => (ManifoldContinuity.contDiffAt_comp_symm hr1 ψ f hw).contDiffWithinAt
  set y := e.val.symm z with hy
  have hye : y ∈ e.val.source := e.val.map_target hz
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, A.χ i y ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [A.sum_eq_one]; exact one_ne_zero)
  have hyi : y ∈ (A.chart i).val.source := A.tsupport_subset i (subset_tsupport _ hi)
  have hPi := hpd i ψ (hψ.trans_le (hρle i)) ((A.chart i).val y) ⟨y, subset_tsupport _ hi, rfl⟩
  have ha11 : ∀ f : ComplexChart n M, ∀ w ∈ f.val.target, IsOneOne (a.coeff f w) :=
    fun f w hw => (ha f w hw).1
  have hJ := isUnit_det_jacobianMatrix e (A.chart i) hye hyi
  set J := HolomorphicMixedDensity.jacobianMatrix (chartTransition e (A.chart i)) (e.val y) with hJdef
  have hJbar : IsUnit (J.map (starRingEnd ℂ)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.map _
  have hcong : normalizedHermitianMatrix (a.coeff e (e.val y)) +
      complexHessian (fun x => ψ (e.val.symm x)) (e.val y) =
      (J.map (starRingEnd ℂ))ᴴ * (normalizedHermitianMatrix (a.coeff (A.chart i) ((A.chart i).val y)) +
        complexHessian (fun x => ψ ((A.chart i).val.symm x)) ((A.chart i).val y)) *
          J.map (starRingEnd ℂ) := by
    rw [conjTranspose_map_conj, coeffMatrix_transition a ha11 hye hyi,
      complexHessian_transition hψC2 hye hyi, Matrix.mul_add, Matrix.add_mul]
  have hz' : e.val y = z := e.val.right_inv hz
  rw [← hz', hcong]
  exact hPi.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hJbar))

end Manifold

section Kahler

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

open ManifoldTubePositivity PositiveClasses

/-- **Openness of the `ε`-path with positivity** (`C^{2,r}` solutions): under the hypotheses of
`YauOpenness.exists_ma_eq_near_of_smooth`, for `t` near `t₀` there is `ψ ∈ C^{2,r}(Y)` close to `φ₀`
with `ma A ψ = tF + εψ` and `H_A + complexHessian ψ` positive definite in every chart. -/
theorem exists_ma_eq_near_posDef [CompactSpace Y] (A : KahlerBackground N Y)
    (HA : HolderAtlas N Y) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) {ε : ℝ} (hε : 0 < ε) {t₀ : ℝ} {φ₀ : Y → ℝ}
    (hφ₀ : ChartSmooth (n := N) φ₀) (hK : (A.form + ddcClosedForm φ₀ hφ₀).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ₀ hφ₀).val.coeff e z) =
        Real.exp (t₀ * F (e.val.symm z) + ε * φ₀ (e.val.symm z)) *
          actualTopPowerDensity (A.form.val.coeff e z)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ → ∃ ψ : HA.HolderMap 2 r ℝ,
      ‖ψ - HolderAtlas.HolderMap.ofChartSmooth hr1.le φ₀ hφ₀‖ < ρ ∧
      (∀ y, ma A.form.val ⇑ψ y = t * F y + ε * ψ y) ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        (normalizedHermitianMatrix (A.form.val.coeff e z) +
          complexHessian (fun x => ψ (e.val.symm x)) z).PosDef := by
  set Φ₀ : HA.HolderMap 2 r ℝ := HolderAtlas.HolderMap.ofChartSmooth hr1.le φ₀ hφ₀ with hΦ₀
  obtain ⟨ρ₁, hρ₁, hpd⟩ := exists_posDef_near A.isKahler.1 hK.1 hr1.le Φ₀
    (fun e z hz => YauOpenness.normalizedHermitianMatrix_add_ddc A.form hφ₀ hz)
  obtain ⟨δ, hδ, hsol⟩ := YauOpenness.exists_ma_eq_near_of_smooth A HA hr0 hr1 hF hε hφ₀ hK hdens
    (lt_min hρ hρ₁)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨ψ, hψ, heq⟩ := hsol t ht
  exact ⟨ψ, hψ.trans_le (min_le_left _ _), heq, hpd ψ (hψ.trans_le (min_le_right _ _))⟩

end Kahler

end SGPT.Foundations.Analysis.Pending.MongeAmperePositivity

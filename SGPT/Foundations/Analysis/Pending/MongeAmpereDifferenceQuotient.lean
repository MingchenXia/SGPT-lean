import SGPT.Foundations.Analysis.Pending.LinearEllipticRegularity
import SGPT.Foundations.Analysis.Pending.MongeAmperePositivity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The first regularity step for the complex Monge–Ampère equation: `C^{2,r} → C^{3,r}`

In a chart, the equation `ma A ψ = tF + εψ` reads `maLocal H (z, kfun u z) = f z`, i.e.
`log det(H(z) + (∂²u/∂z_j∂z̄_k)(z)) - log det H(z) = f(z)` (`MongeAmpereHolder.maLocal`), with `H`
the (smooth, positive definite) coefficient matrix of the Kähler background and
`H + complexHessian u` positive definite.

**Main result** `holderAt_three_of_maLocal_eq`: if `u` is `C^{2,r}` and `f` is `C^{1,r}` near every
point of an open set `U` (`0 < r < 1`), then `u` is `C^{3,r}` near every point of `U`.

Proof (difference quotients for a fully nonlinear equation, Gilbarg--Trudinger §17.4 in the form of
Székelyhidi §3.4).  Fix a direction `ζ`.  For `x` near `z₀` and small `h > 0` the fundamental theorem
of calculus along the segment `p_s = (x + s h ζ, K(x) + s (K(x + hζ) - K(x)))`, `K = kfun u`, gives
`a_h(x) : D²(D_h u)(x) = D_h f(x) - ∫₀¹ ∂_z F(p_s) ζ ds` with the **averaged coefficient**
`a_h(x) = ∫₀¹ ¼ conj(P_s⁻¹) ds`, `P_s = H + herm K_s` (`KahlerLaplacianChart.lapCoeff`; derivative of
`maLocal` by Jacobi's formula, `MongeAmpereHolder.fderiv_maLocal_apply`).  On a compact neighbourhood
of the graph of `K` the matrices `P` stay positive definite (`isOpen_pdDomain`), and a cut-off model
`Tm` of `p ↦ lapCoeff P(p)` is smooth, uniformly elliptic and Lipschitz on the whole space; hence
`a_h` lies in the Schauder class and the right-hand side is bounded and `r`-Hölder, uniformly in `h`
(`K` is `r`-Hölder).  `DifferenceQuotient.exists_mul_fderiv_mem` gives `∂_ζ u ∈ C^{2,r}`.

TN.4 B5, regularity bootstrap (the proof of Yau's theorem, P2, R1);
blueprint `bou:yau-openness` / `bou:yau-closedness`.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff InnerProductSpace ComplexOrder Matrix Interval

namespace SGPT.Foundations.Analysis.Pending.MongeAmpereRegularity

open FirstPass FirstPass.MongeAmpere KahlerLaplacianChart MongeAmpereHolder HolderGerm
  DifferenceQuotient LinearRegularity EllipticMeanValue SchauderBlowup

variable {n : ℕ}

/-! ### Positive definiteness through the real quadratic form -/

theorem posDef_of_inner_pos {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (h : ∀ u : ComplexModel n, u ≠ 0 → 0 < ⟪matCLM P u, u⟫_ℝ) : P.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hP, fun x hx => Complex.pos_iff.mpr ⟨?_, (hP.im_star_dotProduct_mulVec_self x).symm⟩⟩
  rw [MongeAmperePositivity.re_star_dotProduct_mulVec]
  apply h
  intro h0
  apply hx
  funext j
  simpa using congrArg (fun v : ComplexModel n => v j) h0

/-- The domain where `H(z) + herm K` is positive definite. -/
def pdDomain (H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (U : Set (ComplexModel n)) :
    Set (ComplexModel n × (Fin n → Fin n → ℂ)) :=
  {p | p.1 ∈ U ∧ (H p.1 + hermPart p.2).PosDef}

section Domain

variable {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}

theorem continuousOn_matCLM_field (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U) :
    ContinuousOn (fun p : ComplexModel n × (Fin n → Fin n → ℂ) => matCLM (H p.1 + hermPart p.2))
      (Prod.fst ⁻¹' U) := by
  have he := contDiffOn_entries hH
  have h : (fun p : ComplexModel n × (Fin n → Fin n → ℂ) => matCLM (H p.1 + hermPart p.2)) =
      fun p => ∑ j, ∑ k, (((H p.1 + hermPart p.2) j k).re • matCLM (Matrix.single j k 1) +
        ((H p.1 + hermPart p.2) j k).im • matCLM (Matrix.single j k Complex.I)) := by
    funext p
    rw [matCLM_eq_sum]
  rw [h]
  refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
  exact ((Complex.continuous_re.comp_continuousOn (he j k).continuousOn).smul continuousOn_const).add
    ((Complex.continuous_im.comp_continuousOn (he j k).continuousOn).smul continuousOn_const)

/-- **`H + herm K` positive definite is an open condition.** -/
theorem isOpen_pdDomain (hU : IsOpen U) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hHh : ∀ z ∈ U, (H z).IsHermitian) : IsOpen (pdDomain H U) := by
  rw [isOpen_iff_mem_nhds]
  intro p₀ hp₀
  have hU' : IsOpen (Prod.fst ⁻¹' U : Set (ComplexModel n × (Fin n → Fin n → ℂ))) :=
    hU.preimage continuous_fst
  have hQ := continuousOn_matCLM_field hH
  -- joint continuity of the quadratic form
  have hq : ∀ v ∈ sphere (0 : ComplexModel n) 1,
      ∀ᶠ z : (ComplexModel n × (Fin n → Fin n → ℂ)) × ComplexModel n in 𝓝 (p₀, v),
        0 < ⟪matCLM (H z.1.1 + hermPart z.1.2) z.2, z.2⟫_ℝ := by
    intro v hv
    have hv0 : v ≠ 0 := by
      intro h0; rw [h0] at hv; simp at hv
    have hpos : 0 < ⟪matCLM (H p₀.1 + hermPart p₀.2) v, v⟫_ℝ := inner_matCLM_self_pos hp₀.2 hv0
    have hcont : ContinuousAt (fun z : (ComplexModel n × (Fin n → Fin n → ℂ)) × ComplexModel n =>
        ⟪matCLM (H z.1.1 + hermPart z.1.2) z.2, z.2⟫_ℝ) (p₀, v) := by
      have h1 : ContinuousAt (fun z : (ComplexModel n × (Fin n → Fin n → ℂ)) × ComplexModel n =>
          matCLM (H z.1.1 + hermPart z.1.2)) (p₀, v) :=
        ContinuousAt.comp (f := Prod.fst) (g := fun p : ComplexModel n × (Fin n → Fin n → ℂ) =>
          matCLM (H p.1 + hermPart p.2)) (hQ.continuousAt (hU'.mem_nhds hp₀.1)) continuousAt_fst
      exact (h1.clm_apply continuousAt_snd).inner continuousAt_snd
    exact hcont.eventually (lt_mem_nhds hpos)
  have hev := (isCompact_sphere (0 : ComplexModel n) 1).eventually_forall_of_forall_eventually
    (x₀ := p₀) (P := fun p v => 0 < ⟪matCLM (H p.1 + hermPart p.2) v, v⟫_ℝ) hq
  filter_upwards [hev, hU'.mem_nhds hp₀.1] with p hp hpU
  refine ⟨hpU, posDef_of_inner_pos ((hHh p.1 hpU).add (isHermitian_hermPart _)) fun u hu => ?_⟩
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hmem : ‖u‖⁻¹ • u ∈ sphere (0 : ComplexModel n) 1 := by
    simp [norm_smul, hn.ne']
  have h1 : 0 < ⟪matCLM (H p.1 + hermPart p.2) (‖u‖⁻¹ • u), ‖u‖⁻¹ • u⟫_ℝ := hp _ hmem
  rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real, ← mul_assoc] at h1
  have h2 : 0 < ‖u‖⁻¹ * ‖u‖⁻¹ := by positivity
  exact (mul_pos_iff_of_pos_left h2).mp h1

theorem pdDomain_subset_maDomain (hHp : ∀ z ∈ U, (H z).PosDef) : pdDomain H U ⊆ maDomain H U :=
  fun p hp => ⟨hp.1, (Complex.pos_iff.mp hp.2.det_pos).1, (Complex.pos_iff.mp (hHp p.1 hp.1).det_pos).1⟩

/-- The coefficient field `p ↦ ¼ conj((H + herm K)⁻¹)` is smooth on `pdDomain`. -/
theorem contDiffOn_lapCoeffField (hU : IsOpen U)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U) :
    ContDiffOn ℝ ∞ (fun p : ComplexModel n × (Fin n → Fin n → ℂ) =>
      lapCoeff (H p.1 + hermPart p.2)) (pdDomain H U) := by
  have he := contDiffOn_entries hH
  have hM : ContDiffOn ℝ ∞ (fun p : ComplexModel n × (Fin n → Fin n → ℂ) =>
      matCLM ((H p.1 + hermPart p.2).map (starRingEnd ℂ))) (Prod.fst ⁻¹' U) := by
    have h : (fun p : ComplexModel n × (Fin n → Fin n → ℂ) =>
        matCLM ((H p.1 + hermPart p.2).map (starRingEnd ℂ))) = fun p =>
        ∑ j, ∑ k, (((H p.1 + hermPart p.2) j k).re • matCLM (Matrix.single j k 1) +
          (-((H p.1 + hermPart p.2) j k).im) • matCLM (Matrix.single j k Complex.I)) := by
      funext p
      rw [matCLM_eq_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.map_apply, Complex.conj_re, Complex.conj_im]
    rw [h]
    refine ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
    exact ((Complex.reCLM.contDiff.comp_contDiffOn (he j k)).smul contDiffOn_const).add
      ((Complex.imCLM.contDiff.comp_contDiffOn (he j k)).neg.smul contDiffOn_const)
  have hsub : pdDomain H U ⊆ Prod.fst ⁻¹' U := fun p hp => hp.1
  have h1 : ContDiffOn ℝ ∞ (fun p : ComplexModel n × (Fin n → Fin n → ℂ) => (1 / 4 : ℝ) •
      Ring.inverse (matCLM ((H p.1 + hermPart p.2).map (starRingEnd ℂ)))) (pdDomain H U) := by
    refine ContDiffOn.const_smul _ fun p hp => ?_
    have hdet : IsUnit (H p.1 + hermPart p.2).det :=
      isUnit_iff_ne_zero.mpr hp.2.det_pos.ne'
    obtain ⟨w, hw⟩ := isUnit_matCLM_map_conj hdet
    have hinv : ContDiffAt ℝ ∞ Ring.inverse
        (matCLM ((H p.1 + hermPart p.2).map (starRingEnd ℂ))) := by
      rw [← hw]; exact contDiffAt_ringInverse ℝ w
    have hU' : IsOpen (Prod.fst ⁻¹' U : Set (ComplexModel n × (Fin n → Fin n → ℂ))) :=
      hU.preimage continuous_fst
    exact (hinv.comp p ((hM.contDiffAt (hU'.mem_nhds (hsub hp))))).contDiffWithinAt
  exact h1.congr fun p hp => lapCoeff_eq_inverse (isUnit_iff_ne_zero.mpr hp.2.det_pos.ne')

end Domain

/-! ### Helpers on a general parameter space -/

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A continuous field of positive operators on a compact set is uniformly positive. -/
theorem exists_inner_ge' {Y : Type*} [TopologicalSpace Y] {T : Y → E →L[ℝ] E} {K : Set Y}
    (hK : IsCompact K) (hT : ContinuousOn T K) (hpos : ∀ y ∈ K, ∀ v, v ≠ 0 → 0 < ⟪T y v, v⟫_ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ y ∈ K, ∀ v, lam * ‖v‖ ^ 2 ≤ ⟪T y v, v⟫_ℝ := by
  set S := K ×ˢ sphere (0 : E) 1 with hSdef
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun p : Y × E => ⟪T p.1 p.2, p.2⟫_ℝ) S := by
    have h1 : ContinuousOn (fun p : Y × E => T p.1) S :=
      hT.comp continuousOn_fst fun p hp => hp.1
    exact (h1.clm_apply continuousOn_snd).inner continuousOn_snd
  have hscale : ∀ y v, v ≠ 0 → ⟪T y v, v⟫_ℝ = ‖v‖ ^ 2 * ⟪T y (‖v‖⁻¹ • v), ‖v‖⁻¹ • v⟫_ℝ := by
    intro y v hv
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    field_simp
  have hmem : ∀ y ∈ K, ∀ v : E, v ≠ 0 → (y, ‖v‖⁻¹ • v) ∈ S := by
    intro y hy v hv
    refine ⟨hy, ?_⟩
    simp [norm_smul, norm_ne_zero_iff.mpr hv]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun y hy v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · have := hmem y hy v hv
      rw [hSe] at this
      exact this.elim
  · obtain ⟨p, hpS, hpmin⟩ := hS.exists_isMinOn hSne hcont
    have hp2 : p.2 ≠ 0 := by
      intro h0
      have := hpS.2
      rw [h0] at this
      simp at this
    refine ⟨⟪T p.1 p.2, p.2⟫_ℝ, hpos p.1 hpS.1 p.2 hp2, fun y hy v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · have h := hpmin (hmem y hy v hv)
      simp only [Set.mem_ofPred_eq] at h
      rw [hscale y v hv, mul_comm]
      exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **A global elliptic model** of a smooth field of positive symmetric operators on an open set
`O`: a continuous field on the whole space, uniformly elliptic, bounded and Lipschitz, equal to the
given one on a compact `N ⊆ O` (`Tm = id + ξ (T - id)`, `ξ` a cut-off). -/
theorem exists_ellipticModel {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] {T : Y → E →L[ℝ] E} {O N : Set Y} (hO : IsOpen O) (hN : IsCompact N)
    (hNO : N ⊆ O) (hT : ContDiffOn ℝ ∞ T O) (hsymm : ∀ y ∈ O, ∀ u v, ⟪T y u, v⟫_ℝ = ⟪u, T y v⟫_ℝ)
    (hpos : ∀ y ∈ O, ∀ u, u ≠ 0 → 0 < ⟪T y u, u⟫_ℝ) :
    ∃ (Tm : Y → E →L[ℝ] E) (lam Λ : ℝ), 0 < lam ∧ 0 ≤ Λ ∧ Continuous Tm ∧
      (∀ y u v, ⟪Tm y u, v⟫_ℝ = ⟪u, Tm y v⟫_ℝ) ∧ (∀ y v, lam * ‖v‖ ^ 2 ≤ ⟪Tm y v, v⟫_ℝ) ∧
      (∀ y, ‖Tm y‖ ≤ Λ) ∧ (∀ y y', ‖Tm y - Tm y'‖ ≤ Λ * ‖y - y'‖) ∧ ∀ y ∈ N, Tm y = T y := by
  obtain ⟨ξ, hξs, hξc, hξO, hξ1, hξI⟩ := KahlerLaplacianChart.exists_cutoff hN hO hNO
  set I := ContinuousLinearMap.id ℝ E with hI
  set d : Y → E →L[ℝ] E := fun y => ξ y • (T y - I) with hddef
  have hd : ContDiff ℝ ∞ d := contDiff_smul_of_tsupport hO hξs hξO (hT.sub contDiffOn_const)
  have hdc : HasCompactSupport d := hξc.smul_right
  obtain ⟨Kd, hKd0, hKdb, hKdl⟩ :=
    HolderGerm.exists_lipschitz_of_hasCompactSupport (hd.of_le (by exact_mod_cast le_top)) hdc
  obtain ⟨lam0, hlam0, hlam0le⟩ := exists_inner_ge' hξc.isCompact
    (hT.continuousOn.mono hξO) fun y hy => hpos y (hξO hy)
  have hξ0 : ∀ y, y ∉ tsupport ξ → ξ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  set Tm : Y → E →L[ℝ] E := fun y => I + d y with hTmdef
  have happ : ∀ y v, Tm y v = v + ξ y • (T y v - v) := by
    intro y v
    simp [hTmdef, hddef, hI]
  refine ⟨Tm, min lam0 1, 1 + Kd, lt_min hlam0 one_pos, by positivity,
    continuous_const.add hd.continuous, fun y u v => ?_, fun y v => ?_, fun y => ?_,
    fun y y' => ?_, fun y hy => ?_⟩
  · rw [happ, happ]
    by_cases hy : y ∈ tsupport ξ
    · have hs := hsymm y (hξO hy) u v
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, RCLike.conj_to_real, hs]
    · simp [hξ0 y hy]
  · rw [happ]
    have hvv : ⟪v, v⟫_ℝ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    by_cases hy : y ∈ tsupport ξ
    · simp only [inner_add_left, inner_smul_left, inner_sub_left, RCLike.conj_to_real, hvv]
      have h1 : lam0 * ‖v‖ ^ 2 ≤ ⟪T y v, v⟫_ℝ := hlam0le y hy v
      obtain ⟨hξa, hξb⟩ := hξI y
      have hm1 : min lam0 1 ≤ lam0 := min_le_left _ _
      have hm2 : min lam0 1 ≤ 1 := min_le_right _ _
      have hv2 := sq_nonneg ‖v‖
      nlinarith [mul_nonneg hξa hv2, mul_nonneg (sub_nonneg.mpr hξb) hv2,
        mul_le_mul_of_nonneg_right hm1 hv2, mul_le_mul_of_nonneg_right hm2 hv2]
    · simp only [hξ0 y hy, zero_smul, add_zero, hvv]
      exact mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _)
  · calc ‖Tm y‖ ≤ ‖I‖ + ‖d y‖ := norm_add_le _ _
      _ ≤ 1 + Kd := add_le_add ContinuousLinearMap.norm_id_le (hKdb y)
  · have hxy : Tm y - Tm y' = d y - d y' := by simp [hTmdef]
    rw [hxy]
    exact (hKdl y y').trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · simp [hTmdef, hddef, hξ1 y hy, hI]

/-- A bounded map with `‖Φ a - Φ b‖ ≤ L (d + A d^r)` is `r`-Hölder in `d`. -/
theorem norm_sub_le_rpow_of_le {Z : Type*} [NormedAddCommGroup Z] {a b : Z} {B L A d r : ℝ}
    (hB : ‖a‖ ≤ B) (hB' : ‖b‖ ≤ B) (hL0 : 0 ≤ L) (hA : 0 ≤ A) (hd0 : 0 ≤ d) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (h : ‖a - b‖ ≤ L * (d + A * d ^ r)) :
    ‖a - b‖ ≤ (L * (1 + A) + 2 * B) * d ^ r := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hp0 : 0 ≤ d ^ r := Real.rpow_nonneg hd0 r
  rcases le_total d 1 with h1 | h1
  · have hle : d ≤ d ^ r := Real.self_le_rpow_of_le_one hd0 h1 hr1
    calc ‖a - b‖ ≤ L * (d + A * d ^ r) := h
      _ ≤ L * (d ^ r + A * d ^ r) := by gcongr
      _ ≤ (L * (1 + A) + 2 * B) * d ^ r := by nlinarith [mul_nonneg hB0 hp0]
  · have hge : 1 ≤ d ^ r := Real.one_le_rpow h1 hr0
    calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith
      _ ≤ 2 * B * d ^ r := le_mul_of_one_le_right (by positivity) hge
      _ ≤ (L * (1 + A) + 2 * B) * d ^ r := by
          nlinarith [mul_nonneg (mul_nonneg hL0 (by linarith : (0 : ℝ) ≤ 1 + A)) hp0]

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- `A ↦ A : Q` as a continuous linear functional. -/
def hessTraceLeft (Q : E →L[ℝ] E →L[ℝ] ℝ) : (E →L[ℝ] E) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun A => hessTrace b A Q
      map_add' := fun A A' => hessTrace_add_left b A A' Q
      map_smul' := fun c A => by rw [hessTrace_smul_left, smul_eq_mul, RingHom.id_apply] }
    (Fintype.card ι * ‖Q‖) (fun A => by
      rw [Real.norm_eq_abs]
      have := abs_hessTrace_le b A Q
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      nlinarith [norm_nonneg A, norm_nonneg Q])

@[simp]
theorem hessTraceLeft_apply (Q : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    hessTraceLeft b Q A = hessTrace b A Q := rfl

end Helpers

/-! ### `kfun` of a difference quotient -/

theorem kfun_diffQuot {r : ℝ≥0} (w : BoundedContDiffHolderMap 2 r (ComplexModel n) ℝ)
    (ζ : ComplexModel n) (h : ℝ) (x : ComplexModel n) :
    kfun (diffQuot (⇑w) ζ h) x = h⁻¹ • (kfun w (x + h • ζ) - kfun w x) := by
  have hw2 := WholeSpaceSolvability.contDiff_two w
  have hwd : Differentiable ℝ ⇑w := hw2.differentiable (by simp)
  have hDwd : Differentiable ℝ (fderiv ℝ ⇑w) :=
    (hw2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hD2 : fderiv ℝ (fderiv ℝ (diffQuot (⇑w) ζ h)) x = h⁻¹ •
      (fderiv ℝ (fderiv ℝ w) (x + h • ζ) - fderiv ℝ (fderiv ℝ w) x) := by
    rw [fderiv_diffQuot hwd, fderiv_diffQuot hDwd]
    rfl
  simp only [kfun, ComplexHessianDeterminant.complexHessian_eq_complexHessianOfBilin, hD2]
  funext j k
  simp only [kmat, SemiconcaveHessian.complexHessianOfBilin, Pi.smul_apply, Pi.sub_apply,
    _root_.smul_apply, _root_.sub_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-! ### The nonlinear difference-quotient step -/

section Step

variable {r : ℝ≥0} {U : Set (ComplexModel n)} {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}

/-- **One derivative more for the Monge–Ampère equation**: every directional derivative of a
`C^{2,r}` solution of `maLocal H (z, kfun u z) = f z` (`f ∈ C^{1,r}`, `H + complexHessian u > 0`) is
`C^{2,r}` near every point of `U`. -/
theorem holderAt_fderiv_apply_of_maLocal_eq (hr0 : 0 < r) (hr1 : r < 1) (hU : IsOpen U)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U) (hHp : ∀ z ∈ U, (H z).PosDef)
    {u f : ComplexModel n → ℝ} (hu : ∀ z ∈ U, HolderAt 2 r u z) (hf : ∀ z ∈ U, HolderAt 1 r f z)
    (hpos : ∀ z ∈ U, (H z + complexHessian u z).PosDef)
    (heq : ∀ z ∈ U, maLocal H (z, kfun u z) = f z) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ U)
    (ζ : ComplexModel n) : HolderAt 2 r (fun x => fderiv ℝ u x ζ) z₀ := by
  classical
  set b := realBasis (n := n) with hb
  have hr1' : r ≤ 1 := hr1.le
  have hrr0 : (0 : ℝ) ≤ r := r.coe_nonneg
  have hrr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hrr1 : (r : ℝ) ≤ 1 := by exact_mod_cast hr1'
  -- Step A: representatives on a ball
  obtain ⟨w, hw⟩ := hu z₀ hz₀
  obtain ⟨f₁, hf₁⟩ := hf z₀ hz₀
  have hev : ∀ᶠ y in 𝓝 z₀, y ∈ U ∧ f₁ y = f y ∧ (⇑w =ᶠ[𝓝 y] u) :=
    Filter.Eventually.and (hU.mem_nhds hz₀) (hf₁.and hw.eventually_nhds)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hw2 : ContDiff ℝ 2 ⇑w := WholeSpaceSolvability.contDiff_two w
  have hkfun : ∀ y ∈ ball z₀ ρ, kfun w y = kfun u y := fun y hy => by
    simp only [kfun, complexHessian_congr' (hρs y hy).2.2]
  have hA1 : ∀ y ∈ ball z₀ ρ, maLocal H (y, kfun w y) = f₁ y := fun y hy => by
    rw [hkfun y hy, (hρs y hy).2.1]; exact heq y (hρs y hy).1
  have hherm : ∀ y, hermPart (kfun w y) = complexHessian w y := fun y =>
    hermPart_kmat (isHermitian_complexHessian_of_contDiffAt hw2.contDiffAt)
  have hA2 : ∀ y ∈ ball z₀ ρ, (y, kfun w y) ∈ pdDomain H U := fun y hy => by
    refine ⟨(hρs y hy).1, ?_⟩
    show (H y + hermPart (kfun w y)).PosDef
    rw [hherm, complexHessian_congr' (hρs y hy).2.2]
    exact hpos y (hρs y hy).1
  -- Step B: the compact graph and a compact neighbourhood inside `pdDomain`
  set R : ℝ := ρ / 2 with hR
  have hRpos : 0 < R := by positivity
  set G := (fun y => (y, kfun w y)) '' closedBall z₀ R with hGdef
  have hGc : IsCompact G :=
    (isCompact_closedBall z₀ R).image (continuous_id.prodMk (continuous_kfun w))
  have hO : IsOpen (pdDomain H U) := isOpen_pdDomain hU hH fun z hz => (hHp z hz).isHermitian
  have hGO : G ⊆ pdDomain H U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hA2 y (closedBall_subset_ball (by linarith) hy)
  obtain ⟨N, hNc, hGN, hNO⟩ := exists_compact_between hGc hO hGO
  obtain ⟨η, hη, hηN⟩ := hGc.exists_cthickening_subset_open isOpen_interior hGN
  -- Step C: global models of the coefficient and of `∂_z maLocal ζ`
  have hT := contDiffOn_lapCoeffField hU hH
  obtain ⟨Tm, lam, Λ, hlam, hΛ, hTmc, hTms, hTme, hTmb, hTml, hTmN⟩ := exists_ellipticModel hO hNc
    hNO hT (fun p hp u v => lapCoeff_symm hp.2.isHermitian u v)
    (fun p hp u hu => lapCoeff_pos hp.2 hu)
  have hmaD : pdDomain H U ⊆ maDomain H U := pdDomain_subset_maDomain hHp
  have hma : ContDiffOn ℝ ∞ (maLocal H) (pdDomain H U) := (contDiffOn_maLocal hH).mono hmaD
  have hβ : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (maLocal H) p (ζ, 0)) (pdDomain H U) :=
    (hma.fderiv_of_isOpen hO (m := ∞) le_rfl).clm_apply contDiffOn_const
  obtain ⟨ξ, hξs, hξc, hξO, hξ1, -⟩ := KahlerLaplacianChart.exists_cutoff hNc hO hNO
  set βm : ComplexModel n × (Fin n → Fin n → ℂ) → ℝ :=
    fun p => ξ p • fderiv ℝ (maLocal H) p (ζ, 0) with hβmdef
  have hβms : ContDiff ℝ ∞ βm := contDiff_smul_of_tsupport hO hξs hξO hβ
  have hβmc : HasCompactSupport βm := hξc.smul_right
  obtain ⟨Kβ, hKβ0, hKβb, hKβl⟩ :=
    HolderGerm.exists_lipschitz_of_hasCompactSupport (hβms.of_le (by exact_mod_cast le_top)) hβmc
  -- Step D: the segment `p_s` stays in `N` for small `h`
  set pp : ℝ → ℝ → ComplexModel n → ComplexModel n × (Fin n → Fin n → ℂ) := fun h s x =>
    (x, kfun w x) + s • ((h • ζ, kfun w (x + h • ζ) - kfun w x) :
      ComplexModel n × (Fin n → Fin n → ℂ)) with hppdef
  have hKh : ∀ y y', ‖kfun w y - kfun w y'‖ ≤ ‖w‖ * ‖y - y'‖ ^ (r : ℝ) := norm_kfun_holder w
  have hlim : Tendsto (fun h : ℝ => 2 * ‖w‖ * (|h| * ‖ζ‖) ^ (r : ℝ)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ => 2 * ‖w‖ * (|h| * ‖ζ‖) ^ (r : ℝ)) :=
      continuous_const.mul ((continuous_abs.mul continuous_const).rpow_const fun _ => Or.inr hrr0)
    have := hc.tendsto 0
    simpa [Real.zero_rpow hrr0'.ne'] using this
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.mp (hlim.eventually (gt_mem_nhds hη))
  set h₀ : ℝ := min (δ / 2) (R / (2 * (‖ζ‖ + 1))) with hh₀def
  have hh₀ : 0 < h₀ := lt_min (by positivity) (by positivity)
  have hhζ : ∀ h, 0 < h → h ≤ h₀ → h * ‖ζ‖ ≤ R / 2 := by
    intro h hh hhh
    have h1 : h ≤ R / (2 * (‖ζ‖ + 1)) := hhh.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg ζ]
  have hsmall : ∀ h, 0 < h → h ≤ h₀ → 2 * ‖w‖ * (h * ‖ζ‖) ^ (r : ℝ) < η := by
    intro h hh hhh
    have h1 : dist h 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hh]
      linarith [min_le_left (δ / 2) (R / (2 * (‖ζ‖ + 1)))]
    have := hδs h1
    rwa [abs_of_pos hh] at this
  have hpp1 : ∀ h s x, (pp h s x).1 = x + (s * h) • ζ := by
    intros; simp [hppdef, mul_smul]
  have hpp2 : ∀ h s x, (pp h s x).2 = kfun w x + s • (kfun w (x + h • ζ) - kfun w x) := by
    intros; simp [hppdef]
  have hseg : ∀ h, 0 < h → h ≤ h₀ → ∀ x ∈ closedBall z₀ (R / 2), ∀ s ∈ Icc (0 : ℝ) 1,
      pp h s x ∈ interior N := by
    intro h hh hhh x hx s hs
    apply hηN
    have hsh : ‖(s * h) • ζ‖ ≤ h * ‖ζ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hs.1 hh.le)]
      have : s * h ≤ h := by nlinarith [hs.2]
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hxs : x + (s * h) • ζ ∈ closedBall z₀ R := by
      rw [mem_closedBall, dist_eq_norm, add_sub_right_comm]
      have := hhζ h hh hhh
      rw [mem_closedBall, dist_eq_norm] at hx
      linarith [norm_add_le (x - z₀) ((s * h) • ζ)]
    refine Metric.mem_cthickening_of_dist_le _ (x + (s * h) • ζ, kfun w (x + (s * h) • ζ)) _ _
      ⟨_, hxs, rfl⟩ ?_
    rw [Prod.dist_eq, hpp1, hpp2, dist_self, dist_eq_norm]
    refine max_le hη.le ?_
    have e1 : ‖s • (kfun w (x + h • ζ) - kfun w x)‖ ≤ ‖w‖ * (h * ‖ζ‖) ^ (r : ℝ) := by
      rw [norm_smul, Real.norm_of_nonneg hs.1]
      have h2 := hKh (x + h • ζ) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh.le] at h2
      calc s * ‖kfun w (x + h • ζ) - kfun w x‖ ≤ 1 * ‖kfun w (x + h • ζ) - kfun w x‖ :=
            mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ ≤ ‖w‖ * (h * ‖ζ‖) ^ (r : ℝ) := by rw [one_mul]; exact h2
    have e2 : ‖kfun w x - kfun w (x + (s * h) • ζ)‖ ≤ ‖w‖ * (h * ‖ζ‖) ^ (r : ℝ) := by
      refine (hKh x (x + (s * h) • ζ)).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [sub_add_cancel_left, norm_neg]
      exact Real.rpow_le_rpow (norm_nonneg _) hsh hrr0
    have e3 := hsmall h hh hhh
    calc ‖kfun w x + s • (kfun w (x + h • ζ) - kfun w x) - kfun w (x + (s * h) • ζ)‖
        = ‖s • (kfun w (x + h • ζ) - kfun w x) + (kfun w x - kfun w (x + (s * h) • ζ))‖ := by
          congr 1; abel
      _ ≤ ‖s • (kfun w (x + h • ζ) - kfun w x)‖ + ‖kfun w x - kfun w (x + (s * h) • ζ)‖ :=
          norm_add_le _ _
      _ ≤ η := by linarith
  -- Step E: the averaged coefficient and the right-hand side
  have hppc : ∀ h x, Continuous fun s => pp h s x := fun h x =>
    continuous_const.add (continuous_id.smul continuous_const)
  set a : ℝ → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n :=
    fun h x => ∫ s in (0 : ℝ)..1, Tm (pp h s x) with hadef
  set g : ℝ → ComplexModel n → ℝ :=
    fun h x => diffQuot (⇑f₁) ζ h x - ∫ s in (0 : ℝ)..1, βm (pp h s x) with hgdef
  have hint : ∀ h x, IntervalIntegrable (fun s => Tm (pp h s x)) MeasureTheory.volume 0 1 :=
    fun h x => (hTmc.comp (hppc h x)).intervalIntegrable 0 1
  have hintβ : ∀ h x, IntervalIntegrable (fun s => βm (pp h s x)) MeasureTheory.volume 0 1 :=
    fun h x => (hβms.continuous.comp (hppc h x)).intervalIntegrable 0 1
  have hpp_sub : ∀ h s x y, s ∈ Icc (0 : ℝ) 1 →
      ‖pp h s x - pp h s y‖ ≤ ‖x - y‖ + ‖w‖ * ‖x - y‖ ^ (r : ℝ) := by
    intro h s x y hs
    have hp0 : 0 ≤ ‖w‖ * ‖x - y‖ ^ (r : ℝ) := by positivity
    rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, hpp1, hpp1, hpp2, hpp2]
    refine max_le (by rw [add_sub_add_right_eq_sub]; linarith) ?_
    have e : kfun w x + s • (kfun w (x + h • ζ) - kfun w x) -
        (kfun w y + s • (kfun w (y + h • ζ) - kfun w y)) =
        (1 - s) • (kfun w x - kfun w y) + s • (kfun w (x + h • ζ) - kfun w (y + h • ζ)) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
      Real.norm_of_nonneg hs.1]
    have h1 := hKh x y
    have h2 := hKh (x + h • ζ) (y + h • ζ)
    rw [add_sub_add_right_eq_sub] at h2
    have e1 := mul_le_mul_of_nonneg_left h1 (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
    have e2 := mul_le_mul_of_nonneg_left h2 hs.1
    have e3 : (1 - s) * (‖w‖ * ‖x - y‖ ^ (r : ℝ)) + s * (‖w‖ * ‖x - y‖ ^ (r : ℝ)) =
        ‖w‖ * ‖x - y‖ ^ (r : ℝ) := by ring
    linarith [norm_nonneg (x - y)]
  have hmemI : ∀ s ∈ Ι (0 : ℝ) 1, s ∈ Icc (0 : ℝ) 1 := fun s hs => by
    rw [Set.uIoc_of_le zero_le_one] at hs
    exact ⟨hs.1.le, hs.2⟩
  have hinner : ∀ h x u v, ⟪v, a h x u⟫_ℝ = ∫ s in (0 : ℝ)..1, ⟪v, Tm (pp h s x) u⟫_ℝ := by
    intro h x u v
    have := ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ (ComplexModel n) u)
      ).intervalIntegral_comp_comm (hint h x)
    simpa [hadef] using this.symm
  set Λ' : ℝ := Λ * (1 + ‖w‖) + 2 * Λ + Λ with hΛ'def
  have ha_ell : ∀ h, IsEllipticCoeff (a h) lam Λ' r := by
    intro h
    refine ⟨fun x u v => ?_, fun x v => ?_, fun x => ?_, fun x y => ?_⟩
    · have e1 : ⟪a h x u, v⟫_ℝ = ⟪v, a h x u⟫_ℝ := real_inner_comm _ _
      rw [e1, hinner, hinner h x v u]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [real_inner_comm, hTms]
    · rw [real_inner_comm, hinner]
      have h1 : ∫ s in (0 : ℝ)..1, lam * ‖v‖ ^ 2 = lam * ‖v‖ ^ 2 := by simp
      rw [← h1]
      refine intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const ?_
        fun s _ => ?_
      · exact (continuous_const.inner ((hTmc.comp (hppc h x)).clm_apply continuous_const)
          ).intervalIntegrable 0 1
      · rw [real_inner_comm]; exact hTme _ v
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (f := fun s => Tm (pp h s x)) (fun s _ => hTmb _)
      simp only [sub_zero, abs_one, mul_one] at this
      exact this.trans (by rw [hΛ'def]; nlinarith [norm_nonneg w])
    · show ‖(∫ s in (0 : ℝ)..1, Tm (pp h s x)) - ∫ s in (0 : ℝ)..1, Tm (pp h s y)‖ ≤ _
      rw [← intervalIntegral.integral_sub (hint h x) (hint h y)]
      have hb : ∀ s ∈ Ι (0 : ℝ) 1, ‖Tm (pp h s x) - Tm (pp h s y)‖ ≤
          (Λ * (1 + ‖w‖) + 2 * Λ) * ‖x - y‖ ^ (r : ℝ) := fun s hs =>
        norm_sub_le_rpow_of_le (hTmb _) (hTmb _) hΛ (norm_nonneg w) (norm_nonneg _) hrr0 hrr1
          ((hTml _ _).trans (mul_le_mul_of_nonneg_left (hpp_sub h s x y (hmemI s hs)) hΛ))
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      simp only [sub_zero, abs_one, mul_one] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
      rw [hΛ'def]; linarith
  have hf₁d : Differentiable ℝ ⇑f₁ := differentiable_of_one f₁
  set M : ℝ := 3 * ‖f₁‖ * ‖ζ‖ + Kβ + (Kβ * (1 + ‖w‖) + 2 * Kβ) with hMdef
  have hgb : ∀ h, 0 < h → h ≤ h₀ → ∀ x, |g h x| ≤ M := by
    intro h hh _ x
    have e1 : |diffQuot (⇑f₁) ζ h x| ≤ ‖f₁‖ * ‖ζ‖ := by
      rw [← Real.norm_eq_abs]; exact norm_diffQuot_le hf₁d (norm_fderiv_le_of_one f₁) ζ hh.ne' x
    have e2 : |∫ s in (0 : ℝ)..1, βm (pp h s x)| ≤ Kβ := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (f := fun s => βm (pp h s x)) (fun s _ => hKβb _)
      simpa using this
    simp only [hgdef]
    refine (abs_sub _ _).trans ?_
    rw [hMdef]
    nlinarith [mul_nonneg (norm_nonneg f₁) (norm_nonneg ζ), mul_nonneg hKβ0 (norm_nonneg w)]
  have hgh : ∀ h, 0 < h → h ≤ h₀ → ∀ x y, |g h x - g h y| ≤ M * ‖x - y‖ ^ (r : ℝ) := by
    intro h hh _ x y
    have hp0 : 0 ≤ ‖x - y‖ ^ (r : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have e1 : |diffQuot (⇑f₁) ζ h x - diffQuot (⇑f₁) ζ h y| ≤
        2 * ‖f₁‖ * ‖x - y‖ ^ (r : ℝ) * ‖ζ‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_diffQuot_sub_le hf₁d (norm_fderiv_sub_le_of_one hr1' f₁) ζ hh.ne' x y
    have e2 : |(∫ s in (0 : ℝ)..1, βm (pp h s x)) - ∫ s in (0 : ℝ)..1, βm (pp h s y)| ≤
        (Kβ * (1 + ‖w‖) + 2 * Kβ) * ‖x - y‖ ^ (r : ℝ) := by
      rw [← intervalIntegral.integral_sub (hintβ h x) (hintβ h y), ← Real.norm_eq_abs]
      have hb : ∀ s ∈ Ι (0 : ℝ) 1, ‖βm (pp h s x) - βm (pp h s y)‖ ≤
          (Kβ * (1 + ‖w‖) + 2 * Kβ) * ‖x - y‖ ^ (r : ℝ) := fun s hs =>
        norm_sub_le_rpow_of_le (hKβb _) (hKβb _) hKβ0 (norm_nonneg w) (norm_nonneg _) hrr0 hrr1
          ((hKβl _ _).trans (mul_le_mul_of_nonneg_left (hpp_sub h s x y (hmemI s hs)) hKβ0))
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      simpa using this
    simp only [hgdef]
    rw [show ∀ A B C D : ℝ, A - B - (C - D) = (A - C) - (B - D) from fun _ _ _ _ => by ring]
    refine (abs_sub _ _).trans ?_
    rw [hMdef]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg f₁) (norm_nonneg ζ)) hp0]
  -- the equation for the difference quotients
  obtain ⟨θ, hθs, hθc, hθU, hθ1⟩ :=
    exists_cutoff_nhds (ball_mem_nhds z₀ (by positivity : 0 < R / 2))
  have heqh : ∀ h, 0 < h → h ≤ h₀ → ∀ x ∈ tsupport θ,
      hessTrace b (a h x) (fderiv ℝ (fderiv ℝ (diffQuot (⇑w) ζ h)) x) = g h x := by
    intro h hh hhh x hx
    have hxB : x ∈ closedBall z₀ (R / 2) := ball_subset_closedBall (hθU hx)
    set Q := fderiv ℝ (fderiv ℝ (diffQuot (⇑w) ζ h)) x with hQ
    set Δ : ComplexModel n × (Fin n → Fin n → ℂ) := (h • ζ, kfun w (x + h • ζ) - kfun w x)
      with hΔ
    have hpN : ∀ s ∈ Icc (0 : ℝ) 1, pp h s x ∈ N := fun s hs =>
      interior_subset (hseg h hh hhh x hxB s hs)
    have hdq2 : ContDiffAt ℝ 2 (diffQuot (⇑w) ζ h) x := by
      rw [← coe_diffQuotMap]; exact (WholeSpaceSolvability.contDiff_two _).contDiffAt
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, fderiv ℝ (maLocal H) (pp h s x) Δ =
        h * βm (pp h s x) + h * hessTrace b (Tm (pp h s x)) Q := by
      intro s hs
      have hpO : pp h s x ∈ pdDomain H U := hNO (hpN s hs)
      have hdecomp : Δ = h • ((ζ, 0) : ComplexModel n × (Fin n → Fin n → ℂ)) +
          ((0 : ComplexModel n), h • kfun (diffQuot (⇑w) ζ h) x) := by
        rw [kfun_diffQuot, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
        simp [hΔ]
      have hL : fderiv ℝ (maLocal H) (pp h s x)
          ((0 : ComplexModel n), h • kfun (diffQuot (⇑w) ζ h) x) =
          h * fderiv ℝ (maLocal H) (pp h s x) ((0 : ComplexModel n), kfun (diffQuot (⇑w) ζ h) x) := by
        rw [← smul_eq_mul, ← map_smul]
        simp
      rw [hdecomp, map_add, map_smul, smul_eq_mul, hL,
        fderiv_maLocal_apply hU hH (hmaD hpO) hpO.2.isHermitian,
        show kfun (diffQuot (⇑w) ζ h) x = kmat (complexHessian (diffQuot (⇑w) ζ h) x) from rfl,
        hermPart_kmat (isHermitian_complexHessian_of_contDiffAt hdq2),
        re_trace_inv_mul_complexHessian b, ← hTmN _ (hpN s hs)]
      simp only [hβmdef, hξ1 _ (hpN s hs), one_smul]
      rfl
    have hFTC : ∫ s in (0 : ℝ)..1, (h * βm (pp h s x) + h * hessTrace b (Tm (pp h s x)) Q) =
        maLocal H (pp h 1 x) - maLocal H (pp h 0 x) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => maLocal H (pp h s x))
        (f' := fun s => h * βm (pp h s x) + h * hessTrace b (Tm (pp h s x)) Q) (fun s hs => ?_) ?_
      · rw [Set.uIcc_of_le zero_le_one] at hs
        have hpO := hNO (hpN s hs)
        have hd : HasFDerivAt (maLocal H) (fderiv ℝ (maLocal H) (pp h s x)) (pp h s x) :=
          ((hma.contDiffAt (hO.mem_nhds hpO)).differentiableAt (by simp)).hasFDerivAt
        have hl : HasDerivAt (fun s => pp h s x) Δ s := by
          have := ((hasDerivAt_id s).smul_const Δ).const_add
            ((x, kfun w x) : ComplexModel n × (Fin n → Fin n → ℂ))
          simpa [hppdef, hΔ] using this
        have := hd.comp_hasDerivAt s hl
        rw [hderiv s hs] at this
        exact this
      · exact ((continuous_const.mul (hβms.continuous.comp (hppc h x))).add
          (continuous_const.mul ((hessTraceLeft b Q).continuous.comp
            (hTmc.comp (hppc h x))))).intervalIntegrable 0 1
    have hsplit : ∫ s in (0 : ℝ)..1, (h * βm (pp h s x) + h * hessTrace b (Tm (pp h s x)) Q) =
        h * (∫ s in (0 : ℝ)..1, βm (pp h s x)) + h * hessTrace b (a h x) Q := by
      have hi1 : IntervalIntegrable (fun s => h * βm (pp h s x)) MeasureTheory.volume 0 1 :=
        (hintβ h x).const_mul h
      have hi2 : IntervalIntegrable (fun s => h * hessTrace b (Tm (pp h s x)) Q)
          MeasureTheory.volume 0 1 :=
        (continuous_const.mul ((hessTraceLeft b Q).continuous.comp
          (hTmc.comp (hppc h x)))).intervalIntegrable 0 1
      rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      congr 2
      have := (hessTraceLeft b Q).intervalIntegral_comp_comm (hint h x)
      simpa [hadef] using this
    have hp1 : pp h 1 x = (x + h • ζ, kfun w (x + h • ζ)) := by simp [hppdef]
    have hp0 : pp h 0 x = (x, kfun w x) := by simp [hppdef]
    have hx1 : x ∈ ball z₀ ρ := ball_subset_ball (by linarith) (hθU hx)
    have hx2 : x + h • ζ ∈ ball z₀ ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_right_comm]
      have h1 := hhζ h hh hhh
      have h2 : ‖h • ζ‖ = h * ‖ζ‖ := by rw [norm_smul, Real.norm_of_nonneg hh.le]
      have h3 : ‖x - z₀‖ < R / 2 := by rw [← dist_eq_norm]; exact hθU hx
      linarith [norm_add_le (x - z₀) (h • ζ)]
    rw [hsplit, hp1, hp0, hA1 _ hx2, hA1 _ hx1] at hFTC
    simp only [hgdef, diffQuot, smul_eq_mul]
    field_simp
    linarith
  -- Step F: the difference-quotient lemma
  obtain ⟨W, hW⟩ := exists_mul_fderiv_mem b hlam hr0 hr1 w hθs hθc ζ hh₀ a g
    (fun h _ _ => ha_ell h) hgb hgh heqh
  refine ⟨W, ?_⟩
  filter_upwards [hθ1, hw.fderiv (𝕜 := ℝ)] with x hx1 hx2
  rw [hW, hx1, one_mul, hx2]

/-- **The first regularity step for the Monge–Ampère equation**: a `C^{2,r}` solution of
`maLocal H (z, kfun u z) = f z` on `U` (`H` smooth and positive definite, `H + complexHessian u`
positive definite, `f ∈ C^{1,r}`, `0 < r < 1`) is `C^{3,r}` near every point of `U`. -/
theorem holderAt_three_of_maLocal_eq (hr0 : 0 < r) (hr1 : r < 1) (hU : IsOpen U)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U) (hHp : ∀ z ∈ U, (H z).PosDef)
    {u f : ComplexModel n → ℝ} (hu : ∀ z ∈ U, HolderAt 2 r u z) (hf : ∀ z ∈ U, HolderAt 1 r f z)
    (hpos : ∀ z ∈ U, (H z + complexHessian u z).PosDef)
    (heq : ∀ z ∈ U, maLocal H (z, kfun u z) = f z) : ∀ z ∈ U, HolderAt 3 r u z := by
  intro z hz
  have hD : HolderAt 2 r (fderiv ℝ u) z :=
    HolderAt.fderiv_of_apply hr1.le (realBasis (n := n)).toBasis fun i => by
      simpa using holderAt_fderiv_apply_of_maLocal_eq hr0 hr1 hU hH hHp hu hf hpos heq hz
        (realBasis i)
  exact (hu z hz).of_fderiv hr1.le hD ((hu z hz).eventually_differentiableAt (by norm_num))

end Step


end SGPT.Foundations.Analysis.Pending.MongeAmpereRegularity

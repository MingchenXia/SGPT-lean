import SGPT.Foundations.Analysis.Pending.DifferenceQuotientRegularity
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Interior regularity for linear elliptic equations `a : D²v = g` with Hölder coefficients

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`, `0 < r < 1`,
`U ⊆ E` open, and `a : E → (E →L[ℝ] E)` symmetric and positive definite at every point of `U`.

**Main result** `holderAt_of_hessTrace_eq` (blueprint `bou:schauder-global`, regularity clause; the
linear step of the regularity bootstrap): for `k ≥ 1`, if `a` and `g` are `C^{k,r}` near every point
of `U`, `v` is `C^{k+1,r}` near every point of `U` and `a : D²v = g` on `U` (`hessTrace b`), then `v`
is `C^{k+2,r}` near every point of `U`.

* `k = 1` (`holderAt_fderiv_apply_of_hessTrace_eq`, `holderAt_three_of_hessTrace_eq`): the difference
  quotient `D_h v` solves `a : D²(D_h v) = D_h g - (D_h a) : D²v(· + hζ)` (discrete product rule),
  whose right-hand side is bounded and `r`-Hölder uniformly in `h` since `a, g ∈ C^{1,r}`;
  `DifferenceQuotient.exists_mul_fderiv_mem` with a whole-space Schauder-class extension of `a`
  (`exists_ellipticExtension`) gives `∂_ζ v ∈ C^{2,r}`.
* `k → k + 1`: `w = ∂_ζ v` solves `a : D²w = ∂_ζ g - (∂_ζ a) : D²v` (`hessTrace_fderiv_apply_eq`,
  symmetry of third derivatives), with right-hand side in `C^{k,r}`.

TN.4 B5, regularity bootstrap (the proof of Yau's theorem, P2, R2).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff InnerProductSpace

namespace SGPT.Foundations.Analysis.Pending.LinearRegularity

open EllipticMeanValue SchauderBlowup SchauderWholeSpace ManifoldSchauder WholeSpaceSolvability
  HolderGerm DifferenceQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-! ### `hessTrace` as a continuous bilinear map -/

theorem hessTrace_add_left (A A' : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    hessTrace b (A + A') Q = hessTrace b A Q + hessTrace b A' Q := by
  simp [hessTrace, Finset.sum_add_distrib]

theorem hessTrace_smul_left (c : ℝ) (A : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    hessTrace b (c • A) Q = c * hessTrace b A Q := by
  simp [hessTrace, Finset.mul_sum]

/-- `A : Q = ∑ᵢⱼ ⟪bⱼ, A bᵢ⟫ Q(bᵢ, bⱼ)`. -/
theorem hessTrace_eq_sum (A : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    hessTrace b A Q = ∑ i, ∑ j, ⟪b j, A (b i)⟫_ℝ * Q (b i) (b j) := by
  simp only [hessTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← b.sum_repr' (A (b i))]
  rw [map_sum]
  simp [smul_eq_mul]

/-! ### Bounds for `C^{0,r}_b` and `C^{1,r}_b` maps -/

section Bounds

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {r : ℝ≥0}

theorem norm_sub_le_of_zero (hr : r ≤ 1) (g : BoundedContDiffHolderMap 0 r E F) (x y : E) :
    ‖g x - g y‖ ≤ 2 * ‖g‖ * ‖x - y‖ ^ (r : ℝ) := by
  have h := (g.holderWith_iteratedFDeriv hr (le_refl 0)).dist_le x y
  rw [iteratedFDeriv_zero_eq_comp, comp_apply, comp_apply, LinearIsometryEquiv.dist_map] at h
  simpa [dist_eq_norm] using h

theorem norm_fderiv_le_of_one (f : BoundedContDiffHolderMap 1 r E F) (x : E) :
    ‖fderiv ℝ f x‖ ≤ ‖f‖ :=
  (f.fderivMap.norm_apply_le x).trans (BoundedContDiffHolderMap.norm_fderivMap_le f)

theorem norm_fderiv_sub_le_of_one (hr : r ≤ 1) (f : BoundedContDiffHolderMap 1 r E F) (x y : E) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ 2 * ‖f‖ * ‖x - y‖ ^ (r : ℝ) := by
  have h := norm_sub_le_of_zero hr f.fderivMap x y
  simp only [BoundedContDiffHolderMap.coe_fderivMap] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
  linarith [BoundedContDiffHolderMap.norm_fderivMap_le f]

theorem differentiable_of_one (f : BoundedContDiffHolderMap 1 r E F) : Differentiable ℝ f :=
  f.contDiff.differentiable (by simp)

end Bounds

section Partials

variable {r : ℝ≥0} {k : ℕ} {z : E}

/-- The second partial derivatives of a `C^{k+2,r}` germ are `C^{k,r}` germs. -/
theorem holderAt_second_partial (hr : r ≤ 1) {v : E → ℝ} (hv : HolderAt (k + 2) r v z)
    (p q : E) : HolderAt k r (fun x => fderiv ℝ (fderiv ℝ v) x p q) z := by
  have h1 : HolderAt (k + 1) r (fun x => fderiv ℝ v x q) z :=
    hv.derivative.clm hr (ContinuousLinearMap.apply ℝ ℝ q)
  have h2 : HolderAt k r (fun x => fderiv ℝ (fun y => fderiv ℝ v y q) x p) z :=
    h1.derivative.clm hr (ContinuousLinearMap.apply ℝ ℝ p)
  refine h2.congr ?_
  filter_upwards [hv.eventually] with x hx
  have hDv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hx.contDiffAt.fderiv_right (m := 1) (by exact_mod_cast (by omega : 1 + 1 ≤ k + 2))
      ).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hDv (differentiableAt_const q)]
  simp

/-- The coefficients `⟪bⱼ, M x bᵢ⟫` of a `C^{k,r}` germ of operators are `C^{k,r}` germs. -/
theorem holderAt_coeff (hr : r ≤ 1) {M : E → E →L[ℝ] E} (hM : HolderAt k r M z) (i j : ι) :
    HolderAt k r (fun x => ⟪b j, M x (b i)⟫_ℝ) z :=
  hM.clm hr ((innerSL ℝ (b j)).comp (ContinuousLinearMap.apply ℝ E (b i)))

/-- `x ↦ M x : D²v x` is a `C^{k,r}` germ if `M` is `C^{k,r}` and `v` is `C^{k+2,r}`. -/
theorem holderAt_hessTrace (hr : r ≤ 1) {M : E → E →L[ℝ] E} (hM : HolderAt k r M z)
    {v : E → ℝ} (hv : HolderAt (k + 2) r v z) :
    HolderAt k r (fun x => hessTrace b (M x) (fderiv ℝ (fderiv ℝ v) x)) z := by
  have h : HolderAt k r (fun x => ∑ i, ∑ j, ⟪b j, M x (b i)⟫_ℝ *
      fderiv ℝ (fderiv ℝ v) x (b i) (b j)) z :=
    HolderAt.sum _ fun i _ => HolderAt.sum _ fun j _ =>
      (holderAt_coeff b hr hM i j).mul hr (holderAt_second_partial hr hv (b i) (b j))
  exact h.congr (Eventually.of_forall fun x => (hessTrace_eq_sum b _ _).symm)

end Partials

/-! ### Uniform positivity on compact sets and whole-space elliptic extensions -/

/-- A continuous field of positive definite operators is uniformly positive on a compact set. -/
theorem exists_inner_ge {T : E → E →L[ℝ] E} {K : Set E} (hK : IsCompact K)
    (hT : ContinuousOn T K) (hpos : ∀ x ∈ K, ∀ v, v ≠ 0 → 0 < ⟪T x v, v⟫_ℝ) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ K, ∀ v, lam * ‖v‖ ^ 2 ≤ ⟪T x v, v⟫_ℝ := by
  set S := K ×ˢ sphere (0 : E) 1 with hSdef
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun p : E × E => ⟪T p.1 p.2, p.2⟫_ℝ) S := by
    have h1 : ContinuousOn (fun p : E × E => T p.1) S :=
      hT.comp continuousOn_fst fun p hp => hp.1
    exact (h1.clm_apply continuousOn_snd).inner continuousOn_snd
  have hscale : ∀ x v, v ≠ 0 → ⟪T x v, v⟫_ℝ = ‖v‖ ^ 2 * ⟪T x (‖v‖⁻¹ • v), ‖v‖⁻¹ • v⟫_ℝ := by
    intro x v hv
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    field_simp
  have hmem : ∀ x ∈ K, ∀ v : E, v ≠ 0 → (x, ‖v‖⁻¹ • v) ∈ S := by
    intro x hx v hv
    refine ⟨hx, ?_⟩
    simp [norm_smul, norm_ne_zero_iff.mpr hv]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · have := hmem x hx v hv
      rw [hSe] at this
      exact this.elim
  · obtain ⟨p, hpS, hpmin⟩ := hS.exists_isMinOn hSne hcont
    have hp2 : p.2 ≠ 0 := by
      intro h0
      have := hpS.2
      rw [h0] at this
      simp at this
    refine ⟨⟪T p.1 p.2, p.2⟫_ℝ, hpos p.1 hpS.1 p.2 hp2, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · have h := hpmin (hmem x hx v hv)
      simp only [Set.mem_ofPred_eq] at h
      rw [hscale x v hv, mul_comm]
      exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **Whole-space extension of an elliptic coefficient**: a bounded Lipschitz field `a`, symmetric
and positive definite on an open `V ⊇ K` (`K` compact), agrees on `K` with a coefficient in the
Schauder class (`â = id + ξ (a - id)`, `ξ` a cut-off). -/
theorem exists_ellipticExtension {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : E → E →L[ℝ] E} {B : ℝ}
    (hab : ∀ x, ‖a x‖ ≤ B) (hal : ∀ x y, ‖a x - a y‖ ≤ B * ‖x - y‖) {K V : Set E}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hsymm : ∀ x ∈ V, ∀ u w, ⟪a x u, w⟫_ℝ = ⟪u, a x w⟫_ℝ)
    (hpos : ∀ x ∈ V, ∀ u, u ≠ 0 → 0 < ⟪a x u, u⟫_ℝ) :
    ∃ (lam Λ : ℝ) (â : E → E →L[ℝ] E), 0 < lam ∧ IsEllipticCoeff â lam Λ r ∧
      ∀ x ∈ K, â x = a x := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hab 0)
  obtain ⟨ξ, hξs, hξc, hξV, hξ1, hξI⟩ := KahlerLaplacianChart.exists_cutoff hK hV hKV
  obtain ⟨Lξ, hLξ0, -, hLξ⟩ := HolderGerm.exists_lipschitz_of_hasCompactSupport
    (hξs.of_le (by exact_mod_cast le_top)) hξc
  have hac : Continuous a := by
    refine LipschitzWith.continuous (K := B.toNNReal) (LipschitzWith.of_dist_le_mul fun x y => ?_)
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hB]
    exact hal x y
  obtain ⟨lam0, hlam0, hlam0le⟩ :=
    exists_inner_ge hξc.isCompact hac.continuousOn fun x hx => hpos x (hξV hx)
  have hξ0 : ∀ x, x ∉ tsupport ξ → ξ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  set I := ContinuousLinearMap.id ℝ E with hI
  set d : E → E →L[ℝ] E := fun x => ξ x • (a x - I) with hddef
  set â : E → E →L[ℝ] E := fun x => I + d x with hâdef
  have happ : ∀ x v, â x v = v + ξ x • (a x v - v) := by
    intro x v
    simp [hâdef, hddef, hI]
  have hnI : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hdb : ∀ x, ‖d x‖ ≤ B + 1 := by
    intro x
    rw [hddef]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hξI x).1]
    calc ξ x * ‖a x - I‖ ≤ 1 * ‖a x - I‖ :=
          mul_le_mul_of_nonneg_right (hξI x).2 (norm_nonneg _)
      _ ≤ B + 1 := by rw [one_mul]; exact (norm_sub_le _ _).trans (add_le_add (hab x) hnI)
  have hdl : ∀ x y, ‖d x - d y‖ ≤ (Lξ * (B + 1) + B) * ‖x - y‖ := by
    intro x y
    have e : d x - d y = (ξ x - ξ y) • (a x - I) + ξ y • (a x - a y) := by
      simp only [hddef, sub_smul, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hξI y).1]
    have h1 : |ξ x - ξ y| ≤ Lξ * ‖x - y‖ := by rw [← Real.norm_eq_abs]; exact hLξ x y
    have h2 : ‖a x - I‖ ≤ B + 1 := (norm_sub_le _ _).trans (add_le_add (hab x) hnI)
    have h3 : ξ y * ‖a x - a y‖ ≤ 1 * (B * ‖x - y‖) :=
      mul_le_mul (hξI y).2 (hal x y) (norm_nonneg _) zero_le_one
    have h4 : |ξ x - ξ y| * ‖a x - I‖ ≤ Lξ * ‖x - y‖ * (B + 1) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    nlinarith [norm_nonneg (x - y)]
  set Λ : ℝ := (Lξ * (B + 1) + B) + 2 * (B + 1) + 1 with hΛdef
  refine ⟨min lam0 1, Λ, â, lt_min hlam0 one_pos, ⟨?_, ?_, ?_, ?_⟩, fun x hx => ?_⟩
  · intro x u v
    rw [happ, happ]
    by_cases hx : x ∈ tsupport ξ
    · have hs := hsymm x (hξV hx) u v
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, RCLike.conj_to_real, hs]
    · simp [hξ0 x hx]
  · intro x v
    rw [happ]
    have hvv : ⟪v, v⟫_ℝ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    by_cases hx : x ∈ tsupport ξ
    · simp only [inner_add_left, inner_smul_left, inner_sub_left, RCLike.conj_to_real, hvv]
      have h1 : lam0 * ‖v‖ ^ 2 ≤ ⟪a x v, v⟫_ℝ := hlam0le x hx v
      obtain ⟨hξa, hξb⟩ := hξI x
      have hm1 : min lam0 1 ≤ lam0 := min_le_left _ _
      have hm2 : min lam0 1 ≤ 1 := min_le_right _ _
      have hv2 := sq_nonneg ‖v‖
      nlinarith [mul_nonneg hξa hv2, mul_nonneg (sub_nonneg.mpr hξb) hv2,
        mul_le_mul_of_nonneg_right hm1 hv2, mul_le_mul_of_nonneg_right hm2 hv2]
    · simp only [hξ0 x hx, zero_smul, add_zero, hvv]
      exact mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _)
  · intro x
    calc ‖â x‖ ≤ ‖I‖ + ‖d x‖ := norm_add_le _ _
      _ ≤ 1 + (B + 1) := add_le_add hnI (hdb x)
      _ ≤ Λ := by rw [hΛdef]; nlinarith [mul_nonneg hLξ0 (by linarith : (0 : ℝ) ≤ B + 1)]
  · intro x y
    have hxy : â x - â y = d x - d y := by simp [hâdef]
    rw [hxy]
    have := norm_sub_le_rpow_of_lipschitz_of_bound (by positivity) hr0 hr1 hdl hdb x y
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
    rw [hΛdef]; linarith
  · simp [hâdef, hddef, hξ1 x hx, hI]

/-! ### The case `k = 1`: difference quotients -/

section KOne

variable {r : ℝ≥0}

/-- **One derivative more for `a : D²v = g`** (`a, g ∈ C^{1,r}`, `v ∈ C^{2,r}` near every point of
`U`): every directional derivative of `v` is `C^{2,r}` near every point of `U`. -/
theorem holderAt_fderiv_apply_of_hessTrace_eq (hr0 : 0 < r) (hr1 : r < 1) {U : Set E}
    (hU : IsOpen U) {a : E → E →L[ℝ] E} {g v : E → ℝ} (ha : ∀ z ∈ U, HolderAt 1 r a z)
    (hsymm : ∀ z ∈ U, ∀ u w, ⟪a z u, w⟫_ℝ = ⟪u, a z w⟫_ℝ)
    (hpos : ∀ z ∈ U, ∀ u, u ≠ 0 → 0 < ⟪a z u, u⟫_ℝ) (hg : ∀ z ∈ U, HolderAt 1 r g z)
    (hv : ∀ z ∈ U, HolderAt 2 r v z)
    (heq : ∀ z ∈ U, hessTrace b (a z) (fderiv ℝ (fderiv ℝ v) z) = g z) {z₀ : E} (hz₀ : z₀ ∈ U)
    (ζ : E) : HolderAt 2 r (fun x => fderiv ℝ v x ζ) z₀ := by
  have hr1' : r ≤ 1 := hr1.le
  have hrr0 : (0 : ℝ) ≤ r := r.coe_nonneg
  have hrr1 : (r : ℝ) ≤ 1 := by exact_mod_cast hr1'
  obtain ⟨a₁, ha₁⟩ := ha z₀ hz₀
  obtain ⟨g₁, hg₁⟩ := hg z₀ hz₀
  obtain ⟨v₁, hv₁⟩ := hv z₀ hz₀
  have hev : ∀ᶠ x in 𝓝 z₀, x ∈ U ∧ a₁ x = a x ∧ g₁ x = g x ∧ (⇑v₁ =ᶠ[𝓝 x] v) :=
    Filter.Eventually.and (hU.mem_nhds hz₀) (ha₁.and (hg₁.and hv₁.eventually_nhds))
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have heq₁ : ∀ p ∈ ball z₀ ρ, hessTrace b (a₁ p) (fderiv ℝ (fderiv ℝ v₁) p) = g₁ p := by
    intro p hp
    obtain ⟨hpU, e1, e2, e3⟩ := hρs p hp
    rw [e1, e2, e3.fderiv.fderiv_eq]
    exact heq p hpU
  -- the cut-off and the extended coefficient
  obtain ⟨θ, hθs, hθc, hθU, hθ1⟩ := exists_cutoff_nhds (ball_mem_nhds z₀ (by positivity : 0 < ρ / 4))
  have ha₁d : Differentiable ℝ a₁ := differentiable_of_one a₁
  have ha₁l : ∀ x y, ‖a₁ x - a₁ y‖ ≤ ‖a₁‖ * ‖x - y‖ := fun x y =>
    (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => ha₁d z) (fun z _ => norm_fderiv_le_of_one a₁ z) (mem_univ y) (mem_univ x)
  obtain ⟨lam, Λ, â, hlam, hâ, hâK⟩ := exists_ellipticExtension hrr0 hrr1
    (fun x => a₁.norm_apply_le x) ha₁l (isCompact_closedBall z₀ (ρ / 4)) isOpen_ball
    (closedBall_subset_ball (by linarith : ρ / 4 < ρ / 2)) (fun x hx => by
      obtain ⟨hxU, e1, -⟩ := hρs x (ball_subset_ball (by linarith) hx)
      rw [e1]; exact hsymm x hxU)
    (fun x hx => by
      obtain ⟨hxU, e1, -⟩ := hρs x (ball_subset_ball (by linarith) hx)
      rw [e1]; exact hpos x hxU)
  -- the equations for the difference quotients
  have hv₁2 : ContDiff ℝ 2 ⇑v₁ := contDiff_two v₁
  have hv₁d : Differentiable ℝ ⇑v₁ := hv₁2.differentiable (by simp)
  have hDv₁d : Differentiable ℝ (fderiv ℝ ⇑v₁) :=
    (hv₁2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hg₁d : Differentiable ℝ ⇑g₁ := differentiable_of_one g₁
  set h₀ : ℝ := ρ / (4 * (‖ζ‖ + 1)) with hh₀def
  have hh₀ : 0 < h₀ := by positivity
  set gh : ℝ → E → ℝ := fun h x => diffQuot (⇑g₁) ζ h x -
    hessTrace b (diffQuot (⇑a₁) ζ h x) (fderiv ℝ (fderiv ℝ v₁) (x + h • ζ)) with hghdef
  have hmov : ∀ h, 0 < h → h ≤ h₀ → ∀ x ∈ tsupport θ, x ∈ closedBall z₀ (ρ / 4) ∧
      x ∈ ball z₀ ρ ∧ x + h • ζ ∈ ball z₀ ρ := by
    intro h hh hhh x hx
    have hx4 : dist x z₀ < ρ / 4 := hθU hx
    have hhz : h * ‖ζ‖ ≤ ρ / 4 := by
      have h1 : h * ‖ζ‖ ≤ h₀ * (‖ζ‖ + 1) :=
        mul_le_mul hhh (by linarith) (norm_nonneg _) hh₀.le
      have h2 : h₀ * (‖ζ‖ + 1) = ρ / 4 := by rw [hh₀def]; field_simp
      linarith
    refine ⟨mem_closedBall.mpr hx4.le, mem_ball.mpr (by linarith), mem_ball.mpr ?_⟩
    rw [dist_eq_norm, add_sub_right_comm]
    calc ‖x - z₀ + h • ζ‖ ≤ ‖x - z₀‖ + ‖h • ζ‖ := norm_add_le _ _
      _ = dist x z₀ + h * ‖ζ‖ := by rw [dist_eq_norm, norm_smul, Real.norm_of_nonneg hh.le]
      _ < ρ := by linarith
  have heqh : ∀ h, 0 < h → h ≤ h₀ → ∀ x ∈ tsupport θ,
      hessTrace b (â x) (fderiv ℝ (fderiv ℝ (diffQuot (⇑v₁) ζ h)) x) = gh h x := by
    intro h hh hhh x hx
    obtain ⟨hxK, hxB, hxhB⟩ := hmov h hh hhh x hx
    rw [fderiv_diffQuot hv₁d, fderiv_diffQuot hDv₁d, hâK x hxK]
    have e1 := heq₁ x hxB
    have e2 := heq₁ (x + h • ζ) hxhB
    simp only [hghdef, diffQuot, smul_eq_mul]
    rw [hessTrace_smul_right, hessTrace_sub_right, hessTrace_smul_left, hessTrace_sub_left, e1, e2]
    ring
  -- uniform bounds
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set M : ℝ := 3 * ‖g₁‖ * ‖ζ‖ + 3 * d * ‖a₁‖ * ‖ζ‖ * ‖v₁‖ with hMdef
  have hghb : ∀ h, 0 < h → h ≤ h₀ → ∀ x, |gh h x| ≤ M := by
    intro h hh _ x
    have e1 : |diffQuot (⇑g₁) ζ h x| ≤ ‖g₁‖ * ‖ζ‖ := by
      rw [← Real.norm_eq_abs]; exact norm_diffQuot_le hg₁d (norm_fderiv_le_of_one g₁) ζ hh.ne' x
    have e2 : ‖diffQuot (⇑a₁) ζ h x‖ ≤ ‖a₁‖ * ‖ζ‖ :=
      norm_diffQuot_le ha₁d (norm_fderiv_le_of_one a₁) ζ hh.ne' x
    have e3 := abs_hessTrace_le b (diffQuot (⇑a₁) ζ h x) (fderiv ℝ (fderiv ℝ v₁) (x + h • ζ))
    have e4 := norm_fderiv_fderiv_le v₁ (x + h • ζ)
    rw [← hd] at e3
    simp only [hghdef]
    refine (abs_sub _ _).trans ?_
    have e5 : d * ‖diffQuot (⇑a₁) ζ h x‖ * ‖fderiv ℝ (fderiv ℝ v₁) (x + h • ζ)‖ ≤
        d * (‖a₁‖ * ‖ζ‖) * ‖v₁‖ := by gcongr
    rw [hMdef]
    nlinarith [norm_nonneg g₁, norm_nonneg ζ, mul_nonneg (norm_nonneg g₁) (norm_nonneg ζ),
      mul_nonneg (mul_nonneg (mul_nonneg hd0 (norm_nonneg a₁)) (norm_nonneg ζ)) (norm_nonneg v₁)]
  have hghh : ∀ h, 0 < h → h ≤ h₀ → ∀ x y, |gh h x - gh h y| ≤ M * ‖x - y‖ ^ (r : ℝ) := by
    intro h hh _ x y
    set p := ‖x - y‖ ^ (r : ℝ) with hp
    have hp0 : 0 ≤ p := Real.rpow_nonneg (norm_nonneg _) _
    have e1 : |diffQuot (⇑g₁) ζ h x - diffQuot (⇑g₁) ζ h y| ≤ 2 * ‖g₁‖ * p * ‖ζ‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_diffQuot_sub_le hg₁d (norm_fderiv_sub_le_of_one hr1' g₁) ζ hh.ne' x y
    have e2 : ‖diffQuot (⇑a₁) ζ h x - diffQuot (⇑a₁) ζ h y‖ ≤ 2 * ‖a₁‖ * p * ‖ζ‖ :=
      norm_diffQuot_sub_le ha₁d (norm_fderiv_sub_le_of_one hr1' a₁) ζ hh.ne' x y
    have e2' : ‖diffQuot (⇑a₁) ζ h y‖ ≤ ‖a₁‖ * ‖ζ‖ :=
      norm_diffQuot_le ha₁d (norm_fderiv_le_of_one a₁) ζ hh.ne' y
    have e3 := abs_hessTrace_sub_le b (diffQuot (⇑a₁) ζ h x) (diffQuot (⇑a₁) ζ h y)
      (fderiv ℝ (fderiv ℝ v₁) (x + h • ζ)) (fderiv ℝ (fderiv ℝ v₁) (y + h • ζ))
    have e4 := norm_fderiv_fderiv_le v₁ (x + h • ζ)
    have e5 : ‖fderiv ℝ (fderiv ℝ v₁) (x + h • ζ) - fderiv ℝ (fderiv ℝ v₁) (y + h • ζ)‖ ≤
        ‖v₁‖ * p := by
      have := norm_fderiv_fderiv_sub_le v₁ (x + h • ζ) (y + h • ζ)
      simpa using this
    rw [← hd] at e3
    have f1 : ‖diffQuot (⇑a₁) ζ h x - diffQuot (⇑a₁) ζ h y‖ *
        ‖fderiv ℝ (fderiv ℝ v₁) (x + h • ζ)‖ ≤ 2 * ‖a₁‖ * p * ‖ζ‖ * ‖v₁‖ :=
      mul_le_mul e2 e4 (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    have f2 : ‖diffQuot (⇑a₁) ζ h y‖ *
        ‖fderiv ℝ (fderiv ℝ v₁) (x + h • ζ) - fderiv ℝ (fderiv ℝ v₁) (y + h • ζ)‖ ≤
        ‖a₁‖ * ‖ζ‖ * (‖v₁‖ * p) :=
      mul_le_mul e2' e5 (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
    simp only [hghdef]
    rw [show ∀ A B C D : ℝ, A - B - (C - D) = (A - C) - (B - D) from fun _ _ _ _ => by ring]
    refine (abs_sub _ _).trans ?_
    have g1 := mul_le_mul_of_nonneg_left (add_le_add f1 f2) hd0
    rw [hMdef]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg g₁) hp0) (norm_nonneg ζ),
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hd0 (norm_nonneg a₁)) hp0) (norm_nonneg ζ))
        (norm_nonneg v₁)]
  obtain ⟨W, hW⟩ := exists_mul_fderiv_mem b hlam hr0 hr1 v₁ hθs hθc ζ hh₀ (fun _ => â) gh
    (fun _ _ _ => hâ) hghb hghh heqh
  refine ⟨W, ?_⟩
  filter_upwards [hθ1, hv₁.fderiv (𝕜 := ℝ)] with x hx1 hx2
  rw [hW, hx1, one_mul, hx2]

theorem holderAt_three_of_hessTrace_eq (hr0 : 0 < r) (hr1 : r < 1) {U : Set E}
    (hU : IsOpen U) {a : E → E →L[ℝ] E} {g v : E → ℝ} (ha : ∀ z ∈ U, HolderAt 1 r a z)
    (hsymm : ∀ z ∈ U, ∀ u w, ⟪a z u, w⟫_ℝ = ⟪u, a z w⟫_ℝ)
    (hpos : ∀ z ∈ U, ∀ u, u ≠ 0 → 0 < ⟪a z u, u⟫_ℝ) (hg : ∀ z ∈ U, HolderAt 1 r g z)
    (hv : ∀ z ∈ U, HolderAt 2 r v z)
    (heq : ∀ z ∈ U, hessTrace b (a z) (fderiv ℝ (fderiv ℝ v) z) = g z) :
    ∀ z ∈ U, HolderAt 3 r v z := by
  intro z hz
  have hD : HolderAt 2 r (fderiv ℝ v) z := HolderAt.fderiv_of_apply hr1.le b.toBasis fun i => by
    simpa using holderAt_fderiv_apply_of_hessTrace_eq b hr0 hr1 hU ha hsymm hpos hg hv heq hz (b i)
  exact (hv z hz).of_fderiv hr1.le hD ((hv z hz).eventually_differentiableAt (by norm_num))

end KOne

/-! ### The differentiated equation -/

/-- If `a : D²v = g` on the open set `U` and `v` is `C³` at `z ∈ U`, then `w = ∂_ζ v` satisfies
`a : D²w = ∂_ζ g - (∂_ζ a) : D²v` at `z`. -/
theorem hessTrace_fderiv_apply_eq {U : Set E} (hU : IsOpen U) {a : E → E →L[ℝ] E} {g v : E → ℝ}
    {z : E} (hz : z ∈ U) (had : DifferentiableAt ℝ a z) (hv3 : ContDiffAt ℝ 3 v z)
    (heq : ∀ x ∈ U, hessTrace b (a x) (fderiv ℝ (fderiv ℝ v) x) = g x) (ζ : E) :
    hessTrace b (a z) (fderiv ℝ (fderiv ℝ (fun x => fderiv ℝ v x ζ)) z) =
      fderiv ℝ g z ζ - hessTrace b (fderiv ℝ a z ζ) (fderiv ℝ (fderiv ℝ v) z) := by
  set D2 := fderiv ℝ (fderiv ℝ v) with hD2
  have h23 : minSmoothness ℝ 2 ≤ (3 : WithTop ℕ∞) := by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)
  -- `D(∂_ζ v) = D²v(ζ, ·)` near `z` (symmetry of second derivatives)
  have hev : (fderiv ℝ (fun y => fderiv ℝ v y ζ)) =ᶠ[𝓝 z] fun x => D2 x ζ := by
    filter_upwards [hv3.eventually (by simp)] with x hx
    have hsymm := hx.isSymmSndFDerivAt h23
    have hDv : DifferentiableAt ℝ (fderiv ℝ v) x :=
      (hx.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [fderiv_clm_apply hDv (differentiableAt_const ζ)]
    ext p
    rw [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
    exact hsymm p ζ
  have hD3 : ContDiffAt ℝ 1 D2 z := (hv3.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)
  have hD2d : DifferentiableAt ℝ D2 z := hD3.differentiableAt one_ne_zero
  have hw2 : fderiv ℝ (fderiv ℝ (fun x => fderiv ℝ v x ζ)) z = (fderiv ℝ D2 z).flip ζ := by
    rw [hev.fderiv_eq, fderiv_clm_apply hD2d (differentiableAt_const ζ)]
    simp
  -- symmetry of the third derivative in the first two slots
  have hsymm3 : IsSymmSndFDerivAt ℝ (fderiv ℝ v) z := by
    refine (hv3.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt ?_
    simp only [minSmoothness_of_isRCLikeNormedField]; exact le_rfl
  have hflip : (fderiv ℝ D2 z).flip ζ = fderiv ℝ D2 z ζ := by
    ext p q
    simp only [ContinuousLinearMap.flip_apply]
    rw [hD2, hsymm3 p ζ]
  -- differentiate the equation, written as `∑ᵢ D²v(bᵢ, a bᵢ)`
  have hterm : ∀ i, HasFDerivAt (fun x => D2 x (b i) (a x (b i)))
      ((D2 z (b i)).comp ((fderiv ℝ a z).flip (b i)) +
        ((fderiv ℝ D2 z).flip (b i)).flip (a z (b i))) z := by
    intro i
    have hc : HasFDerivAt (fun x => D2 x (b i)) ((fderiv ℝ D2 z).flip (b i)) z := by
      have := hD2d.hasFDerivAt.clm_apply (hasFDerivAt_const (b i) z)
      simpa using this
    have hu : HasFDerivAt (fun x => a x (b i)) ((fderiv ℝ a z).flip (b i)) z := by
      have := had.hasFDerivAt.clm_apply (hasFDerivAt_const (b i) z)
      simpa using this
    exact hc.clm_apply hu
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  have hE : (fun x => ∑ i, D2 x (b i) (a x (b i))) =ᶠ[𝓝 z] g := by
    filter_upwards [hU.mem_nhds hz] with x hx
    exact heq x hx
  have hder : fderiv ℝ g z = ∑ i, ((D2 z (b i)).comp ((fderiv ℝ a z).flip (b i)) +
      ((fderiv ℝ D2 z).flip (b i)).flip (a z (b i))) := by
    rw [← hE.fderiv_eq]
    exact hsum.fderiv
  have hζ := congrArg (fun L => L ζ) hder
  simp only [_root_.sum_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hζ
  rw [hw2, hflip, hζ]
  simp only [hessTrace, Finset.sum_add_distrib]
  ring

/-! ### The general case -/

section General

variable {r : ℝ≥0}

/-- **Interior regularity for `a : D²v = g`** (blueprint `bou:schauder-global`, regularity clause):
for `k ≥ 1`, if `a, g` are `C^{k,r}` and `v` is `C^{k+1,r}` near every point of `U` (`a` symmetric
and positive definite on `U`) and `a : D²v = g` on `U`, then `v` is `C^{k+2,r}` near every point of
`U`. -/
theorem holderAt_of_hessTrace_eq (hr0 : 0 < r) (hr1 : r < 1) {U : Set E} (hU : IsOpen U)
    {a : E → E →L[ℝ] E} (hsymm : ∀ z ∈ U, ∀ u w, ⟪a z u, w⟫_ℝ = ⟪u, a z w⟫_ℝ)
    (hpos : ∀ z ∈ U, ∀ u, u ≠ 0 → 0 < ⟪a z u, u⟫_ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ g v : E → ℝ, (∀ z ∈ U, HolderAt k r a z) → (∀ z ∈ U, HolderAt k r g z) →
      (∀ z ∈ U, HolderAt (k + 1) r v z) →
      (∀ z ∈ U, hessTrace b (a z) (fderiv ℝ (fderiv ℝ v) z) = g z) →
      ∀ z ∈ U, HolderAt (k + 2) r v z := by
  have hr1' : r ≤ 1 := hr1.le
  induction k, hk using Nat.le_induction with
  | base =>
    intro g v ha hg hv heq
    exact holderAt_three_of_hessTrace_eq b hr0 hr1 hU ha hsymm hpos hg hv heq
  | succ k hk ih =>
    intro g v ha hg hv heq z hz
    -- the equation for each directional derivative
    have key : ∀ ζ : E, ∀ y ∈ U, HolderAt (k + 2) r (fun x => fderiv ℝ v x ζ) y := by
      intro ζ
      set w : E → ℝ := fun x => fderiv ℝ v x ζ with hwdef
      set g' : E → ℝ := fun x => fderiv ℝ g x ζ -
        hessTrace b (fderiv ℝ a x ζ) (fderiv ℝ (fderiv ℝ v) x) with hg'def
      have hw : ∀ y ∈ U, HolderAt (k + 1) r w y := fun y hy =>
        (hv y hy).derivative.clm hr1' (ContinuousLinearMap.apply ℝ ℝ ζ)
      have hg' : ∀ y ∈ U, HolderAt k r g' y := by
        intro y hy
        have h1 : HolderAt k r (fun x => fderiv ℝ g x ζ) y :=
          (hg y hy).derivative.clm hr1' (ContinuousLinearMap.apply ℝ ℝ ζ)
        have h2 : HolderAt k r (fun x => fderiv ℝ a x ζ) y :=
          (ha y hy).derivative.clm hr1' (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) ζ)
        exact h1.sub (holderAt_hessTrace b hr1' h2 (hv y hy))
      have heq' : ∀ y ∈ U, hessTrace b (a y) (fderiv ℝ (fderiv ℝ w) y) = g' y := by
        intro y hy
        have had : DifferentiableAt ℝ a y :=
          (ha y hy).contDiffAt.differentiableAt (by exact_mod_cast (by omega : k + 1 ≠ 0))
        have hv3 : ContDiffAt ℝ 3 v y :=
          (hv y hy).contDiffAt.of_le (by exact_mod_cast (by omega : 3 ≤ k + 1 + 1))
        exact hessTrace_fderiv_apply_eq b hU hy had hv3 heq ζ
      exact ih g' w (fun y hy => (ha y hy).of_succ hr1') hg' hw heq'
    have hD : HolderAt (k + 2) r (fderiv ℝ v) z := HolderAt.fderiv_of_apply hr1' b.toBasis
      fun i => by simpa using key (b i) z hz
    exact (hv z hz).of_fderiv hr1' hD ((hv z hz).eventually_differentiableAt (by omega))

end General

end SGPT.Foundations.Analysis.Pending.LinearRegularity

import SGPT.Foundations.Analysis.Pending.MongeAmpereDifferenceQuotient

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Regularity of `C^{2,r}` solutions of the complex Monge–Ampère equation

**Local form** (`holderAt_of_maLocal_eq`): let `U ⊆ ℂⁿ` be open, `H` smooth and positive definite on
`U`, `φ` smooth on `U`, `ε ∈ ℝ`, `0 < r < 1`, and `u` of class `C^{2,r}` near every point of `U` with
`H + complexHessian u` positive definite and
`log det(H + (∂²u/∂z_j∂z̄_k)) - log det H = φ + εu` on `U` (`maLocal H (z, kfun u z) = φ z + ε u z`).
Then `u` is `C^{k,r}` near every point of `U` for every `k`, hence smooth on `U`.

Proof: `C^{2,r} → C^{3,r}` is the nonlinear difference-quotient step
(`MongeAmpereRegularity.holderAt_three_of_maLocal_eq`).  For `k ≥ 1`, if `u ∈ C^{k+2,r}`, every
directional derivative `v = ∂_ζ u` solves the linear equation
`lapCoeff(H + herm K) : D²v = ∂_ζ φ + ε v - ∂_z F(z, K) ζ`, `K = kfun u` (`hessTrace_lapCoeff_eq`,
derivative of the equation along a line), whose coefficients are `C^{k,r}` by the Nemytskii lemma
(`HolderGerm.HolderAt.comp_contDiff`, `holderAt_kfun`); the linear interior regularity
(`LinearRegularity.holderAt_of_hessTrace_eq`) gives `v ∈ C^{k+2,r}`, so `u ∈ C^{k+3,r}`.

**Manifold form** (`chartSmooth_of_ma_eq`): on a complex manifold with a Kähler background `A` and a
Hölder atlas, a solution `ψ ∈ C^{2,r}(M)` of `ma A ψ = tF + εψ` (`F` chart-smooth) with
`H_A + complexHessian ψ > 0` in every chart is chart-smooth.

TN.4 B5, regularity bootstrap (the proof of Yau's theorem, P2);
consumers: openness of the set of smooth solutions of the `ε`-continuity path and the closedness
step N5 (blueprint `bou:yau-openness`, `bou:yau-closedness`).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff InnerProductSpace ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.MongeAmpereRegularity

open FirstPass FirstPass.MongeAmpere KahlerLaplacianChart MongeAmpereHolder HolderGerm
  DifferenceQuotient LinearRegularity EllipticMeanValue SchauderBlowup

variable {n : ℕ}

/-! ### Germs with values in a finite product -/

section Pi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ} {r : ℝ≥0} {z : E}

theorem holderAt_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hr : r ≤ 1) {f : E → ι → F} (h : ∀ i, HolderAt k r (fun x => f x i) z) :
    HolderAt k r f z := by
  have hs : HolderAt k r (fun x => ∑ i, ContinuousLinearMap.single ℝ (fun _ : ι => F) i (f x i)) z :=
    HolderAt.sum _ fun i _ => (h i).clm hr (ContinuousLinearMap.single ℝ (fun _ : ι => F) i)
  refine hs.congr (Eventually.of_forall fun x => ?_)
  simpa using Finset.univ_sum_single (f x)

/-- A complex-valued germ from its real and imaginary parts. -/
theorem holderAt_complex (hr : r ≤ 1) {f g : E → ℝ} (hf : HolderAt k r f z) (hg : HolderAt k r g z) :
    HolderAt k r (fun x => ((f x : ℝ) : ℂ) + Complex.I * (g x : ℂ)) z := by
  have h1 : HolderAt k r (fun x => Complex.ofRealCLM (f x)) z := hf.clm hr Complex.ofRealCLM
  have h2 : HolderAt k r (fun x => g x • Complex.I) z := hg.smul hr (holderAt_const hr _)
  refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
  simp [Complex.real_smul, mul_comm]

end Pi

/-! ### The array of second derivatives -/

section Kfun

variable {k : ℕ} {r : ℝ≥0} {z : ComplexModel n}

theorem kfun_apply (u : ComplexModel n → ℝ) (x : ComplexModel n) (j l : Fin n) :
    kfun u x j l =
      (((fderiv ℝ (fderiv ℝ u) x (coordinateVector j) (coordinateVector l) +
        fderiv ℝ (fderiv ℝ u) x (Complex.I • coordinateVector j) (Complex.I • coordinateVector l)) /
          4 : ℝ) : ℂ) + Complex.I *
        (((fderiv ℝ (fderiv ℝ u) x (coordinateVector j) (Complex.I • coordinateVector l) -
          fderiv ℝ (fderiv ℝ u) x (Complex.I • coordinateVector j) (coordinateVector l)) / 4 :
            ℝ) : ℂ) := by
  simp only [kfun, kmat, ComplexHessianDeterminant.complexHessian_eq_complexHessianOfBilin,
    SemiconcaveHessian.complexHessianOfBilin]
  push_cast
  ring

/-- `kfun u` is a `C^{k,r}` germ if `u` is a `C^{k+2,r}` germ. -/
theorem holderAt_kfun (hr : r ≤ 1) {u : ComplexModel n → ℝ} (hu : HolderAt (k + 2) r u z) :
    HolderAt k r (kfun u) z := by
  classical
  refine holderAt_pi hr fun j => holderAt_pi hr fun l => ?_
  have hs := fun p q => holderAt_second_partial hr hu p q
  have h1 := ((hs (coordinateVector j) (coordinateVector l)).add
    (hs (Complex.I • coordinateVector j) (Complex.I • coordinateVector l))).const_smul (1 / 4 : ℝ)
  have h2 := ((hs (coordinateVector j) (Complex.I • coordinateVector l)).sub
    (hs (Complex.I • coordinateVector j) (coordinateVector l))).const_smul (1 / 4 : ℝ)
  refine (holderAt_complex hr h1 h2).congr (Eventually.of_forall fun x => ?_)
  simp only [kfun_apply, smul_eq_mul]
  push_cast
  ring

end Kfun

/-! ### Composition with a map smooth on an open set -/

theorem holderAt_comp_of_contDiffOn {E F₁ F₂ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {k : ℕ} {r : ℝ≥0} {z : E} (hr : r ≤ 1)
    {w : E → F₁} (hw : HolderAt k r w z) {O : Set (E × F₁)} (hO : IsOpen O) (hzO : (z, w z) ∈ O)
    {G : E × F₁ → F₂} (hG : ContDiffOn ℝ ∞ G O) : HolderAt k r (fun x => G (x, w x)) z := by
  obtain ⟨ξ, hξs, -, hξO, hξ1⟩ := exists_cutoff_nhds (hO.mem_nhds hzO)
  have hG' : ContDiff ℝ ∞ (fun p => ξ p • G p) :=
    KahlerLaplacianChart.contDiff_smul_of_tsupport hO hξs hξO hG
  have h := hw.comp_contDiff hr hG'
  refine h.congr ?_
  have hc : ContinuousAt (fun x => (x, w x)) z := continuousAt_id.prodMk hw.contDiffAt.continuousAt
  filter_upwards [hc.eventually hξ1] with x hx
  simp [hx]

/-! ### Differentiating the equation along a line -/

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `D²(∂_ζ u) = ∂_ζ D²u` for `u` of class `C³` (symmetry of second derivatives). -/
theorem fderiv_fderiv_fderiv_apply {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (ζ : E) :
    fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y ζ)) x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x ζ := by
  set D2 := fderiv ℝ (fderiv ℝ u) with hD2
  have h23 : minSmoothness ℝ 2 ≤ (3 : WithTop ℕ∞) := by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)
  have hev : (fderiv ℝ (fun y => fderiv ℝ u y ζ)) =ᶠ[𝓝 x] fun y => D2 y ζ := by
    filter_upwards [hu.eventually (by simp)] with y hy
    have hsymm := hy.isSymmSndFDerivAt h23
    have hDu : DifferentiableAt ℝ (fderiv ℝ u) y :=
      (hy.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [fderiv_clm_apply hDu (differentiableAt_const ζ)]
    ext p
    rw [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
    exact hsymm p ζ
  have hD3 : ContDiffAt ℝ 1 D2 x := (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)
  have hD2d : DifferentiableAt ℝ D2 x := hD3.differentiableAt one_ne_zero
  rw [hev.fderiv_eq, fderiv_clm_apply hD2d (differentiableAt_const ζ)]
  have hsymm3 : IsSymmSndFDerivAt ℝ (fderiv ℝ u) x := by
    refine (hu.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt ?_
    simp only [minSmoothness_of_isRCLikeNormedField]; exact le_rfl
  ext p q
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [hD2, hsymm3 p ζ]

end Derivative

/-- `t ↦ kfun u (x + t ζ)` has derivative `kfun (∂_ζ u) x` at `0` (`u` of class `C³` at `x`). -/
theorem hasDerivAt_kfun_line {u : ComplexModel n → ℝ} {x : ComplexModel n} (hu : ContDiffAt ℝ 3 u x)
    (ζ : ComplexModel n) :
    HasDerivAt (fun t : ℝ => kfun u (x + t • ζ)) (kfun (fun y => fderiv ℝ u y ζ) x) 0 := by
  set D2 := fderiv ℝ (fderiv ℝ u) with hD2
  have hD2d : DifferentiableAt ℝ D2 x := ((hu.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hline : HasDerivAt (fun t : ℝ => x + t • ζ) ζ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add x
  have hpq : ∀ p q, HasDerivAt (fun t : ℝ => D2 (x + t • ζ) p q)
      (fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y ζ)) x p q) 0 := by
    intro p q
    rw [fderiv_fderiv_fderiv_apply hu ζ]
    have hg := (hD2d.hasFDerivAt.clm_apply (hasFDerivAt_const p x)).clm_apply
      (hasFDerivAt_const q x)
    have h' := hg.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    refine h'.congr_deriv ?_
    simp [hD2]
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro l
  have h1 := (((hpq (coordinateVector j) (coordinateVector l)).add
    (hpq (Complex.I • coordinateVector j) (Complex.I • coordinateVector l))).div_const 4).ofReal_comp
  have h2 := (((hpq (coordinateVector j) (Complex.I • coordinateVector l)).sub
    (hpq (Complex.I • coordinateVector j) (coordinateVector l))).div_const 4).ofReal_comp
  have h3 := h1.add (h2.const_mul Complex.I)
  simp only [kfun_apply]
  exact h3

section Equation

variable {U : Set (ComplexModel n)} {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}

/-- **The differentiated Monge–Ampère equation**: if `maLocal H (z, kfun u z) = φ z + ε u z` on the
open set `U` and `u` is `C³` at `x ∈ U`, then `v = ∂_ζ u` satisfies
`lapCoeff(H + herm K) : D²v = ∂_ζ φ + ε v - ∂_z maLocal ζ` at `x`. -/
theorem hessTrace_lapCoeff_eq (hU : IsOpen U) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hHp : ∀ z ∈ U, (H z).PosDef) {u φ : ComplexModel n → ℝ} {ε : ℝ}
    (hφ : ContDiffOn ℝ ∞ φ U) (hpos : ∀ z ∈ U, (H z + complexHessian u z).PosDef)
    (heq : ∀ z ∈ U, maLocal H (z, kfun u z) = φ z + ε * u z) {x : ComplexModel n} (hx : x ∈ U)
    (hu3 : ContDiffAt ℝ 3 u x) (ζ : ComplexModel n) :
    hessTrace realBasis (lapCoeff (H x + hermPart (kfun u x)))
        (fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y ζ)) x) =
      fderiv ℝ φ x ζ + ε * fderiv ℝ u x ζ - fderiv ℝ (maLocal H) (x, kfun u x) (ζ, 0) := by
  have hherm : hermPart (kfun u x) = complexHessian u x :=
    hermPart_kmat (isHermitian_complexHessian_of_contDiffAt (hu3.of_le (by norm_num)))
  have hpO : (x, kfun u x) ∈ pdDomain H U := ⟨hx, by
    show (H x + hermPart (kfun u x)).PosDef
    rw [hherm]; exact hpos x hx⟩
  have hO : IsOpen (pdDomain H U) := isOpen_pdDomain hU hH fun z hz => (hHp z hz).isHermitian
  have hma : ContDiffOn ℝ ∞ (maLocal H) (pdDomain H U) :=
    (contDiffOn_maLocal hH).mono (pdDomain_subset_maDomain hHp)
  have hd : HasFDerivAt (maLocal H) (fderiv ℝ (maLocal H) (x, kfun u x)) (x, kfun u x) :=
    ((hma.contDiffAt (hO.mem_nhds hpO)).differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => x + t • ζ) ζ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add x
  have hγ : HasDerivAt (fun t : ℝ => ((x + t • ζ, kfun u (x + t • ζ)) :
      ComplexModel n × (Fin n → Fin n → ℂ))) (ζ, kfun (fun y => fderiv ℝ u y ζ) x) 0 :=
    hline.prodMk (hasDerivAt_kfun_line hu3 ζ)
  have h1 := hd.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hφd : DifferentiableAt ℝ φ x :=
    (hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hud : DifferentiableAt ℝ u x := hu3.differentiableAt (by norm_num)
  have h2 : HasDerivAt (fun t : ℝ => φ (x + t • ζ) + ε * u (x + t • ζ))
      (fderiv ℝ φ x ζ + ε * fderiv ℝ u x ζ) 0 := by
    have e1 := hφd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have e2 := hud.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact e1.add (e2.const_mul ε)
  have hev : (fun t : ℝ => φ (x + t • ζ) + ε * u (x + t • ζ)) =ᶠ[𝓝 0]
      (maLocal H ∘ fun t : ℝ => ((x + t • ζ, kfun u (x + t • ζ)) :
        ComplexModel n × (Fin n → Fin n → ℂ))) := by
    have hc : ContinuousAt (fun t : ℝ => x + t • ζ) 0 := hline.continuousAt
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • ζ ∈ U :=
      hc.eventually (by simpa using hU.mem_nhds hx)
    filter_upwards [hmem] with t ht
    exact (heq _ ht).symm
  have huniq := h1.unique (h2.congr_of_eventuallyEq hev.symm)
  have hv2 : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y ζ) x :=
    (hu3.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hdecomp : ((ζ, kfun (fun y => fderiv ℝ u y ζ) x) : ComplexModel n × (Fin n → Fin n → ℂ)) =
      (ζ, 0) + (0, kfun (fun y => fderiv ℝ u y ζ) x) := by simp
  rw [hdecomp, map_add, fderiv_maLocal_apply hU hH (pdDomain_subset_maDomain hHp hpO)
    hpO.2.isHermitian,
    show kfun (fun y => fderiv ℝ u y ζ) x = kmat (complexHessian (fun y => fderiv ℝ u y ζ) x) from rfl,
    hermPart_kmat (isHermitian_complexHessian_of_contDiffAt hv2),
    re_trace_inv_mul_complexHessian realBasis] at huniq
  linarith

end Equation

/-! ### The bootstrap -/

section Bootstrap

variable {r : ℝ≥0} {U : Set (ComplexModel n)} {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}

/-- **Regularity of `C^{2,r}` solutions** (local form): a `C^{2,r}` solution of
`log det(H + u_{j k̄}) - log det H = φ + εu` on `U` (`H`, `φ` smooth, `H` and `H + u_{j k̄}` positive
definite) is `C^{k+2,r}` near every point of `U`, for every `k`. -/
theorem holderAt_of_maLocal_eq (hr0 : 0 < r) (hr1 : r < 1) (hU : IsOpen U)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U) (hHp : ∀ z ∈ U, (H z).PosDef)
    {u φ : ComplexModel n → ℝ} {ε : ℝ} (hu : ∀ z ∈ U, HolderAt 2 r u z)
    (hφ : ContDiffOn ℝ ∞ φ U) (hpos : ∀ z ∈ U, (H z + complexHessian u z).PosDef)
    (heq : ∀ z ∈ U, maLocal H (z, kfun u z) = φ z + ε * u z) :
    ∀ k : ℕ, ∀ z ∈ U, HolderAt (k + 2) r u z := by
  have hr1' : r ≤ 1 := hr1.le
  have hO : IsOpen (pdDomain H U) := isOpen_pdDomain hU hH fun z hz => (hHp z hz).isHermitian
  have hma : ContDiffOn ℝ ∞ (maLocal H) (pdDomain H U) :=
    (contDiffOn_maLocal hH).mono (pdDomain_subset_maDomain hHp)
  have hφh : ∀ j, ∀ z ∈ U, HolderAt j r φ z := fun j z hz =>
    holderAt_of_contDiffAt hr1' ((hφ.contDiffAt (hU.mem_nhds hz)).of_le
      (by exact_mod_cast le_top))
  have hgraph : ∀ z ∈ U, ContDiffAt ℝ 2 u z → (z, kfun u z) ∈ pdDomain H U := by
    intro z hz h2
    refine ⟨hz, ?_⟩
    show (H z + hermPart (kfun u z)).PosDef
    rw [show kfun u z = kmat (complexHessian u z) from rfl,
      hermPart_kmat (isHermitian_complexHessian_of_contDiffAt h2)]
    exact hpos z hz
  intro k
  induction k with
  | zero => exact hu
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- the nonlinear step `C^{2,r} → C^{3,r}`
      have hf : ∀ z ∈ U, HolderAt 1 r (fun z => φ z + ε * u z) z := by
        intro z hz
        have h1 := ((hu z hz).of_le hr1' (by norm_num : 1 ≤ 2)).const_smul ε
        exact (hφh 1 z hz).add (h1.congr (Eventually.of_forall fun x => by simp [smul_eq_mul]))
      exact holderAt_three_of_maLocal_eq hr0 hr1 hU hH hHp hu hf hpos heq
    · -- the linear step for every directional derivative
      intro z hz
      have key : ∀ ζ : ComplexModel n, ∀ y ∈ U,
          HolderAt (k + 2) r (fun x => fderiv ℝ u x ζ) y := by
        intro ζ
        set a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n :=
          fun x => lapCoeff (H x + hermPart (kfun u x)) with hadef
        set g : ComplexModel n → ℝ := fun x => fderiv ℝ φ x ζ + ε * fderiv ℝ u x ζ -
          fderiv ℝ (maLocal H) (x, kfun u x) (ζ, 0) with hgdef
        have hu2 : ∀ y ∈ U, ContDiffAt ℝ 2 u y := fun y hy =>
          (ih y hy).contDiffAt.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
        have ha : ∀ y ∈ U, HolderAt k r a y := fun y hy =>
          holderAt_comp_of_contDiffOn hr1' (holderAt_kfun hr1' (ih y hy)) hO (hgraph y hy (hu2 y hy))
            (contDiffOn_lapCoeffField hU hH)
        have hv : ∀ y ∈ U, HolderAt (k + 1) r (fun x => fderiv ℝ u x ζ) y := fun y hy =>
          (ih y hy).derivative.clm hr1' (ContinuousLinearMap.apply ℝ ℝ ζ)
        have hg : ∀ y ∈ U, HolderAt k r g y := by
          intro y hy
          have hDφ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ φ x ζ) U :=
            (hφ.fderiv_of_isOpen hU (m := ∞) le_rfl).clm_apply contDiffOn_const
          have h1 : HolderAt k r (fun x => fderiv ℝ φ x ζ) y :=
            holderAt_of_contDiffAt hr1' ((hDφ.contDiffAt (hU.mem_nhds hy)).of_le
              (by exact_mod_cast le_top))
          have h2 : HolderAt k r (fun x => ε * fderiv ℝ u x ζ) y :=
            (((hv y hy).of_succ hr1').const_smul ε).congr
              (Eventually.of_forall fun x => by simp [smul_eq_mul])
          have hβ : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (maLocal H) p (ζ, 0)) (pdDomain H U) :=
            (hma.fderiv_of_isOpen hO (m := ∞) le_rfl).clm_apply contDiffOn_const
          have h3 := holderAt_comp_of_contDiffOn hr1' (holderAt_kfun hr1' (ih y hy)) hO
            (hgraph y hy (hu2 y hy)) hβ
          exact (h1.add h2).sub h3
        have hsymm : ∀ y ∈ U, ∀ v w, ⟪a y v, w⟫_ℝ = ⟪v, a y w⟫_ℝ := fun y hy v w =>
          lapCoeff_symm (hgraph y hy (hu2 y hy)).2.isHermitian v w
        have hposa : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < ⟪a y v, v⟫_ℝ := fun y hy v hv =>
          lapCoeff_pos (hgraph y hy (hu2 y hy)).2 hv
        have heqa : ∀ y ∈ U, hessTrace realBasis (a y)
            (fderiv ℝ (fderiv ℝ (fun x => fderiv ℝ u x ζ)) y) = g y := fun y hy =>
          hessTrace_lapCoeff_eq hU hH hHp hφ hpos heq hy
            ((ih y hy).contDiffAt.of_le (by exact_mod_cast (by omega : 3 ≤ k + 2))) ζ
        exact holderAt_of_hessTrace_eq realBasis hr0 hr1 hU hsymm hposa k hk g _ ha hg hv heqa
      have hD : HolderAt (k + 2) r (fderiv ℝ u) z :=
        HolderAt.fderiv_of_apply hr1' (realBasis (n := n)).toBasis fun i => by
          simpa using key (realBasis i) z hz
      exact (ih z hz).of_fderiv hr1' hD ((ih z hz).eventually_differentiableAt (by omega))

/-- Smoothness: under the hypotheses of `holderAt_of_maLocal_eq`, `u` is smooth on `U`. -/
theorem contDiffOn_of_maLocal_eq (hr0 : 0 < r) (hr1 : r < 1) (hU : IsOpen U)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U) (hHp : ∀ z ∈ U, (H z).PosDef)
    {u φ : ComplexModel n → ℝ} {ε : ℝ} (hu : ∀ z ∈ U, HolderAt 2 r u z)
    (hφ : ContDiffOn ℝ ∞ φ U) (hpos : ∀ z ∈ U, (H z + complexHessian u z).PosDef)
    (heq : ∀ z ∈ U, maLocal H (z, kfun u z) = φ z + ε * u z) : ContDiffOn ℝ ∞ u U := by
  intro z hz
  refine (contDiffAt_infty_of_holderAt (r := r) fun k => ?_).contDiffWithinAt
  exact (holderAt_of_maLocal_eq hr0 hr1 hU hH hHp hu hφ hpos heq k z hz).of_le hr1.le
    (by omega)

end Bootstrap

/-! ### On a complex manifold -/

section Manifold

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

open PositiveClasses

/-- **Regularity of `C^{2,r}` solutions of the `ε`-path equation** (blueprint `bou:yau-openness`,
`bou:yau-closedness`): if `ψ ∈ C^{2,r}(Y)` solves `ma A ψ = tF + εψ` (`F` chart-smooth, `A` Kähler)
and `H_A + complexHessian ψ` is positive definite in every chart, then `ψ` is chart-smooth. -/
theorem chartSmooth_of_ma_eq (A : KahlerBackground N Y) {HA : HolderAtlas N Y} {r : ℝ≥0}
    (hr0 : 0 < r) (hr1 : r < 1) {F : Y → ℝ} (hF : ChartSmooth (n := N) F) {t ε : ℝ}
    (ψ : HA.HolderMap 2 r ℝ)
    (hpos : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => ψ (e.val.symm x)) z).PosDef)
    (heq : ∀ y, ma A.form.val ⇑ψ y = t * F y + ε * ψ y) : ChartSmooth (n := N) ⇑ψ := by
  intro e
  set H : ComplexModel N → Matrix (Fin N) (Fin N) ℂ :=
    fun z => normalizedHermitianMatrix (A.form.val.coeff e z) with hHdef
  have hH : ∀ j k, ContDiffOn ℝ ∞ (fun z => H z j k) e.val.target := by
    intro j k
    have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (KahlerLaplacianChart.contDiffOn_apply (A.form.val.smooth e)
        ![coordinateVector j, Complex.I • coordinateVector k])
    have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn
      (KahlerLaplacianChart.contDiffOn_apply (A.form.val.smooth e)
        ![coordinateVector j, coordinateVector k])
    exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul h2))
  have hHp : ∀ z ∈ e.val.target, (H z).PosDef := fun z hz => posDef_coeff A.isKahler.1 hz
  have hu : ∀ z ∈ e.val.target, HolderAt 2 r (fun x => ψ (e.val.symm x)) z := fun z hz =>
    holderAt_comp_symm hr1.le ψ e hz
  have hφ : ContDiffOn ℝ ∞ (fun x => t * F (e.val.symm x)) e.val.target :=
    contDiffOn_const.mul (hF e)
  have hψC2 : ∀ f : ComplexChart N Y,
      ContDiffOn ℝ 2 (fun w => ψ (f.val.symm w)) f.val.target := fun f w hw =>
    (ManifoldContinuity.contDiffAt_comp_symm hr1.le ψ f hw).contDiffWithinAt
  have heq' : ∀ z ∈ e.val.target, maLocal H (z, kfun (fun x => ψ (e.val.symm x)) z) =
      t * F (e.val.symm z) + ε * ψ (e.val.symm z) := by
    intro z hz
    have hye : e.val.symm z ∈ e.val.source := e.val.map_target hz
    have hdet : (normalizedHermitianMatrix (A.form.val.coeff e (e.val (e.val.symm z))) +
        complexHessian (fun w => ψ (e.val.symm w)) (e.val (e.val.symm z))).det.re ≠ 0 := by
      rw [e.val.right_inv hz]
      exact (Complex.pos_iff.mp (hpos e z hz).det_pos).1.ne'
    have hma := MongeAmpereHolder.ma_eq A.isKahler.1 hψC2 hye hdet
    rw [e.val.right_inv hz, heq] at hma
    rw [hma]
    simp only [maLocal, maChart, hHdef]
    rw [show kfun (fun x => ψ (e.val.symm x)) z =
        kmat (complexHessian (fun x => ψ (e.val.symm x)) z) from rfl,
      hermPart_kmat (isHermitian_complexHessian_of_contDiffAt
        (ManifoldContinuity.contDiffAt_comp_symm hr1.le ψ e hz))]
  exact contDiffOn_of_maLocal_eq hr0 hr1 e.val.open_target hH hHp hu hφ (hpos e) heq'

end Manifold

end SGPT.Foundations.Analysis.Pending.MongeAmpereRegularity

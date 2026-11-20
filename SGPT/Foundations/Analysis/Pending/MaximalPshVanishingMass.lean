import SGPT.Foundations.Analysis.Pending.SemiconcaveDegenerateHessian
import SGPT.Foundations.Analysis.Pending.BedfordTaylorGauge
import SGPT.Foundations.Analysis.Pending.BedfordTaylorExistence
import SGPT.Foundations.Analysis.Pending.BedfordTaylorStepP

set_option autoImplicit false

/-!
# A maximal semiconcave plurisubharmonic function has no Monge--Ampere mass

This is the measure-level form of Blocki's Theorem 2.3.1 in the direction the
balayage argument needs: if `u` is locally bounded, plurisubharmonic, *maximal*
on `Ω` (Sadullaev's competitor form, `Pending.MaximalPsh.IsMaximalPshOn`), and
locally semiconcave, then every Bedford--Taylor limit of the constant tuple
`(u, ..., u)` on `Ω` is the zero measure.

The semiconcavity hypothesis is Blocki's `C^{1,1}` estimate, Theorem 2.3.2
(Bedford--Taylor), which for a maximal function is a theorem rather than an
assumption; it is *not* available in this workspace (its intended home is
`Pending.PolydiskSecondDifference`, which so far carries only the Mobius
automorphism infrastructure), so it is carried here as an explicit hypothesis
rather than as a `sorry`.  Everything else in Blocki's proof is already present
and was, until now, used by nothing:

* `SemiconcaveHessian.exists_mollifier_family` -- the radial mollifications
  `F j` of `u`, decreasing, smooth, with nonnegative Levi form;
* `SemiconcaveHessian.secondDifference_translationPairing` and
  `norm_fderiv_fderiv_le_of_secondDifference` (Blocki Prop. 2.3.3) -- the
  mollifications inherit the second-difference bound, hence `‖D²F j‖ ≤ 2K`;
* `SemiconcaveHessian.ae_exists_hasPeanoExpansion` (Aleksandrov) -- almost every
  point of the smaller ball carries a second-order Peano expansion of `u`;
* `SemiconcaveHessian.tendsto_realHessian_translationPairing_of_hasPeanoExpansion`
  -- at such a point the Hessians of the mollifications converge;
* `SemiconcaveHessian.tendsto_det_complexHessian_zero` -- and then maximality
  forces the limiting determinant to vanish.

What is added here is the passage from that almost-everywhere vanishing of the
smooth densities to the measure.  It is a dominated convergence argument: the
uniform bound `‖D²F j‖ ≤ 2K` bounds every entry of the complex Hessian, hence
bounds the determinant by `n! (2K)^n`, so the densities are uniformly bounded
on the ball and their integrals against a test function tend to `0`.  The
Bedford--Taylor limit integrates every test function to the same value, so it
is zero on a ball around each point of `Ω`, hence on `Ω`, hence everywhere.

**Degenerate cases.**  If `Ω` is empty the conclusion is already contained in
`IsBTLimit`, which asks `μ` to vanish off `Ω`.  In dimension `n = 0` the
hypothesis `IsMaximalPshOn Ω u` is itself unsatisfiable on a nonempty `Ω`:
the whole model is compact, so the competitor condition is vacuous and
maximality would force `u` to dominate `u + 1`.  So no separate case
distinction is needed, and none is made.

Source: Z. Blocki, *The complex Monge--Ampere operator in pluripotential
theory*, lecture notes, Theorem 2.3.1; Bedford--Taylor, Invent. Math. 37 (1976).
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback

variable {n : ℕ}

/-! ### Uniform bounds on the smooth Monge--Ampere density -/

/-- A determinant is bounded by `N!` times the `N`-th power of an entry bound. -/
theorem norm_det_le_of_norm_entries_le {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {x : ℝ}
    (hx : ∀ i j, ‖A i j‖ ≤ x) : ‖A.det‖ ≤ (N.factorial : ℝ) * x ^ N := by
  classical
  have hterm : ∀ σ : Equiv.Perm (Fin N),
      ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ x ^ N := by
    intro σ
    have hsign : ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ = ‖∏ i, A (σ i) i‖ := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
    rw [hsign, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : Fin N, x :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
      _ = x ^ N := by simp
  calc ‖A.det‖ = ‖∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := by
        rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm (Fin N), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), x ^ N := Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (N.factorial : ℝ) * x ^ N := by
        simp [Fintype.card_perm, nsmul_eq_mul]

/-- Every entry of the complex Hessian is bounded by the operator norm of the
second derivative. -/
theorem norm_complexHessian_entry_le (f : ComplexModel n → ℝ) (z : ComplexModel n)
    (j k : Fin n) : ‖complexHessian f z j k‖ ≤ ‖fderiv ℝ (fderiv ℝ f) z‖ := by
  set T := fderiv ℝ (fderiv ℝ f) z with hT
  have hnorm1 (i : Fin n) : ‖coordinateVector (n := n) i‖ = 1 := by
    simp [coordinateVector]
  have hnormI (i : Fin n) : ‖(Complex.I : ℂ) • coordinateVector (n := n) i‖ = 1 := by
    rw [norm_smul, hnorm1]
    simp
  have hbd (v w : ComplexModel n) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      |realHessian f z v w| ≤ ‖T‖ := by
    have h := T.le_opNorm₂ v w
    rw [realHessian_eq_fderiv]
    simpa [hv, hw, Real.norm_eq_abs] using h
  have h1 := hbd _ _ (hnorm1 j) (hnorm1 k)
  have h2 := hbd _ _ (hnormI j) (hnormI k)
  have h3 := hbd _ _ (hnorm1 j) (hnormI k)
  have h4 := hbd _ _ (hnormI j) (hnorm1 k)
  have hsplit : complexHessian f z j k =
      (((realHessian f z (coordinateVector j) (coordinateVector k) +
          realHessian f z (Complex.I • coordinateVector j)
            (Complex.I • coordinateVector k)) / 4 : ℝ) : ℂ) +
        Complex.I * (((realHessian f z (coordinateVector j) (Complex.I • coordinateVector k) -
          realHessian f z (Complex.I • coordinateVector j) (coordinateVector k)) / 4 : ℝ) : ℂ) := by
    simp only [complexHessian]
    push_cast
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have e1 : |(realHessian f z (coordinateVector j) (coordinateVector k) +
      realHessian f z (Complex.I • coordinateVector j)
        (Complex.I • coordinateVector k)) / 4| ≤ ‖T‖ / 2 := by
    rw [abs_div]
    have := by
      simpa [Real.norm_eq_abs] using
        norm_add_le (realHessian f z (coordinateVector j) (coordinateVector k))
          (realHessian f z (Complex.I • coordinateVector j) (Complex.I • coordinateVector k))
    have h4' : |(4 : ℝ)| = 4 := by norm_num
    rw [h4']
    linarith
  have e2 : |(realHessian f z (coordinateVector j) (Complex.I • coordinateVector k) -
      realHessian f z (Complex.I • coordinateVector j) (coordinateVector k)) / 4| ≤ ‖T‖ / 2 := by
    rw [abs_div]
    have := abs_sub (realHessian f z (coordinateVector j) (Complex.I • coordinateVector k))
      (realHessian f z (Complex.I • coordinateVector j) (coordinateVector k))
    have h4' : |(4 : ℝ)| = 4 := by norm_num
    rw [h4']
    linarith [abs_sub_abs_le_abs_sub
      (realHessian f z (coordinateVector j) (Complex.I • coordinateVector k))
      (realHessian f z (Complex.I • coordinateVector j) (coordinateVector k))]
  linarith

/-- The smooth Monge--Ampere density is bounded by `n!/pi^n * n! * T^n` wherever
the second derivative has operator norm at most `T`. -/
theorem abs_smoothDensity_le {f : ComplexModel n → ℝ} {z : ComplexModel n} {T : ℝ}
    (hT : ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ T) :
    |smoothDensity f z| ≤ (n.factorial : ℝ) / Real.pi ^ n * ((n.factorial : ℝ) * T ^ n) := by
  have hentry : ∀ j k, ‖complexHessian f z j k‖ ≤ T := fun j k =>
    (norm_complexHessian_entry_le f z j k).trans hT
  have hdet := norm_det_le_of_norm_entries_le hentry
  have hre : |((complexHessian f z).det).re| ≤ ‖(complexHessian f z).det‖ :=
    Complex.abs_re_le_norm _
  have hc : (0 : ℝ) ≤ (n.factorial : ℝ) / Real.pi ^ n := by positivity
  rw [smoothDensity, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hre.trans hdet) hc

/-! ### Semiconcavity -/

/-- **Local one-sided second-difference bound.**  This is the conclusion of
Blocki's `C^{1,1}` estimate (Theorem 2.3.2); it is a hypothesis here. -/
def IsLocallySemiconcaveOn (Ω : Opens (ComplexModel n)) (u : ComplexModel n → ℝ) : Prop :=
  ∀ z ∈ Ω, ∃ r K : ℝ, 0 < r ∧ 0 ≤ K ∧
    closedBall z (2 * r) ⊆ (Ω : Set (ComplexModel n)) ∧
    ∀ y ∈ closedBall z r, ∀ h : ComplexModel n, ‖h‖ ≤ r →
      u (y + h) + u (y - h) - 2 * u y ≤ K * ‖h‖ ^ 2

/-! ### The vanishing theorem -/

/-- **Local form.**  Around every point of `Ω` there is a ball carrying no
Bedford--Taylor mass of a maximal semiconcave potential. -/
theorem measure_ball_eq_zero_of_isMaximalPshOn
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hmax : IsMaximalPshOn Ω u)
    (hsc : IsLocallySemiconcaveOn Ω u)
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω (fun _ => u) μ)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ Ω) :
    ∃ ρ > 0, μ (ball z₀ ρ) = 0 := by
  classical
  obtain ⟨r, K, hr, hK, hballΩ, hsd⟩ := hsc z₀ hz₀
  set Ω' : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩ with hΩ'def
  have hΩ'Ω : (Ω' : Set (ComplexModel n)) ⊆ (Ω : Set (ComplexModel n)) := fun x hx =>
    hballΩ (by
      have : dist x z₀ < r := mem_ball.mp hx
      exact mem_closedBall.mpr (by linarith))
  set A : Opens (ComplexModel n) := ⟨ball z₀ (r / 4), isOpen_ball⟩ with hAdef
  have hAΩ' : (A : Set (ComplexModel n)) ⊆ (Ω' : Set (ComplexModel n)) :=
    ball_subset_ball (by linarith)
  have hclA : closure (A : Set (ComplexModel n)) = closedBall z₀ (r / 4) :=
    closure_ball z₀ (by positivity)
  have hArc : RelativelyCompactIn A Ω' := by
    refine ⟨?_, ?_⟩
    · rw [hclA]
      have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
      exact isCompact_closedBall z₀ (r / 4)
    · rw [hclA]
      intro x hx
      exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith))
  have hu' : IsLocallyBoundedPshOn Ω' u := by
    refine ⟨hu.1.mono hΩ'Ω, fun z hz => ?_⟩
    obtain ⟨V, hzV, hVΩ, C, hC⟩ := hu.2 z (hΩ'Ω hz)
    exact ⟨V ⊓ Ω', ⟨hzV, hz⟩, inf_le_right, C, fun w hw => hC w hw.1⟩
  obtain ⟨R, hR, g, hRδ, hg, hballR, hgu, hdec, hC2, hlevi⟩ :=
    exists_mollifier_family hArc hu' (δ₀ := r / 4) (by positivity)
  set F : ℕ → ComplexModel n → ℝ :=
    fun j => translationPairing volume g (explicitRadialKernel R hR j) with hFdef
  -- the mollifications inherit the second-difference bound, hence a Hessian bound
  have hnormD : ∀ j, ∀ z ∈ (A : Set (ComplexModel n)),
      ‖fderiv ℝ (fderiv ℝ (F j)) z‖ ≤ 2 * K := by
    intro j z hz
    refine norm_fderiv_fderiv_le_of_secondDifference (hC2 j) hK ?_ (fun v => hlevi j z hz v)
    filter_upwards [ball_mem_nhds (0 : ComplexModel n) hR] with h hh
    have hhR : ‖h‖ ≤ R := le_of_lt (by simpa [dist_zero_right] using mem_ball.mp hh)
    refine secondDifference_translationPairing hR hg (hgu z hz) ?_ j hhR
    intro y hy h' hh'
    refine hsd y ?_ h' (le_trans hh' (by linarith))
    have hyz : dist y z ≤ R := mem_closedBall.mp hy
    have hzz : dist z z₀ < r / 4 := mem_ball.mp hz
    refine mem_closedBall.mpr ?_
    have := dist_triangle y z z₀
    linarith
  -- uniform sup bound of the family on a slightly smaller ball
  set rho : ℝ := r / 8 with hrhodef
  have hrho : 0 < rho := by positivity
  have hballrhoA : ball z₀ rho ⊆ (A : Set (ComplexModel n)) := ball_subset_ball (by linarith)
  have hK₀A : closedBall z₀ rho ⊆ (A : Set (ComplexModel n)) := by
    intro x hx
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith))
  have hK₀c : IsCompact (closedBall z₀ rho) := by
    have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
    exact isCompact_closedBall z₀ rho
  obtain ⟨m, hm⟩ := hdec.2.2.2 (closedBall z₀ rho) hK₀c hK₀A
  obtain ⟨M₀, hM₀⟩ := hK₀c.exists_bound_of_continuousOn ((hC2 0).continuous.continuousOn)
  have hCbound : ∀ j, ∀ y ∈ ball z₀ rho, |F j y| ≤ max |m| M₀ := by
    intro j y hy
    have hyK : y ∈ closedBall z₀ rho := ball_subset_closedBall hy
    have hyA : y ∈ (A : Set (ComplexModel n)) := hballrhoA hy
    have hlow : m ≤ u y := hm ⟨y, hyK, rfl⟩
    have huF : u y ≤ F j y :=
      le_of_tendsto (hdec.2.2.1 y hyA)
        (eventually_atTop.2 ⟨j, fun k hk => hdec.2.1 y hyA hk⟩)
    have hup : F j y ≤ M₀ := by
      have h0 : |F 0 y| ≤ M₀ := by
        have h1 := hM₀ y hyK
        rw [Real.norm_eq_abs] at h1
        exact h1
      exact le_trans (hdec.2.1 y hyA (Nat.zero_le j)) (le_trans (le_abs_self _) h0)
    have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ z₀ (mem_closedBall_self hrho.le))
    rw [abs_le]
    constructor
    · have : -|m| ≤ m := neg_abs_le m
      have h1 : -max |m| M₀ ≤ -|m| := by
        simp only [neg_le_neg_iff]
        exact le_max_left _ _
      linarith
    · exact le_trans hup (le_max_right _ _)
  -- almost every point carries a second-order expansion, and there the density vanishes
  have hae := ae_exists_hasPeanoExpansion (c := z₀) (ρ := rho) (M := 2 * K)
    (C := max |m| M₀) hrho (by linarith) hC2
    (fun j y hy => hnormD j y (hballrhoA hy)) hCbound
    (fun y hy => hdec.2.2.1 y (hballrhoA hy))
  set U : Opens (ComplexModel n) := ⟨ball z₀ (rho / 4), isOpen_ball⟩ with hUdef
  have hUA : (U : Set (ComplexModel n)) ⊆ (A : Set (ComplexModel n)) :=
    (ball_subset_ball (by linarith)).trans hballrhoA
  have hUrho : (U : Set (ComplexModel n)) ⊆ ball z₀ rho := ball_subset_ball (by linarith)
  have hdens : ∀ᵐ x : ComplexModel n, x ∈ (U : Set (ComplexModel n)) →
      Tendsto (fun k => smoothDensity (F k) x) atTop (𝓝 0) := by
    filter_upwards [hae] with x hx hxU
    obtain ⟨Ax, hsymm, hpeano⟩ := hx hxU
    have hxA : x ∈ (A : Set (ComplexModel n)) := hUA hxU
    have hconv : ∀ v w, Tendsto (fun k => realHessian (F k) x v w) atTop (𝓝 (Ax v w)) :=
      fun v w => tendsto_realHessian_translationPairing_of_hasPeanoExpansion hR hg hsymm hpeano
        (fun y hy => hgu x hxA y
          (closedBall_subset_closedBall (by linarith) hy)) v w
    have hdet0 := tendsto_det_complexHessian_zero hmax hC2 (hΩ'Ω (hAΩ' hxA))
      (fun k v => hlevi k x hxA v) hsymm hpeano hconv
    have := hdet0.const_mul ((n.factorial : ℝ) / Real.pi ^ n)
    simpa [smoothDensity] using this
  -- transfer to the Bedford--Taylor limit by dominated convergence
  have hUΩ : (U : Set (ComplexModel n)) ⊆ (Ω : Set (ComplexModel n)) :=
    (hUA.trans hAΩ').trans hΩ'Ω
  have hUrc : RelativelyCompactIn U Ω := by
    have hcl : closure (U : Set (ComplexModel n)) = closedBall z₀ (rho / 4) :=
      closure_ball z₀ (by positivity)
    refine ⟨?_, ?_⟩
    · rw [hcl]
      have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
      exact isCompact_closedBall z₀ (rho / 4)
    · rw [hcl]
      intro x hx
      refine hballΩ (mem_closedBall.mpr ?_)
      have := mem_closedBall.mp hx
      linarith
  have hdecU : IsDecApprox U u F := hdec.mono hUA
  have hadm : IsAdmissible n U (fun _ => u) (fun _ => F) :=
    ⟨fun _ => hdecU, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  have hTM := hμ.tendstoMixed hUrc hadm
  set D : ℝ := (n.factorial : ℝ) / Real.pi ^ n * ((n.factorial : ℝ) * (2 * K) ^ n) with hDdef
  have hD : ∀ k, ∀ z ∈ (U : Set (ComplexModel n)), |smoothDensity (F k) z| ≤ D := by
    intro k z hz
    exact abs_smoothDensity_le (hnormD k z (hUA hz))
  have hD0 : 0 ≤ D := by
    have : (0 : ℝ) ≤ 2 * K := by linarith
    positivity
  have hμfin : ∀ Kc : Set (ComplexModel n), IsCompact Kc → Kc ⊆ U → μ Kc < ⊤ :=
    fun Kc hKc hKcU => hμ.2.1 Kc hKc (hKcU.trans hUΩ)
  have hrestrict : μ.restrict (U : Set (ComplexModel n)) =
      (0 : Measure (ComplexModel n)).restrict (U : Set (ComplexModel n)) := by
    refine restrict_eq_of_testFunction_integral_eq hμfin (by simp) fun φ => ?_
    have hφU := φ.tsupport_subset
    have hlim := hTM φ φ.continuous φ.hasCompactSupport hφU
    simp only [mixedDensity_diagonal] at hlim
    have hcont : ∀ k, ContinuousOn (smoothDensity (F k)) (U : Set (ComplexModel n)) := by
      intro k
      have h := continuousOn_mixedDensity (n := n) (U := U) (f := fun _ : Fin n => F k)
        (fun _ => (hdecU.1 k).1)
      exact h.congr fun x _ => (mixedDensity_diagonal (F k) x).symm
    have hmeas : ∀ k, AEStronglyMeasurable
        (fun z => φ z * smoothDensity (F k) z) volume := fun k =>
      (integrable_mul_of_continuousOn (hcont k) φ.continuous φ.hasCompactSupport
        hφU).aestronglyMeasurable
    have hintb : Integrable (fun z => |φ z| * D) volume :=
      ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).abs).mul_const D
    have hbdd : ∀ k, ∀ z, ‖φ z * smoothDensity (F k) z‖ ≤ |φ z| * D := by
      intro k z
      by_cases hz : z ∈ (U : Set (ComplexModel n))
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hD k z hz) (abs_nonneg _)
      · have hφ0 : φ z = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hz (hφU h)
        simp [hφ0]
    have hlim0 : ∀ᵐ z : ComplexModel n,
        Tendsto (fun k => φ z * smoothDensity (F k) z) atTop (𝓝 0) := by
      filter_upwards [hdens] with z hz
      by_cases hzU : z ∈ (U : Set (ComplexModel n))
      · have := (hz hzU).const_mul (φ z)
        simpa using this
      · have hφ0 : φ z = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hzU (hφU h)
        simp [hφ0]
    have hzero : Tendsto (fun k => ∫ z, φ z * smoothDensity (F k) z) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (F := fun k z => φ z * smoothDensity (F k) z)
        (f := fun _ : ComplexModel n => (0 : ℝ)) (fun z => |φ z| * D) hmeas hintb
        (fun k => Eventually.of_forall (hbdd k)) hlim0
      simpa using this
    have hval : ∫ z, φ z ∂μ = 0 := tendsto_nhds_unique hlim hzero
    simp [hval]
  refine ⟨rho / 4, by positivity, ?_⟩
  have h0 : μ (U : Set (ComplexModel n)) = 0 := by simpa using hrestrict
  exact h0

/-- **Blocki, Theorem 2.3.1 (the direction balayage needs).**  A maximal,
locally bounded, locally semiconcave plurisubharmonic function carries no
Bedford--Taylor mass. -/
theorem eq_zero_of_isBTLimit_of_isMaximalPshOn
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hmax : IsMaximalPshOn Ω u)
    (hsc : IsLocallySemiconcaveOn Ω u)
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω (fun _ => u) μ) :
    μ = 0 := by
  classical
  have key : ∀ z ∈ (Ω : Set (ComplexModel n)), ∃ ρ : ℝ, 0 < ρ ∧ μ (ball z ρ) = 0 := by
    intro z hz
    obtain ⟨ρ, hρ, hzero⟩ := measure_ball_eq_zero_of_isMaximalPshOn hu hmax hsc hμ hz
    exact ⟨ρ, hρ, hzero⟩
  choose! ρ hρpos hρzero using key
  set S : {x : ComplexModel n // x ∈ (Ω : Set (ComplexModel n))} → Set (ComplexModel n) :=
    fun z => ball (z : ComplexModel n) (ρ (z : ComplexModel n)) with hSdef
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable S fun _ => isOpen_ball
  have hcover : (Ω : Set (ComplexModel n)) ⊆ ⋃ i, S i := by
    intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hρpos x hx)⟩
  have hnull : μ (⋃ i, S i) = 0 := by
    rw [← hTU]
    exact (measure_biUnion_null_iff hTc).2 fun i _ => hρzero (i : ComplexModel n) i.property
  have hΩ0 : μ (Ω : Set (ComplexModel n)) = 0 := measure_mono_null hcover hnull
  have huniv : μ univ = 0 := by
    have := measure_union_null hΩ0 hμ.1
    simpa using this
  exact Measure.measure_univ_eq_zero.mp huniv

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end

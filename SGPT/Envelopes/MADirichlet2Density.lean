import SGPT.Foundations.Analysis.Pending.MaximalPshVanishingMass
import SGPT.Envelopes.MADirichletMeasure

/-!
# Upper bounds for the Monge–Ampère measure of a semiconcave plurisubharmonic function

Xia, *Foundations of pluripotential theory* (FPT), `lem:second-difference-regularity`, the
measure part, in the form needed for the upper bound of `thm:continuous-density-ball-dirichlet`,
Step 3: if `u` is locally bounded, plurisubharmonic and locally semiconcave on `Ω` (one-sided
second differences `u(y + h) + u(y - h) - 2u(y) ≤ K|h|²`, TN's `IsLocallySemiconcaveOn`), then
almost every point carries a second-order (Peano) expansion of `u` (TN, Rademacher), and

  `(ddᶜu)ⁿ ≤ (n!/πⁿ) g dV`   on `Ω`

as soon as `det(u_{j k̄}(x)) ≤ g(x)` at every such point, for a continuous `g ≥ 0`
(`canonicalBedfordTaylorMeasure_le_of_peano`). Here `(u_{j k̄}(x))` is the complex Hessian of the
quadratic part of the expansion (`complexHessianOfBilin`), which is positive semidefinite
(`posSemidef_complexHessianOfBilin_of_tendsto`).

The proof is TN's proof of `measure_ball_eq_zero_of_isMaximalPshOn` (Błocki, Theorem 2.3.1) with
the vanishing of the limiting determinant replaced by the bound `g`: the radial mollifications
`Fₖ = u ∗ ρₖ` have uniformly bounded Hessians, their Monge–Ampère densities converge at the Peano
points to `(n!/πⁿ) det(u_{j k̄})`, and dominated convergence applied to the positive part of
`(n!/πⁿ) det (Fₖ)_{j k̄} - (n!/πⁿ) g` gives the bound for every nonnegative test function.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace Matrix
open scoped Topology ENNReal ComplexOrder

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- The complex Hessian of a limit of real Hessians of functions with nonnegative Levi forms is
positive semidefinite (extracted from TN's `tendsto_det_complexHessian_zero`). -/
theorem posSemidef_complexHessianOfBilin_of_tendsto {F : ℕ → ComplexModel n → ℝ}
    (hF : ∀ k, ContDiff ℝ 2 (F k)) {z₀ : ComplexModel n} (hlevi : ∀ k v, 0 ≤ leviForm (F k) z₀ v)
    {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hconv : ∀ v w, Tendsto (fun k ↦ realHessian (F k) z₀ v w) atTop (𝓝 (A v w))) :
    (complexHessianOfBilin A).PosSemidef := by
  set H := complexHessianOfBilin A with hHdef
  have hmat := tendsto_complexHessian_of_tendsto_realHessian hconv
  have hℓ : ∀ v, Tendsto (fun k ↦ leviForm (F k) z₀ v) atTop (𝓝 (leviFormOfBilin A v)) := by
    intro v
    simp only [leviForm, leviFormOfBilin]
    exact ((hconv v v).add (hconv _ _)).div_const 4
  have hℓnonneg : ∀ v, 0 ≤ leviFormOfBilin A v := fun v ↦
    ge_of_tendsto (hℓ v) (Eventually.of_forall fun k ↦ hlevi k v)
  have hquad : ∀ y : Fin n → ℂ,
      star y ⬝ᵥ (H.mulVec y) = ((leviFormOfBilin A (coordCombination y) : ℝ) : ℂ) := by
    intro y
    have h1 := tendsto_dotProduct_mulVec hmat y
    have h2 : ∀ k, star y ⬝ᵥ ((complexHessian (F k) z₀).mulVec y)
        = ((leviForm (F k) z₀ (coordCombination y) : ℝ) : ℂ) := fun k ↦
      dotProduct_mulVec_complexHessian_eq_leviForm ((hF k).contDiffAt) y
    have h3 : Tendsto (fun k ↦ star y ⬝ᵥ ((complexHessian (F k) z₀).mulVec y)) atTop
        (𝓝 ((leviFormOfBilin A (coordCombination y) : ℝ) : ℂ)) := by
      simp only [h2]
      exact tendsto_ofReal (hℓ (coordCombination y))
    exact tendsto_nhds_unique h1 h3
  have hherm : H.IsHermitian := by
    have hk : ∀ k, (complexHessian (F k) z₀).IsHermitian := fun k ↦
      complexHessian_isHermitian ((hF k).contDiffAt)
    have hconj : Tendsto (fun k ↦ (complexHessian (F k) z₀)ᴴ) atTop (𝓝 Hᴴ) := by
      refine tendsto_pi_nhds.2 fun j ↦ tendsto_pi_nhds.2 fun l ↦ ?_
      simp only [conjTranspose_apply]
      exact ((continuous_star (R := ℂ)).tendsto (H l j)).comp
        (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hmat l) j)
    have hself : Tendsto (fun k ↦ (complexHessian (F k) z₀)ᴴ) atTop (𝓝 H) := by
      have hfun : (fun k ↦ (complexHessian (F k) z₀)ᴴ) = fun k ↦ complexHessian (F k) z₀ :=
        funext fun k ↦ hk k
      rw [hfun]
      exact hmat
    exact tendsto_nhds_unique hconj hself
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun y ↦ ?_
  rw [hquad y]
  exact Complex.zero_le_real.mpr (hℓnonneg _)

/-- **Local upper bound for the Monge–Ampère measure of a semiconcave psh function.** -/
theorem exists_ball_restrict_le_of_peano {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hsc : IsLocallySemiconcaveOn Ω u)
    {g : ComplexModel n → ℝ} (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z)
    (hpeano : ∀ x ∈ Ω, ∀ A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ,
      (∀ v w, A v w = A w v) → HasPeanoExpansionAt u x (fderiv ℝ u x) A →
      (complexHessianOfBilin A).PosSemidef → (complexHessianOfBilin A).det.re ≤ g x)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ Ω) :
    ∃ ρ > 0, (canonicalBedfordTaylorMeasure Ω u hu).restrict (ball z₀ ρ) ≤
      (volume.withDensity fun z => ENNReal.ofReal (mongeAmpereConst n * g z)).restrict
        (ball z₀ ρ) := by
  classical
  set μ := canonicalBedfordTaylorMeasure Ω u hu with hμdef
  have hμ : IsBTLimit Ω (fun _ => u) μ := isBTLimit_canonicalBedfordTaylorMeasure hu
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
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  have hArc : RelativelyCompactIn A Ω' := by
    refine ⟨?_, ?_⟩
    · rw [hclA]
      exact isCompact_closedBall z₀ (r / 4)
    · rw [hclA]
      intro x hx
      exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith))
  have hu' : IsLocallyBoundedPshOn Ω' u := by
    refine ⟨hu.1.mono hΩ'Ω, fun z hz => ?_⟩
    obtain ⟨V, hzV, hVΩ, C, hC⟩ := hu.2 z (hΩ'Ω hz)
    exact ⟨V ⊓ Ω', ⟨hzV, hz⟩, inf_le_right, C, fun w hw => hC w hw.1⟩
  obtain ⟨R, hR, g₀, hRδ, hg₀, hballR, hgu, hdec, hC2, hlevi⟩ :=
    exists_mollifier_family hArc hu' (δ₀ := r / 4) (by positivity)
  set F : ℕ → ComplexModel n → ℝ :=
    fun j => translationPairing volume g₀ (explicitRadialKernel R hR j) with hFdef
  have hnormD : ∀ j, ∀ z ∈ (A : Set (ComplexModel n)),
      ‖fderiv ℝ (fderiv ℝ (F j)) z‖ ≤ 2 * K := by
    intro j z hz
    refine norm_fderiv_fderiv_le_of_secondDifference (hC2 j) hK ?_ (fun v => hlevi j z hz v)
    filter_upwards [ball_mem_nhds (0 : ComplexModel n) hR] with h hh
    have hhR : ‖h‖ ≤ R := le_of_lt (by simpa [dist_zero_right] using mem_ball.mp hh)
    refine secondDifference_translationPairing hR hg₀ (hgu z hz) ?_ j hhR
    intro y hy h' hh'
    refine hsd y ?_ h' (le_trans hh' (by linarith))
    have hyz : dist y z ≤ R := mem_closedBall.mp hy
    have hzz : dist z z₀ < r / 4 := mem_ball.mp hz
    refine mem_closedBall.mpr ?_
    have := dist_triangle y z z₀
    linarith
  set rho : ℝ := r / 8 with hrhodef
  have hrho : 0 < rho := by positivity
  have hballrhoA : ball z₀ rho ⊆ (A : Set (ComplexModel n)) := ball_subset_ball (by linarith)
  have hK₀A : closedBall z₀ rho ⊆ (A : Set (ComplexModel n)) := by
    intro x hx
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith))
  have hK₀c : IsCompact (closedBall z₀ rho) := isCompact_closedBall z₀ rho
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
    rw [abs_le]
    constructor
    · have : -|m| ≤ m := neg_abs_le m
      have h1 : -max |m| M₀ ≤ -|m| := by
        simp only [neg_le_neg_iff]
        exact le_max_left _ _
      linarith
    · exact le_trans hup (le_max_right _ _)
  have hae := ae_exists_hasPeanoExpansion (c := z₀) (ρ := rho) (M := 2 * K)
    (C := max |m| M₀) hrho (by linarith) hC2
    (fun j y hy => hnormD j y (hballrhoA hy)) hCbound
    (fun y hy => hdec.2.2.1 y (hballrhoA hy))
  set U : Opens (ComplexModel n) := ⟨ball z₀ (rho / 4), isOpen_ball⟩ with hUdef
  have hUA : (U : Set (ComplexModel n)) ⊆ (A : Set (ComplexModel n)) :=
    (ball_subset_ball (by linarith)).trans hballrhoA
  have hUΩ : (U : Set (ComplexModel n)) ⊆ (Ω : Set (ComplexModel n)) :=
    (hUA.trans hAΩ').trans hΩ'Ω
  set c : ℝ := mongeAmpereConst n with hcdef
  have hc0 : 0 ≤ c := mongeAmpereConst_pos.le
  -- at almost every point the positive part of `density - c g` tends to zero
  have hdens : ∀ᵐ x : ComplexModel n, x ∈ (U : Set (ComplexModel n)) →
      Tendsto (fun k => max (smoothDensity (F k) x - c * g x) 0) atTop (𝓝 0) := by
    filter_upwards [hae] with x hx hxU
    obtain ⟨Ax, hsymm, hpe⟩ := hx hxU
    have hxA : x ∈ (A : Set (ComplexModel n)) := hUA hxU
    have hconv : ∀ v w, Tendsto (fun k => realHessian (F k) x v w) atTop (𝓝 (Ax v w)) :=
      fun v w => tendsto_realHessian_translationPairing_of_hasPeanoExpansion hR hg₀ hsymm hpe
        (fun y hy => hgu x hxA y
          (closedBall_subset_closedBall (by linarith) hy)) v w
    have hpsd := posSemidef_complexHessianOfBilin_of_tendsto hC2 (fun k v ↦ hlevi k x hxA v) hconv
    have hle := hpeano x (hUΩ hxU) Ax hsymm hpe hpsd
    have hmat := tendsto_complexHessian_of_tendsto_realHessian hconv
    have hdet : Tendsto (fun k ↦ (complexHessian (F k) x).det) atTop
        (𝓝 (complexHessianOfBilin Ax).det) :=
      (Continuous.matrix_det continuous_id).tendsto _ |>.comp hmat
    have hre := ((Complex.continuous_re.tendsto _).comp hdet).const_mul c
    have hsd : Tendsto (fun k ↦ smoothDensity (F k) x) atTop
        (𝓝 (c * (complexHessianOfBilin Ax).det.re)) := by
      simpa [smoothDensity, hcdef, mongeAmpereConst, Function.comp_def] using hre
    have hlim := (hsd.sub_const (c * g x)).max (tendsto_const_nhds (x := (0 : ℝ)))
    have h0 : max (c * (complexHessianOfBilin Ax).det.re - c * g x) 0 = 0 :=
      max_eq_right (by nlinarith)
    rwa [h0] at hlim
  -- transfer to the Bedford–Taylor measure by dominated convergence
  have hUrc : RelativelyCompactIn U Ω := by
    have hcl : closure (U : Set (ComplexModel n)) = closedBall z₀ (rho / 4) :=
      closure_ball z₀ (by positivity)
    refine ⟨?_, ?_⟩
    · rw [hcl]
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
  set ν : Measure (ComplexModel n) :=
    volume.withDensity fun z => ENNReal.ofReal (mongeAmpereConst n * g z) with hνdef
  have hgm : Measurable fun z => ENNReal.ofReal (mongeAmpereConst n * g z) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hg.measurable)
  have hνf : ∀ Kc, IsCompact Kc → Kc ⊆ (U : Set (ComplexModel n)) → ν Kc < ⊤ := by
    intro Kc hKc _
    obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hg.continuousOn (s := Kc))
    rw [hνdef, withDensity_apply _ hKc.measurableSet]
    refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal
      (mongeAmpereConst n * B)) measurable_const fun z hz => ?_) ?_
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc0)
      have := hB z hz
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    · rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top
  have hμf : ∀ Kc : Set (ComplexModel n), IsCompact Kc → Kc ⊆ U → μ Kc < ⊤ :=
    fun Kc hKc hKcU => hμ.2.1 Kc hKc (hKcU.trans hUΩ)
  have htest : ∀ φ : ComplexModel n → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ (U : Set (ComplexModel n)) → (∀ z, 0 ≤ φ z) →
      ∫ z, φ z ∂μ ≤ ∫ z, φ z ∂ν := by
    intro φ hφ hφc hφU hφ0
    have hlim := hTM φ hφ hφc hφU
    simp only [mixedDensity_diagonal] at hlim
    have hcont : ∀ k, ContinuousOn (smoothDensity (F k)) (U : Set (ComplexModel n)) := by
      intro k
      have h := continuousOn_mixedDensity (n := n) (U := U) (f := fun _ : Fin n => F k)
        (fun _ => (hdecU.1 k).1)
      exact h.congr fun x _ => (mixedDensity_diagonal (F k) x).symm
    have hgcU : ContinuousOn (fun z => c * g z) (U : Set (ComplexModel n)) :=
      (continuous_const.mul hg).continuousOn
    have hpos : ∀ k, ContinuousOn (fun z => max (smoothDensity (F k) z - c * g z) 0)
        (U : Set (ComplexModel n)) := fun k =>
      ContinuousOn.sup (f := fun z => smoothDensity (F k) z - c * g z)
        ((hcont k).sub hgcU) continuousOn_const
    have hint1 : ∀ k, Integrable fun z => φ z * smoothDensity (F k) z := fun k =>
      integrable_mul_of_continuousOn (hcont k) hφ hφc hφU
    have hint2 : Integrable fun z => φ z * (c * g z) :=
      integrable_mul_of_continuousOn hgcU hφ hφc hφU
    have hint3 : ∀ k, Integrable fun z => φ z * max (smoothDensity (F k) z - c * g z) 0 :=
      fun k => integrable_mul_of_continuousOn (hpos k) hφ hφc hφU
    have hpt : ∀ k, (∫ z, φ z * smoothDensity (F k) z) ≤
        (∫ z, φ z * (c * g z)) + ∫ z, φ z * max (smoothDensity (F k) z - c * g z) 0 := by
      intro k
      rw [← integral_add hint2 (hint3 k)]
      refine integral_mono (hint1 k) (hint2.add (hint3 k)) fun z => ?_
      have := hφ0 z
      have hm : smoothDensity (F k) z ≤ c * g z + max (smoothDensity (F k) z - c * g z) 0 := by
        have := le_max_left (smoothDensity (F k) z - c * g z) 0
        linarith
      nlinarith
    -- the error term tends to zero
    have hbdd : ∀ k, ∀ z, ‖φ z * max (smoothDensity (F k) z - c * g z) 0‖ ≤ |φ z| * D := by
      intro k z
      by_cases hz : z ∈ (U : Set (ComplexModel n))
      · rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_of_nonneg (le_max_right _ _)]
        refine max_le ?_ ((abs_nonneg _).trans (hD k z hz))
        have := mul_nonneg hc0 (hg0 z)
        linarith [le_abs_self (smoothDensity (F k) z), hD k z hz]
      · have hφ0' : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hφU h)
        simp [hφ0']
    have hintb : Integrable (fun z => |φ z| * D) volume :=
      ((hφ.integrable_of_hasCompactSupport hφc).abs).mul_const D
    have hlim0 : ∀ᵐ z : ComplexModel n,
        Tendsto (fun k => φ z * max (smoothDensity (F k) z - c * g z) 0) atTop (𝓝 0) := by
      filter_upwards [hdens] with z hz
      by_cases hzU : z ∈ (U : Set (ComplexModel n))
      · simpa using (hz hzU).const_mul (φ z)
      · have hφ0' : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzU (hφU h)
        simp [hφ0']
    have hzero : Tendsto (fun k => ∫ z, φ z * max (smoothDensity (F k) z - c * g z) 0)
        atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence
        (F := fun k z => φ z * max (smoothDensity (F k) z - c * g z) 0)
        (f := fun _ : ComplexModel n => (0 : ℝ)) (fun z => |φ z| * D)
        (fun k => (hint3 k).aestronglyMeasurable) hintb
        (fun k => Eventually.of_forall (hbdd k)) hlim0
      simpa using this
    have hle : ∫ z, φ z ∂μ ≤ ∫ z, φ z * (c * g z) := by
      have h2 := (tendsto_const_nhds (x := ∫ z, φ z * (c * g z))).add hzero
      rw [add_zero] at h2
      exact le_of_tendsto_of_tendsto' hlim h2 hpt
    have hν : ∫ z, φ z ∂ν = ∫ z, φ z * (c * g z) := by
      rw [hνdef, integral_withDensity_eq_integral_toReal_smul hgm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [smul_eq_mul]
      rw [ENNReal.toReal_ofReal (mul_nonneg hc0 (hg0 z))]
      ring
    rw [hν]
    exact hle
  have hcpt : ∀ Kc, IsCompact Kc → Kc ⊆ (U : Set (ComplexModel n)) → μ Kc ≤ ν Kc :=
    fun Kc hKc hKcU => measure_le_of_testFunction_integral_le hμf hνf htest hKc hKcU
  have hres := restrict_le_of_isCompact_le (Ω := U) hμf hcpt
  refine ⟨rho / 4, by positivity, ?_⟩
  have h1 : μ.restrict (U : Set (ComplexModel n)) ≤ ν.restrict (U : Set (ComplexModel n)) := by
    have := Measure.restrict_mono (s := (U : Set (ComplexModel n))) subset_rfl hres
    rwa [Measure.restrict_restrict_of_subset subset_rfl] at this
  exact h1

/-- **The Monge–Ampère measure of a semiconcave psh function is bounded by the determinant of
its almost-everywhere complex Hessian** (FPT `lem:second-difference-regularity`, upper bound). -/
theorem canonicalBedfordTaylorMeasure_le_of_peano {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hsc : IsLocallySemiconcaveOn Ω u)
    {g : ComplexModel n → ℝ} (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z)
    (hpeano : ∀ x ∈ Ω, ∀ A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ,
      (∀ v w, A v w = A w v) → HasPeanoExpansionAt u x (fderiv ℝ u x) A →
      (complexHessianOfBilin A).PosSemidef → (complexHessianOfBilin A).det.re ≤ g x) :
    canonicalBedfordTaylorMeasure Ω u hu ≤
      (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        fun z => ENNReal.ofReal (mongeAmpereConst n * g z) := by
  set μ := canonicalBedfordTaylorMeasure Ω u hu
  set ν : Measure (ComplexModel n) :=
    volume.withDensity fun z => ENNReal.ofReal (mongeAmpereConst n * g z)
  have hglue := restrict_le_restrict_of_isLindelof (μ := μ) (ν := ν)
    (HereditarilyLindelofSpace.isLindelof (Ω : Set (ComplexModel n))) fun x hx => by
      obtain ⟨ρ, hρ, hle⟩ := exists_ball_restrict_le_of_peano hu hsc hg hg0 hpeano hx
      exact ⟨ball x ρ, isOpen_ball, mem_ball_self hρ, hle⟩
  have hμΩ : μ.restrict (Ω : Set (ComplexModel n)) = μ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (canonicalBedfordTaylorMeasure_compl Ω u hu))
  rw [hμΩ, restrict_withDensity Ω.isOpen.measurableSet] at hglue
  exact hglue

end SGPT.Envelopes.MADirichlet

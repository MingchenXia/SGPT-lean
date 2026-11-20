import SGPT.Unibranch.FNLChart

/-!
# Sublevel sets of weakly psh functions on sets with local branched-covering charts

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), proof of Theorem 5.3.1, first half (`[FN80]`), used for SGPT `thm:FN`
(2) ⇒ (1) (`appendix_unibranch.tex`).

The first half of the proof of `[FN80, Thm. 5.3.1]` shows that `{ψ < 0}` is Runge in `X × ℂ`
for `ψ(z, w) = φ(z) + log |w|`. Its argument works for every weakly plurisubharmonic function on
a set `Y ⊆ ℂᴺ` which near each of its points is (after a linear change of coordinates) a finite
branched covering of a polydisc, and this is what we prove here
(`polyHull_subset_sublevel_of_charts`):

> `Y` with local branched-covering charts (`FNL.HasCoveringChartAt`) at all of its points,
> `u ∈ WP(Y)`, `K ⊆ Y` compact with `K̂ ⊆ Y` and `u < 0` on `K`  ⟹  `u < 0` on `K̂`.

Proof (`[FN80]`): otherwise choose `ε > 0` with `φ₁ = u + ε‖x‖² < 0` on `K`, and a point `p`
of the compact set `K̂` where `φ₁` attains its maximum `m ≥ 0`. The function
`u₂ = φ₁ - m - (ε/2)‖x - p‖² = u + (ε/2)‖x + p‖² - ε‖p‖² - m` is weakly psh on `Y`,
`u₂(p) = 0` and `u₂ < 0` on `F = K̂ ∩ ∂B(p, ρ)`. By Rossi's local maximum principle
(`FNR.mem_polyHull_inter_sphere`) `p ∈ F̂`; in a branched-covering chart `T` at `p` this
contradicts `[FN80]` Lemma 5.2 (`FNL.runge_sublevel_of_isWeaklyPSHOn`) applied to `u₂ ∘ T⁻¹`
and `T(F)`, since polynomial hulls are invariant under linear maps
(`image_polyHull_subset_clm`).
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNH

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron SGPT.Unibranch.E2Nov16FNHolomorphicHullMaximum
open SGPT.Unibranch.FNR SGPT.Unibranch.FNL

variable {N : ℕ}

/-! ### Linear maps and polynomial hulls -/

/-- Coordinates of a linear map. -/
theorem clm_apply_eq_sum {m : ℕ} (T : ComplexModel N →L[ℂ] ComplexModel m) (z : ComplexModel N)
    (i : Fin m) : T z i = ∑ j, T (EuclideanSpace.single j 1) i * z j := by
  classical
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℂ).sum_repr z]
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, map_sum, map_smul]
  rw [WithLp.ofLp_sum]
  simp [mul_comm]

/-- A continuous linear map `ℂᴺ → ℂᵐ` is a polynomial map. -/
theorem clm_eq_polyMap {m : ℕ} (T : ComplexModel N →L[ℂ] ComplexModel m) :
    ⇑T = polyMap fun i => ∑ j, MvPolynomial.C (T (EuclideanSpace.single j 1) i) *
      MvPolynomial.X j := by
  funext z
  ext i
  rw [clm_apply_eq_sum]
  simp [polyMap, polyEval]

/-- Linear maps send polynomial hulls into polynomial hulls. -/
theorem image_polyHull_subset_clm {m : ℕ} (T : ComplexModel N →L[ℂ] ComplexModel m)
    (K : Set (ComplexModel N)) : T '' polyHull K ⊆ polyHull (T '' K) := by
  rw [clm_eq_polyMap T]
  exact image_polyHull_subset _ K

/-- Weak plurisubharmonicity is preserved by pull-back along linear maps. -/
theorem isWeaklyPSHOn_comp_clm {M : ℕ} {X : Set (ComplexModel N)} {φ : ComplexModel N → EReal}
    (hφ : IsWeaklyPSHOn X φ) (L : ComplexModel M →L[ℂ] ComplexModel N)
    {Y : Set (ComplexModel M)} (hY : MapsTo L Y X) : IsWeaklyPSHOn Y (fun y => φ (L y)) :=
  ⟨fun _ hy => hφ.ne_top _ (hY hy), hφ.upperSemicontinuousOn.comp L.continuous.continuousOn hY,
    fun f hf hfY => hφ.disc (fun t => L (f t)) (L.differentiable.comp_differentiableOn hf)
      (fun _ ht => hY (hfY ht))⟩

/-! ### The Runge property from local branched-covering charts -/

theorem parallelogram_sq (y p : ComplexModel N) :
    ‖y + p‖ ^ 2 + ‖y - p‖ ^ 2 = 2 * ‖y‖ ^ 2 + 2 * ‖p‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℂ y p
  nlinarith [h]

/-- **`[FN80]` Thm. 5.3.1, the Runge step, for sets with local branched-covering charts.** Let
`Y ⊆ ℂᴺ` have a branched-covering chart (`FNL.HasCoveringChartAt`) at each of its points, let
`u ∈ WP(Y)`, and let `K ⊆ ℂᴺ` be compact with `K̂ ⊆ Y` and `u < 0` on `K`. Then `u < 0` on the
polynomial hull `K̂`. -/
theorem polyHull_subset_sublevel_of_charts {Y K : Set (ComplexModel N)}
    {u : ComplexModel N → EReal} (hchart : ∀ p ∈ Y, HasCoveringChartAt Y p univ)
    (hu : IsWeaklyPSHOn Y u) (hK : IsCompact K) (hKY : polyHull K ⊆ Y)
    (hKu : ∀ x ∈ K, u x < 0) : polyHull K ⊆ {x | u x < 0} := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe, polyHull_empty]; exact empty_subset _
  have hKsub : K ⊆ polyHull K := subset_polyHull K
  have hKY' : K ⊆ Y := hKsub.trans hKY
  -- a real negative bound for `u` on `K`
  obtain ⟨k₀, hk₀K, hk₀max⟩ := (hu.upperSemicontinuousOn.mono hKY').exists_isMaxOn hKne hK
  obtain ⟨s, hk₀s, hs0⟩ := EReal.exists_between_coe_real (hKu k₀ hk₀K)
  have hs : s < 0 := by exact_mod_cast hs0
  obtain ⟨C₀, hC₀⟩ := hK.isBounded.exists_norm_le
  set C : ℝ := C₀ ^ 2 with hCdef
  have hC : 0 ≤ C := sq_nonneg _
  set ε : ℝ := -s / (2 * (C + 1)) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hεC : ε * C ≤ -s / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- `φ₁ = u + ε ‖x‖²`
  set φ₁ : ComplexModel N → EReal := fun x => u x + ((ε * ‖x‖ ^ 2 : ℝ) : EReal) with hφ₁def
  have hφ₁K : ∀ x ∈ K, φ₁ x < 0 := by
    intro x hx
    have h1 : u x < (s : EReal) := lt_of_le_of_lt (hk₀max hx) hk₀s
    have h2 : ε * ‖x‖ ^ 2 ≤ ε * C := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      rw [hCdef]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC₀ x hx) 2
    calc φ₁ x < ((s : ℝ) : EReal) + ((ε * ‖x‖ ^ 2 : ℝ) : EReal) :=
          EReal.add_lt_add_right_coe h1 _
      _ = ((s + ε * ‖x‖ ^ 2 : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ < 0 := by
          rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]
          linarith
  set H := polyHull K with hHdef
  have hHc : IsCompact H := isCompact_polyHull hK
  have hHne : H.Nonempty := hKne.mono hKsub
  have hquad_cont : Continuous fun x : ComplexModel N => ((ε * ‖x‖ ^ 2 : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp (continuous_const.mul (continuous_norm.pow 2))
  have hφ₁usc : UpperSemicontinuousOn φ₁ H :=
    (hu.upperSemicontinuousOn.mono hKY).add' (hquad_cont.upperSemicontinuous.upperSemicontinuousOn H)
      fun x hx => EReal.continuousAt_add (Or.inl (hu.ne_top x (hKY hx)))
        (Or.inr (EReal.coe_ne_top _))
  obtain ⟨p, hpH, hpmax⟩ := hφ₁usc.exists_isMaxOn hHne hHc
  intro z hz
  by_contra hzu
  have hz0 : 0 ≤ u z := not_lt.mp hzu
  have hφ₁z : u z ≤ φ₁ z := le_add_of_nonneg_right (EReal.coe_nonneg.mpr (by positivity))
  have hp0 : 0 ≤ φ₁ p := hz0.trans (hφ₁z.trans (hpmax hz))
  have hpY : p ∈ Y := hKY hpH
  have hpK : p ∉ K := fun hpK => absurd (hφ₁K p hpK) (not_lt.mpr hp0)
  -- `u p` is finite
  have hup_bot : u p ≠ ⊥ := by
    intro h
    have : φ₁ p = ⊥ := by simp only [hφ₁def, h, EReal.bot_add]
    rw [this] at hp0
    exact absurd hp0 (not_le.mpr EReal.bot_lt_zero)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, u p = a :=
    ⟨(u p).toReal, (EReal.coe_toReal (hu.ne_top p hpY) hup_bot).symm⟩
  set m : ℝ := a + ε * ‖p‖ ^ 2 with hmdef
  have hφ₁p : φ₁ p = (m : EReal) := by
    simp only [hφ₁def, ha, hmdef, EReal.coe_add]
  -- a branched-covering chart at `p`
  obtain ⟨T, d, hdN, r, D, deg, δ, hr, -, hπ, hcov, heq⟩ := hchart p hpY
  -- the radius `ρ`
  obtain ⟨ρ₁, hρ₁, hρ₁K⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl p hpK
  have hTpre : IsOpen (T ⁻¹' pdisc (T p) r) := (isOpen_pdisc _ _).preimage T.continuous
  have hTp : p ∈ T ⁻¹' pdisc (T p) r := fun i => by simpa using hr i
  obtain ⟨ρ₂, hρ₂, hρ₂T⟩ := Metric.isOpen_iff.mp hTpre p hTp
  set ρ : ℝ := min ρ₁ ρ₂ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ < ρ₁ := by
    have := min_le_left ρ₁ ρ₂; rw [hρdef]; linarith
  have hρ2 : ρ < ρ₂ := by
    have := min_le_right ρ₁ ρ₂; rw [hρdef]; linarith
  have hdisj : Disjoint K (closedBall p ρ) := by
    rw [disjoint_comm, Set.disjoint_iff]
    intro y ⟨hy, hyK⟩
    exact hρ₁K (closedBall_subset_ball hρ1 hy) hyK
  have hBT : closedBall p ρ ⊆ T ⁻¹' pdisc (T p) r := (closedBall_subset_ball hρ2).trans hρ₂T
  -- Rossi
  set F := H ∩ sphere p ρ with hFdef
  have hpF : p ∈ polyHull F := mem_polyHull_inter_sphere hK hpH hρ hdisj
  have hFc : IsCompact F := hHc.inter_right isClosed_sphere
  have hFY : F ⊆ Y := fun y hy => hKY hy.1
  -- `u₂ = u + (ε/2) ‖x + p‖² - ε ‖p‖² - m`
  set u₂ : ComplexModel N → EReal := fun x =>
    u x + (((ε / 2) * ‖x - -p‖ ^ 2 + (-(ε * ‖p‖ ^ 2) - m) : ℝ) : EReal) with hu₂def
  have hu₂ : IsWeaklyPSHOn Y u₂ :=
    hu.add (IsWeaklyPSHOn.of_plurisubharmonicOn
      (plurisubharmonicOn_quadratic (by positivity : (0 : ℝ) ≤ ε / 2) (-p)
        (-(ε * ‖p‖ ^ 2) - m)) (subset_univ _))
  have hu₂p : u₂ p = 0 := by
    have hpp : ‖p - -p‖ = 2 * ‖p‖ := by
      rw [sub_neg_eq_add, ← two_smul ℝ p, norm_smul]; norm_num
    simp only [hu₂def, ha, ← EReal.coe_add, hpp, hmdef]
    rw [← EReal.coe_zero, EReal.coe_eq_coe_iff]
    ring
  have hu₂F : ∀ y ∈ F, u₂ y < 0 := by
    intro y hy
    have hyH : y ∈ H := hy.1
    have hyρ : ‖y - p‖ = ρ := by rw [← dist_eq_norm]; exact hy.2
    have hle : φ₁ y ≤ (m : EReal) := hφ₁p ▸ hpmax hyH
    induction hyu : u y using EReal.rec with
    | bot => simp [hu₂def, hyu, EReal.bot_lt_zero]
    | top => exact absurd hyu (hu.ne_top y (hFY hy))
    | coe b =>
      have hb : b + ε * ‖y‖ ^ 2 ≤ m := by
        have h := hle
        simp only [hφ₁def, hyu, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
        exact h
      simp only [hu₂def, hyu, ← EReal.coe_add]
      rw [← EReal.coe_zero, EReal.coe_lt_coe_iff, sub_neg_eq_add]
      have hpar := parallelogram_sq y p
      rw [hyρ] at hpar
      have h1 : ‖y + p‖ ^ 2 = 2 * ‖y‖ ^ 2 + 2 * ‖p‖ ^ 2 - ρ ^ 2 := by linarith
      have h2 : 0 < ε * ρ ^ 2 := by positivity
      rw [h1]
      linarith
  -- transport to the chart
  set Z := T '' Y ∩ pdisc (T p) r with hZdef
  set v : ComplexModel N → EReal := fun x => u₂ (T.symm x) with hvdef
  have hv : IsWeaklyPSHOn Z v := by
    refine isWeaklyPSHOn_comp_clm hu₂ (T.symm : ComplexModel N →L[ℂ] ComplexModel N) ?_
    rintro x ⟨⟨y, hy, rfl⟩, -⟩
    simpa using hy
  have hTFc : IsCompact (T '' F) := hFc.image T.continuous
  have hTFZ : T '' F ⊆ Z := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨⟨y, hFY hy, rfl⟩, hBT (sphere_subset_closedBall hy.2)⟩
  have hTFv : ∀ x ∈ T '' F, v x < 0 := by
    rintro x ⟨y, hy, rfl⟩
    simpa [hvdef] using hu₂F y hy
  have hrunge := runge_sublevel_of_isWeaklyPSHOn hdN deg hcov hπ inter_subset_right heq hv hTFc
    hTFZ hTFv
  have hTp : T p ∈ polyHull (T '' F) :=
    image_polyHull_subset_clm (T : ComplexModel N →L[ℂ] ComplexModel N) F ⟨p, hpF, rfl⟩
  have hlt : v (T p) < 0 := hrunge hTp
  simp only [hvdef, ContinuousLinearEquiv.symm_apply_apply] at hlt
  rw [hu₂p] at hlt
  exact lt_irrefl _ hlt

end SGPT.Unibranch.FNH

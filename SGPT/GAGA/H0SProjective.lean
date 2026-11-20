import SGPT.GAGA.H0SLojasiewicz

/-!
# Holomorphic sections of `𝒪(k)` on a projective submanifold are polynomials


Let `Φ : M → ℙᴺ` be a holomorphic embedding of a compact complex manifold of dimension `n`
(`IsHolomorphicEmbedding`), and suppose `Φ(M)` has polynomial equations satisfying the Jacobian
criterion (`IsJacobianPresentation`): in every affine chart `U_i ≅ ℂᴺ` polynomials `g_{i,j}`
vanish on `Φ(M) ∩ U_i`, have no other common zeros in `U_i`, and at every point of
`Φ(M) ∩ U_i` every vector killed by all their differentials is tangent to `Φ(M)`.

**Theorem** (`exists_isHomogeneous_eq_of_jacobianPresentation`).  There is `k₀` such that for
`k ≥ k₀`, every function `F` on the affine cone `Ŝ` over `Φ(M)`, homogeneous of degree `k` and
holomorphic on `Ŝ ∖ 0` (a holomorphic section of `𝒪(k)|_{Φ(M)}`), is the restriction of a
homogeneous polynomial of degree `k`.

Proof: the cone is closed and a local graph of codimension `N - n` off the vertex
(`isLocalGraphAt_affineCone`); the Jacobian criterion gives the local Łojasiewicz inequality
(`exists_local_lojasiewicz` in the coordinates of `exists_affine_graph`), hence the global one
for the homogenized equations (`exists_cone_lojasiewicz`); the `L²` extension theorem
`SGPT.GAGA.H0.exists_isHomogeneous_eq_of_isLocallyHolomorphicOn` concludes.  In codimension `0`
the cone is all of `ℂ^{N+1}` (connectedness of `ℂ^{N+1} ∖ 0`) and `F` is a homogeneous
holomorphic function on `ℂ^{N+1} ∖ 0` (`SGPT.GAGA.exists_isHomogeneous_eq_of_homogeneous`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0S

open Set Filter Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.GAGA.H0

variable {n N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Polynomial equations of `Φ(M)` satisfying the Jacobian criterion**: in every affine chart
`U_i`, the polynomials `g_{i,j}` vanish on `Φ(M) ∩ U_i`, their common zeros in `U_i` lie in
`Φ(M)`, and at `Φ p ∈ U_i` every vector killed by all the differentials `d g_{i,j}` lies in the
image of the derivative of `Φ` (read in the chart `U_i` and the preferred chart at `p`). -/
structure IsJacobianPresentation (Φ : M → ComplexProjectiveSpace N) {q : ℕ}
    (g : Fin (N + 1) → Fin q → MvPolynomial (Fin N) ℂ) : Prop where
  vanish : ∀ i j (y : ComplexModel N), affinePoint i y ∈ range Φ →
    MvPolynomial.eval (fun k => y k) (g i j) = 0
  zero : ∀ i (y : ComplexModel N), (∀ j, MvPolynomial.eval (fun k => y k) (g i j) = 0) →
    affinePoint i y ∈ range Φ
  jacobian : ∀ (p : M) (i : Fin (N + 1)), Φ p ∈ (affineChart i).source → ∀ w : ComplexModel N,
    (∀ j, fderiv ℂ (fun y : ComplexModel N => MvPolynomial.eval (fun k => y k) (g i j))
      (affineChart i (Φ p)) w = 0) →
    ∃ v, fderiv ℂ (chartMap (n := n) Φ p i) ((complexChartAt (n := n) p).val p) v = w

theorem differentiable_eval_mvPolynomial {m : ℕ} (P : MvPolynomial (Fin m) ℂ) :
    Differentiable ℂ (fun y : ComplexModel m => MvPolynomial.eval (fun k => y k) P) :=
  differentiable_polyFun (fun _ : Fin 1 => P) 0

variable [CompactSpace M] {Φ : M → ComplexProjectiveSpace N}

/-- The Jacobian criterion gives the local Łojasiewicz inequality at the points of `Φ(M)`. -/
theorem exists_local_lojasiewicz_of_jacobian (hΦ : IsHolomorphicEmbedding (n := n) Φ) {q : ℕ}
    {g : Fin (N + 1) → Fin q → MvPolynomial (Fin N) ℂ} (hg : IsJacobianPresentation (n := n) Φ g)
    (i : Fin (N + 1)) (y₀ : ComplexModel N) (hy₀ : affinePoint i y₀ ∈ range Φ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ y ∈ ball y₀ δ, c * infDist y {y | affinePoint i y ∈ range Φ} ^ 2 ≤
      ∑ j, ‖MvPolynomial.eval (fun k => y k) (g i j)‖ ^ 2 := by
  obtain ⟨p₀, hp₀⟩ := hy₀
  have hsrc : Φ p₀ ∈ (affineChart i).source := by rw [hp₀]; exact affinePoint_mem_source i y₀
  have hy : affineChart i (Φ p₀) = y₀ := by rw [hp₀, affineChart_affinePoint]
  obtain ⟨-, L0, ε, O, g', ψ, hε, hOo, hg', -, -, hL0, hgraph⟩ := exists_affine_graph hΦ p₀ i hsrc
  rw [hy] at hgraph
  have hO₀ := (hgraph y₀ (mem_ball_self hε)).1
  refine exists_local_lojasiewicz (V := {y | affinePoint i y ∈ range Φ}) ⟨p₀, hp₀⟩ L0 hε
    (hg'.differentiableAt (hOo.mem_nhds hO₀)).continuousAt (fun y hy => (hgraph y hy).2.1)
    (fun j y => MvPolynomial.eval (fun k => y k) (g i j))
    (fun j => (contDiffAt_of_differentiableOn_complex
      (differentiable_eval_mvPolynomial (g i j)).differentiableOn isOpen_univ
      (mem_univ y₀)).of_le (by exact_mod_cast le_top))
    (fun j y hy => hg.vanish i j y hy) fun u hu => ?_
  obtain ⟨v, hv⟩ := hg.jacobian p₀ i hsrc (L0.symm (0, u)) (by rw [hy]; exact hu)
  have h := hL0 v
  rw [hv, ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

/-- In codimension `0` the cone is everything: if `Ŝ` is a closed cone which is a local graph of
codimension `0` at its nonzero points and contains a nonzero point, it contains `ℂ^{m} ∖ 0`. -/
theorem subset_of_isLocalGraphAt_zero {m : ℕ} {C : Set (ComplexModel m)} (hCc : IsClosed C)
    (hgraph : ∀ p ∈ C, p ≠ 0 → IsLocalGraphAt C 0 p) {p₀ : ComplexModel m} (hp₀ : p₀ ∈ C)
    (hp₀0 : p₀ ≠ 0) : {(0 : ComplexModel m)}ᶜ ⊆ C := by
  have hint : ∀ p ∈ C, p ≠ 0 → p ∈ interior C := by
    intro p hp hp0
    obtain ⟨n', L, ε, U', g, hε, -, -, -, hC⟩ := hgraph p hp hp0
    refine mem_interior_iff_mem_nhds.mpr (mem_of_superset (ball_mem_nhds p hε) fun Z hZ => ?_)
    exact (hC Z hZ).mpr (Subsingleton.elim _ _)
  have hm : 1 < Module.rank ℝ (ComplexModel m) := by
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp₀0 (Subsingleton.elim _ _)
    rw [← Module.finrank_eq_rank, finrank_real_complexModel]
    exact_mod_cast (by omega : 1 < 2 * m)
  have hconn := isConnected_compl_singleton_of_one_lt_rank hm (0 : ComplexModel m)
  have hsub := hconn.isPreconnected.subset_left_of_subset_union isOpen_interior
    hCc.isOpen_compl (disjoint_compl_right.mono_left interior_subset)
    (fun Z hZ => by
      by_cases hZC : Z ∈ C
      · exact Or.inl (hint Z hZC hZ)
      · exact Or.inr hZC) ⟨p₀, hp₀0, hint p₀ hp₀ hp₀0⟩
  exact hsub.trans interior_subset

/-- **Holomorphic sections of `𝒪(k)` over a projective submanifold are polynomials, `k ≫ 0`.**
For a holomorphic embedding `Φ : M → ℙᴺ` of a compact complex manifold whose image has polynomial
equations satisfying the Jacobian criterion, there is `k₀` such that for `k ≥ k₀` every function
`F` on the affine cone over `Φ(M)`, homogeneous of degree `k` and holomorphic off the vertex, is
the restriction of a homogeneous polynomial of degree `k`. -/
theorem exists_isHomogeneous_eq_of_jacobianPresentation (hΦ : IsHolomorphicEmbedding (n := n) Φ)
    {q : ℕ} {g : Fin (N + 1) → Fin q → MvPolynomial (Fin N) ℂ}
    (hg : IsJacobianPresentation (n := n) Φ g) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ F : ComplexModel (N + 1) → ℂ,
      (∀ (c : ℂ) (Z : ComplexModel (N + 1)), Z ∈ affineCone (range Φ) → F (c • Z) = c ^ k * F Z) →
      IsLocallyHolomorphicOn (affineCone (range Φ)) F →
      ∃ P : MvPolynomial (Fin (N + 1)) ℂ, P.IsHomogeneous k ∧
        ∀ Z ∈ affineCone (range Φ), MvPolynomial.eval (fun i => Z i) P = F Z := by
  classical
  set C := affineCone (range Φ) with hCdef
  have hCc : IsClosed C := isClosed_affineCone (isCompact_range hΦ.continuous).isClosed
  have hC : ∀ (c : ℂ) (Z : ComplexModel (N + 1)), Z ∈ C → c • Z ∈ C :=
    fun c _ hZ => smul_mem_affineCone c hZ
  have hgraph : ∀ p ∈ C, p ≠ 0 → IsLocalGraphAt C (N - n) p :=
    fun _ hp hp0 => isLocalGraphAt_affineCone hΦ hp hp0
  rcases Nat.eq_zero_or_pos (N - n) with hr | hr
  · -- codimension `0`: `F` is holomorphic on `ℂ^{N+1} ∖ 0`
    refine ⟨1, fun k hk F hF hloc => ?_⟩
    have hF0 : F 0 = 0 := by
      have h := hF 0 0 (zero_mem_affineCone _)
      rwa [zero_smul, zero_pow (by omega), zero_mul] at h
    have hP0 : ∀ P : MvPolynomial (Fin (N + 1)) ℂ, P.IsHomogeneous k →
        MvPolynomial.eval (fun i => (0 : ComplexModel (N + 1)) i) P = 0 := by
      intro P hP
      have h0 : (fun i => (0 : ComplexModel (N + 1)) i) = 0 := rfl
      rw [h0, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
      exact hP.coeff_eq_zero (by simp; omega)
    by_cases hC0 : ∃ p ∈ C, p ≠ 0
    swap
    · push Not at hC0
      refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun Z hZ => ?_⟩
      rw [hC0 Z hZ, hF0, map_zero]
    obtain ⟨p₀, hp₀C, hp₀⟩ := hC0
    rw [hr] at hgraph
    have hsub := subset_of_isLocalGraphAt_zero hCc hgraph hp₀C hp₀
    have hFd : DifferentiableOn ℂ F {x | x ≠ 0} := by
      intro Z hZ
      obtain ⟨U, hU, h, hh, hhF⟩ := hloc Z (hsub hZ) hZ
      have hev : h =ᶠ[𝓝 Z] F := by
        filter_upwards [hU, isOpen_ne.mem_nhds hZ] with W hWU hW0
        exact hhF W hWU (hsub hW0)
      exact ((hh.differentiableAt hU).congr_of_eventuallyEq hev.symm).differentiableWithinAt
    obtain ⟨P, hP, hPF⟩ := SGPT.GAGA.exists_isHomogeneous_eq_of_homogeneous hFd
      (fun c x _ hx => hF c x (hsub hx))
    refine ⟨P, hP, fun Z hZ => ?_⟩
    by_cases hZ0 : Z = 0
    · subst hZ0; rw [hP0 P hP, hF0]
    · exact (hPF Z hZ0).symm
  · -- positive codimension: the `L²` extension theorem of lane H0-GAGA
    set D : ℕ := Finset.univ.sup fun ij : Fin (N + 1) × Fin q => (g ij.1 ij.2).totalDegree
    set d : ℕ := D + 1 with hddef
    have hd : ∀ i j, (g i j).totalDegree < d := fun i j =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun ij : Fin (N + 1) × Fin q =>
        (g ij.1 ij.2).totalDegree) (Finset.mem_univ (i, j)))
    obtain ⟨c, hc, hLoj⟩ := exists_cone_lojasiewicz (S := range Φ) g (by omega) hd hg.zero
      (exists_local_lojasiewicz_of_jacobian hΦ hg)
    set e := (finProdFinEquiv : Fin (N + 1) × Fin q ≃ Fin ((N + 1) * q))
    set G : Fin ((N + 1) * q) → MvPolynomial (Fin (N + 1)) ℂ :=
      fun t => homogenize (e.symm t).1 d (g (e.symm t).1 (e.symm t).2) with hGdef
    have hGC' : ∀ i j, ∀ Z ∈ C, MvPolynomial.eval (fun k => Z k) (homogenize i d (g i j)) = 0 := by
      intro i j Z hZ
      rw [eval_homogenize i (hd i j)]
      split_ifs with hZi
      · rfl
      · have hv := hg.vanish i j _ ((mem_affineCone_iff hZi).mp hZ)
        have hfun : (fun k => Z (i.succAbove k) / Z i) =
            fun k => affineRatio i (WithLp.ofLp Z) k := rfl
        rw [hfun, hv, mul_zero]
    have hGC : ∀ t, ∀ Z ∈ C, MvPolynomial.eval (fun i => Z i) (G t) = 0 :=
      fun t Z hZ => hGC' (e.symm t).1 (e.symm t).2 Z hZ
    have hLoj' : ∀ Z : ComplexModel (N + 1), c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z C ^ 2 ≤
        ∑ t, ‖MvPolynomial.eval (fun i => Z i) (G t)‖ ^ 2 := by
      intro Z
      refine (hLoj Z).trans (le_of_eq ?_)
      exact (Equiv.sum_comp e.symm (fun ij => ‖MvPolynomial.eval (fun k => Z k)
        (homogenize ij.1 d (g ij.1 ij.2))‖ ^ 2)).symm
    refine ⟨(d - 1) * (N - n) + 2, fun k hk F hF hloc => ?_⟩
    exact exists_isHomogeneous_eq_of_isLocallyHolomorphicOn hCc hC hr hgraph G hGC hc hLoj' hk hF
      hloc

end SGPT.GAGA.H0S

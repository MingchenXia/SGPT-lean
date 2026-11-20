import SGPT.GAGA.H0ConeEnergy
import SGPT.GAGA.H0ConeVanishing
import SGPT.GAGA.H0ConeTaylor

/-!
# Extension of sections of `𝒪(k)` from a smooth projective variety to `ℙᴺ` (step H2 of GAGA)


Let `X ⊆ ℙ^{m-1}` be a closed complex submanifold of codimension `r > 0`, given through its
affine cone `C ⊆ ℂ^m` (a closed set stable under complex scalars which is, off the vertex, a
complex submanifold of codimension `r`: `IsLocalGraphAt C r p` for `p ∈ C ∖ {0}`), and let
`G_1, …, G_q` be polynomials vanishing on `C` that cut out `C` *with multiplicity one* in the
quantitative (Łojasiewicz) sense
`∑_j |G_j(Z)|² ≥ c |Z|^{2d-2} dist(Z, C)²`
(for homogeneous generators of degree `d` of the ideal of a smooth `X` this is the Jacobian
criterion).  A holomorphic section of `𝒪(k)` over `X` is a function `F` on `C`, homogeneous of
degree `k` (`F(cZ) = c^k F(Z)`) and holomorphic on `C ∖ {0}` (locally the restriction of
holomorphic functions, `IsLocallyHolomorphicOn`).

**Theorem** (`exists_isHomogeneous_eq_of_isLocallyHolomorphicOn`).  For `k ≥ (d - 1) r + 2`,
every such `F` is the restriction to `C` of a homogeneous polynomial of degree `k`, i.e. every
holomorphic section of `𝒪(k)|_X` extends to a section of `𝒪(k)` on `ℙ^{m-1}`, hence is a
polynomial (`H⁰(X, 𝒪(k))^{an}` is spanned by restrictions of `ℂ[Z]_k`).

Proof (`L²` method for `H¹(ℙ, 𝓘_X(k)) = 0`, in the cone over `X`):
1. `exists_smoothExtension`: a `C¹` homogeneous extension `a` of `F` with
   `|∂̄a(Z)|² ≤ M |Z|^{2k-4} dist(Z, C)²`;
2. the weight `Ψ = r log ∑_j |G_j|²` is plurisubharmonic, `∫_{B(0,2)} |∂̄a|² e^{-Ψ-|Z|²} < ∞`
   (`lintegral_dbarNormSq_coneWeight_lt_top`, using the Łojasiewicz inequality and
   `k ≥ (d-1) r + 2`), while `e^{-Ψ}` is not integrable near any point of `C ∖ {0}`
   (`lintegral_coneWeight_eq_top`);
3. Hörmander's estimate on the ball (`localBallCorrectionC1`) gives `H` holomorphic on `B(0,1)`
   with `∫ |a - H|² e^{-Ψ - |Z|²} < ∞`, so `H = a = F` on `C ∩ B(0,1)`
   (`exists_holomorphic_eq_on_of_nonintegrable`);
4. the degree-`k` Taylor term of `H` at `0` is the required polynomial
   (`exists_isHomogeneous_eq_on_cone`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.PSH.GlobalL2

variable {m : ℕ}

/-- A local graph of codimension `r` in `ℂ^m` has `r ≤ m`. -/
theorem IsLocalGraphAt.le_dim {C : Set (ComplexModel m)} {r : ℕ} {p : ComplexModel m}
    (h : IsLocalGraphAt C r p) : r ≤ m := by
  obtain ⟨n', L, -⟩ := h
  have h1 := L.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at h1
  omega

/-- **Extension of holomorphic sections of `𝒪(k)` from a smooth projective variety**
(`claude-h0-gaga:cone-extension`, step H2 of `H⁰`-GAGA).  Let `C ⊆ ℂ^m` be a closed cone which is
a complex submanifold of codimension `r > 0` off the vertex, and `G_1, …, G_q` polynomials
vanishing on `C` with `∑_j |G_j(Z)|² ≥ c |Z|^{2(d-1)} dist(Z, C)²`.  For `k ≥ (d - 1) r + 2`,
every `F` homogeneous of degree `k` on `C` and holomorphic on `C ∖ {0}` is the restriction of a
homogeneous polynomial of degree `k`. -/
theorem exists_isHomogeneous_eq_of_isLocallyHolomorphicOn {C : Set (ComplexModel m)}
    (hCc : IsClosed C) (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C)
    {r : ℕ} (hr : 0 < r) (hgraph : ∀ p ∈ C, p ≠ 0 → IsLocalGraphAt C r p)
    {q d : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ)
    (hGC : ∀ j, ∀ Z ∈ C, MvPolynomial.eval (fun i => Z i) (G j) = 0)
    {c : ℝ} (hc : 0 < c)
    (hLoj : ∀ Z : ComplexModel m, c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z C ^ 2 ≤
      ∑ j, ‖MvPolynomial.eval (fun i => Z i) (G j)‖ ^ 2)
    {k : ℕ} (hk : (d - 1) * r + 2 ≤ k) {F : ComplexModel m → ℂ}
    (hF : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → F (c • Z) = c ^ k * F Z)
    (hloc : IsLocallyHolomorphicOn C F) :
    ∃ P : MvPolynomial (Fin m) ℂ, P.IsHomogeneous k ∧
      ∀ Z ∈ C, MvPolynomial.eval (fun i => Z i) P = F Z := by
  have hk2 : 2 ≤ k := le_trans (Nat.le_add_left 2 _) hk
  by_cases hC0 : ∃ p ∈ C, p ≠ 0
  swap
  · -- `C ⊆ {0}`: the zero polynomial
    push Not at hC0
    refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun Z hZ => ?_⟩
    have hZ0 : Z = 0 := hC0 Z hZ
    subst hZ0
    have h := hF 0 0 hZ
    rw [zero_smul, zero_pow (by omega), zero_mul] at h
    rw [h, map_zero]
  obtain ⟨p₀, hp₀C, hp₀⟩ := hC0
  have hrm : r ≤ m := (hgraph p₀ hp₀C hp₀).le_dim
  -- 1. the smooth extension
  obtain ⟨a, ha1, haF, M, hM0, haM⟩ := exists_smoothExtension hCc hC hk2 hF hloc
  -- 2. finite energy and non-integrability
  have hE := lintegral_dbarNormSq_coneWeight_lt_top hCc hC hr hrm hgraph G hc (fun Z => hLoj Z)
    hk hM0 haM 2
  have hGC' : ∀ j, ∀ Z ∈ C, polyFun G j Z = 0 := hGC
  -- 3. the correction interpolates `F` along `C`
  obtain ⟨H, hH, hHa⟩ := exists_holomorphic_eq_on_of_nonintegrable (r := 1) (R := 2) one_pos
    (by norm_num) (plurisubharmonicOn_coneWeight hr G _) ha1.contDiffOn hE.ne
    (Y := C \ {0}) fun p hp _ δ hδ =>
      lintegral_coneWeight_eq_top hCc hr G hGC' hp.1 (hgraph p hp.1 hp.2) hδ
  -- 4. the Taylor term of degree `k`
  exact exists_isHomogeneous_eq_on_cone one_pos hH hC (by omega) hF
    fun Z hZC hZb hZ0 => (hHa Z ⟨hZC, hZ0⟩ hZb).trans (haF Z hZC)

/-- **Algebraicity of holomorphic sections of `𝒪(k)|_X` for every `k`**
(`claude-h0-gaga:all-degrees`).  Under the hypotheses of
`exists_isHomogeneous_eq_of_isLocallyHolomorphicOn`, for every degree `k` (no lower bound), every
`F` homogeneous of degree `k` on `C` and holomorphic on `C ∖ {0}`, and every coordinate index `i`,
there are `l` and a homogeneous polynomial `P` of degree `k + l` with `P = Z_i^l F` on `C`.  So on
the affine chart `{Z_i ≠ 0}` the section is the regular function `P / Z_i^{k+l}` times the frame
`Z_i^k`: holomorphic sections of `𝒪(k)|_X` are algebraic in every degree (the step "small `m` via
`s · Z_i^l`" of the plan). -/
theorem exists_isHomogeneous_eq_pow_mul {C : Set (ComplexModel m)}
    (hCc : IsClosed C) (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C)
    {r : ℕ} (hr : 0 < r) (hgraph : ∀ p ∈ C, p ≠ 0 → IsLocalGraphAt C r p)
    {q d : ℕ} (G : Fin q → MvPolynomial (Fin m) ℂ)
    (hGC : ∀ j, ∀ Z ∈ C, MvPolynomial.eval (fun i => Z i) (G j) = 0)
    {c : ℝ} (hc : 0 < c)
    (hLoj : ∀ Z : ComplexModel m, c * ‖Z‖ ^ (2 * (d - 1)) * infDist Z C ^ 2 ≤
      ∑ j, ‖MvPolynomial.eval (fun i => Z i) (G j)‖ ^ 2)
    (k : ℕ) {F : ComplexModel m → ℂ}
    (hF : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → F (c • Z) = c ^ k * F Z)
    (hloc : IsLocallyHolomorphicOn C F) (i : Fin m) :
    ∃ (l : ℕ) (P : MvPolynomial (Fin m) ℂ), P.IsHomogeneous (k + l) ∧
      ∀ Z ∈ C, MvPolynomial.eval (fun i => Z i) P = Z i ^ l * F Z := by
  set l : ℕ := (d - 1) * r + 2 with hl
  refine ⟨l, ?_⟩
  have hproj : Differentiable ℂ (fun Z : ComplexModel m => Z i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable
  refine exists_isHomogeneous_eq_of_isLocallyHolomorphicOn hCc hC hr hgraph G hGC hc hLoj
    (by omega) (F := fun Z => Z i ^ l * F Z) ?_ ?_
  · intro c' Z hZ
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [hF c' Z hZ]
    ring
  · intro p hpC hp0
    obtain ⟨U, hU, h, hh, hhF⟩ := hloc p hpC hp0
    refine ⟨U, hU, fun Z => Z i ^ l * h Z, ((hproj.pow l).differentiableOn).mul hh, ?_⟩
    intro Z hZU hZC
    simp only
    rw [hhF Z hZU hZC]

end SGPT.GAGA.H0

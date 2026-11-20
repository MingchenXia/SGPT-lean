import SGPT.Okounkov.TranscendentalBodyConvex
import SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure

/-!
# Hausdorff continuity of transcendental Okounkov bodies on the big cone

Source: blueprint node `tok:hausdorff-continuity` (DRWNXZ Proposition 3.5); the book's
`thm:Okounkovtranmain` item 4: `α ↦ Δ_{Y•}(α)` is continuous on the big cone for the
(Euclidean) Hausdorff metric.

## Route (blueprint `tok:hausdorff-continuity`)

Fix a big class `ξ = {θ}` and a gentle Kähler current `T = θ + dd^c ψ ≥ κ` (`Ω(ξ) ≠ ∅`,
`tok:sing-decrease`). For `δ ∈ ℚ_{>0}` and a closed form `η` with `-r ω ≤ η ≤ r ω`, `r` small
compared with `δ`, the forms `δκ - η` and `δκ + (1 + δ) η` are semipositive, so the potential
`δ ψ` is a gentle potential for the representatives `δθ - η` and `δθ + (1 + δ) η` of the
classes `(1 + δ) ξ - ξ'` and `(1 + δ) ξ' - ξ` (`ξ' = {θ + η}`), with valuation `δ ν(T)`.
Superadditivity and rational homogeneity (`tok:body-basic`) give

`Δ(ξ') + δ ν(T) ⊆ (1 + δ) Δ(ξ)` and `Δ(ξ) + δ ν(T) ⊆ (1 + δ) Δ(ξ')`.

All these bodies lie in one cube `[0, C]ⁿ` (`tok:valuation-bound`, uniform form). If
`x + δν = (1 + δ) y`, then `(1 + δ)(x - y) = δ (x - ν)`, so `|x - y| ≤ δ |x - ν| ≤ δ K C`.
Hence `d_Haus(Δ(ξ'), Δ(ξ)) ≤ δ K C`. (The source's inclusion `Δ(ξ') ⊆ (1 + δ) Δ(ξ)` is replaced by
the inclusion up to the translation by `δ ν(T)`, which needs no `0 ∈ Δ` assumption.)

The topology of `H^{1,1}(X, ℝ)` is TN's quotient `C⁰` topology `classC0Topology`: the quotient
map is open (`isOpenQuotientMap_ofRepresentative`), so a neighbourhood of `ξ = {θ}` contains the
classes `{θ + η}` with `‖η‖_{C⁰, ω} < r`, and `‖η‖_{C⁰, ω} ≤ r ⇔ -r ω ≤ η ≤ r ω`
(`XiaoFormC0Topology.formC0Seminorm_le_iff`).

## Main results

* `perturbation_inclusions`: the two inclusions above.
* `hausdorffDist_euclideanImage_le`: the Hausdorff estimate.
* `hausdorffContinuity`: the conjunct `HausdorffContinuityStatement` (item 4) of the fixed
  target `OkounkovTranMainStatement`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalBody

open Set Filter Metric
open scoped Pointwise Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
open SGPT.Foundations.Analysis.Pending.XiaoBottChernC0Closure
open SGPT.Okounkov.TranscendentalCore

/-! ### The perturbation inclusions -/

section Inclusions

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n}

/-- A positive rational multiple of a gentle potential is a gentle potential for every
background for which it is quasi-psh. -/
theorem smul_mem_gentleCurrents {θ σ : ClosedRealOneOneForm n F.carrier} {ψ : F.carrier → EReal}
    (hψ : ψ ∈ gentleCurrents θ) {q : ℚ} (hq : 0 < q)
    (hσ : IsThetaPshPotential σ.val (fun x => ((q : ℝ) : EReal) * ψ x)) :
    (fun x => ((q : ℝ) : EReal) * ψ x) ∈ gentleCurrents σ := by
  have h := add_smul_mem_gentleCurrents hψ hψ hq.le le_rfl (Or.inl hq)
  have hfun : (fun x => ((q : ℝ) : EReal) * ψ x + (((0 : ℚ) : ℝ) : EReal) * ψ x) =
      fun x => ((q : ℝ) : EReal) * ψ x := by
    funext x
    simp
  rw [hfun] at h
  exact ⟨hσ, h.2⟩

/-- `q ν(ψ) ∈ Δ(σ)` if `ψ` is gentle and `q ψ ∈ PSH(X, σ)`. -/
theorem smul_flagValuation_mem_tradOkounkovBody {θ σ : ClosedRealOneOneForm n F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ gentleCurrents θ) {q : ℚ} (hq : 0 < q)
    (hσ : IsThetaPshPotential σ.val (fun x => ((q : ℝ) : EReal) * ψ x)) :
    (q : ℝ) • flagValuation F ψ ∈ tradOkounkovBody F σ := by
  rw [← flagValuation_smul (isThetaPshPotential_of_mem_gentleCurrents hψ)
    (by exact_mod_cast hq.le), tradOkounkovBody_eq_closure_image]
  exact subset_closure ⟨_, smul_mem_gentleCurrents hψ hq hσ, rfl⟩

/-- If `v ∈ Δ(θ₂)` and `θ₁ + θ₂ = q θ₀` (`q ∈ ℚ_{>0}`), then every `x ∈ Δ(θ₁)` satisfies
`x + v = q y` for some `y ∈ Δ(θ₀)`. -/
theorem exists_add_eq_smul_of_add_eq {θ₀ θ₁ θ₂ : ClosedRealOneOneForm n F.carrier}
    {v : Fin n → ℝ} (hv : v ∈ tradOkounkovBody F θ₂) {q : ℚ} (hq : 0 < q)
    (h : θ₁ + θ₂ = (q : ℝ) • θ₀) :
    ∀ x ∈ tradOkounkovBody F θ₁, ∃ y ∈ tradOkounkovBody F θ₀, x + v = (q : ℝ) • y := by
  intro x hx
  have hmem := tradOkounkovBody_add_subset θ₁ θ₂ ⟨x, hx, v, hv, rfl⟩
  rw [h, tradOkounkovBody_rat_smul θ₀ hq] at hmem
  obtain ⟨y, hy, hxy⟩ := hmem
  exact ⟨y, hy, hxy.symm⟩

/-- **The perturbation inclusions** (blueprint `tok:hausdorff-continuity`): let
`θ + dd^c ψ ≥ κ` with `ψ` gentle, `δ ∈ ℚ_{>0}`, and `η` with `δκ - η ≥ 0` and
`δκ + (1 + δ) η ≥ 0`. Then `Δ(θ + η) + δν(ψ) ⊆ (1 + δ) Δ(θ)` and
`Δ(θ) + δν(ψ) ⊆ (1 + δ) Δ(θ + η)`. -/
theorem perturbation_inclusions {θ η : ClosedRealOneOneForm n F.carrier}
    {κ : KahlerBackground n F.carrier} {ψ : F.carrier → EReal} (hψ : ψ ∈ gentleCurrents θ)
    (hκ : IsThetaPshPotential (θ - κ.form).val ψ) {δ : ℚ} (hδ : 0 < δ)
    (h₁ : ((δ : ℝ) • κ.form - η).val.IsSemipositive)
    (h₂ : ((δ : ℝ) • κ.form + (1 + (δ : ℝ)) • η).val.IsSemipositive) :
    (∀ x ∈ tradOkounkovBody F (θ + η), ∃ y ∈ tradOkounkovBody F θ,
        x + (δ : ℝ) • flagValuation F ψ = (1 + (δ : ℝ)) • y) ∧
      (∀ x ∈ tradOkounkovBody F θ, ∃ y ∈ tradOkounkovBody F (θ + η),
        x + (δ : ℝ) • flagValuation F ψ = (1 + (δ : ℝ)) • y) := by
  have hδR : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ.le
  have hsmul := TranscendentalCore.isThetaPshPotential_nonneg_smul hκ hδR
  have hq : (0 : ℚ) < 1 + δ := by linarith
  have hcast : (((1 + δ : ℚ)) : ℝ) = 1 + (δ : ℝ) := by push_cast; ring
  constructor
  · have hv : (δ : ℝ) • flagValuation F ψ ∈ tradOkounkovBody F ((δ : ℝ) • θ - η) := by
      refine smul_flagValuation_mem_tradOkounkovBody hψ hδ (isThetaPshPotential_of_le hsmul ?_)
      have heq : (δ : ℝ) • θ - η - (δ : ℝ) • (θ - κ.form) = (δ : ℝ) • κ.form - η := by module
      rw [heq]
      exact h₁
    have h := exists_add_eq_smul_of_add_eq hv hq
      (show θ + η + ((δ : ℝ) • θ - η) = (((1 + δ : ℚ)) : ℝ) • θ by rw [hcast]; module)
    simpa only [hcast] using h
  · have hv : (δ : ℝ) • flagValuation F ψ ∈
        tradOkounkovBody F ((δ : ℝ) • θ + (1 + (δ : ℝ)) • η) := by
      refine smul_flagValuation_mem_tradOkounkovBody hψ hδ (isThetaPshPotential_of_le hsmul ?_)
      have heq : (δ : ℝ) • θ + (1 + (δ : ℝ)) • η - (δ : ℝ) • (θ - κ.form) =
          (δ : ℝ) • κ.form + (1 + (δ : ℝ)) • η := by module
      rw [heq]
      exact h₂
    have h := exists_add_eq_smul_of_add_eq hv hq
      (show θ + ((δ : ℝ) • θ + (1 + (δ : ℝ)) • η) = (((1 + δ : ℚ)) : ℝ) • (θ + η) by
        rw [hcast]; module)
    simpa only [hcast] using h

end Inclusions

/-! ### The Hausdorff estimate -/

section Estimate

variable {k : ℕ}

/-- The Euclidean norm of a vector of `[-C, C]^k` (written as a difference of two vectors of
`[0, C]^k`) is at most `K C` with `K` the norm of `ℝ^k → EuclideanSpace`. -/
theorem norm_euclidean_sub_le {C : ℝ} (hC : 0 ≤ C) {x v : Fin k → ℝ}
    (hx : x ∈ Icc (0 : Fin k → ℝ) (fun _ => C)) (hv : v ∈ Icc (0 : Fin k → ℝ) (fun _ => C)) :
    ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (x - v)‖ ≤
      ‖((EuclideanSpace.equiv (Fin k) ℝ).symm : (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k))‖ *
        C := by
  refine (((EuclideanSpace.equiv (Fin k) ℝ).symm :
    (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k)).le_opNorm (x - v)).trans ?_
  gcongr
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  have hx0 := hx.1 i
  have hx1 := hx.2 i
  have hv0 := hv.1 i
  have hv1 := hv.2 i
  simp only [Pi.zero_apply] at hx0 hv0
  constructor <;> linarith

/-- If `x + δ v = (1 + δ) y` with `x, v ∈ [0, C]^k`, then the Euclidean distance of `x` and `y`
is at most `δ K C`. -/
theorem dist_euclidean_le_of_add_eq {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    {x v y : Fin k → ℝ} (hx : x ∈ Icc (0 : Fin k → ℝ) (fun _ => C))
    (hv : v ∈ Icc (0 : Fin k → ℝ) (fun _ => C)) (hxy : x + δ • v = (1 + δ) • y) :
    dist ((EuclideanSpace.equiv (Fin k) ℝ).symm x) ((EuclideanSpace.equiv (Fin k) ℝ).symm y) ≤
      δ * (‖((EuclideanSpace.equiv (Fin k) ℝ).symm :
        (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k))‖ * C) := by
  set e := (EuclideanSpace.equiv (Fin k) ℝ).symm
  have hkey : (1 + δ) • (x - y) = δ • (x - v) := by
    rw [smul_sub, ← hxy]
    module
  have hnorm : (1 + δ) * ‖e (x - y)‖ = δ * ‖e (x - v)‖ := by
    have h := congrArg (fun z => ‖e z‖) hkey
    have h1 : e ((1 + δ) • (x - y)) = (1 + δ) • e (x - y) := map_smul e _ _
    have h2 : e (δ • (x - v)) = δ • e (x - v) := map_smul e _ _
    simp only [h1, h2] at h
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hδ,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + δ)] at h
    exact h
  rw [dist_eq_norm, ← map_sub]
  have hb := norm_euclidean_sub_le hC hx hv
  have hpos : 0 ≤ ‖e (x - y)‖ := norm_nonneg _
  calc ‖e (x - y)‖ ≤ (1 + δ) * ‖e (x - y)‖ := by nlinarith
    _ = δ * ‖e (x - v)‖ := hnorm
    _ ≤ δ * (‖(e : (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k))‖ * C) := by gcongr

/-- **The Hausdorff estimate** (blueprint `tok:hausdorff-continuity`): if `K, L ⊆ [0, C]^k`,
`v ∈ [0, C]^k`, `L + δ v ⊆ (1 + δ) K` and `K + δ v ⊆ (1 + δ) L` (pointwise, `δ ≥ 0`), then the
Euclidean Hausdorff distance of `L` and `K` is at most `δ K₀ C`. -/
theorem hausdorffDist_euclideanImage_le {K L : Set (Fin k → ℝ)} {C δ : ℝ} (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hK : K ⊆ Icc 0 (fun _ => C)) (hL : L ⊆ Icc 0 (fun _ => C))
    {v : Fin k → ℝ} (hv : v ∈ Icc (0 : Fin k → ℝ) (fun _ => C))
    (hLK : ∀ x ∈ L, ∃ y ∈ K, x + δ • v = (1 + δ) • y)
    (hKL : ∀ x ∈ K, ∃ y ∈ L, x + δ • v = (1 + δ) • y) :
    hausdorffDist (TranscendentalMain.euclideanImage L) (TranscendentalMain.euclideanImage K) ≤
      δ * (‖((EuclideanSpace.equiv (Fin k) ℝ).symm :
        (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k))‖ * C) := by
  have hr : 0 ≤ δ * (‖((EuclideanSpace.equiv (Fin k) ℝ).symm :
      (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k))‖ * C) := by positivity
  refine hausdorffDist_le_of_mem_dist hr ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hLK x hx
    exact ⟨_, ⟨y, hy, rfl⟩, dist_euclidean_le_of_add_eq hC hδ (hL hx) hv hxy⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hKL x hx
    exact ⟨_, ⟨y, hy, rfl⟩, dist_euclidean_le_of_add_eq hC hδ (hK hx) hv hxy⟩

end Estimate

/-! ### Continuity on the big cone -/

section Continuity

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n}

/-- Uniform cube for the bodies `Δ(θ + η)`, `η ≤ ω` (blueprint `tok:valuation-bound`). -/
theorem exists_tradOkounkovBody_add_subset_Icc (θ : ClosedRealOneOneForm n F.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ClosedRealOneOneForm n F.carrier,
      (F.omega.form - η).val.IsSemipositive →
        tradOkounkovBody F (θ + η) ⊆ Icc (0 : Fin n → ℝ) (fun _ => C) := by
  obtain ⟨C, hC0, hC⟩ := exists_flagValuation_le_uniform (F := F) θ
  refine ⟨C, hC0, fun η hη => ?_⟩
  rw [tradOkounkovBody_eq_closure_image]
  refine closure_minimal ?_ isClosed_Icc
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨fun i => flagValuation_nonneg φ i,
    fun i => hC η hη φ (isThetaPshPotential_of_mem_gentleCurrents hφ) i⟩

/-- **Blueprint `tok:hausdorff-continuity`, sequential `C⁰` form**: let `{θ}` be big. For every
`ε > 0` there is `r > 0` such that `d_Haus(Δ(θ + η), Δ(θ)) < ε` for every closed real
`(1,1)`-form `η` with `-r ω ≤ η ≤ r ω`. -/
theorem exists_hausdorffDist_lt {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
    {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ η : ClosedRealOneOneForm (m + 1) F.carrier,
      (r • F.omega.form + η).val.IsSemipositive → (r • F.omega.form - η).val.IsSemipositive →
        hausdorffDist (TranscendentalMain.euclideanImage (tradOkounkovBody F (θ + η)))
          (TranscendentalMain.euclideanImage (tradOkounkovBody F θ)) < ε := by
  -- a gentle Kähler current `θ + dd^c ψ ≥ κ`
  obtain ⟨ψ, hψK⟩ := exists_mem_gentleKahlerCurrents_of_isBig (F := F) hbig
  obtain ⟨hψ, κ, hκ⟩ := id hψK
  -- the uniform cube
  obtain ⟨C, hC0, hC⟩ := exists_tradOkounkovBody_add_subset_Icc (F := F) θ
  have hKθ : tradOkounkovBody F θ ⊆ Icc (0 : Fin (m + 1) → ℝ) (fun _ => C) := by
    have h := hC 0 (by simpa using F.omega.isSemipositive)
    rwa [add_zero] at h
  have hν : flagValuation F ψ ∈ Icc (0 : Fin (m + 1) → ℝ) (fun _ => C) :=
    hKθ (image_gentleKahlerCurrents_subset_tradOkounkovBody θ ⟨ψ, hψK, rfl⟩)
  -- `ω ≤ D κ`
  obtain ⟨D, hD, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-F.omega.form)
  set K₀ : ℝ := ‖((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm :
    (Fin (m + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))‖ with hK₀
  have hK₀0 : 0 ≤ K₀ := norm_nonneg _
  -- a rational `δ ∈ (0, 1]` with `δ K₀ C < ε`
  have hpos : 0 < min 1 (ε / (K₀ * C + 1)) := lt_min one_pos (by positivity)
  obtain ⟨δ, hδ0, hδ1⟩ := exists_rat_btwn hpos
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδq : (0 : ℚ) < δ := by exact_mod_cast hδ0
  have hδle1 : (δ : ℝ) ≤ 1 := hδ1.le.trans (min_le_left _ _)
  have hδε : (δ : ℝ) * (K₀ * C) < ε := by
    have h := hδ1.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    nlinarith
  set r : ℝ := min 1 ((δ : ℝ) / (2 * D)) with hr
  have hr0 : 0 < r := lt_min one_pos (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrD : r * D ≤ (δ : ℝ) / 2 := by
    have h := min_le_right 1 ((δ : ℝ) / (2 * D))
    rw [← hr] at h
    calc r * D ≤ (δ : ℝ) / (2 * D) * D := by gcongr
      _ = (δ : ℝ) / 2 := by field_simp
  refine ⟨r, hr0, fun η hηp hηm => ?_⟩
  -- the three semipositivity conditions
  have hsemi_le : (F.omega.form - η).val.IsSemipositive := by
    have heq : F.omega.form - η = (r • F.omega.form - η) + (1 - r) • F.omega.form := by module
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add hηm
      (KahlerDomination.isSemipositive_smul F.omega.isSemipositive (by linarith))
  have h₁ : ((δ : ℝ) • κ.form - η).val.IsSemipositive := by
    have heq : (δ : ℝ) • κ.form - η = (r • F.omega.form - η) +
        r • (-F.omega.form + D • κ.form) + ((δ : ℝ) - r * D) • κ.form := by module
    rw [heq]
    refine UniformPerturbedKahlerLowerBound.isSemipositive_add
      (UniformPerturbedKahlerLowerBound.isSemipositive_add hηm
        (KahlerDomination.isSemipositive_smul hdom hr0.le))
      (KahlerDomination.isSemipositive_smul κ.isSemipositive (by linarith))
  have h₂ : ((δ : ℝ) • κ.form + (1 + (δ : ℝ)) • η).val.IsSemipositive := by
    have heq : (δ : ℝ) • κ.form + (1 + (δ : ℝ)) • η =
        (1 + (δ : ℝ)) • (r • F.omega.form + η) +
          ((1 + (δ : ℝ)) * r) • (-F.omega.form + D • κ.form) +
          ((δ : ℝ) - (1 + (δ : ℝ)) * r * D) • κ.form := by module
    rw [heq]
    have hcoef : (1 + (δ : ℝ)) * r * D ≤ (δ : ℝ) := by
      have : (1 + (δ : ℝ)) * (r * D) ≤ 2 * ((δ : ℝ) / 2) := by
        gcongr
        · linarith
      calc (1 + (δ : ℝ)) * r * D = (1 + (δ : ℝ)) * (r * D) := by ring
        _ ≤ 2 * ((δ : ℝ) / 2) := this
        _ = (δ : ℝ) := by ring
    refine UniformPerturbedKahlerLowerBound.isSemipositive_add
      (UniformPerturbedKahlerLowerBound.isSemipositive_add
        (KahlerDomination.isSemipositive_smul hηp (by linarith))
        (KahlerDomination.isSemipositive_smul hdom (by positivity)))
      (KahlerDomination.isSemipositive_smul κ.isSemipositive (by linarith))
  obtain ⟨hLK, hKL⟩ := perturbation_inclusions hψ hκ hδq h₁ h₂
  have hest := hausdorffDist_euclideanImage_le hC0 hδ0'.le hKθ (hC η hsemi_le) hν hLK hKL
  exact hest.trans_lt (by rw [← hK₀]; exact hδε)

variable (F) in
/-- **Source `thm:Okounkovtranmain` (4)** (blueprint `tok:hausdorff-continuity`; DRWNXZ
Proposition 3.5): `α ↦ Δ_{Y•}(α)` is continuous on the big cone for the Euclidean Hausdorff
metric and the quotient `C⁰` topology of `H^{1,1}(X, ℝ)`; the conjunct
`HausdorffContinuityStatement` of the fixed target `OkounkovTranMainStatement`. -/
theorem hausdorffContinuity {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) :
    TranscendentalMain.HausdorffContinuityStatement F := by
  let : TopologicalSpace (RealBottChern (m + 1) F.carrier) := classC0Topology F.omega
  let : TopologicalSpace (ClosedRealOneOneForm (m + 1) F.carrier) := formC0Topology F.omega
  intro α hα
  set θ : ClosedRealOneOneForm (m + 1) F.carrier := Quotient.out α with hθ
  have hrep : RealBottChern.ofRepresentative θ = α := Quotient.out_eq α
  have hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) := by
    rw [hrep]; exact hα
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  refine eventually_nhdsWithin_of_eventually_nhds ?_
  obtain ⟨r, hr, hball⟩ := exists_hausdorffDist_lt (F := F) hbig hε
  -- neighbourhoods of `α` are images of neighbourhoods of `θ`
  have hmap : map RealBottChern.ofRepresentative (𝓝 θ) = 𝓝 α := by
    rw [← hrep]
    exact (isOpenQuotientMap_ofRepresentative F.omega).map_nhds_eq θ
  rw [← hmap, eventually_map]
  have hopen := isOpen_formC0Seminorm_ball F.omega θ r
  have hmem : θ ∈ (formC0Seminorm F.omega).ball θ r :=
    (formC0Seminorm F.omega).mem_ball_self hr
  filter_upwards [hopen.mem_nhds hmem] with θ' hθ'
  rw [Seminorm.mem_ball] at hθ'
  have hle := (formC0Seminorm_le_iff F.omega (θ' - θ) hr.le).mp hθ'.le
  have hθ'eq : θ' = θ + (θ' - θ) := by abel
  have hdist := hball (θ' - θ) hle.1 hle.2
  rw [← hθ'eq] at hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg,
    classOkounkovBody_ofRepresentative]
  exact hdist

end Continuity

end SGPT.Okounkov.TranscendentalBody

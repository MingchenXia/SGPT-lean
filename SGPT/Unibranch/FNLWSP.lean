import SGPT.Unibranch.FNLCollapse
import SGPT.Unibranch.FNRAnalyticHull
import SGPT.Foundations.Analysis.SmoothPlurisubharmonic

/-!
# FN80 §5: weakly strongly plurisubharmonic functions; polydisc restrictions

Source: `[FN80]` §5 (definition of `WSP(X)`) and Lemma 5.2, proof.

* `IsWeaklyStrictlyPSHOn X φ` (`φ ∈ WSP(X)`): locally `φ - c‖·‖² ∈ WP` for some `c > 0`.  This is
  `[FN80]`'s "locally `φ = φ₁ + φ₂` with `φ₁ ∈ SP(X)`, `φ₂ ∈ WP(X)`" (a strongly psh `φ₁` is locally
  `c‖·‖²` plus a psh function and conversely).
* `IsWeaklyPSHOn.add`, `IsWeaklyPSHOn.of_plurisubharmonicOn`: `WP + WP ⊆ WP`, restrictions of
  ambient psh functions are weakly psh (`discPshOn_comp_disc`).
* `IsBranchedCovering.exists_restrict_pdisc`: a polydisc around a point of `X`, inside any given
  neighbourhood, over which `X` is a branched covering whose number of sheets is the sheet number
  of the point.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {n k : ℕ}

/-- The polydisc `Δ(a, r) = {z | ∀ i, |zᵢ - aᵢ| < rᵢ}` (as). -/
abbrev pdisc (a : ComplexModel n) (r : Fin n → ℝ) : Set (ComplexModel n) :=
  {z | ∀ i, ‖z i - a i‖ < r i}

theorem isOpen_pdisc (a : ComplexModel n) (r : Fin n → ℝ) : IsOpen (pdisc a r) := by
  simp only [pdisc, ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt
    (continuous_norm.comp ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _) |>.sub
      continuous_const)) continuous_const

theorem norm_apply_le (z : ComplexModel n) (i : Fin n) : ‖z i‖ ≤ ‖z‖ := by
  have h : ‖z i‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem norm_le_sum_apply (z : ComplexModel n) : ‖z‖ ≤ ∑ i, ‖z i‖ := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i, ‖z i‖ ^ 2) ≤ √((∑ i, ‖z i‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ i, ‖z i‖ := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem pdisc_subset_ball (a : ComplexModel n) {ρ t : ℝ} (hρ : 0 < ρ)
    (ht : t ≤ ρ / (n + 1)) {r : Fin n → ℝ} (hr : ∀ i, r i ≤ t) : pdisc a r ⊆ ball a ρ := by
  intro z hz
  rw [mem_ball, dist_eq_norm]
  calc ‖z - a‖ ≤ ∑ i, ‖(z - a) i‖ := norm_le_sum_apply _
    _ ≤ ∑ _i : Fin n, t := Finset.sum_le_sum fun i _ => by
        simpa using (hz i).le.trans (hr i)
    _ = n * t := by simp
    _ < ρ := by
        have h1 : (n : ℝ) * t ≤ n * (ρ / (n + 1)) :=
          mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
        have h2 : (n : ℝ) * (ρ / (n + 1)) < ρ := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
        linarith

/-- The pull-back of an ambient psh function by a holomorphic disc is disc-subharmonic. -/
theorem discPshOn_comp_disc {N : ℕ} {u : ComplexModel N → EReal} {V : Set (ComplexModel N)}
    (hu : PlurisubharmonicOn u V) {f : ℂ → ComplexModel N}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (hfV : MapsTo f (ball (0 : ℂ) 1) V) :
    DiscPshOn (fun t => u (f t)) (ball (0 : ℂ) 1) := by
  let P : ComplexModel 1 →L[ℂ] ℂ := EuclideanSpace.proj (0 : Fin 1)
  let L : ℂ →L[ℂ] ComplexModel 1 :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))
  have hPL : ∀ t, P (L t) = t := fun t => by simp [P, L]
  set U₁ : Set (ComplexModel 1) := P ⁻¹' ball (0 : ℂ) 1
  have hU₁ : IsOpen U₁ := isOpen_ball.preimage P.continuous
  have hF : DifferentiableOn ℂ (fun z => f (P z)) U₁ :=
    hf.comp P.differentiable.differentiableOn fun z hz => hz
  have h := (HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hU₁ hF
    (fun z hz => hfV hz) hu).discPshOn.comp_affine L 0
  have hpre : (fun t : ℂ => 0 + L t) ⁻¹' U₁ = ball (0 : ℂ) 1 := by
    ext t; simp [U₁, hPL]
  rw [hpre] at h
  simpa [hPL] using h

/-- Restrictions of ambient plurisubharmonic functions are weakly plurisubharmonic. -/
theorem IsWeaklyPSHOn.of_plurisubharmonicOn {X : Set (ComplexModel n)} {u : ComplexModel n → EReal}
    {O : Set (ComplexModel n)} (hu : PlurisubharmonicOn u O) (hXO : X ⊆ O) :
    IsWeaklyPSHOn X u := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun f hf hfX => discPshOn_comp_disc hu hf
    (hfX.mono_right hXO)⟩
  · obtain ⟨W, -, hxW, hW⟩ := hu x (hXO hx)
    exact hW.ne_top x hxW
  · obtain ⟨W, hWo, hxW, hW⟩ := hu x (hXO hx)
    intro y hy
    have h := hW.upperSemicontinuousOn x hxW y hy
    rw [nhdsWithin_eq_nhds.mpr (hWo.mem_nhds hxW)] at h
    exact nhdsWithin_le_nhds h

/-- `WP(X) + WP(X) ⊆ WP(X)`. -/
theorem IsWeaklyPSHOn.add {X : Set (ComplexModel n)} {φ ψ : ComplexModel n → EReal}
    (hφ : IsWeaklyPSHOn X φ) (hψ : IsWeaklyPSHOn X ψ) :
    IsWeaklyPSHOn X (fun x => φ x + ψ x) := by
  refine ⟨fun x hx => EReal.add_ne_top (hφ.ne_top x hx) (hψ.ne_top x hx), ?_,
    fun f hf hfX => (hφ.disc f hf hfX).add (hψ.disc f hf hfX)⟩
  refine hφ.upperSemicontinuousOn.add' hψ.upperSemicontinuousOn (fun x hx => ?_)
  exact EReal.continuousAt_add (Or.inl (hφ.ne_top x hx)) (Or.inr (hψ.ne_top x hx))

/-- The quadratic functions `a ‖x - q‖² + b`, `a ≥ 0`, are plurisubharmonic. -/
theorem plurisubharmonicOn_quadratic {a : ℝ} (ha : 0 ≤ a) (q : ComplexModel n) (b : ℝ) :
    PlurisubharmonicOn (fun x : ComplexModel n => ((a * ‖x - q‖ ^ 2 + b : ℝ) : EReal)) univ := by
  have h1 := (discPshOn_norm_sq (H := ComplexModel n) univ).comp_affine
    ((Real.sqrt a : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)) (-((Real.sqrt a : ℂ) • q))
  have h2 := h1.add (discPshOn_const ((b : ℝ) : EReal) (EReal.coe_ne_top b)
    ((fun y => -((Real.sqrt a : ℂ) • q) +
      ((Real.sqrt a : ℂ) • ContinuousLinearMap.id ℂ (ComplexModel n)) y) ⁻¹' univ))
  refine (h2.congr fun x _ => ?_).plurisubharmonicOn isOpen_univ
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq]
  rw [← EReal.coe_add]
  congr 1
  have : -((Real.sqrt a : ℂ) • q) + (Real.sqrt a : ℂ) • x = (Real.sqrt a : ℂ) • (x - q) := by
    rw [smul_sub]; abel
  rw [this, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt ha]

/-- `[FN80]` §5: `φ ∈ WSP(X)`: locally, `φ - c‖·‖² ∈ WP` for some `c > 0`. -/
def IsWeaklyStrictlyPSHOn (X : Set (ComplexModel n)) (φ : ComplexModel n → EReal) : Prop :=
  ∀ x ∈ X, ∃ U : Set (ComplexModel n), IsOpen U ∧ x ∈ U ∧ ∃ c : ℝ, 0 < c ∧
    IsWeaklyPSHOn (X ∩ U) (fun y => φ y + ((-(c * ‖y‖ ^ 2) : ℝ) : EReal))

theorem IsWeaklyStrictlyPSHOn.mono {X Y : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyStrictlyPSHOn X φ) (hYX : Y ⊆ X) : IsWeaklyStrictlyPSHOn Y φ := by
  intro x hx
  obtain ⟨U, hU, hxU, c, hc, h⟩ := hφ x (hYX hx)
  exact ⟨U, hU, hxU, c, hc, h.mono (inter_subset_inter_left _ hYX)⟩

theorem IsWeaklyPSHOn.congr {X : Set (ComplexModel n)} {φ ψ : ComplexModel n → EReal}
    (hφ : IsWeaklyPSHOn X φ) (h : EqOn φ ψ X) : IsWeaklyPSHOn X ψ :=
  ⟨fun x hx => h hx ▸ hφ.ne_top x hx, fun x hx y hy => by
    have hy' : φ x < y := by rw [h hx]; exact hy
    have h1 := hφ.upperSemicontinuousOn x hx y hy'
    filter_upwards [h1, self_mem_nhdsWithin] with x' hx' hx'X
    rw [← h hx'X]
    exact hx',
    fun f hf hfX => (hφ.disc f hf hfX).congr fun t ht => h (hfX ht)⟩

theorem quad_identity (y q : ComplexModel n) {c a : ℝ} (hα : 3 * c / 4 - a ≠ 0) :
    c * ‖y‖ ^ 2 - a * ‖y - q‖ ^ 2 - c / 4 * ‖y‖ ^ 2 =
      (3 * c / 4 - a) * ‖y - (((-(a / (3 * c / 4 - a)) : ℝ) : ℂ) • q)‖ ^ 2 +
        (-(a ^ 2 / (3 * c / 4 - a) * ‖q‖ ^ 2) - a * ‖q‖ ^ 2) := by
  set α := 3 * c / 4 - a with hαdef
  have e1 := norm_sub_sq (𝕜 := ℂ) y q
  set t : ℂ := ((-(a / α) : ℝ) : ℂ) with htdef
  have e2 := norm_sub_sq (𝕜 := ℂ) y (t • q)
  have e3 : RCLike.re (inner ℂ y (t • q)) = -(a / α) * RCLike.re (inner ℂ y q) := by
    rw [inner_smul_right, htdef]
    simp
  have e4 : ‖t • q‖ ^ 2 = (a / α) ^ 2 * ‖q‖ ^ 2 := by
    rw [htdef]
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
  rw [e1, e2, e3, e4]
  field_simp
  ring

/-- `WSP ⊆ WP` near each point, and the quadratic strictification `φ - a‖· - q‖²`
(`0 ≤ a ≤ c/2`) of a `WSP` function is still `WSP` there. -/
theorem IsWeaklyStrictlyPSHOn.local {X : Set (ComplexModel n)}
    {φ : ComplexModel n → EReal} (hφ : IsWeaklyStrictlyPSHOn X φ) {x : ComplexModel n}
    (hx : x ∈ X) : ∃ U : Set (ComplexModel n), IsOpen U ∧ x ∈ U ∧ ∃ c : ℝ, 0 < c ∧
      IsWeaklyPSHOn (X ∩ U) φ ∧
      ∀ (a : ℝ) (q : ComplexModel n), 0 ≤ a → a ≤ c / 2 →
        IsWeaklyStrictlyPSHOn (X ∩ U) (fun y => φ y + ((-(a * ‖y - q‖ ^ 2) : ℝ) : EReal)) := by
  obtain ⟨U, hU, hxU, c, hc, h⟩ := hφ x hx
  refine ⟨U, hU, hxU, c, hc, ?_, ?_⟩
  · refine (h.add (IsWeaklyPSHOn.of_plurisubharmonicOn (X := X ∩ U)
      (plurisubharmonicOn_quadratic hc.le 0 0) (subset_univ _))).congr fun y _ => ?_
    simp only [sub_zero, add_zero]
    rw [add_assoc, ← EReal.coe_add]
    simp
  · intro a q ha hac y hy
    refine ⟨U, hU, hy.2, c / 4, by positivity, ?_⟩
    have hα : 0 < 3 * c / 4 - a := by linarith
    have hq := IsWeaklyPSHOn.of_plurisubharmonicOn (X := X ∩ U ∩ U)
      (plurisubharmonicOn_quadratic hα.le ((((-(a / (3 * c / 4 - a))) : ℝ) : ℂ) • q)
        (-(a ^ 2 / (3 * c / 4 - a) * ‖q‖ ^ 2) - a * ‖q‖ ^ 2)) (subset_univ _)
    refine ((h.mono inter_subset_left).add hq).congr fun z _ => ?_
    simp only
    rw [add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add]
    congr 2
    linarith [quad_identity z q hα.ne']

end SGPT.Unibranch.FNL

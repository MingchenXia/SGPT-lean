import SGPT.Unibranch.FNSSiu
import SGPT.Unibranch.FNSHartogs
import SGPT.Unibranch.FNLBasic

/-!
# Theorem 5.3.1 of Fornæss–Narasimhan from the Runge property

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), Theorem 5.3.1 (`[FN80]`): `WP(X) = P(X)`; used for `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`, after `def:unibranch:L105`).

The proof of `[FN80, Thm. 5.3.1]` has two halves. For `φ ∈ WP(X)` on a closed subvariety `X` of
a polydisc, consider the Hartogs domain over `X`

`Ω_φ = {(w, z) ∈ ℂ × X : φ(z) + log |w| < 0}` (`hartogsDomain`).

1. `Ω_φ` is Runge in `X × ℂ` (`HartogsRunge`; Lemma 5.2 + Rossi's local maximum principle;
   lane FNL).
2. A Stein neighbourhood `V` of `Ω_φ` with `V ∩ (X × ℂ) = Ω_φ` (Siu), its Hartogs radius
   `|w| < e^{-λ(z)}` and `λ|_X = φ` with `λ` plurisubharmonic.

This file proves the second half from the first: `exists_ambient_psh_of_hartogsRunge`. If
`X ∩ O = {h = 0}` near `x₀` (`h` holomorphic on the open `O`), `φ` is upper semicontinuous on `X`
with values in `[-∞, ∞)`, and `Ω_φ` (over `X ∩ O`) is Runge, then `φ` is, near `x₀`, the
restriction to `X` of a plurisubharmonic function. The Stein neighbourhood is the increasing union
of monomial polyhedra `P_j ⊇ K_j` of `FNSSiu.exists_nested_monoPoly` (for a compact rotation
invariant exhaustion `K_j` of `Ω_φ` over a small polydisc, `exhaustion`), and
`λ = inf_j λ_{P_j}` (`FNSHartogs`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNS

open E2Nov16FNPolynomialPolyhedron FNR

variable {n r : ℕ}

/-! ### The Hartogs domain and the Runge property -/

/-- `Ω_φ = {(w, z) : z ∈ X, φ(z) + log |w| < 0}` (`[FN80, §5.3]`), written without extended-real
arithmetic: `φ(z) < c` and `|w| < e^{-c}` for some real `c` (`w` is the coordinate `0`). -/
def hartogsDomain (X : Set (ComplexModel n)) (φ : ComplexModel n → EReal) :
    Set (ComplexModel (n + 1)) :=
  {x | zpart x ∈ X ∧ ∃ c : ℝ, φ (zpart x) < c ∧ ‖x 0‖ < Real.exp (-c)}

/-- `[FN80, Thm. 5.3.1]`, first half: `Ω_φ` is Runge in `X × ℂ` — the polynomial hull of a compact
subset of `Ω_φ` meets `X × ℂ` only in `Ω_φ`. -/
def HartogsRunge (X : Set (ComplexModel n)) (φ : ComplexModel n → EReal) : Prop :=
  ∀ K : Set (ComplexModel (n + 1)), IsCompact K → K ⊆ hartogsDomain X φ →
    polyHull K ∩ zpart ⁻¹' X ⊆ hartogsDomain X φ

theorem ereal_lt_neg_of_add_lt {a : EReal} {L : ℝ} (h : a + (L : EReal) < 0) :
    a < ((-L : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => exact EReal.bot_lt_coe _
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_lt_coe_iff] at h
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  | top => simp at h

theorem exists_real_gt_of_ne_top {a : EReal} (ha : a ≠ ⊤) : ∃ c : ℝ, a < c := by
  obtain ⟨c, hc, -⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr ha)
  exact ⟨c, hc⟩

/-- The logarithmic form: `(w, z) ∈ Ω_φ` iff `z ∈ X` and `φ(z) + log |w| < 0`. -/
theorem mem_hartogsDomain_iff_log {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    {x : ComplexModel (n + 1)} (hφ : φ (zpart x) ≠ ⊤) :
    x ∈ hartogsDomain X φ ↔ zpart x ∈ X ∧ φ (zpart x) + ENNReal.log ‖x 0‖ₑ < 0 := by
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨c, hc, hw⟩
    have hlog : ENNReal.log ‖x 0‖ₑ < ((-c : ℝ) : EReal) := by
      rcases eq_or_ne (x 0) 0 with h0 | h0
      · rw [h0, enorm_zero, ENNReal.log_zero]; exact EReal.bot_lt_coe _
      · rw [enorm_eq_nnnorm, ENNReal.log_of_nnreal (nnnorm_ne_zero_iff.mpr h0),
          EReal.coe_lt_coe_iff, coe_nnnorm, Real.log_lt_iff_lt_exp (norm_pos_iff.mpr h0)]
        exact hw
    calc φ (zpart x) + ENNReal.log ‖x 0‖ₑ < (c : EReal) + ((-c : ℝ) : EReal) :=
          EReal.add_lt_add hc hlog
      _ = 0 := by rw [← EReal.coe_add]; simp
  · intro h
    rcases eq_or_ne (x 0) 0 with h0 | h0
    · obtain ⟨c, hc⟩ := exists_real_gt_of_ne_top hφ
      exact ⟨c, hc, by rw [h0, norm_zero]; exact Real.exp_pos _⟩
    · have hlog : ENNReal.log ‖x 0‖ₑ = (Real.log ‖x 0‖ : EReal) := by
        rw [enorm_eq_nnnorm, ENNReal.log_of_nnreal (nnnorm_ne_zero_iff.mpr h0), coe_nnnorm]
      rw [hlog] at h
      have h' : φ (zpart x) < ((-Real.log ‖x 0‖ : ℝ) : EReal) := ereal_lt_neg_of_add_lt h
      obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp h'
      refine ⟨c, hc1, ?_⟩
      rw [EReal.coe_lt_coe_iff] at hc2
      have : Real.log ‖x 0‖ < -c := by linarith
      rwa [Real.log_lt_iff_lt_exp (norm_pos_iff.mpr h0)] at this

theorem hartogsDomain_subset {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal} :
    hartogsDomain X φ ⊆ zpart ⁻¹' X := fun _ hx => hx.1

/-- `Ω_φ` is relatively open in `X × ℂ` when `φ` is upper semicontinuous on `X`. -/
theorem exists_isOpen_hartogsDomain {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : UpperSemicontinuousOn φ X) :
    ∃ G : Set (ComplexModel (n + 1)), IsOpen G ∧ hartogsDomain X φ = G ∩ zpart ⁻¹' X := by
  choose u hu hXu using fun c : ℝ => upperSemicontinuousOn_iff_preimage_Iio.mp hφ (c : EReal)
  refine ⟨⋃ c : ℝ, zpart ⁻¹' u c ∩ {x | ‖x 0‖ < Real.exp (-c)}, isOpen_iUnion fun c =>
    ((hu c).preimage continuous_zpart).inter (isOpen_lt
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).continuous.norm) continuous_const), ?_⟩
  ext x
  simp only [hartogsDomain, mem_setOf_eq, mem_inter_iff, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨hxX, c, hc, hw⟩
    have : zpart x ∈ X ∩ φ ⁻¹' Iio (c : EReal) := ⟨hxX, hc⟩
    rw [hXu c] at this
    exact ⟨⟨c, this.2, hw⟩, hxX⟩
  · rintro ⟨⟨c, hxu, hw⟩, hxX⟩
    have : zpart x ∈ X ∩ u c := ⟨hxX, hxu⟩
    rw [← hXu c] at this
    exact ⟨hxX, c, this.2, hw⟩

/-! ### Rotations -/

theorem dist_wscale {c : ℂ} (hc : ‖c‖ = 1) (x y : ComplexModel (n + 1)) :
    dist (wscale c x) (wscale c y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [wscale_zero, wscale_zero, dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hc, one_mul]
  · simp only [wscale_succ]

theorem wscale_wscale_inv {c : ℂ} (hc : ‖c‖ = 1) (x : ComplexModel (n + 1)) :
    wscale c (wscale c⁻¹ x) = x := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mul_inv_cancel_left₀ hc0]
  · simp

theorem wscale_inv_wscale {c : ℂ} (hc : c ≠ 0) (x : ComplexModel (n + 1)) :
    wscale c⁻¹ (wscale c x) = x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [inv_mul_cancel_left₀ hc]
  · simp

theorem mem_hartogsDomain_wscale {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    {c : ℂ} (hc : ‖c‖ = 1) {x : ComplexModel (n + 1)} (hx : x ∈ hartogsDomain X φ) :
    wscale c x ∈ hartogsDomain X φ := by
  obtain ⟨hxX, d, hd, hw⟩ := hx
  refine ⟨by rwa [zpart_wscale], d, by rwa [zpart_wscale], ?_⟩
  rwa [wscale_zero, norm_mul, hc, one_mul]

theorem wscale_mkPt_zero (c : ℂ) (z : ComplexModel n) : wscale c (mkPt z 0) = mkPt z 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-! ### A compact rotation invariant exhaustion -/

/-- **Exhaustion.** Over a closed polydisc `zpoly x₀ ρ ⊆ O`, `Ω_φ` is exhausted by compact
rotation invariant sets `K_j`. -/
theorem exists_exhaustion {X O : Set (ComplexModel n)} {h : Fin r → ComplexModel n → ℂ}
    (hh : ∀ l, ContinuousOn (h l) O) (hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0)
    {φ : ComplexModel n → EReal} (hφ : UpperSemicontinuousOn φ (X ∩ O))
    {x₀ : ComplexModel n} {ρ : ℝ} (hρO : zpoly x₀ ρ ⊆ O) :
    ∃ K : ℕ → Set (ComplexModel (n + 1)), (∀ j, IsCompact (K j)) ∧
      (∀ j, IsRotationInvariant (K j)) ∧ (∀ j, K j ⊆ hartogsDomain (X ∩ O) φ) ∧
      (∀ j, K j ⊆ zcyl x₀ ρ) ∧
      ∀ x ∈ hartogsDomain (X ∩ O) φ, x ∈ zcyl x₀ ρ → ∃ j, x ∈ K j := by
  set Ω := hartogsDomain (X ∩ O) φ with hΩdef
  obtain ⟨G, hG, hΩG⟩ := exists_isOpen_hartogsDomain hφ
  rw [← hΩdef] at hΩG
  set Y' : Set (ComplexModel (n + 1)) := zpart ⁻¹' (X ∩ zpoly x₀ ρ) with hY'def
  have hY' : IsClosed Y' := (isClosed_inter_zpoly hh hXO hρO).preimage continuous_zpart
  set F : Set (ComplexModel (n + 1)) := Y' ∩ Gᶜ with hFdef
  have hFΩ : ∀ y ∈ F, y ∉ Ω := by
    rintro y ⟨-, hyG⟩ hyΩ
    rw [hΩG] at hyΩ
    exact hyG hyΩ.1
  have hY'Ω : ∀ x ∈ Y', x ∉ F → x ∈ Ω := by
    intro x hx hxF
    rw [hΩG]
    refine ⟨?_, hx.1, hρO hx.2⟩
    by_contra hxG
    exact hxF ⟨hx, hxG⟩
  set K : ℕ → Set (ComplexModel (n + 1)) := fun j =>
    Y' ∩ {x | ‖x 0‖ ≤ j} ∩ {x | ∀ y ∈ F, ((j : ℝ) + 1)⁻¹ ≤ dist x y} with hKdef
  -- rotations preserve `Y'`, `F` and the distance conditions
  have hY'rot : ∀ x ∈ Y', ∀ c : ℂ, wscale c x ∈ Y' := fun x hx c => by
    simpa [hY'def, zpart_wscale] using hx
  have hFrot : ∀ y ∈ F, ∀ c : ℂ, ‖c‖ = 1 → wscale c y ∈ F := by
    intro y hy c hc
    refine ⟨hY'rot y hy.1 c, fun hG' => hy.2 ?_⟩
    have hyY : y ∈ zpart ⁻¹' (X ∩ O) := ⟨hy.1.1, hρO hy.1.2⟩
    have h1 : wscale c y ∈ Ω := by
      rw [hΩG]; exact ⟨hG', by simpa [zpart_wscale] using hyY⟩
    have hc' : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
    have h2 := mem_hartogsDomain_wscale hc' h1
    rw [wscale_inv_wscale (by rintro rfl; simp at hc)] at h2
    have h3 : y ∈ Ω := h2
    rw [hΩG] at h3
    exact h3.1
  refine ⟨K, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
  · -- compactness
    have hcl : IsClosed (K j) := by
      refine (hY'.inter (isClosed_le
        ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (n + 1))).continuous.norm)
        continuous_const)).inter ?_
      have : {x : ComplexModel (n + 1) | ∀ y ∈ F, ((j : ℝ) + 1)⁻¹ ≤ dist x y} =
          ⋂ y ∈ F, {x | ((j : ℝ) + 1)⁻¹ ≤ dist x y} := by ext x; simp
      rw [this]
      exact isClosed_biInter fun y _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
    refine (isCompact_closedBall (0 : ComplexModel (n + 1))
      ((j : ℝ) + ∑ i : Fin n, (ρ + ‖x₀ i‖))).of_isClosed_subset hcl fun x hx => ?_
    rw [mem_closedBall_zero_iff]
    refine (SGPT.GAGA.Core.Box.norm_le_sum_norm x).trans ?_
    rw [Fin.sum_univ_succ]
    refine add_le_add hx.1.2 (Finset.sum_le_sum fun i _ => ?_)
    have h1 : ‖zpart x i - x₀ i‖ ≤ ρ := hx.1.1.2 i
    have h2 : ‖x i.succ‖ ≤ ‖x i.succ - x₀ i‖ + ‖x₀ i‖ := norm_le_norm_sub_add _ _
    rw [zpart_apply] at h1
    linarith
  · -- rotation invariance
    rintro x ⟨⟨hxY, hx0⟩, hxF⟩ c hc
    refine ⟨⟨hY'rot x hxY c, ?_⟩, fun y hy => ?_⟩
    · show ‖wscale c x 0‖ ≤ j
      rwa [wscale_zero, norm_mul, hc, one_mul]
    · have hc' : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
      have h := hxF (wscale c⁻¹ y) (hFrot y hy c⁻¹ hc')
      rwa [← dist_wscale hc, wscale_wscale_inv hc] at h
  · -- inside `Ω`
    rintro x ⟨⟨hxY, -⟩, hxF⟩
    refine hY'Ω x hxY fun hxF' => ?_
    have := hxF x hxF'
    rw [dist_self] at this
    have hpos : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
    linarith
  · rintro x ⟨⟨hxY, -⟩, -⟩
    exact hxY.2
  · -- covering
    intro x hxΩ hxρ
    have hxG : x ∈ G := by rw [hΩG] at hxΩ; exact hxΩ.1
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hG x hxG
    obtain ⟨j, hj⟩ := exists_nat_ge (max ‖x 0‖ δ⁻¹)
    refine ⟨j, ⟨⟨⟨hxΩ.1.1, hxρ⟩, (le_max_left _ _).trans hj⟩, fun y hy => ?_⟩⟩
    have hyx : δ ≤ dist x y := by
      by_contra hlt
      push Not at hlt
      exact hy.2 (hball (by rw [mem_ball, dist_comm]; exact hlt))
    have h1 : ((j : ℝ) + 1)⁻¹ ≤ δ := by
      rw [inv_le_comm₀ (by positivity) hδ]
      linarith [le_max_right ‖x 0‖ δ⁻¹]
    linarith

/-! ### The local theorem -/

/-- **`[FN80, Thm. 5.3.1]` from the Runge property.** Let `X ∩ O = {h = 0}` with `h` holomorphic
on the open set `O ⊆ ℂⁿ`, and let `φ : ℂⁿ → [-∞, ∞)` be weakly plurisubharmonic on `X`
(only upper semicontinuity and `φ < +∞` are used). If the Hartogs domain `Ω_φ` over `X ∩ O` is
Runge in `(X ∩ O) × ℂ`, then near every `x₀ ∈ X ∩ O` the function `φ` is the restriction to `X` of a
plurisubharmonic function: there are an open `D ∋ x₀` and `ψ` satisfying the disc criterion on
`D` with `ψ = φ` on `X ∩ D`. -/
theorem exists_ambient_psh_of_hartogsRunge {X O : Set (ComplexModel n)} (hO : IsOpen O)
    {h : Fin r → ComplexModel n → ℂ} (hh : ∀ l, DifferentiableOn ℂ (h l) O)
    (hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0)
    {φ : ComplexModel n → EReal} (hφ : SGPT.Unibranch.FNL.IsWeaklyPSHOn X φ)
    (hR : HartogsRunge (X ∩ O) φ) {x₀ : ComplexModel n} (hx₀ : x₀ ∈ X ∩ O) :
    ∃ D : Set (ComplexModel n), IsOpen D ∧ x₀ ∈ D ∧ ∃ ψ : ComplexModel n → EReal,
      DiscPshOn ψ D ∧ ∀ z ∈ X ∩ D, ψ z = φ z := by
  classical
  set Ω := hartogsDomain (X ∩ O) φ with hΩdef
  set Y : Set (ComplexModel (n + 1)) := zpart ⁻¹' (X ∩ O) with hYdef
  have husc : UpperSemicontinuousOn φ (X ∩ O) := hφ.upperSemicontinuousOn.mono inter_subset_left
  -- a polydisc of radius `2ρ` inside `O`
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO x₀ hx₀.2
  set ρ : ℝ := ε / (2 * ((n : ℝ) + 1)) with hρdef
  have hρ : 0 < ρ := by positivity
  have h2ρO : zpoly x₀ (2 * ρ) ⊆ O := by
    intro z hz
    apply hεO
    rw [mem_ball, dist_eq_norm]
    calc ‖z - x₀‖ ≤ ∑ i, ‖(z - x₀) i‖ := SGPT.GAGA.Core.Box.norm_le_sum_norm _
      _ ≤ ∑ _i : Fin n, 2 * ρ := Finset.sum_le_sum fun i _ => by simpa using hz i
      _ = n * (2 * ρ) := by simp
      _ < ε := by
        rw [hρdef]
        have hn : (0 : ℝ) ≤ n := n.cast_nonneg
        field_simp
        nlinarith
  have hρO : zpoly x₀ ρ ⊆ O := (zpoly_mono (by linarith)).trans h2ρO
  -- the exhaustion, together with the point `(0, x₀)`
  obtain ⟨K, hKc, hKr, hKΩ, hKρ, hKcov⟩ :=
    exists_exhaustion (fun l => (hh l).continuousOn) hXO husc hρO
  have hp₀ : mkPt x₀ 0 ∈ Ω := by
    refine ⟨by simpa using hx₀, ?_⟩
    obtain ⟨c, hc⟩ := exists_real_gt_of_ne_top (hφ.ne_top x₀ hx₀.1)
    exact ⟨c, by simpa using hc, by simpa using Real.exp_pos (-c)⟩
  set K' : ℕ → Set (ComplexModel (n + 1)) := fun j => K j ∪ {mkPt x₀ 0} with hK'def
  obtain ⟨G, hG, hΩG⟩ := exists_isOpen_hartogsDomain husc
  obtain ⟨S, hSmono, hKS, hSΩ⟩ := exists_nested_monoPoly hO hh hXO (hartogsDomain_subset)
    hR hG hΩG hρ h2ρO (K := K') (fun j => (hKc j).union isCompact_singleton)
    (fun j => (hKr j).union fun x hx c _ => by rw [mem_singleton_iff.mp hx, wscale_mkPt_zero]; rfl)
    (fun j => union_subset (hKΩ j) (singleton_subset_iff.mpr hp₀))
    (fun j => union_subset (hKρ j) (singleton_subset_iff.mpr fun i => by simp [hρ.le]))
  -- the domain and the function
  set D : Set (ComplexModel n) := {z | zcond (S 0) z} ∩ {z | ∀ i, ‖z i - x₀ i‖ < ρ} with hDdef
  have hD : IsOpen D := by
    refine (isOpen_setOf_zcond (S 0)).inter ?_
    have : {z : ComplexModel n | ∀ i, ‖z i - x₀ i‖ < ρ} = ⋂ i, {z | ‖z i - x₀ i‖ < ρ} := by
      ext z; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt
      (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.sub continuous_const).norm) continuous_const
  have hx₀D : x₀ ∈ D := by
    refine ⟨(zcond_iff_mem_monoPoly _ _).mpr (hKS 0 (Or.inr rfl)), fun i => by simpa using hρ⟩
  refine ⟨D, hD, hx₀D, fun z => ⨅ j, polyLambda (S j) z,
    (discPshOn_iInf_polyLambda hSmono).mono inter_subset_left, ?_⟩
  rintro z ⟨hzX, hzD⟩
  have hzO : z ∈ O := hρO fun i => (hzD.2 i).le
  have hmono : ∀ j, monoPoly (S 0) ⊆ monoPoly (S j) := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact ih.trans (hSmono j)
  have hzj : ∀ j, zcond (S j) z := fun j =>
    zcond_of_mem_monoPoly (hmono j ((zcond_iff_mem_monoPoly (S 0) z).mp hzD.1))
  apply le_antisymm
  · -- `inf_j λ_j ≤ φ`
    by_contra hlt
    push Not at hlt
    obtain ⟨c₂, hc₂1, hc₂2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    obtain ⟨c₁, hc₁1, hc₁2⟩ := EReal.lt_iff_exists_real_btwn.mp hc₂1
    have hc12 : c₁ < c₂ := EReal.coe_lt_coe_iff.mp hc₁2
    set x := mkPt z (Real.exp (-c₂) : ℂ) with hxdef
    have hxn : ‖x 0‖ = Real.exp (-c₂) := by
      rw [hxdef, mkPt_zero, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hxΩ : x ∈ Ω := by
      refine ⟨by simpa [hxdef] using (⟨hzX, hzO⟩ : z ∈ X ∩ O), c₁, by simpa [hxdef] using hc₁1, ?_⟩
      rw [hxn, Real.exp_lt_exp]
      linarith
    obtain ⟨j, hj⟩ := hKcov x hxΩ (fun i => by simpa [hxdef] using (hzD.2 i).le)
    have hmem := hKS j (Or.inl hj)
    have hlam := polyLambda_lt_of_mem_monoPoly hmem
      (Complex.ofReal_ne_zero.mpr (Real.exp_pos (-c₂)).ne')
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.log_exp, neg_neg] at hlam
    have := (iInf_le (fun j => polyLambda (S j) z) j).trans_lt hlam
    exact absurd (hc₂2.trans this) (lt_irrefl _)
  · -- `φ ≤ λ_j` for every `j`
    refine le_iInf fun j => ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    have hn : ‖(Real.exp (-t) : ℂ)‖ = Real.exp (-t) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hmem := mem_monoPoly_of_polyLambda_lt (hzj j) ht1 hn.le
    have hxΩ := hSΩ j ⟨hmem, by simpa using (⟨hzX, hzO⟩ : z ∈ X ∩ O)⟩
    obtain ⟨-, c, hc1, hc2⟩ := hxΩ
    rw [zpart_mkPt] at hc1
    rw [mkPt_zero, hn, Real.exp_lt_exp] at hc2
    have : φ z < t := hc1.trans (EReal.coe_lt_coe_iff.mpr (by linarith))
    exact absurd (ht2.trans this) (lt_irrefl _)

end SGPT.Unibranch.FNS

import SGPT.Toric.GeodesicGeneral
import SGPT.Toric.BigToricConvexBodies
import SGPT.PSH.SourceGeodesicRays
import SGPT.Envelopes.SourceRelativeEnergyClosure

/-!
# Toric geodesic rays

Source `chapter_toric_big.tex`, `cor:geod_tor_char`: let `φ ∈ PSH_tor(X, θ) ∩ PSH(X, θ)_{>0}` be
a model potential and
`R_tor(X, θ; φ) = {ℓ ∈ R(X, θ; φ) : ℓ_t ∈ PSH_tor(X, θ) for all t ≥ 0}`.  There is a canonical
bijection between `R_tor(X, θ; φ)` and the proper closed convex functions `g` on `M_ℝ` with
`cl Dom g = Δ(θ, φ)`, and `G_{ℓ_t} = G_φ + t g` for `t > 0` (`eq:geod_ray_G`).

`R(X, θ; φ)` is the source collection `sourceGeodesicRays` (`def:geodraydef`: relative full
mass at every time, every segment a geodesic, initial value `φ`).

## Route

`g ↦ ℓ`: `G_φ + t g` is closed proper convex and `+∞` off `P_D`, so it is `G_{ℓ_t}` for a unique
toric `ℓ_t` (`thm:toricpshbig`); all `Δ(θ, ℓ_t) = Δ(θ, φ)`, so the `ℓ_t` have the mass of `φ`,
are `P`-equivalent, and `ℓ_t ≼ φ`; on every segment the geodesic is toric with linear `G`
(`cor:toricgeodgeneral`), hence equal to `ℓ`.  `ℓ ↦ g`: by `cor:toricgeodgeneral` on the
segments `[0, b]`, `G_{ℓ_t} = G_φ + t g'` with `g' = G_{ℓ_1} - G_φ` on `Dom G_{ℓ_1}` and `+∞`
elsewhere; `g'` is convex and bounded below (by `-sup_X ℓ_1`, `prop:raysuplinear`), and
`g = cl g'` agrees with `g'` on the relative interior of the common domain, whence
`G_{ℓ_t} = G_φ + t g` by `prop:closedcvx_domain`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators RealInnerProductSpace

/-! ### Extended-real helpers -/

theorem EReal.coe_mul_monotone {t : ℝ} (ht : 0 ≤ t) : Monotone (fun y : EReal => (t : EReal) * y) :=
  fun _ _ hab => mul_le_mul_of_nonneg_left hab (by exact_mod_cast ht)

theorem EReal.continuous_coe_mul {t : ℝ} (ht : 0 < t) : Continuous (fun y : EReal => (t : EReal) * y) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hne : ((t : EReal), y).1 ≠ 0 := by change (t : EReal) ≠ 0; exact_mod_cast ht.ne'
  have := EReal.continuousAt_mul (p := ((t : EReal), y)) (Or.inl hne) (Or.inl hne)
    (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t))
  exact this.comp (continuous_const.prodMk continuous_id).continuousAt

theorem EReal.coe_mul_ne_bot_of_nonneg {t : ℝ} (ht : 0 ≤ t) {x : EReal} (hx : x ≠ ⊥) :
    (t : EReal) * x ≠ ⊥ := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; simp
  · exact EReal.coe_mul_ne_bot_of_pos hpos hx

section ConvexHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `t • g` is convex for `t ≥ 0`. -/
theorem isConvex_coe_mul {g : E → EReal} (hg : IsConvex g) (hgb : ∀ x, g x ≠ ⊥) {t : ℝ}
    (ht : 0 ≤ t) : IsConvex (fun x => (t : EReal) * g x) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [EReal.coe_zero, zero_mul]
    have : (fun _ : E => (0 : EReal)) = fun x => ((fun _ : E => (0 : ℝ)) x : EReal) := by
      funext x; simp
    rw [this]
    exact isConvex_coe_iff.mpr (convexOn_const 0 convex_univ)
  apply isConvex_iff_strict_combo.mpr
  intro x y r s a b hxr hys ha hb hab
  have hlt (z : E) (q : ℝ) (hz : (t : EReal) * g z < (q : EReal)) : g z < ((q / t : ℝ) : EReal) := by
    induction hgz : g z using EReal.rec with
    | bot => exact absurd hgz (hgb z)
    | top => rw [hgz, EReal.coe_mul_top_of_pos hpos] at hz; exact absurd hz (not_lt.mpr le_top)
    | coe c =>
      rw [hgz, ← EReal.coe_mul, EReal.coe_lt_coe_iff] at hz
      exact EReal.coe_lt_coe_iff.mpr ((lt_div_iff₀ hpos).mpr (by linarith))
  have hcomb := isConvex_iff_strict_combo.mp hg x y (r / t) (s / t) a b (hlt x r hxr) (hlt y s hys)
    ha hb hab
  induction hgc : g (a • x + b • y) using EReal.rec with
  | bot => exact absurd hgc (hgb _)
  | top => rw [hgc] at hcomb; exact absurd hcomb (not_lt.mpr le_top)
  | coe c =>
    rw [hgc, EReal.coe_lt_coe_iff] at hcomb
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff]
    have : t * c < t * (a * (r / t) + b * (s / t)) := mul_lt_mul_of_pos_left hcomb hpos
    calc t * c < t * (a * (r / t) + b * (s / t)) := this
      _ = a * r + b * s := by field_simp

omit [NormedSpace ℝ E] in
/-- `t • g` is lower semicontinuous for `t ≥ 0`. -/
theorem lowerSemicontinuous_coe_mul {g : E → EReal} (hg : LowerSemicontinuous g) {t : ℝ}
    (ht : 0 ≤ t) : LowerSemicontinuous (fun x => (t : EReal) * g x) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [EReal.coe_zero, zero_mul]
    exact lowerSemicontinuous_const
  exact (EReal.continuous_coe_mul hpos).comp_lowerSemicontinuous hg (EReal.coe_mul_monotone ht)

omit [NormedSpace ℝ E] in
/-- The sum of two lower semicontinuous functions which are never `-∞`. -/
theorem lowerSemicontinuous_add_of_ne_bot {f g : E → EReal} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) (hfb : ∀ x, f x ≠ ⊥) (hgb : ∀ x, g x ≠ ⊥) :
    LowerSemicontinuous (fun x => f x + g x) :=
  hf.add' hg fun x => EReal.continuousAt_add (Or.inr (hgb x)) (Or.inl (hfb x))

end ConvexHelpers

/-- Affinity in `t` of `G + t g`: `(1-s)(A + a g) + s(A + b g) = A + ((1-s)a + s b) g`. -/
theorem EReal.affine_combo {A g : EReal} (hA : A ≠ ⊥) (hg : g ≠ ⊥) {a b s : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hs : s ∈ Ioo (0 : ℝ) 1) :
    ((1 - s : ℝ) : EReal) * (A + (a : EReal) * g) + (s : EReal) * (A + (b : EReal) * g) =
      A + (((1 - s) * a + s * b : ℝ) : EReal) * g := by
  have h1s : 0 < 1 - s := sub_pos.mpr hs.2
  have hb : 0 ≤ b := ha.trans hab
  induction A using EReal.rec with
  | bot => exact absurd rfl hA
  | top =>
    rw [EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot_of_nonneg ha hg),
      EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot_of_nonneg hb hg),
      EReal.coe_mul_top_of_pos h1s, EReal.coe_mul_top_of_pos hs.1, EReal.top_add_top,
      EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot_of_nonneg (by nlinarith [hs.1]) hg)]
  | coe A =>
    induction g using EReal.rec with
    | bot => exact absurd rfl hg
    | coe g =>
      simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
      ring
    | top =>
      rcases hb.eq_or_lt with hb0 | hbpos
      · have ha0 : a = 0 := le_antisymm (hb0 ▸ hab) ha
        subst ha0; subst hb0
        simp only [EReal.coe_zero, zero_mul, add_zero, mul_zero]
        rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
        congr 1; ring
      · have hc : 0 < (1 - s) * a + s * b := by nlinarith [hs.1]
        rw [EReal.coe_mul_top_of_pos hbpos, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _), EReal.coe_mul_top_of_pos hs.1,
          EReal.add_top_of_ne_bot, EReal.coe_mul_top_of_pos hc, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
        rcases ha.eq_or_lt with ha0 | hapos
        · subst ha0
          simp only [EReal.coe_zero, zero_mul, add_zero]
          rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
        · rw [EReal.coe_mul_top_of_pos hapos, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _), EReal.coe_mul_top_of_pos h1s]
          exact top_ne_bot

/-- A point of the intrinsic interior is not on the intrinsic frontier. -/
theorem not_mem_intrinsicFrontier_of_mem_intrinsicInterior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {x : E} (hx : x ∈ intrinsicInterior ℝ s) :
    x ∉ intrinsicFrontier ℝ s := by
  rintro ⟨y', hy', rfl⟩
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = y' := Subtype.ext hyx
  subst this
  exact hy'.2 hy

/-- The pointwise extended-real algebra behind `G_{ℓ_t} = G_φ + t g`: from the segment relations
`C = (1-t) A + t B` (`t < 1`), `B = (1-1/t) A + (1/t) C` (`t > 1`), deduce
`C = A + t (B - A)` with the convention `B - A = +∞` when `B = +∞`. -/
theorem EReal.ray_case {A B C : EReal} (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hC : C ≠ ⊥) {t : ℝ} (ht : 0 < t)
    (h1 : t < 1 → C = ((1 - t : ℝ) : EReal) * A + (t : EReal) * B)
    (h2 : 1 < t → B = ((1 - 1 / t : ℝ) : EReal) * A + ((1 / t : ℝ) : EReal) * C)
    (h3 : t = 1 → C = B) (hAC : A = ⊤ → C = ⊤) (hAB : A = ⊤ → B = ⊤) :
    C = A + (t : EReal) * (if B = ⊤ then ⊤ else ((B.toReal - A.toReal : ℝ) : EReal)) := by
  have hne : (t : EReal) * (if B = ⊤ then ⊤ else ((B.toReal - A.toReal : ℝ) : EReal)) ≠ ⊥ := by
    apply EReal.coe_mul_ne_bot_of_pos ht
    split_ifs
    · exact top_ne_bot
    · exact EReal.coe_ne_bot _
  by_cases hAt : A = ⊤
  · rw [hAC hAt]
    rw [hAt] at hne ⊢
    exact (EReal.top_add_of_ne_bot hne).symm
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, A = a := ⟨A.toReal, (EReal.coe_toReal hAt hA).symm⟩
  by_cases hBt : B = ⊤
  · rw [if_pos hBt, EReal.coe_mul_top_of_pos ht, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    rcases lt_trichotomy t 1 with hlt | heq | hgt
    · rw [h1 hlt, hBt, EReal.coe_mul_top_of_pos ht, ← EReal.coe_mul,
        EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    · rw [h3 heq, hBt]
    · by_contra hCt
      obtain ⟨c, rfl⟩ : ∃ c : ℝ, C = c := ⟨C.toReal, (EReal.coe_toReal hCt hC).symm⟩
      have := h2 hgt
      rw [hBt, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at this
      exact EReal.coe_ne_top _ this.symm
  obtain ⟨b, rfl⟩ : ∃ b : ℝ, B = b := ⟨B.toReal, (EReal.coe_toReal hBt hB).symm⟩
  rw [if_neg hBt, EReal.toReal_coe, EReal.toReal_coe, ← EReal.coe_mul, ← EReal.coe_add]
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · rw [h1 hlt, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  · rw [h3 heq, heq, EReal.coe_eq_coe_iff]; ring
  · have hCt : C ≠ ⊤ := by
      intro hCt
      have := h2 hgt
      have h1t : 0 < 1 / t := by positivity
      rw [hCt, EReal.coe_mul_top_of_pos h1t, ← EReal.coe_mul,
        EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at this
      exact EReal.coe_ne_top _ this
    obtain ⟨c, rfl⟩ : ∃ c : ℝ, C = c := ⟨C.toReal, (EReal.coe_toReal hCt hC).symm⟩
    have := h2 hgt
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff] at this
    rw [EReal.coe_eq_coe_iff]
    field_simp at this
    nlinarith

/-- Cancellation of a finite summand in `EReal`. -/
theorem EReal.add_left_cancel_coe {c : ℝ} {x y : EReal} (h : (c : EReal) + x = (c : EReal) + y) :
    x = y := by
  have := congrArg (fun z => ((-c : ℝ) : EReal) + z) h
  simp only [← add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add] at this
  exact this

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (omega : KahlerBackground n (PolytopeToricVariety γ hs))

/-- Source `R_tor(X, θ; φ)`: the geodesic rays from the model potential `φ` all of whose
values are toric. -/
def toricRays (φ : PolytopeToricVariety γ hs → EReal) (hφ : SourceModelPotential h.atlasForm φ) :
    Set (SourceRayFamily (PolytopeToricVariety γ hs)) :=
  {ℓ | ℓ ∈ sourceGeodesicRays omega h.atlasForm φ hφ ∧ ∀ t, ℓ t ∈ h.PSHTor}

/-- Set (2) of `cor:geod_tor_char`: the proper closed convex functions `g` on `M_ℝ` with
`cl Dom g = Δ(θ, φ)`. -/
def rayLegendreClass (φ : PolytopeToricVariety γ hs → EReal) :
    Set (EuclideanSpace ℝ (Fin n) → EReal) :=
  {g | IsProper g ∧ LowerSemicontinuous g ∧ closure (effectiveDomain g) = h.newtonBody φ}

/-- Two toric potentials with the same Legendre transform coincide. -/
theorem eq_of_legendre_eq {u v : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (hv : v ∈ h.PSHTor) (heq : h.legendre u = h.legendre v) : u = v := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu
  have := (h.equivClosedProper hP).injective (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩)
    (Subtype.ext (by rw [equivClosedProper_apply, equivClosedProper_apply]; exact heq))
  exact congrArg Subtype.val this

theorem legendre_isProper {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    IsProper (h.legendre u) :=
  (h.legendre_mem_closedProperOnBody (h.nonempty_toricDivisorPolytope_of_mem hu) hu).1

theorem newtonBody_eq_closure_dom {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.newtonBody u = closure (effectiveDomain (h.legendre u)) :=
  h.newtonBody_eq_closure_effectiveDomain (h.nonempty_toricDivisorPolytope_of_mem hu) hu

section FromLegendre

variable {φ : PolytopeToricVariety γ hs → EReal} (hφt : φ ∈ h.PSHTor)
include hφt

/-- For `g` in set (2), `ri Dom g = ri Dom G_φ` (both have closure `Δ(θ, φ)`). -/
theorem intrinsicInterior_dom_eq {g : EuclideanSpace ℝ (Fin n) → EReal}
    (hg : g ∈ h.rayLegendreClass φ) :
    intrinsicInterior ℝ (effectiveDomain g) =
      intrinsicInterior ℝ (effectiveDomain (h.legendre φ)) :=
  intrinsicInterior_eq_of_closure_eq (convex_effectiveDomain hg.1.1)
    (convex_effectiveDomain (h.legendre_isProper hφt).1)
    (by rw [hg.2.2, h.newtonBody_eq_closure_dom hφt])

theorem nonempty_intrinsicInterior_dom :
    (intrinsicInterior ℝ (effectiveDomain (h.legendre φ))).Nonempty :=
  (h.legendre_isProper hφt).2.1.intrinsicInterior (convex_effectiveDomain (h.legendre_isProper hφt).1)

/-- `G_φ + t g`. -/
def legendreRaySum (g : EuclideanSpace ℝ (Fin n) → EReal) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun m => h.legendre φ m + (t : EReal) * g m

omit hφt in
theorem legendreRaySum_def (g : EuclideanSpace ℝ (Fin n) → EReal) (t : ℝ) :
    h.legendreRaySum (φ := φ) g t = fun m => h.legendre φ m + (t : EReal) * g m := rfl

/-- The domain of `G_φ + t g` lies between `ri Dom G_φ` and `Dom G_φ`. -/
theorem dom_legendreRaySum {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ)
    {t : ℝ} (ht : 0 ≤ t) :
    intrinsicInterior ℝ (effectiveDomain (h.legendre φ)) ⊆
        effectiveDomain (h.legendreRaySum (φ := φ) g t) ∧
      effectiveDomain (h.legendreRaySum (φ := φ) g t) ⊆ effectiveDomain (h.legendre φ) := by
  constructor
  · intro m hm
    have hm1 : m ∈ effectiveDomain (h.legendre φ) := intrinsicInterior_subset hm
    rw [← h.intrinsicInterior_dom_eq hφt hg] at hm
    have hm2 : m ∈ effectiveDomain g := intrinsicInterior_subset hm
    change h.legendre φ m < ⊤ at hm1
    change g m < ⊤ at hm2
    change h.legendre φ m + (t : EReal) * g m < ⊤
    have hg2 : (t : EReal) * g m < ⊤ := by
      induction hgm : g m using EReal.rec with
      | bot => exact absurd hgm (hg.1.2.2 m)
      | top => rw [hgm] at hm2; exact absurd hm2 (lt_irrefl _)
      | coe c => rw [← EReal.coe_mul]; exact EReal.coe_lt_top _
    exact EReal.add_lt_top hm1.ne hg2.ne
  · intro m hm
    by_contra hnot
    have htop : h.legendre φ m = ⊤ := not_lt_top_iff.mp hnot
    change h.legendre φ m + (t : EReal) * g m < ⊤ at hm
    rw [htop, EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot_of_nonneg ht (hg.1.2.2 m))] at hm
    exact lt_irrefl _ hm

/-- `G_φ + t g ∈ ClosedProperOnBody P_D` for `t ≥ 0`. -/
theorem legendreRaySum_mem {g : EuclideanSpace ℝ (Fin n) → EReal}
    (hg : g ∈ h.rayLegendreClass φ) {t : ℝ} (ht : 0 ≤ t) :
    h.legendreRaySum (φ := φ) g t ∈ ClosedProperOnBody (toricDivisorPolytope D) := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφt
  have hG := h.legendre_mem_closedProperOnBody hP hφt
  have htg : IsProper (fun m => (t : EReal) * g m) := by
    refine ⟨isConvex_coe_mul hg.1.1 hg.1.2.2 ht, ?_, fun m => EReal.coe_mul_ne_bot_of_nonneg ht
      (hg.1.2.2 m)⟩
    obtain ⟨m, hm⟩ := hg.1.2.1
    change g m < ⊤ at hm
    refine ⟨m, ?_⟩
    change (t : EReal) * g m < ⊤
    induction hgm : g m using EReal.rec with
    | bot => exact absurd hgm (hg.1.2.2 m)
    | top => rw [hgm] at hm; exact absurd hm (lt_irrefl _)
    | coe c => rw [← EReal.coe_mul]; exact EReal.coe_lt_top _
  refine ⟨⟨isConvex_add_of_isProper hG.1 htg, ?_, fun m => ?_⟩, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := h.nonempty_intrinsicInterior_dom hφt
    exact ⟨m, (h.dom_legendreRaySum hφt hg ht).1 hm⟩
  · exact EReal.add_ne_bot_iff.mpr ⟨hG.1.2.2 m, EReal.coe_mul_ne_bot_of_nonneg ht (hg.1.2.2 m)⟩
  · exact lowerSemicontinuous_add_of_ne_bot hG.2.1 (lowerSemicontinuous_coe_mul hg.2.1 ht)
      hG.1.2.2 fun m => EReal.coe_mul_ne_bot_of_nonneg ht (hg.1.2.2 m)
  · intro m hm
    change h.legendre φ m + (t : EReal) * g m = ⊤
    rw [hG.2.2 m hm, EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot_of_nonneg ht (hg.1.2.2 m))]

/-- The ray `ℓ^g` attached to `g`: `ℓ^g_t` is the toric potential with `G = G_φ + t g`. -/
def rayOfLegendre {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ) :
    SourceRayFamily (PolytopeToricVariety γ hs) :=
  fun t => ((h.equivClosedProper (h.nonempty_toricDivisorPolytope_of_mem hφt)).symm
    ⟨_, h.legendreRaySum_mem hφt hg t.2⟩).1

theorem rayOfLegendre_mem {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ)
    (t : Ici (0 : ℝ)) : h.rayOfLegendre hφt hg t ∈ h.PSHTor :=
  ((h.equivClosedProper (h.nonempty_toricDivisorPolytope_of_mem hφt)).symm
    ⟨_, h.legendreRaySum_mem hφt hg t.2⟩).2

theorem legendre_rayOfLegendre {g : EuclideanSpace ℝ (Fin n) → EReal}
    (hg : g ∈ h.rayLegendreClass φ) (t : Ici (0 : ℝ)) :
    h.legendre (h.rayOfLegendre hφt hg t) = h.legendreRaySum (φ := φ) g t := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφt
  have := h.equivClosedProper_apply hP ((h.equivClosedProper hP).symm
    ⟨_, h.legendreRaySum_mem hφt hg t.2⟩)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

theorem rayOfLegendre_zero {g : EuclideanSpace ℝ (Fin n) → EReal}
    (hg : g ∈ h.rayLegendreClass φ) : h.rayOfLegendre hφt hg ⟨0, by simp⟩ = φ := by
  apply h.eq_of_legendre_eq (h.rayOfLegendre_mem hφt hg _) hφt
  rw [legendre_rayOfLegendre]
  funext m
  simp [legendreRaySum]

theorem newtonBody_rayOfLegendre {g : EuclideanSpace ℝ (Fin n) → EReal}
    (hg : g ∈ h.rayLegendreClass φ) (t : Ici (0 : ℝ)) :
    h.newtonBody (h.rayOfLegendre hφt hg t) = h.newtonBody φ := by
  rw [h.newtonBody_eq_closure_dom (h.rayOfLegendre_mem hφt hg t), legendre_rayOfLegendre,
    h.newtonBody_eq_closure_dom hφt]
  obtain ⟨h1, h2⟩ := h.dom_legendreRaySum hφt hg t.2
  apply le_antisymm (closure_mono h2)
  rw [← closure_intrinsicInterior_eq_closure_of_convex
    (convex_effectiveDomain (h.legendre_isProper hφt).1)]
  exact closure_mono h1

theorem MA_rayOfLegendre {g : EuclideanSpace ℝ (Fin n) → EReal}
    (hg : g ∈ h.rayLegendreClass φ) (t : Ici (0 : ℝ)) :
    h.MA (h.rayOfLegendre_mem hφt hg t) univ = h.MA hφt univ := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφt
  rw [h.MA_univ hP, h.MA_univ hP, h.newtonBody_rayOfLegendre]

/-- `ℓ^g_t ≼ φ` and `ℓ^g_t` has full mass relative to `φ`. -/
theorem relativeFullMass_rayOfLegendre (hφ : SourceModelPotential h.atlasForm φ)
    {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ) (t : Ici (0 : ℝ)) :
    SourceRelativeFullMass h.atlasForm φ (h.rayOfLegendre hφt hg t) hφ := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφt
  have hr := h.rayOfLegendre_mem hφt hg t
  refine ⟨hr.1, ?_, h.MA_rayOfLegendre hφt hg t⟩
  apply (h.singularityLE_iff hr hφt).mpr
  apply (h.profile_singularityLE_iff_legendre hP hr hφt).mpr
  -- `g` is bounded below
  have hgB : g ∈ ClosedProperOnBody (h.newtonBody φ) := by
    refine ⟨hg.1, hg.2.1, fun y hy => ?_⟩
    by_contra hne
    exact hy (hg.2.2 ▸ subset_closure (lt_top_iff_ne_top.mpr hne))
  obtain ⟨r, hr'⟩ := exists_real_global_lower_bound_of_mem_closedProperOnBody
    (h.newtonBody_properties hP hφt).2.1 hgB
  refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨-(t.1 * r), fun m => ?_⟩
  rw [legendre_rayOfLegendre]
  change h.legendre φ m ≤ h.legendre φ m + (t.1 : EReal) * g m + ((-(t.1 * r) : ℝ) : EReal)
  have hmul : ((t.1 * r : ℝ) : EReal) ≤ (t.1 : EReal) * g m := by
    rw [EReal.coe_mul]; exact EReal.coe_mul_monotone t.2 (hr' m)
  calc h.legendre φ m = h.legendre φ m + ((t.1 * r : ℝ) : EReal) + ((-(t.1 * r) : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
    _ ≤ _ := add_le_add (add_le_add le_rfl hmul) le_rfl

theorem rayExt_mem {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ)
    (t : ℝ) : sourceRayExtension (h.rayOfLegendre hφt hg) t ∈ h.PSHTor :=
  h.rayOfLegendre_mem hφt hg _

theorem legendre_rayExt {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ)
    {t : ℝ} (ht : 0 ≤ t) :
    h.legendre (sourceRayExtension (h.rayOfLegendre hφt hg) t) = h.legendreRaySum (φ := φ) g t := by
  rw [sourceRayExtension_nonneg _ t ht, legendre_rayOfLegendre]

theorem MA_rayExt_pos (hφ : SourceModelPotential h.atlasForm φ)
    {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ) (t : ℝ) :
    0 < h.MA (h.rayExt_mem hφt hg t) univ := by
  obtain ⟨_, _, hpos⟩ := hφ
  rw [show h.MA (h.rayExt_mem hφt hg t) univ = h.MA hφt univ from h.MA_rayOfLegendre hφt hg _]
  exact hpos

/-- Every segment of `ℓ^g` is the geodesic between its end points. -/
theorem geodesicClosedInterval_rayOfLegendre (hφ : SourceModelPotential h.atlasForm φ)
    {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    SourceGeodesicClosedInterval omega h.atlasForm a b
      (sourceRayExtension (h.rayOfLegendre hφt hg)) := by
  set ext := sourceRayExtension (h.rayOfLegendre hφt hg)
  rcases hab.eq_or_lt with heq | hlt
  · subst heq
    exact (sourceGeodesicClosedInterval_self_iff omega h.atlasForm a ext).mpr
      (h.rayExt_mem hφt hg a).1
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφt
  have hb : 0 ≤ b := ha.trans hab
  have hpa := h.MA_rayExt_pos hφt hφ hg a
  have hpb := h.MA_rayExt_pos hφt hφ hg b
  have hPeq : GlobalPComparison.sourcePEquivalent (n := n) (ext a) (ext b) := by
    apply (h.sourcePEquivalent_iff_newtonBody_eq hP (h.rayExt_mem hφt hg a)
      (h.rayExt_mem hφt hg b) hpa hpb).mpr
    change h.newtonBody (h.rayOfLegendre hφt hg _) = h.newtonBody (h.rayOfLegendre hφt hg _)
    rw [newtonBody_rayOfLegendre, newtonBody_rayOfLegendre]
  have tg := h.toric_geodesic_general omega (h.rayExt_mem hφt hg a) (h.rayExt_mem hφt hg b) hpa hpb
  have hPerron := sourcePerronGeodesic_isGeodesicFrom omega (h.rayExt_mem hφt hg a).1
    (h.rayExt_mem hφt hg b).1
  refine ⟨hab, fun t _ => (h.rayExt_mem hφt hg t).1, (h.rayExt_mem hφt hg a).1,
    (h.rayExt_mem hφt hg b).1, fun s _ => Or.inl (h.rayExt_mem hφt hg _).1, ?_⟩
  intro s hs
  obtain ⟨hPmem, hPleg⟩ := tg.2 hPeq _ hPerron s hs
  apply h.eq_of_legendre_eq (h.rayExt_mem hφt hg _) hPmem
  have hsb : 0 ≤ s * b + (1 - s) * a := by nlinarith [hs.1, hs.2]
  rw [hPleg, h.legendre_rayExt hφt hg hsb, h.legendre_rayExt hφt hg ha,
    h.legendre_rayExt hφt hg hb]
  funext m
  simp only [legendreRaySum]
  rw [EReal.affine_combo (h.legendre_ne_bot hφt m) (hg.1.2.2 m) ha hab hs]
  congr 3
  ring

/-- `cor:geod_tor_char`, map (2) → (1): `ℓ^g ∈ R_tor(X, θ; φ)`. -/
theorem rayOfLegendre_mem_toricRays (hφ : SourceModelPotential h.atlasForm φ)
    {g : EuclideanSpace ℝ (Fin n) → EReal} (hg : g ∈ h.rayLegendreClass φ) :
    h.rayOfLegendre hφt hg ∈ h.toricRays omega φ hφ :=
  ⟨⟨⟨fun t => h.relativeFullMass_rayOfLegendre hφt hφ hg t,
      fun _ _ ha hab => h.geodesicClosedInterval_rayOfLegendre omega hφt hφ hg ha hab⟩,
    h.rayOfLegendre_zero hφt hg⟩, fun t => h.rayOfLegendre_mem hφt hg t⟩

end FromLegendre

section FromRay

variable {φ : PolytopeToricVariety γ hs → EReal} (hφt : φ ∈ h.PSHTor)
  (hφ : SourceModelPotential h.atlasForm φ)
  {ℓ : SourceRayFamily (PolytopeToricVariety γ hs)} (hℓ : ℓ ∈ h.toricRays omega φ hφ)
include hφt hℓ

omit hφt in
theorem rayExt_mem_of_toricRays (t : ℝ) : sourceRayExtension ℓ t ∈ h.PSHTor := hℓ.2 _

omit hφt in
theorem rayExt_zero : sourceRayExtension ℓ 0 = φ := by
  rw [sourceRayExtension_nonneg ℓ 0 le_rfl]; exact hℓ.1.2

omit hφt in
theorem relativeFullMass_rayExt (t : ℝ) :
    SourceRelativeFullMass h.atlasForm φ (sourceRayExtension ℓ t) hφ := by
  have := hℓ.1.1.1 ⟨max t 0, le_max_right t 0⟩
  exact this

omit hφt in
theorem MA_rayExt_pos_of_toricRays (t : ℝ) :
    0 < h.MA (h.rayExt_mem_of_toricRays omega hφ hℓ t) univ := by
  obtain ⟨_, _, hmass⟩ := h.relativeFullMass_rayExt omega hφ hℓ t
  obtain ⟨_, _, hpos⟩ := hφ
  change 0 < sourcePotentialNonPluripolarMeasure h.atlasForm _ _ univ
  rw [hmass]; exact hpos

omit hφt in
/-- All values of a toric ray are `P`-equivalent. -/
theorem sourcePEquivalent_rayExt (a b : ℝ) :
    GlobalPComparison.sourcePEquivalent (n := n) (sourceRayExtension ℓ a) (sourceRayExtension ℓ b) := by
  have ha := h.rayExt_mem_of_toricRays omega hφ hℓ a
  have hb := h.rayExt_mem_of_toricRays omega hφ hℓ b
  have hea := (sourceRelativeFullMass_iff_envelope_eq omega ha.1).mp
    (h.relativeFullMass_rayExt omega hφ hℓ a)
  have heb := (sourceRelativeFullMass_iff_envelope_eq omega hb.1).mp
    (h.relativeFullMass_rayExt omega hφ hℓ b)
  apply (Pending.SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith omega
    (atlasClosedFormToNative h.atlasForm) ((isThetaPSH_iff_nativeThetaPotential _ _).mp ha.1)
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hb.1)
    (h.MA_rayExt_pos_of_toricRays omega hφ hℓ a)
    (h.MA_rayExt_pos_of_toricRays omega hφ hℓ b)).mpr
  apply POrder.pEquivalentWith_iff_envelope_eq.mpr
  rw [← sourceSingularityEnvelope_eq_native, ← sourceSingularityEnvelope_eq_native, hea, heb]

theorem newtonBody_rayExt (t : ℝ) :
    h.newtonBody (sourceRayExtension ℓ t) = h.newtonBody φ := by
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφt
  have := (h.sourcePEquivalent_iff_newtonBody_eq hP (h.rayExt_mem_of_toricRays omega hφ hℓ t)
    (h.rayExt_mem_of_toricRays omega hφ hℓ 0) (h.MA_rayExt_pos_of_toricRays omega hφ hℓ t)
    (h.MA_rayExt_pos_of_toricRays omega hφ hℓ 0)).mp (h.sourcePEquivalent_rayExt omega hφ hℓ t 0)
  rw [this, h.rayExt_zero omega hφ hℓ]

omit hφt in
/-- On every segment, `G` is affine in time (`cor:toricgeodgeneral`). -/
theorem legendre_rayExt_segment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) {p : ℝ} (hp : p = s * b + (1 - s) * a) :
    h.legendre (sourceRayExtension ℓ p) = fun m =>
      ((1 - s : ℝ) : EReal) * h.legendre (sourceRayExtension ℓ a) m +
        (s : EReal) * h.legendre (sourceRayExtension ℓ b) m := by
  have hseg := hℓ.1.1.2 a b ha hab.le
  have tg := h.toric_geodesic_general omega (h.rayExt_mem_of_toricRays omega hφ hℓ a)
    (h.rayExt_mem_of_toricRays omega hφ hℓ b) (h.MA_rayExt_pos_of_toricRays omega hφ hℓ a)
    (h.MA_rayExt_pos_of_toricRays omega hφ hℓ b)
  have := (tg.2 (h.sourcePEquivalent_rayExt omega hφ hℓ a b) _ hseg.2.2 s hs).2
  rw [hp]; exact this

omit hφt hℓ in
/-- `G_t = G_{ℓ_t}` for the ray. -/
abbrev rayG (ℓ : SourceRayFamily (PolytopeToricVariety γ hs)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  h.legendre (sourceRayExtension ℓ t)

omit hφt hℓ in
/-- `g' = G_{ℓ_1} - G_φ` on `Dom G_{ℓ_1}`, `+∞` elsewhere. -/
def rayDifference (φ : PolytopeToricVariety γ hs → EReal)
    (ℓ : SourceRayFamily (PolytopeToricVariety γ hs)) (m : EuclideanSpace ℝ (Fin n)) : EReal :=
  if h.legendre (sourceRayExtension ℓ 1) m = ⊤ then ⊤ else
    (((h.legendre (sourceRayExtension ℓ 1) m).toReal - (h.legendre φ m).toReal : ℝ) : EReal)

omit hφt in
theorem legendre_top_of_top {t : ℝ} (ht : 0 < t) {m : EuclideanSpace ℝ (Fin n)}
    (hm : h.legendre φ m = ⊤) : h.legendre (sourceRayExtension ℓ t) m = ⊤ := by
  have := congrFun (h.legendre_rayExt_segment omega hφ hℓ le_rfl (by linarith : (0 : ℝ) < 2 * t)
    (s := 1 / 2) ⟨by norm_num, by norm_num⟩ (p := t) (by ring)) m
  rw [this, h.rayExt_zero omega hφ hℓ, hm, EReal.coe_mul_top_of_pos (by norm_num),
    EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot_of_pos (by norm_num)
      (h.legendre_ne_bot (h.rayExt_mem_of_toricRays omega hφ hℓ _) m))]

/-- `G_{ℓ_t} = G_φ + t g'` for all `t ≥ 0`. -/
theorem legendre_rayExt_eq {t : ℝ} (ht : 0 ≤ t) :
    h.legendre (sourceRayExtension ℓ t) =
      fun m => h.legendre φ m + (t : EReal) * h.rayDifference φ ℓ m := by
  funext m
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; simp [h.rayExt_zero omega hφ hℓ]
  have hmem := h.rayExt_mem_of_toricRays omega hφ hℓ
  have hz := h.rayExt_zero omega hφ hℓ
  apply EReal.ray_case (h.legendre_ne_bot hφt m) (h.legendre_ne_bot (hmem 1) m)
    (h.legendre_ne_bot (hmem t) m) hpos
  · intro hlt
    have := congrFun (h.legendre_rayExt_segment omega hφ hℓ le_rfl zero_lt_one
      ⟨hpos, hlt⟩ (p := t) (by ring)) m
    rw [this, hz]
  · intro hgt
    have h1t : 1 / t ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, (div_lt_one hpos).mpr hgt⟩
    have := congrFun (h.legendre_rayExt_segment omega hφ hℓ le_rfl hpos h1t (p := 1)
      (by field_simp; ring)) m
    rw [this, hz]
  · intro h1; rw [h1]
  · exact h.legendre_top_of_top omega hφ hℓ hpos
  · exact h.legendre_top_of_top omega hφ hℓ one_pos

omit hφt hℓ in
theorem rayDifference_ne_bot (m : EuclideanSpace ℝ (Fin n)) : h.rayDifference φ ℓ m ≠ ⊥ := by
  unfold rayDifference
  split_ifs
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _

omit hφt hℓ in
theorem mem_dom_rayDifference_iff (m : EuclideanSpace ℝ (Fin n)) :
    m ∈ effectiveDomain (h.rayDifference φ ℓ) ↔ m ∈ effectiveDomain (h.rayG ℓ 1) := by
  change h.rayDifference φ ℓ m < ⊤ ↔ h.legendre (sourceRayExtension ℓ 1) m < ⊤
  unfold rayDifference
  split_ifs with hm
  · rw [hm]
  · exact ⟨fun _ => lt_top_iff_ne_top.mpr hm, fun _ => EReal.coe_lt_top _⟩

omit hφt in
theorem dom_rayG_subset (m : EuclideanSpace ℝ (Fin n)) (hm : m ∈ effectiveDomain (h.rayG ℓ 1)) :
    m ∈ effectiveDomain (h.legendre φ) := by
  by_contra hnot
  have htop : h.legendre φ m = ⊤ := not_lt_top_iff.mp hnot
  have := h.legendre_top_of_top omega hφ hℓ one_pos htop
  change h.legendre (sourceRayExtension ℓ 1) m < ⊤ at hm
  rw [this] at hm
  exact lt_irrefl _ hm

/-- `Dom G_{ℓ_t} = Dom G_{ℓ_1}` for `t > 0`. -/
theorem dom_rayG_eq {t : ℝ} (ht : 0 < t) :
    effectiveDomain (h.rayG ℓ t) = effectiveDomain (h.rayG ℓ 1) := by
  ext m
  change h.legendre (sourceRayExtension ℓ t) m < ⊤ ↔ h.legendre (sourceRayExtension ℓ 1) m < ⊤
  rw [h.legendre_rayExt_eq omega hφt hφ hℓ ht.le]
  dsimp only
  constructor
  · intro hm
    have hφm : h.legendre φ m ≠ ⊤ := by
      intro htop; rw [htop, EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot_of_pos ht
        (h.rayDifference_ne_bot (φ := φ) (ℓ := ℓ) m))] at hm; exact lt_irrefl _ hm
    have hg : h.rayDifference φ ℓ m ≠ ⊤ := by
      intro htop
      rw [htop, EReal.coe_mul_top_of_pos ht, EReal.add_top_of_ne_bot (h.legendre_ne_bot hφt m)] at hm
      exact lt_irrefl _ hm
    exact (h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) m).mp (lt_top_iff_ne_top.mpr hg)
  · intro hm
    have h1 : h.legendre φ m < ⊤ := h.dom_rayG_subset omega hφ hℓ m hm
    have h2 : h.rayDifference φ ℓ m < ⊤ := (h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) m).mpr hm
    obtain ⟨c, hc⟩ : ∃ c : ℝ, h.rayDifference φ ℓ m = c :=
      ⟨_, (EReal.coe_toReal h2.ne (h.rayDifference_ne_bot (φ := φ) (ℓ := ℓ) m)).symm⟩
    rw [hc, ← EReal.coe_mul]
    exact EReal.add_lt_top h1.ne (EReal.coe_ne_top _)

/-- On `Dom G_{ℓ_1}`, `(G_{ℓ_t})` is real and equal to `G_φ + t g'`. -/
theorem toReal_rayG {t : ℝ} (ht : 0 < t) {m : EuclideanSpace ℝ (Fin n)}
    (hm : m ∈ effectiveDomain (h.rayG ℓ 1)) :
    (h.rayG ℓ t m).toReal = (h.legendre φ m).toReal + t * (h.rayDifference φ ℓ m).toReal := by
  have h1 : h.legendre φ m < ⊤ := h.dom_rayG_subset omega hφ hℓ m hm
  have h2 : h.rayDifference φ ℓ m < ⊤ := (h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) m).mpr hm
  change (h.legendre (sourceRayExtension ℓ t) m).toReal = _
  rw [h.legendre_rayExt_eq omega hφt hφ hℓ ht.le]
  dsimp only
  rw [← EReal.coe_toReal h1.ne (h.legendre_ne_bot hφt m),
    ← EReal.coe_toReal h2.ne (h.rayDifference_ne_bot (φ := φ) (ℓ := ℓ) m), ← EReal.coe_mul,
    ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe, EReal.toReal_coe]

/-- `g'` is convex. -/
theorem isConvex_rayDifference : IsConvex (h.rayDifference φ ℓ) := by
  apply isConvex_iff_strict_combo.mpr
  intro x y r s a b hx hy ha hb hab
  have hxD : x ∈ effectiveDomain (h.rayG ℓ 1) :=
    (h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) x).mp (hx.trans (EReal.coe_lt_top _))
  have hyD : y ∈ effectiveDomain (h.rayG ℓ 1) :=
    (h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) y).mp (hy.trans (EReal.coe_lt_top _))
  have hmem := h.rayExt_mem_of_toricRays omega hφ hℓ
  have hzD : a • x + b • y ∈ effectiveDomain (h.rayG ℓ 1) :=
    convex_effectiveDomain (h.legendre_isProper (hmem 1)).1 hxD hyD ha.le hb.le hab
  have hfin (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ effectiveDomain (h.rayG ℓ 1)) :
      h.rayDifference φ ℓ w = ((h.rayDifference φ ℓ w).toReal : EReal) :=
    (EReal.coe_toReal ((h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) w).mpr hw).ne
      (h.rayDifference_ne_bot (φ := φ) (ℓ := ℓ) w)).symm
  rw [hfin x hxD, EReal.coe_lt_coe_iff] at hx
  rw [hfin y hyD, EReal.coe_lt_coe_iff] at hy
  rw [hfin _ hzD, EReal.coe_lt_coe_iff]
  set gx := (h.rayDifference φ ℓ x).toReal
  set gy := (h.rayDifference φ ℓ y).toReal
  set gz := (h.rayDifference φ ℓ (a • x + b • y)).toReal
  set Φx := (h.legendre φ x).toReal
  set Φy := (h.legendre φ y).toReal
  set Φz := (h.legendre φ (a • x + b • y)).toReal
  -- convexity of each `G_{ℓ_T}` on the common domain
  have hT : ∀ T : ℝ, 0 < T → Φz + T * gz ≤ a * (Φx + T * gx) + b * (Φy + T * gy) := by
    intro T hTpos
    have hcv := convexOn_toReal_effectiveDomain (h.legendre_isProper (hmem T))
    have hdomT := h.dom_rayG_eq omega hφt hφ hℓ hTpos
    have hxT : x ∈ effectiveDomain (h.rayG ℓ T) := hdomT ▸ hxD
    have hyT : y ∈ effectiveDomain (h.rayG ℓ T) := hdomT ▸ hyD
    have := hcv.2 hxT hyT ha.le hb.le hab
    simp only [smul_eq_mul] at this
    change (h.rayG ℓ T (a • x + b • y)).toReal ≤ a * (h.rayG ℓ T x).toReal +
      b * (h.rayG ℓ T y).toReal at this
    rwa [h.toReal_rayG omega hφt hφ hℓ hTpos hzD, h.toReal_rayG omega hφt hφ hℓ hTpos hxD,
      h.toReal_rayG omega hφt hφ hℓ hTpos hyD] at this
  have hle : gz ≤ a * gx + b * gy := by
    by_contra hcon
    rw [not_le] at hcon
    set δ := gz - (a * gx + b * gy)
    have hδ : 0 < δ := by simp only [δ]; linarith
    set T := (|a * Φx + b * Φy - Φz| + 1) / δ
    have hTpos : 0 < T := by positivity
    have := hT T hTpos
    have hkey : T * δ = |a * Φx + b * Φy - Φz| + 1 := by
      simp only [T]; field_simp
    have hab' : b = 1 - a := by linarith
    have : T * δ ≤ a * Φx + b * Φy - Φz := by
      simp only [δ]; nlinarith
    linarith [le_abs_self (a * Φx + b * Φy - Φz)]
  nlinarith

/-- `g' ≥ -sup_X ℓ_1` (`prop:raysuplinear`). -/
theorem le_rayDifference (m : EuclideanSpace ℝ (Fin n)) :
    ((-(⨆ x, ℓ ⟨1, by norm_num⟩ x).toReal : ℝ) : EReal) ≤ h.rayDifference φ ℓ m := by
  set C₁ := (⨆ x, ℓ ⟨1, by norm_num⟩ x).toReal
  by_cases hm : m ∈ effectiveDomain (h.rayG ℓ 1)
  swap
  · have : h.rayDifference φ ℓ m = ⊤ := by
      by_contra hne
      exact hm ((h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) m).mp (lt_top_iff_ne_top.mpr hne))
    rw [this]; exact le_top
  have hmem := h.rayExt_mem_of_toricRays omega hφ hℓ
  have hfin : h.rayDifference φ ℓ m = ((h.rayDifference φ ℓ m).toReal : EReal) :=
    (EReal.coe_toReal ((h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) m).mpr hm).ne
      (h.rayDifference_ne_bot (φ := φ) (ℓ := ℓ) m)).symm
  rw [hfin, EReal.coe_le_coe_iff]
  set gm := (h.rayDifference φ ℓ m).toReal
  set Φm := (h.legendre φ m).toReal
  set c₀ := h.potential 0
  -- for every `T > 0`: `Φm + T gm ≥ -(T C₁ + c₀)`
  have hT : ∀ T : ℝ, 0 < T → -(T * C₁ + c₀) ≤ Φm + T * gm := by
    intro T hTpos
    rw [← h.toReal_rayG omega hφt hφ hℓ hTpos hm]
    have hdomT := h.dom_rayG_eq omega hφt hφ hℓ hTpos
    have hmT' : m ∈ effectiveDomain (h.rayG ℓ T) := by rw [hdomT]; exact hm
    have hmT : h.rayG ℓ T m < ⊤ := hmT'
    -- `G_T(m) ≥ -F_T(0)`
    have hG0 : ((0 - h.realProfile (sourceRayExtension ℓ T) 0 : ℝ) : EReal) ≤ h.rayG ℓ T m := by
      change _ ≤ h.legendre _ m
      unfold legendre conjugate
      refine le_trans ?_ (le_iSup _ (0 : EuclideanSpace ℝ (Fin n)))
      rw [(h.realProfile_mem (hmem T)).2, innerₗ_apply_apply, inner_zero_left, EReal.coe_sub]
    -- `F_T(0) ≤ T C₁ + c₀`
    have hsup := sourceRay_globalSup_eq omega hℓ.1 ⟨T, hTpos.le⟩
    have hF : h.realProfile (sourceRayExtension ℓ T) 0 ≤ T * C₁ + c₀ := by
      have hp := congrFun (h.realProfile_mem (hmem T)).2 0
      have h1 : h.profile (sourceRayExtension ℓ T) 0 ≤ ((T * C₁ + c₀ : ℝ) : EReal) := by
        unfold profile
        rw [EReal.coe_add]
        apply add_le_add _ le_rfl
        rw [sourceRayExtension_nonneg ℓ T hTpos.le]
        exact (le_iSup (fun x => ℓ ⟨T, hTpos.le⟩ x) _).trans_eq hsup
      rw [hp] at h1
      exact EReal.coe_le_coe_iff.mp h1
    have h2 := EReal.coe_le_coe_iff.mp ((hG0.trans_eq
      (EReal.coe_toReal hmT.ne (h.legendre_ne_bot (hmem T) m)).symm))
    linarith
  by_contra hcon
  rw [not_le] at hcon
  set δ := -C₁ - gm
  have hδ : 0 < δ := by simp only [δ]; linarith
  set T := (|c₀ + Φm| + 1) / δ
  have hTpos : 0 < T := by positivity
  have := hT T hTpos
  have hkey : T * δ = |c₀ + Φm| + 1 := by simp only [T]; field_simp
  have : T * δ ≤ c₀ + Φm := by simp only [δ] at hkey ⊢; nlinarith
  linarith [le_abs_self (c₀ + Φm)]

theorem isProper_rayDifference : IsProper (h.rayDifference φ ℓ) := by
  refine ⟨h.isConvex_rayDifference omega hφt hφ hℓ, ?_, h.rayDifference_ne_bot (φ := φ) (ℓ := ℓ)⟩
  obtain ⟨m, hm⟩ := (h.legendre_isProper (h.rayExt_mem_of_toricRays omega hφ hℓ 1)).2.1
  exact ⟨m, (h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) m).mpr hm⟩

omit hφt hℓ in
/-- `g = cl g'`. -/
def rayLegendre (φ : PolytopeToricVariety γ hs → EReal)
    (ℓ : SourceRayFamily (PolytopeToricVariety γ hs)) : EuclideanSpace ℝ (Fin n) → EReal :=
  convexClosure (h.rayDifference φ ℓ)

theorem isProper_rayLegendre : IsProper (h.rayLegendre φ ℓ) :=
  isProper_convexClosure_of_continuous_minorant (h.isProper_rayDifference omega hφt hφ hℓ) _
    continuous_const (h.le_rayDifference omega hφt hφ hℓ)

theorem closure_dom_rayDifference :
    closure (effectiveDomain (h.rayDifference φ ℓ)) = h.newtonBody φ := by
  have : effectiveDomain (h.rayDifference φ ℓ) = effectiveDomain (h.rayG ℓ 1) := by
    ext m; exact h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) m
  rw [this, ← h.newtonBody_eq_closure_dom (h.rayExt_mem_of_toricRays omega hφ hℓ 1),
    h.newtonBody_rayExt omega hφt hφ hℓ 1]

omit hφt hℓ in
theorem dom_rayLegendre_subset :
    effectiveDomain (h.rayDifference φ ℓ) ⊆ effectiveDomain (h.rayLegendre φ ℓ) ∧
      effectiveDomain (h.rayLegendre φ ℓ) ⊆ closure (effectiveDomain (h.rayDifference φ ℓ)) := by
  constructor
  · intro m hm
    exact (convexClosure_le _ m).trans_lt hm
  · intro m hm
    by_contra hcl
    have := regularization_eq_top_of_not_mem_closure_effectiveDomain hcl
    change h.rayLegendre φ ℓ m < ⊤ at hm
    rw [rayLegendre, convexClosure_of_forall_ne_bot (h.rayDifference_ne_bot (φ := φ) (ℓ := ℓ)),
      this] at hm
    exact lt_irrefl _ hm

theorem rayLegendre_mem : h.rayLegendre φ ℓ ∈ h.rayLegendreClass φ := by
  refine ⟨h.isProper_rayLegendre omega hφt hφ hℓ, lowerSemicontinuous_convexClosure _, ?_⟩
  obtain ⟨h1, h2⟩ := h.dom_rayLegendre_subset (φ := φ) (ℓ := ℓ)
  rw [← h.closure_dom_rayDifference omega hφt hφ hℓ]
  exact le_antisymm (closure_minimal h2 isClosed_closure) (closure_mono h1)

/-- `eq:geod_ray_G`: `G_{ℓ_t} = G_φ + t g` for `t > 0`. -/
theorem legendre_rayExt_eq_rayLegendre {t : ℝ} (ht : 0 < t) :
    h.legendre (sourceRayExtension ℓ t) = h.legendreRaySum (φ := φ) (h.rayLegendre φ ℓ) t := by
  have hmem := h.rayExt_mem_of_toricRays omega hφ hℓ
  have hP := h.nonempty_toricDivisorPolytope_of_mem hφt
  have hcls := h.rayLegendre_mem omega hφt hφ hℓ
  have hsum := h.legendreRaySum_mem hφt hcls ht.le
  have hGt := h.legendre_mem_closedProperOnBody hP (hmem t)
  obtain ⟨hsub1, hsub2⟩ := h.dom_rayLegendre_subset (φ := φ) (ℓ := ℓ)
  have hdomD : effectiveDomain (h.rayDifference φ ℓ) = effectiveDomain (h.rayG ℓ 1) := by
    ext m; exact h.mem_dom_rayDifference_iff (φ := φ) (ℓ := ℓ) m
  -- domains
  have hdomt : effectiveDomain (h.legendre (sourceRayExtension ℓ t)) =
      effectiveDomain (h.rayDifference φ ℓ) := by
    rw [hdomD]; exact h.dom_rayG_eq omega hφt hφ hℓ ht
  have hdomS1 : effectiveDomain (h.rayDifference φ ℓ) ⊆
      effectiveDomain (h.legendreRaySum (φ := φ) (h.rayLegendre φ ℓ) t) := by
    intro m hm
    have h1 : h.legendre φ m < ⊤ := h.dom_rayG_subset omega hφ hℓ m (hdomD ▸ hm)
    have h2 : h.rayLegendre φ ℓ m < ⊤ := hsub1 hm
    change h.legendre φ m + (t : EReal) * h.rayLegendre φ ℓ m < ⊤
    obtain ⟨c, hc⟩ : ∃ c : ℝ, h.rayLegendre φ ℓ m = c :=
      ⟨_, (EReal.coe_toReal h2.ne (hcls.1.2.2 m)).symm⟩
    rw [hc, ← EReal.coe_mul]
    exact EReal.add_lt_top h1.ne (EReal.coe_ne_top _)
  have hdomS2 : effectiveDomain (h.legendreRaySum (φ := φ) (h.rayLegendre φ ℓ) t) ⊆
      closure (effectiveDomain (h.rayDifference φ ℓ)) := by
    intro m hm
    apply hsub2
    change h.legendre φ m + (t : EReal) * h.rayLegendre φ ℓ m < ⊤ at hm
    change h.rayLegendre φ ℓ m < ⊤
    by_contra htop
    rw [not_lt_top_iff.mp htop, EReal.coe_mul_top_of_pos ht,
      EReal.add_top_of_ne_bot (h.legendre_ne_bot hφt m)] at hm
    exact lt_irrefl _ hm
  have hri : intrinsicInterior ℝ (effectiveDomain (h.legendre (sourceRayExtension ℓ t))) =
      intrinsicInterior ℝ (effectiveDomain (h.legendreRaySum (φ := φ) (h.rayLegendre φ ℓ) t)) := by
    apply intrinsicInterior_eq_of_closure_eq (convex_effectiveDomain hGt.1.1)
      (convex_effectiveDomain hsum.1.1)
    rw [hdomt]
    exact le_antisymm (closure_mono hdomS1) (closure_minimal hdomS2 isClosed_closure)
  apply eq_of_isClosedConvex_of_eqOn_intrinsicInterior (Or.inr (Or.inr ⟨hGt.1, hGt.2.1⟩))
    (Or.inr (Or.inr ⟨hsum.1, hsum.2.1⟩)) hri
  intro m hm
  rw [hdomt] at hm
  have hcl : h.rayLegendre φ ℓ m = h.rayDifference φ ℓ m := by
    rw [rayLegendre, convexClosure_of_forall_ne_bot (h.rayDifference_ne_bot (φ := φ) (ℓ := ℓ))]
    exact regularization_eq_of_mem_intrinsicInterior (h.isProper_rayDifference omega hφt hφ hℓ) hm
  rw [h.legendre_rayExt_eq omega hφt hφ hℓ ht.le]
  change _ = h.legendre φ m + (t : EReal) * h.rayLegendre φ ℓ m
  rw [hcl]

end FromRay

/-! ### The bijection -/

/-- Source `cor:geod_tor_char`: for a model potential `φ ∈ PSH_tor(X, θ)` of positive mass, the
canonical bijection between `R_tor(X, θ; φ)` and the proper closed convex functions `g` on `M_ℝ`
with `cl Dom g = Δ(θ, φ)`; it satisfies `G_{ℓ_t} = G_φ + t g` for `t > 0`
(`toricRayEquiv_legendre`). -/
def toricRayEquiv {φ : PolytopeToricVariety γ hs → EReal} (hφt : φ ∈ h.PSHTor)
    (hφ : SourceModelPotential h.atlasForm φ) :
    {ℓ // ℓ ∈ h.toricRays omega φ hφ} ≃ {g // g ∈ h.rayLegendreClass φ} where
  toFun ℓ := ⟨h.rayLegendre φ ℓ.1, h.rayLegendre_mem omega hφt hφ ℓ.2⟩
  invFun g := ⟨h.rayOfLegendre hφt g.2, h.rayOfLegendre_mem_toricRays omega hφt hφ g.2⟩
  left_inv ℓ := by
    apply Subtype.ext
    funext t
    apply h.eq_of_legendre_eq (h.rayOfLegendre_mem hφt (h.rayLegendre_mem omega hφt hφ ℓ.2) t)
      (ℓ.2.2 t)
    rw [legendre_rayOfLegendre]
    rcases (show (0 : ℝ) ≤ t.1 from t.2).eq_or_lt with h0 | hpos
    · have ht0 : t = ⟨0, by simp⟩ := Subtype.ext h0.symm
      rw [ht0, ℓ.2.1.2]
      funext m
      simp [legendreRaySum]
    · have := h.legendre_rayExt_eq_rayLegendre omega hφt hφ ℓ.2 hpos
      rw [sourceRayExtension_nonneg ℓ.1 t.1 t.2] at this
      exact this.symm
  right_inv g := by
    apply Subtype.ext
    set ℓ := h.rayOfLegendre hφt g.2
    have hℓ := h.rayOfLegendre_mem_toricRays omega hφt hφ g.2
    have hcls := h.rayLegendre_mem omega hφt hφ hℓ
    change h.rayLegendre φ ℓ = g.1
    -- `G_φ + g' = G_φ + g`
    have h1 := h.legendre_rayExt_eq_rayLegendre omega hφt hφ hℓ one_pos
    rw [h.legendre_rayExt hφt g.2 zero_le_one] at h1
    have hEqDom : ∀ m ∈ effectiveDomain (h.legendre φ), h.rayLegendre φ ℓ m = g.1 m := by
      intro m hm
      have := congrFun h1 m
      simp only [legendreRaySum, EReal.coe_one, one_mul] at this
      obtain ⟨c, hc⟩ : ∃ c : ℝ, h.legendre φ m = c :=
        ⟨_, (EReal.coe_toReal (ne_of_lt hm) (h.legendre_ne_bot hφt m)).symm⟩
      rw [hc] at this
      exact (EReal.add_left_cancel_coe this).symm
    have hri : intrinsicInterior ℝ (effectiveDomain (h.rayLegendre φ ℓ)) =
        intrinsicInterior ℝ (effectiveDomain g.1) :=
      intrinsicInterior_eq_of_closure_eq (convex_effectiveDomain hcls.1.1)
        (convex_effectiveDomain g.2.1.1) (by rw [hcls.2.2, g.2.2.2])
    apply eq_of_isClosedConvex_of_eqOn_intrinsicInterior (Or.inr (Or.inr ⟨hcls.1, hcls.2.1⟩))
      (Or.inr (Or.inr ⟨g.2.1, g.2.2.1⟩)) hri
    intro m hm
    rw [hri, h.intrinsicInterior_dom_eq hφt g.2] at hm
    exact hEqDom m (intrinsicInterior_subset hm)

/-- `eq:geod_ray_G`: `G_{ℓ_t} = G_φ + t g` for `t > 0`, `g` the image of `ℓ`. -/
theorem toricRayEquiv_legendre {φ : PolytopeToricVariety γ hs → EReal} (hφt : φ ∈ h.PSHTor)
    (hφ : SourceModelPotential h.atlasForm φ) (ℓ : {ℓ // ℓ ∈ h.toricRays omega φ hφ})
    (t : Ici (0 : ℝ)) (ht : 0 < t.1) :
    h.legendre (ℓ.1 t) = fun m =>
      h.legendre φ m + (t.1 : EReal) * (h.toricRayEquiv omega hφt hφ ℓ).1 m := by
  have := h.legendre_rayExt_eq_rayLegendre omega hφt hφ ℓ.2 ht
  rw [sourceRayExtension_nonneg ℓ.1 t.1 t.2] at this
  exact this

end BigToricMetric

end SGPT.Toric

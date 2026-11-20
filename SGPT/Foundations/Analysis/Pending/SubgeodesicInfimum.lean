import SGPT.Foundations.Analysis.FirstPass.SubgeodesicConvexity
import SGPT.Foundations.Analysis.Pending.Subgeodesics
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false

/-!
# The infimum of the slices of a subgeodesic

Xia's Proposition 4.1.2 (`xia-sgpt:page-0149`--`xia-sgpt:page-0150`) makes three
assertions about a subgeodesic `(u_t)_{t in (0,1)}` from `u_0` to `u_1`:

1. `t |-> u_t x` is convex on `[0,1]` for every `x`;
2. `inf_{t in (0,1)} u_t` lies in `PSH(X, theta)`;
3. `inf_{t in (0,1)} u_t <= u_0 /\ u_1`.

Assertion 1 is already in the tree: the interior half is
`FirstPass.IsSubgeodesicInterior.verticalTrace_convexity_dichotomy` and the
boundary inequality, the source's (4.1), is
`FirstPass.IsSubgeodesicFrom.le_eRealChord`.

This module proves assertion 3, and the *nondegeneracy* half of assertion 2.
The other half of assertion 2 -- that the pointwise infimum satisfies the raw
`theta`-PSH criterion -- is Kiselman's minimum principle; it is the one input
this module does not reach and is isolated separately.

Assertion 3 is `iInf_eRealChord_le_min` combined with (4.1): the chord
`t |-> (1-t) u_0 x + t u_1 x` has infimum `min (u_0 x) (u_1 x)` over `(0,1)`,
and the pole conventions of `FirstPass.eRealChord` make the degenerate cases
agree, since the chord is identically `⊥` on `(0,1)` as soon as one endpoint
is `⊥`.

The nondegeneracy argument does not use Kiselman.  A subgeodesic has genuine
`theta`-PSH potentials as its interior slices, so `u_{1/2}` is finite
somewhere; at such a point the vertical-trace dichotomy puts the whole trace
in the finite branch, where it is a real convex function on the bounded
interval `(0,1)` and hence bounded below.  So the infimum is finite there, and
on a connected manifold one finite value gives local nondegeneracy
(`Pending.ThetaPshIdentityPrinciple`).
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicInfimum

open FirstPass

noncomputable section

/-! ### The infimum of an extended-real chord over the open unit interval -/

/-- On the open unit interval an extended-real chord with a pole at either end
is identically `⊥`: both coefficients are strictly positive there. -/
theorem eRealChord_eq_bot_of_endpoint_eq_bot {a b : EReal} (h : a = ⊥ ∨ b = ⊥)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : eRealChord a b t = ⊥ := by
  rcases h with ha | hb
  · rw [ha, eRealChord, mul_comm,
      EReal.bot_mul_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ht.2))]
    exact EReal.bot_add _
  · rw [hb, eRealChord, mul_comm ((t : ℝ) : EReal),
      EReal.bot_mul_of_pos (EReal.coe_pos.mpr ht.1)]
    exact EReal.add_bot _

/-- A finite chord is the coercion of the ordinary real chord. -/
theorem eRealChord_coe_coe (p q t : ℝ) :
    eRealChord (p : EReal) (q : EReal) t = (((1 - t) * p + t * q : ℝ) : EReal) := by
  rw [eRealChord, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]

/-- **The chord infimum.**  Over the open unit interval the infimum of
`t |-> (1-t) a + t b` is `min a b`, for any two extended-real endpoints below
`⊤`.  Only the inequality `<=` is recorded, which is the direction Xia's
Proposition 4.1.2 uses. -/
theorem iInf_eRealChord_le_min {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (⨅ t : ↥(Ioo (0 : ℝ) 1), eRealChord a b (t : ℝ)) ≤ min a b := by
  by_cases hbot : a = ⊥ ∨ b = ⊥
  · refine le_trans (le_of_eq ?_) bot_le
    refine le_antisymm ?_ bot_le
    exact iInf_le_of_le ⟨1 / 2, by norm_num, by norm_num⟩
      (le_of_eq (eRealChord_eq_bot_of_endpoint_eq_bot hbot (by norm_num)))
  rw [not_or] at hbot
  obtain ⟨hab, hbb⟩ := hbot
  obtain ⟨p, hp⟩ : ∃ p : ℝ, a = (p : EReal) := ⟨a.toReal, (EReal.coe_toReal ha hab).symm⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, b = (q : EReal) := ⟨b.toReal, (EReal.coe_toReal hb hbb).symm⟩
  subst hp; subst hq
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by norm_num)
  have hIoo' : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num)
  refine le_min ?_ ?_
  · have hreal : Tendsto (fun t : ℝ => ((1 - t) * p + t * q : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
      have hcont : Continuous fun t : ℝ => ((1 - t) * p + t * q : ℝ) := by fun_prop
      simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have htend : Tendsto (fun t : ℝ => eRealChord (p : EReal) (q : EReal) t)
        (𝓝[>] (0 : ℝ)) (𝓝 ((p : EReal))) := by
      simp only [eRealChord_coe_coe]
      exact EReal.tendsto_coe.mpr hreal
    refine ge_of_tendsto htend ?_
    filter_upwards [hIoo] with t ht
    exact iInf_le_of_le ⟨t, ht⟩ le_rfl
  · have hreal : Tendsto (fun t : ℝ => ((1 - t) * p + t * q : ℝ)) (𝓝[<] (1 : ℝ)) (𝓝 q) := by
      have hcont : Continuous fun t : ℝ => ((1 - t) * p + t * q : ℝ) := by fun_prop
      simpa using (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    have htend : Tendsto (fun t : ℝ => eRealChord (p : EReal) (q : EReal) t)
        (𝓝[<] (1 : ℝ)) (𝓝 ((q : EReal))) := by
      simp only [eRealChord_coe_coe]
      exact EReal.tendsto_coe.mpr hreal
    refine ge_of_tendsto htend ?_
    filter_upwards [hIoo'] with t ht
    exact iInf_le_of_le ⟨t, ht⟩ le_rfl

/-! ### A real convex function on a bounded open interval is bounded below -/

/-- A real convex function on `(0, 1)` is bounded below.  Only one reference
point and the monotonicity of its slope function are used: for `t` on either
side of `1/2`, the slope from `1/2` to `t` is squeezed by the slope from `1/2`
to a fixed point on the far side, and the interval has length at most one. -/
theorem exists_lowerBound_of_convexOn_Ioo {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Ioo (0 : ℝ) 1) g) :
    ∃ C : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, C ≤ g t := by
  have hc : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hp : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hq : (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hmono := hg.slope_mono hc
  refine ⟨g (1 / 2) - |slope g (1 / 2) (3 / 4)| - |slope g (1 / 2) (1 / 4)|, ?_⟩
  intro t ht
  rcases lt_trichotomy t (1 / 2 : ℝ) with hlt | heq | hgt
  · have hne : t - (1 / 2 : ℝ) ≠ 0 := sub_ne_zero.mpr hlt.ne
    have hslope : slope g (1 / 2) t ≤ slope g (1 / 2) (3 / 4) :=
      hmono ⟨ht, by simpa using hlt.ne⟩ ⟨hq, by norm_num⟩ (by linarith)
    have hkey : slope g (1 / 2) t * (t - 1 / 2) = g t - g (1 / 2) := by
      rw [slope_def_field]
      exact div_mul_cancel₀ _ hne
    have hprod : slope g (1 / 2) (3 / 4) * (t - 1 / 2) ≤ g t - g (1 / 2) := by
      rw [← hkey]
      exact mul_le_mul_of_nonpos_right hslope (by linarith)
    have habs : |slope g (1 / 2) (3 / 4) * (t - 1 / 2)| ≤
        |slope g (1 / 2) (3 / 4)| := by
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rw [abs_of_nonpos (by linarith : t - (1 / 2 : ℝ) ≤ 0)]
      linarith [ht.1]
    have h1 := neg_abs_le (slope g (1 / 2) (3 / 4) * (t - 1 / 2))
    have h2 := abs_nonneg (slope g (1 / 2) (1 / 4))
    linarith
  · rw [heq]
    have h1 := abs_nonneg (slope g (1 / 2) (3 / 4))
    have h2 := abs_nonneg (slope g (1 / 2) (1 / 4))
    linarith
  · have hne : t - (1 / 2 : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hgt)
    have hslope : slope g (1 / 2) (1 / 4) ≤ slope g (1 / 2) t :=
      hmono ⟨hp, by norm_num⟩ ⟨ht, by simpa using (ne_of_gt hgt)⟩ (by linarith)
    have hkey : slope g (1 / 2) t * (t - 1 / 2) = g t - g (1 / 2) := by
      rw [slope_def_field]
      exact div_mul_cancel₀ _ hne
    have hprod : slope g (1 / 2) (1 / 4) * (t - 1 / 2) ≤ g t - g (1 / 2) := by
      rw [← hkey]
      exact mul_le_mul_of_nonneg_right hslope (by linarith)
    have habs : |slope g (1 / 2) (1 / 4) * (t - 1 / 2)| ≤
        |slope g (1 / 2) (1 / 4)| := by
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - 1 / 2)]
      linarith [ht.2]
    have h1 := neg_abs_le (slope g (1 / 2) (1 / 4) * (t - 1 / 2))
    have h2 := abs_nonneg (slope g (1 / 2) (3 / 4))
    linarith

/-! ### The slice infimum of a subgeodesic -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The pointwise infimum of the interior slices of a path of potentials,
`inf_{t in (0,1)} u_t` in Xia's Proposition 4.1.2. -/
def sliceInfimum (curve : ℝ → M → EReal) : M → EReal :=
  fun x => ⨅ t : ↥(Ioo (0 : ℝ) 1), curve (t : ℝ) x

/-- **Xia, Proposition 4.1.2, last display (`xia-sgpt:page-0149`).**  The slice
infimum of a subgeodesic lies below both prescribed endpoints, everywhere. -/
theorem sliceInfimum_le_min {theta : SmoothRealForm n M 2}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) (x : M) :
    sliceInfimum curve x ≤ min (u₀ x) (u₁ x) := by
  refine le_trans (iInf_mono fun t => h.le_eRealChord t.2 x) ?_
  exact iInf_eRealChord_le_min
    (h.left_endpoint.1.quasiPlurisubharmonic.ne_top x)
    (h.right_endpoint.1.quasiPlurisubharmonic.ne_top x)

/-- The slice infimum of a subgeodesic lies below the left endpoint. -/
theorem sliceInfimum_le_left {theta : SmoothRealForm n M 2}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) : sliceInfimum curve ≤ u₀ :=
  fun x => (sliceInfimum_le_min h x).trans (min_le_left _ _)

/-- The slice infimum of a subgeodesic lies below the right endpoint. -/
theorem sliceInfimum_le_right {theta : SmoothRealForm n M 2}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : IsSubgeodesicFrom theta curve u₀ u₁) : sliceInfimum curve ≤ u₁ :=
  fun x => (sliceInfimum_le_min h x).trans (min_le_right _ _)

/-- **Nondegeneracy of the slice infimum.**  The interior slices of a
subgeodesic are genuine `theta`-PSH potentials, so `u_{1/2}` is finite at some
point; there the whole vertical trace is finite and convex on `(0,1)`, hence
bounded below, and the infimum is finite.  This is the half of Xia's
`inf_{t in (0,1)} u_t in PSH(X, theta)` which does not need Kiselman's minimum
principle. -/
theorem exists_sliceInfimum_ne_bot [Nonempty M] {theta : SmoothRealForm n M 2}
    {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior theta curve) :
    ∃ x : M, sliceInfimum curve x ≠ ⊥ := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  obtain ⟨y, -, hy⟩ :=
    (h.thetaPshPotential hhalf).2 (Classical.arbitrary M) univ isOpen_univ
      (mem_univ _)
  rcases h.verticalTrace_convexity_dichotomy y with hall | ⟨hfin, hconv⟩
  · exact absurd (hall _ hhalf) hy
  obtain ⟨C, hC⟩ := exists_lowerBound_of_convexOn_Ioo hconv
  refine ⟨y, ?_⟩
  have hle : ((C : ℝ) : EReal) ≤ sliceInfimum curve y := by
    refine le_iInf fun t => ?_
    have ht := (hfin (t : ℝ) t.2)
    rw [← EReal.coe_toReal ht.1 ht.2]
    exact EReal.coe_le_coe_iff.mpr (hC (t : ℝ) t.2)
  intro hbot
  rw [hbot] at hle
  exact (EReal.coe_ne_bot C) (le_bot_iff.mp hle)

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicInfimum

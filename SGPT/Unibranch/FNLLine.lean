import SGPT.Unibranch.FNLCovering
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# FN80 Lemma 5.1: the branched covering over a punctured complex line

Source: `[FN80]` Lemma 5.1, proof: "Let `e` be a unit vector such that
`L = {p + te}` meets `B` in isolated points. [...] We can parametrize each `Y_j` by a germ of
a holomorphic map `A_j(t_j) = (p + t_j^{n_j} e, f_j(t_j))`."

Given a finite branched covering `π : X → D` (`IsBranchedCovering`) and `z₀ ∈ D`:

* `IsBranchedCovering.exists_line`: there is a complex line `τ ↦ z₀ + τ e` whose punctured
  disc `0 < |τ| ≤ ρ` lies in `D ∩ {δ ≠ 0}`;
* `lineTotal`, `lineProj`: the restriction of `X` over that punctured disc, as a space over
  the punctured disc;
* `IsBranchedCovering.isCoveringMap_lineProj`: it is a covering map (closed map with finite
  fibres, local homeomorphism by the local holomorphic graphs).

The lifting of the universal covering `exp` of the punctured disc, the monodromy and the
Puiseux-type parametrization are in `FNLPuiseux`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n k : ℕ}
variable {X : Set (ComplexModel n)} {π : ComplexModel n →L[ℂ] ComplexModel k}
  {D : Set (ComplexModel k)} {deg : ℕ} {δ : ComplexModel k → ℂ}

namespace IsBranchedCovering

variable (hX : IsBranchedCovering X π D deg δ)
include hX

/-- A complex line through `z₀` meeting `{δ = 0}` only at `z₀`, near `z₀`. -/
theorem exists_line {z₀ : ComplexModel k} (hz₀ : z₀ ∈ D) :
    ∃ (e : ComplexModel k) (ρ : ℝ), 0 < ρ ∧ (∀ τ : ℂ, ‖τ‖ ≤ ρ → z₀ + τ • e ∈ D) ∧
      ∀ τ : ℂ, τ ≠ 0 → ‖τ‖ ≤ ρ → δ (z₀ + τ • e) ≠ 0 := by
  obtain ⟨r₀, hr₀, hr₀D⟩ := hX.exists_closedBall_subset hz₀
  obtain ⟨z₁, hδz₁, hz₁⟩ := ((hX.frequently_disc_ne z₀ hz₀).and_eventually
    (ball_mem_nhds z₀ hr₀)).exists
  set e := z₁ - z₀ with hedef
  by_cases he : e = 0
  · have hz : z₁ = z₀ := sub_eq_zero.mp he
    refine ⟨e, 1, one_pos, fun τ _ => ?_, fun τ _ _ => ?_⟩
    · rw [he, smul_zero, add_zero]
      exact hz₀
    · rw [he, smul_zero, add_zero, ← hz]
      exact hδz₁
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he
  have helt : ‖e‖ < r₀ := by
    have := mem_ball.mp hz₁
    rwa [dist_eq_norm] at this
  set R : ℝ := r₀ / ‖e‖ with hRdef
  have hR1 : 1 < R := (one_lt_div hepos).mpr helt
  have hR : 0 < R := by linarith
  have hmaps : ∀ τ ∈ ball (0 : ℂ) R, z₀ + τ • e ∈ ball z₀ r₀ := by
    intro τ hτ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ‖τ‖ < R := mem_ball_zero_iff.mp hτ
    calc ‖τ‖ * ‖e‖ < R * ‖e‖ := mul_lt_mul_of_pos_right h1 hepos
      _ = r₀ := by rw [hRdef]; field_simp
  set h : ℂ → ℂ := fun τ => δ (z₀ + τ • e) with hhdef
  have hd : DifferentiableOn ℂ h (ball (0 : ℂ) R) := by
    have haff : Differentiable ℂ (fun τ : ℂ => z₀ + τ • e) := by fun_prop
    exact hX.differentiableOn_disc.comp haff.differentiableOn
      (fun τ hτ => hr₀D (ball_subset_closedBall (hmaps τ hτ)))
  have han := hd.analyticOnNhd isOpen_ball
  have h1 : h 1 ≠ 0 := by
    simp only [hhdef, one_smul, hedef, add_sub_cancel]
    exact hδz₁
  rcases (han 0 (mem_ball_self hR)).eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · exfalso
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_ball)
      (mem_ball_self hR) hz (show (1 : ℂ) ∈ ball (0 : ℂ) R by
        rw [mem_ball_zero_iff, norm_one]; exact hR1)
    exact h1 this
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hnz
    obtain ⟨ρ₁, hρ₁, hρ₁h⟩ := hnz
    refine ⟨e, min (ρ₁ / 2) (R / 2), by positivity, fun τ hτ => ?_, fun τ hτ0 hτ => ?_⟩
    · apply hr₀D (ball_subset_closedBall (hmaps τ _))
      rw [mem_ball_zero_iff]
      linarith [min_le_right (ρ₁ / 2) (R / 2)]
    · apply hρ₁h _ hτ0
      rw [dist_zero_right]
      linarith [min_le_left (ρ₁ / 2) (R / 2)]

end IsBranchedCovering

/-- The punctured disc `0 < |τ| < ρ`. -/
def punctured (ρ : ℝ) : Set ℂ := {τ | τ ≠ 0 ∧ ‖τ‖ < ρ}

theorem isOpen_punctured (ρ : ℝ) : IsOpen (punctured ρ) := by
  have h : punctured ρ = {τ : ℂ | τ ≠ 0} ∩ ball 0 ρ := by
    ext τ
    simp [punctured]
  rw [h]
  exact isOpen_ne.inter isOpen_ball

/-- The part of `X` over the punctured line `z₀ + τ e`, `0 < |τ| < ρ`, as pairs `(τ, x)`. -/
def lineTotal (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (z₀ e : ComplexModel k) (ρ : ℝ) : Set (ℂ × ComplexModel n) :=
  {q | q.1 ∈ punctured ρ ∧ q.2 ∈ X ∧ π q.2 = z₀ + q.1 • e}

/-- The projection of `lineTotal` to the punctured disc. -/
def lineProj (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (z₀ e : ComplexModel k) (ρ : ℝ) : lineTotal X π z₀ e ρ → punctured ρ :=
  fun q => ⟨q.val.1, q.property.1⟩

theorem continuous_lineProj (z₀ e : ComplexModel k) (ρ : ℝ) :
    Continuous (lineProj X π z₀ e ρ) :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

namespace IsBranchedCovering

variable (hX : IsBranchedCovering X π D deg δ)
include hX

section line

variable {z₀ e : ComplexModel k} {ρ : ℝ}
  (hline : ∀ τ : ℂ, ‖τ‖ ≤ ρ → z₀ + τ • e ∈ D)
  (hgen : ∀ τ : ℂ, τ ≠ 0 → ‖τ‖ ≤ ρ → δ (z₀ + τ • e) ≠ 0)

include hline in
theorem finite_lineProj_fiber (τ : punctured ρ) :
    (lineProj X π z₀ e ρ ⁻¹' {τ}).Finite := by
  have hτD : z₀ + τ.val • e ∈ D := hline τ.val τ.property.2.le
  have hfin := hX.finite_fibre _ hτD
  have hinj : InjOn (fun q : lineTotal X π z₀ e ρ => q.val.2) (lineProj X π z₀ e ρ ⁻¹' {τ}) := by
    intro q hq q' hq' h
    have h1 : q.val.1 = τ.val := congrArg Subtype.val hq
    have h1' : q'.val.1 = τ.val := congrArg Subtype.val hq'
    exact Subtype.ext (Prod.ext (h1.trans h1'.symm) h)
  refine Set.Finite.of_finite_image (hfin.subset ?_) hinj
  rintro _ ⟨q, hq, rfl⟩
  have h1 : q.val.1 = τ.val := congrArg Subtype.val hq
  refine ⟨q.property.2.1, ?_⟩
  change π q.val.2 = z₀ + τ.val • e
  rw [q.property.2.2, h1]

include hline in
theorem isProperMap_lineProj : IsProperMap (lineProj X π z₀ e ρ) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_lineProj z₀ e ρ, fun K hK => ?_⟩
  rw [Subtype.isCompact_iff]
  set K' : Set ℂ := (↑) '' K with hK'def
  have hK'c : IsCompact K' := hK.image continuous_subtype_val
  have hK'P : K' ⊆ punctured ρ := by
    rintro _ ⟨τ, -, rfl⟩
    exact τ.property
  set Λ : ℂ → ComplexModel k := fun τ => z₀ + τ • e with hΛdef
  have hΛc : Continuous Λ := by fun_prop
  have hΛK : Λ '' K' ⊆ D := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hline τ (hK'P hτ).2.le
  have hXc : IsCompact (X ∩ π ⁻¹' (Λ '' K')) :=
    hX.isCompact_inter_preimage _ hΛK (hK'c.image hΛc)
  have hprod : IsCompact (K' ×ˢ (X ∩ π ⁻¹' (Λ '' K'))) := hK'c.prod hXc
  have hclosed : IsClosed {q : ℂ × ComplexModel n | π q.2 = z₀ + q.1 • e} :=
    isClosed_eq (π.continuous.comp continuous_snd) (by fun_prop)
  have heq : (↑) '' (lineProj X π z₀ e ρ ⁻¹' K) =
      (K' ×ˢ (X ∩ π ⁻¹' (Λ '' K'))) ∩ {q : ℂ × ComplexModel n | π q.2 = z₀ + q.1 • e} := by
    ext q
    constructor
    · rintro ⟨q, hqK, rfl⟩
      refine ⟨⟨⟨lineProj X π z₀ e ρ q, hqK, rfl⟩, q.property.2.1, ?_⟩, q.property.2.2⟩
      exact ⟨q.val.1, ⟨lineProj X π z₀ e ρ q, hqK, rfl⟩, q.property.2.2.symm⟩
    · rintro ⟨⟨⟨κ, hκK, hκq⟩, hqX, -⟩, hqπ⟩
      have hq1 : q.1 ∈ punctured ρ := by rw [← hκq]; exact κ.property
      refine ⟨⟨q, hq1, hqX, hqπ⟩, ?_, rfl⟩
      have : lineProj X π z₀ e ρ ⟨q, hq1, hqX, hqπ⟩ = κ := Subtype.ext hκq.symm
      rw [mem_preimage, this]
      exact hκK
  rw [heq]
  exact hprod.inter_right hclosed

include hgen in
theorem isLocalHomeomorph_lineProj : IsLocalHomeomorph (lineProj X π z₀ e ρ) := by
  classical
  apply IsLocalHomeomorph.mk
  intro q₀
  set Λ : ℂ → ComplexModel k := fun τ => z₀ + τ • e with hΛdef
  have hΛc : Continuous Λ := by fun_prop
  have hq₀π : π q₀.val.2 = Λ q₀.val.1 := q₀.property.2.2
  have hδ : δ (π q₀.val.2) ≠ 0 := by
    rw [hq₀π]
    exact hgen _ q₀.property.1.1 q₀.property.1.2.le
  obtain ⟨U, V, g, hU, hV, -, hx₁V, -, hgd, hgX, huniq⟩ :=
    hX.local_graph q₀.val.2 q₀.property.2.1 hδ
  have hUV : IsOpen (U ∩ g ⁻¹' V) := hgd.continuousOn.isOpen_inter_preimage hU hV
  let inv : punctured ρ → lineTotal X π z₀ e ρ := fun τ =>
    if h : Λ τ.val ∈ U then ⟨(τ.val, g (Λ τ.val)), τ.property, (hgX _ h).1, (hgX _ h).2⟩ else q₀
  have hsrc : ∀ q : lineTotal X π z₀ e ρ, q.val.2 ∈ V →
      Λ q.val.1 ∈ U ∧ g (Λ q.val.1) = q.val.2 := by
    intro q hq
    have h := huniq q.val.2 ⟨q.property.2.1, hq⟩
    rw [q.property.2.2] at h
    exact h
  let E₀ : PartialEquiv (lineTotal X π z₀ e ρ) (punctured ρ) :=
    { toFun := lineProj X π z₀ e ρ
      invFun := inv
      source := {q | q.val.2 ∈ V}
      target := {τ | Λ τ.val ∈ U ∧ g (Λ τ.val) ∈ V}
      map_source' := by
        intro q hq
        obtain ⟨h1, h2⟩ := hsrc q hq
        refine ⟨h1, ?_⟩
        change g (Λ q.val.1) ∈ V
        rw [h2]
        exact hq
      map_target' := by
        intro τ hτ
        change (inv τ).val.2 ∈ V
        simp only [inv, dif_pos hτ.1]
        exact hτ.2
      left_inv' := by
        intro q hq
        obtain ⟨h1, h2⟩ := hsrc q hq
        change inv (lineProj X π z₀ e ρ q) = q
        simp only [inv, lineProj, dif_pos h1]
        exact Subtype.ext (Prod.ext rfl h2)
      right_inv' := by
        intro τ hτ
        change lineProj X π z₀ e ρ (inv τ) = τ
        simp only [inv, dif_pos hτ.1]
        rfl }
  have hsrc_open : IsOpen E₀.source :=
    hV.preimage (continuous_snd.comp continuous_subtype_val)
  have htgt_open : IsOpen E₀.target := by
    have : E₀.target = (fun τ : punctured ρ => Λ τ.val) ⁻¹' (U ∩ g ⁻¹' V) := by
      ext τ
      rfl
    rw [this]
    exact hUV.preimage (hΛc.comp continuous_subtype_val)
  refine ⟨{ E₀ with
      open_source := hsrc_open
      open_target := htgt_open
      continuousOn_toFun := (continuous_lineProj z₀ e ρ).continuousOn
      continuousOn_invFun := ?_ }, ?_, fun _ _ => rfl⟩
  · intro τ hτ
    apply ContinuousAt.continuousWithinAt
    rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
    have hgc : ContinuousAt g (Λ τ.val) :=
      (hgd.differentiableAt (hU.mem_nhds hτ.1)).continuousAt
    have hcont : ContinuousAt (fun τ' : punctured ρ => ((τ'.val, g (Λ τ'.val)) : ℂ × ComplexModel n)) τ :=
      continuous_subtype_val.continuousAt.prodMk
        (ContinuousAt.comp (f := fun τ' : punctured ρ => Λ τ'.val) hgc
          (hΛc.comp continuous_subtype_val).continuousAt)
    refine hcont.congr ?_
    have hev : ∀ᶠ τ' : punctured ρ in 𝓝 τ, Λ τ'.val ∈ U :=
      (hU.preimage (hΛc.comp continuous_subtype_val)).mem_nhds hτ.1
    filter_upwards [hev] with τ' hτ'
    change ((τ'.val, g (Λ τ'.val)) : ℂ × ComplexModel n) = (inv τ').val
    simp only [inv, dif_pos hτ']
  · change q₀.val.2 ∈ V
    exact hx₁V

include hline hgen in
theorem isCoveringMap_lineProj : IsCoveringMap (lineProj X π z₀ e ρ) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact (hX.isProperMap_lineProj hline).isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun τ _ => hX.finite_lineProj_fiber hline τ)
    (hX.isLocalHomeomorph_lineProj hgen).isLocalHomeomorphOn

end line

end IsBranchedCovering

end SGPT.Unibranch.FNL

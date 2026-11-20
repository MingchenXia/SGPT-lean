import SGPT.Okounkov.TranscendentalExtensionStatement
import SGPT.Okounkov.TranscendentalExtensionLocal
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Comparison of local extensions (DRWNXZ Lemma 6.2)

Blueprint `tok:ct-key` (package EXT). Source: DRWNXZ, Lemma 6.2; Xia, *Foundations of
pluripotential theory*, proof of `thm:holder-positive-potential-extension`, Step 3.

Let `G₁`, `G₂` be two flattening charts of `Y`, `π₁`, `π₂` their retractions (`retr`), and `q` a
point of `Y` in both. Assume that `e^φ` is `α`-Hölder continuous on `Y`, and let `P` be a
function with `|w|² ≤ C e^P` near `q` in the normal coordinates `w` of `G₁` (the normal pole).
For `0 < 2s < α` the extensions satisfy, for every `η > 0`, near `q`,
`max (φ ∘ π₁, s P) ≤ max (φ ∘ π₂, s P) + η` (`eventually_max_retr_le`).

The proof follows FPT: `|e^{φ(π₁ x)} - e^{φ(π₂ x)}| ≤ C_H |pr Φ₂(π₁ x) - pr Φ₂(x)|^α` by the
Hölder estimate in the chart of `G₂`; the map `Λ = pr ∘ Φ₂ ∘ e₂ ∘ e₁⁻¹ ∘ Φ₁⁻¹` is holomorphic,
hence locally Lipschitz, and `Φ₁(e₁(π₁ x)) - Φ₁(e₁ x) = -w(x)`, so the difference is
`≤ C_H K^α |w|^α`; since `2s < α`, this is `≤ (e^η - 1) |w|^{2s} / C^s ≤ (e^η - 1) e^{s P}` near
`q`. Hence `max(e^{φ∘π₁}, e^{sP}) ≤ e^η max(e^{φ∘π₂}, e^{sP})`.

(DRWNXZ and FPT compare `log(e^{φ∘π} + e^F)`; we use the maximum `max(φ ∘ π, F)`, which satisfies
the same comparison and is `θ`-psh as a maximum, see `TranscendentalExtensionLocal`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff NNReal

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace

/-! ### Exponentials of extended reals -/

theorem exp_ne_top_of_ne_top {a : EReal} (ha : a ≠ ⊤) : EReal.exp a ≠ ⊤ :=
  fun h => ha (EReal.exp_eq_top_iff.mp h)

/-- `e^{max(a,b)} = max(e^a, e^b)`. -/
theorem toReal_exp_max {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (EReal.exp (max a b)).toReal = max (EReal.exp a).toReal (EReal.exp b).toReal := by
  rw [EReal.exp_monotone.map_max,
    ENNReal.toReal_max (exp_ne_top_of_ne_top ha) (exp_ne_top_of_ne_top hb)]

/-- `e^{s a} = (e^a)^s` for `s > 0`. -/
theorem toReal_exp_smul {a : EReal} (ha : a ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    (EReal.exp ((s : EReal) * a)).toReal = (EReal.exp a).toReal ^ s := by
  induction a using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hs, Real.zero_rpow hs.ne']
  | top => exact absurd rfl ha
  | coe r =>
      rw [← EReal.coe_mul, EReal.exp_coe, EReal.exp_coe,
        ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (Real.exp_pos _).le,
        ← Real.exp_mul, mul_comm]

/-- From `e^a ≤ e^η e^b` to `a ≤ b + η`. -/
theorem le_add_of_toReal_exp_le {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) {η : ℝ}
    (h : (EReal.exp a).toReal ≤ Real.exp η * (EReal.exp b).toReal) : a ≤ b + (η : EReal) := by
  rw [← EReal.exp_le_exp_iff, EReal.exp_add, EReal.exp_coe,
    ← ENNReal.ofReal_toReal (exp_ne_top_of_ne_top ha),
    ← ENNReal.ofReal_toReal (exp_ne_top_of_ne_top hb),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact h)

/-- The elementary inequality behind DRWNXZ (6.5): if `|f₁ - f₂| ≤ (e^η - 1) E` then
`max(f₁, E) ≤ e^η max(f₂, E)`. -/
theorem max_le_exp_mul_max {f₁ f₂ E η : ℝ} (hE : 0 ≤ E) (hη : 0 ≤ η)
    (h : |f₁ - f₂| ≤ (Real.exp η - 1) * E) : max f₁ E ≤ Real.exp η * max f₂ E := by
  have he : 1 ≤ Real.exp η := Real.one_le_exp hη
  have hm : 0 ≤ max f₂ E := le_max_of_le_right hE
  have h1 : f₁ ≤ f₂ + (Real.exp η - 1) * E := by
    have := le_abs_self (f₁ - f₂); linarith
  have h2 : f₂ + (Real.exp η - 1) * E ≤ Real.exp η * max f₂ E := by
    have hf : f₂ ≤ max f₂ E := le_max_left _ _
    have hE' : E ≤ max f₂ E := le_max_right _ _
    nlinarith
  refine max_le (h1.trans h2) ?_
  calc E ≤ max f₂ E := le_max_right _ _
    _ ≤ Real.exp η * max f₂ E := le_mul_of_one_le_left hm he

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Set X}

/-! ### The transition of the tangential coordinates -/

/-- `Λ = pr ∘ Φ₂ ∘ e₂ ∘ e₁⁻¹ ∘ Φ₁⁻¹`: the tangential coordinates of `G₂` read in the flattened
coordinates of `G₁`. -/
def tangentialTransition (G₁ G₂ : FlatData n k X Y) (z : ComplexModel n) : ComplexModel k :=
  flatProj G₂ (G₁.amb.val.symm (G₁.flat.symm z))

theorem tangentialTransition_flatCoord (G₁ G₂ : FlatData n k X Y) {x : X}
    (hx : x ∈ G₁.ambSource) : tangentialTransition G₁ G₂ (flatCoord G₁ x) = flatProj G₂ x := by
  rw [tangentialTransition, flatCoord, G₁.flat.left_inv hx.2, G₁.amb.val.left_inv hx.1]

theorem contDiffAt_tangentialTransition (G₁ G₂ : FlatData n k X Y) {q : X}
    (hq₁ : q ∈ G₁.ambSource) (hq₂ : q ∈ G₂.ambSource) :
    ContDiffAt ℂ 1 (tangentialTransition G₁ G₂) (flatCoord G₁ q) := by
  let T := chartTransition G₁.amb G₂.amb
  let U : Set (ComplexModel n) := G₁.flat.target ∩ G₁.flat.symm ⁻¹' (T.source ∩ T ⁻¹' G₂.flat.source)
  have hTs : IsOpen (T.source ∩ T ⁻¹' G₂.flat.source) :=
    T.continuousOn.isOpen_inter_preimage T.open_source G₂.flat.open_source
  have hU : IsOpen U :=
    G₁.flat.continuousOn_symm.isOpen_inter_preimage G₁.flat.open_target hTs
  have hdiff : DifferentiableOn ℂ (tangentialTransition G₁ G₂) U := by
    have h1 : DifferentiableOn ℂ (fun w => coordinateProjection n k (G₂.flat w)) G₂.flat.source :=
      (coordinateProjection n k).differentiable.comp_differentiableOn G₂.differentiableOn_flat
    have h2 : DifferentiableOn ℂ (fun w => coordinateProjection n k (G₂.flat (T w)))
        (T.source ∩ T ⁻¹' G₂.flat.source) :=
      h1.comp ((differentiableOn_chartTransition G₁.amb G₂.amb).mono inter_subset_left)
        fun w hw => hw.2
    exact h2.comp (G₁.differentiableOn_flat_symm.mono inter_subset_left) fun z hz => hz.2
  have hq : flatCoord G₁ q ∈ U := by
    have hs : G₁.flat.symm (flatCoord G₁ q) = G₁.amb.val q := G₁.flat.left_inv hq₁.2
    refine ⟨G₁.flat.map_source hq₁.2, ?_, ?_⟩
    · show G₁.flat.symm (flatCoord G₁ q) ∈ T.source
      rw [hs]
      refine ⟨G₁.amb.val.map_source hq₁.1, ?_⟩
      show G₁.amb.val.symm (G₁.amb.val q) ∈ G₂.amb.val.source
      rw [G₁.amb.val.left_inv hq₁.1]
      exact hq₂.1
    · show T (G₁.flat.symm (flatCoord G₁ q)) ∈ G₂.flat.source
      rw [hs]
      show G₂.amb.val (G₁.amb.val.symm (G₁.amb.val q)) ∈ G₂.flat.source
      rw [G₁.amb.val.left_inv hq₁.1]
      exact hq₂.2
  exact (contDiffAt_of_differentiableOn_complex hdiff hU hq).of_le (by exact_mod_cast le_top)

theorem flatCoord_of_mem (G : FlatData n k X Y) {q : X} (hqY : q ∈ Y) (hq : q ∈ G.ambSource) :
    coordinateInclusion n k (flatProj G q) = flatCoord G q :=
  G.coordinateInclusion_toCoord ⟨q, hqY⟩ hq

theorem normalPart_flatCoord_of_mem (G : FlatData n k X Y) {q : X} (hqY : q ∈ Y)
    (hq : q ∈ G.ambSource) : normalPart n k (flatCoord G q) = 0 := by
  rw [normalPart, ← flatProj, flatCoord_of_mem G hqY hq, sub_self]

theorem continuousAt_flatCoord (G : FlatData n k X Y) {q : X} (hq : q ∈ G.ambSource) :
    ContinuousAt (flatCoord G) q :=
  (continuousOn_flatCoord G).continuousAt (G.isOpen_ambSource.mem_nhds hq)

/-! ### The comparison -/

/-- **Comparison of local extensions** (DRWNXZ Lemma 6.2, blueprint `tok:ct-key`). -/
theorem eventually_max_retr_le (hk : k ≤ n) (hY : ∀ x ∈ Y, RegularAtDim (n := n) Y x k)
    (G₁ G₂ : FlatData n k X Y) {q : X} (hqY : q ∈ Y) (hq₁ : q ∈ G₁.ambSource)
    (hq₂ : q ∈ G₂.ambSource) {φ : Y → EReal} (hφtop : ∀ y, φ y ≠ ⊤) {α : ℝ}
    (hHolder : letI := chartedSpace hk hY
      IsChartHolderWith (k := k) α (expPotential φ))
    {P : X → EReal} (hPtop : ∀ x, P x ≠ ⊤) {CF : ℝ} (hCF : 0 < CF)
    (hlow : ∀ᶠ x in 𝓝 q, ‖normalPart n k (flatCoord G₁ x)‖ ^ 2 ≤ CF * expPotential P x)
    {s : ℝ} (hs : 0 < s) (hsα : 2 * s < α) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x in 𝓝 q, max (φ (retr G₁ x)) ((s : EReal) * P x) ≤
      max (φ (retr G₂ x)) ((s : EReal) * P x) + (η : EReal) := by
  let _ := chartedSpace hk hY
  let q' : Y := ⟨q, hqY⟩
  -- the Hölder estimate in the chart of `G₂`
  obtain ⟨V, hV, -, CH, hCH, hHol⟩ :=
    hHolder (G₂.chart hk) (chart_mem_atlas hk hY G₂) q' (show q' ∈ (G₂.chart hk).source from hq₂)
  -- continuity of the two retractions
  have hr₁ : ContinuousAt (retr G₁) q :=
    (continuousOn_retr G₁).continuousAt
      ((isOpen_retrDomain G₁).mem_nhds (mem_retrDomain_of_mem G₁ hqY hq₁))
  have hr₂ : ContinuousAt (retr G₂) q :=
    (continuousOn_retr G₂).continuousAt
      ((isOpen_retrDomain G₂).mem_nhds (mem_retrDomain_of_mem G₂ hqY hq₂))
  have hV₁ : ∀ᶠ x in 𝓝 q, retr G₁ x ∈ V :=
    hr₁.preimage_mem_nhds (by rw [retr_of_mem hk G₁ hqY hq₁]; exact hV)
  have hV₂ : ∀ᶠ x in 𝓝 q, retr G₂ x ∈ V :=
    hr₂.preimage_mem_nhds (by rw [retr_of_mem hk G₂ hqY hq₂]; exact hV)
  -- the Lipschitz estimate for the tangential transition
  obtain ⟨K, t, ht, hLip⟩ := (contDiffAt_tangentialTransition G₁ G₂ hq₁ hq₂).exists_lipschitzOnWith
  have ht₁ : ∀ᶠ x in 𝓝 q, flatCoord G₁ x ∈ t := (continuousAt_flatCoord G₁ hq₁).preimage_mem_nhds ht
  have ht₂ : ∀ᶠ x in 𝓝 q, coordinateInclusion n k (flatProj G₁ x) ∈ t := by
    have hc : ContinuousAt (fun x => coordinateInclusion n k (flatProj G₁ x)) q :=
      (coordinateInclusion n k).continuous.continuousAt.comp
        ((coordinateProjection n k).continuous.continuousAt.comp (continuousAt_flatCoord G₁ hq₁))
    exact hc.preimage_mem_nhds (by rw [flatCoord_of_mem G₁ hqY hq₁]; exact ht)
  -- the normal coordinate tends to zero
  set D : ℝ := (Real.exp η - 1) / (CF ^ s * (CH * (K : ℝ) ^ α + 1)) with hD
  have hDpos : 0 < D := by
    have : 0 < Real.exp η - 1 := by linarith [Real.add_one_lt_exp hη.ne']
    positivity
  have hsmall : ∀ᶠ x in 𝓝 q, ‖normalPart n k (flatCoord G₁ x)‖ ^ (α - 2 * s) < D := by
    have hc : ContinuousAt (fun x => ‖normalPart n k (flatCoord G₁ x)‖ ^ (α - 2 * s)) q := by
      refine (Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).comp ?_
      exact (continuous_norm.continuousAt.comp
        ((continuous_id.sub ((coordinateInclusion n k).continuous.comp
          (coordinateProjection n k).continuous)).continuousAt.comp
          (continuousAt_flatCoord G₁ hq₁)))
    have h0 : ‖normalPart n k (flatCoord G₁ q)‖ ^ (α - 2 * s) = 0 := by
      rw [normalPart_flatCoord_of_mem G₁ hqY hq₁, norm_zero, Real.zero_rpow (by linarith)]
    exact hc.eventually (gt_mem_nhds (by simp only [h0]; exact hDpos))
  have hdom₁ : ∀ᶠ x in 𝓝 q, x ∈ retrDomain G₁ :=
    (isOpen_retrDomain G₁).mem_nhds (mem_retrDomain_of_mem G₁ hqY hq₁)
  have hdom₂ : ∀ᶠ x in 𝓝 q, x ∈ retrDomain G₂ :=
    (isOpen_retrDomain G₂).mem_nhds (mem_retrDomain_of_mem G₂ hqY hq₂)
  filter_upwards [hV₁, hV₂, ht₁, ht₂, hsmall, hdom₁, hdom₂, hlow] with x hx₁ hx₂ hxt₁ hxt₂ hxs
    hxd₁ hxd₂ hxlow
  set w : ℝ := ‖normalPart n k (flatCoord G₁ x)‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  set f₁ := expPotential φ (retr G₁ x)
  set f₂ := expPotential φ (retr G₂ x)
  set E := expPotential P x
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  -- Hölder
  have h1 : |f₁ - f₂| ≤ CH * ‖G₂.chart hk (retr G₁ x) - G₂.chart hk (retr G₂ x)‖ ^ α :=
    hHol _ hx₁ _ hx₂
  have hc₂ : G₂.chart hk (retr G₂ x) = flatProj G₂ x := (G₂.chart hk).right_inv hxd₂.2
  have hc₁ : G₂.chart hk (retr G₁ x) = tangentialTransition G₁ G₂
      (coordinateInclusion n k (flatProj G₁ x)) := by
    rw [← flatCoord_retr hxd₁, tangentialTransition_flatCoord G₁ G₂ (retr_mem_ambSource hxd₁)]
    rfl
  -- Lipschitz
  have h2 : ‖G₂.chart hk (retr G₁ x) - G₂.chart hk (retr G₂ x)‖ ≤ K * w := by
    rw [hc₁, hc₂, ← tangentialTransition_flatCoord G₁ G₂ hxd₁.1]
    refine (hLip.norm_sub_le hxt₂ hxt₁).trans_eq ?_
    rw [hw, normalPart, norm_sub_rev]
    rfl
  have hα : 0 < α := by linarith
  have h3 : |f₁ - f₂| ≤ CH * ((K : ℝ) ^ α * w ^ α) := by
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCH)
    rw [← Real.mul_rpow K.coe_nonneg hw0]
    exact Real.rpow_le_rpow (norm_nonneg _) h2 hα.le
  -- the pole lower bound
  have hEs : w ^ (2 * s) / CF ^ s ≤ E ^ s := by
    have hw2 : w ^ 2 / CF ≤ E := by rw [div_le_iff₀ hCF, mul_comm]; exact hxlow
    have := Real.rpow_le_rpow (by positivity) hw2 hs.le
    rw [Real.div_rpow (by positivity) hCF.le, ← Real.rpow_natCast, ← Real.rpow_mul hw0] at this
    simpa using this
  have hsplit : w ^ α = w ^ (2 * s) * w ^ (α - 2 * s) := by
    rw [← Real.rpow_add' hw0 (by linarith)]
    ring_nf
  have h4 : |f₁ - f₂| ≤ (Real.exp η - 1) * E ^ s := by
    refine h3.trans ?_
    have hA : 0 ≤ CH * (K : ℝ) ^ α := by positivity
    have hws : 0 ≤ w ^ (2 * s) := by positivity
    have hkey : CH * (K : ℝ) ^ α * D ≤ (Real.exp η - 1) / CF ^ s := by
      rw [hD, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 < Real.exp η - 1 := by linarith [Real.add_one_lt_exp hη.ne']
      have hCFs : 0 < CF ^ s := by positivity
      nlinarith [mul_pos this hCFs]
    calc CH * ((K : ℝ) ^ α * w ^ α)
        = CH * (K : ℝ) ^ α * w ^ (α - 2 * s) * w ^ (2 * s) := by rw [hsplit]; ring
      _ ≤ CH * (K : ℝ) ^ α * D * w ^ (2 * s) := by
          gcongr
      _ ≤ (Real.exp η - 1) / CF ^ s * w ^ (2 * s) := by gcongr
      _ = (Real.exp η - 1) * (w ^ (2 * s) / CF ^ s) := by ring
      _ ≤ (Real.exp η - 1) * E ^ s := by
          gcongr
          linarith [Real.add_one_lt_exp hη.ne']
  have h5 := max_le_exp_mul_max (f₁ := f₁) (f₂ := f₂) (Real.rpow_nonneg hE0 s) hη.le h4
  -- back to extended reals
  have hsP : (s : EReal) * P x ≠ ⊤ := by
    induction h : P x using EReal.rec with
    | bot => rw [EReal.coe_mul_bot_of_pos hs]; exact bot_ne_top
    | top => exact absurd h (hPtop x)
    | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  have hm₁ : max (φ (retr G₁ x)) ((s : EReal) * P x) ≠ ⊤ :=
    (max_lt (lt_top_iff_ne_top.mpr (hφtop _)) (lt_top_iff_ne_top.mpr hsP)).ne
  have hm₂ : max (φ (retr G₂ x)) ((s : EReal) * P x) ≠ ⊤ :=
    (max_lt (lt_top_iff_ne_top.mpr (hφtop _)) (lt_top_iff_ne_top.mpr hsP)).ne
  refine le_add_of_toReal_exp_le hm₁ hm₂ ?_
  rw [toReal_exp_max (hφtop _) hsP, toReal_exp_max (hφtop _) hsP, toReal_exp_smul (hPtop x) hs]
  exact h5

end SGPT.Okounkov.TranscendentalExtension

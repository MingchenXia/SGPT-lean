import SGPT.Foundations.Analysis.Pending.FiniteEnergyCharacterization
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

set_option autoImplicit false

/-!
# Concavity of the Monge–Ampère energy for a bounded model potential

Let `(M, ω)` be a compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form and `φ` a
**bounded** model potential (for instance `θ` Kähler and `φ = V_θ = 0`), and let `E` be Xia's
extended energy (3.30) on `PSH(X, θ; φ)`.

* `relativePSH_convexComb`: `PSH(X, θ; φ)` is convex.
* **Concavity** (`relativeMongeAmpereEnergy_concave`): for `u, v ∈ PSH(X, θ; φ)` and `0 < t < 1`,
  `t E(u) + (1 - t) E(v) ≤ E(t u + (1 - t) v)` in `[-∞, ∞)` (Xia, SGPT, the concavity of the
  energy, for a bounded model potential).
* `relativeFiniteEnergy_convexComb`: the finite-energy class `E^1(X, θ; φ)` is convex.

## The proof

The convex combinations `w_j = t max(u, φ - j) + (1 - t) max(v, φ - j)` are bounded relative
potentials decreasing to `t u + (1 - t) v` (also where `u` or `v` is `-∞`). For bounded potentials
the energy is concave (`BoundedMongeAmpereEnergy.relativeEnergyOfMinimalType_concave`) and
increasing, so `E(w_j) ≥ t E(max(u, φ - j)) + (1 - t) E(max(v, φ - j)) ≥ t E(u) + (1 - t) E(v)`,
and `E(w_j) → E(t u + (1 - t) v)` by decreasing continuity
(`MongeAmpereEnergyDecreasing.relativeMongeAmpereEnergy_tendsto_of_antitone`).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyConcavity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar BoundedGlobalProduct
open RelativeEnergy BoundedMongeAmpereEnergy MongeAmpereEnergyDecreasing
open FiniteEnergyCharacterization ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Convex combinations of bounded and relative potentials -/

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A real-valued function is its own convex combination. -/
theorem convexComb_self_of_bounded {φ : M → EReal} (hφb : IsBoundedPotential φ) (t : ℝ) :
    convexComb t φ φ = φ := by
  funext x
  obtain ⟨p, hp⟩ : ∃ p : ℝ, φ x = p :=
    ⟨(φ x).toReal, (EReal.coe_toReal (hφb.ne_top x) (hφb.ne_bot x)).symm⟩
  rw [convexComb_apply, hp, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  congr 1
  ring

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem convexComb_le {φ u v : M → EReal} (hφb : IsBoundedPotential φ) (huφ : u ≤ φ)
    (hvφ : v ≤ φ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : convexComb t u v ≤ φ :=
  (convexComb_mono ht0 ht1 huφ hvφ).trans_eq (convexComb_self_of_bounded hφb t)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A convex combination of bounded functions is bounded. -/
theorem isBoundedPotential_convexComb {u v : M → EReal} (hub : IsBoundedPotential u)
    (hvb : IsBoundedPotential v) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsBoundedPotential (convexComb t u v) := by
  obtain ⟨a₁, b₁, h₁⟩ := hub
  obtain ⟨a₂, b₂, h₂⟩ := hvb
  have hconst : ∀ p q : ℝ, convexComb t (fun _ : M => (p : EReal)) (fun _ => (q : EReal)) =
      fun _ => ((t * p + (1 - t) * q : ℝ) : EReal) := by
    intro p q
    funext x
    rw [convexComb_apply, EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
  refine ⟨t * a₁ + (1 - t) * a₂, t * b₁ + (1 - t) * b₂, fun x => ⟨?_, ?_⟩⟩
  · have h := convexComb_mono ht0 ht1 (a := fun _ : M => (a₁ : EReal))
      (b := fun _ : M => (a₂ : EReal)) (c := u) (d := v) (fun y => (h₁ y).1) (fun y => (h₂ y).1)
    rw [hconst] at h
    exact h x
  · have h := convexComb_mono ht0 ht1 (a := u) (b := v) (c := fun _ : M => (b₁ : EReal))
      (d := fun _ : M => (b₂ : EReal)) (fun y => (h₁ y).2) (fun y => (h₂ y).2)
    rw [hconst] at h
    exact h x

/-- **`PSH(X, θ; φ)` is convex** for a bounded reference `φ`. -/
theorem relativePSH_convexComb {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hφb : IsBoundedPotential φ) (hu : RelativePSH θ φ u) (hv : RelativePSH θ φ v) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : RelativePSH θ φ (convexComb t u v) :=
  ⟨isThetaPshPotential_convexComb hu.1 hv.1 ht0 ht1, convexComb_le hφb hu.2 hv.2 ht0.le ht1.le⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A positive real multiple of an extended real below `⊤` stays below `⊤`. -/
theorem coe_mul_ne_top {c : ℝ} (hc : 0 ≤ c) {a : EReal} (ha : a ≠ ⊤) : (c : EReal) * a ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top (c * a.toReal))
    ((mul_le_mul_of_nonneg_left (EReal.le_coe_toReal ha) (EReal.coe_nonneg.mpr hc)).trans_eq
      (EReal.coe_mul c a.toReal).symm)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Convex combinations are continuous at pairs of extended reals below `⊤`. -/
theorem tendsto_convexComb {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {f g : ℕ → EReal} {a b : EReal}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    Tendsto (fun j => (t : EReal) * f j + ((1 - t : ℝ) : EReal) * g j) atTop
      (𝓝 ((t : EReal) * a + ((1 - t : ℝ) : EReal) * b)) := by
  have hf' : Tendsto (fun j => (t : EReal) * f j) atTop (𝓝 ((t : EReal) * a)) :=
    EReal.Tendsto.const_mul hf (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t))
  have hg' : Tendsto (fun j => ((1 - t : ℝ) : EReal) * g j) atTop
      (𝓝 (((1 - t : ℝ) : EReal) * b)) :=
    EReal.Tendsto.const_mul hg (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hcont := EReal.continuousAt_add (p := ((t : EReal) * a, ((1 - t : ℝ) : EReal) * b))
    (Or.inl (coe_mul_ne_top ht0.le ha)) (Or.inr (coe_mul_ne_top (by linarith) hb))
  exact hcont.tendsto.comp (hf'.prodMk_nhds hg')

/-! ### Concavity of the extended energy -/

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Concavity of the Monge–Ampère energy** (bounded model potential): for
`u, v ∈ PSH(X, θ; φ)` and `0 < t < 1`, `t E(u) + (1 - t) E(v) ≤ E(t u + (1 - t) v)`, in
`[-∞, ∞)`. -/
theorem relativeMongeAmpereEnergy_concave (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsModelPotential θ φ)
    (hφb : IsBoundedPotential φ) (hu : RelativePSH θ φ u) (hv : RelativePSH θ φ v) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    (t : EReal) * relativeMongeAmpereEnergy θ φ u hφ hu +
        ((1 - t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ v hφ hv ≤
      relativeMongeAmpereEnergy θ φ (convexComb t u v) hφ
        (relativePSH_convexComb hφb hu hv ht0 ht1) := by
  have hφp := hφ.plurisubharmonic
  have hut : ∀ j, RelativePSH θ φ (truncation φ u j) := fun j =>
    ⟨isThetaPshPotential_truncation hφp.1 hu.1.1 hφb hu.2 j, truncation_le hu.2 j⟩
  have hvt : ∀ j, RelativePSH θ φ (truncation φ v j) := fun j =>
    ⟨isThetaPshPotential_truncation hφp.1 hv.1.1 hφb hv.2 j, truncation_le hv.2 j⟩
  set w : ℕ → M → EReal := fun j => convexComb t (truncation φ u j) (truncation φ v j)
    with hw_def
  have hwr : ∀ j, RelativePSH θ φ (w j) := fun j =>
    relativePSH_convexComb hφb (hut j) (hvt j) ht0 ht1
  have hanti : ∀ x, Antitone fun j => w j x := fun x i j hij =>
    convexComb_mono ht0.le ht1.le (fun y => truncation_antitone φ u y hij)
      (fun y => truncation_antitone φ v y hij) x
  have hlim : ∀ x, Tendsto (fun j => w j x) atTop (𝓝 (convexComb t u v x)) := fun x =>
    tendsto_convexComb ht0 ht1 (tendsto_truncation hφb x) (tendsto_truncation hφb x)
      (ne_top_of_le_ne_top (hφb.ne_top x) (hu.2 x)) (ne_top_of_le_ne_top (hφb.ne_top x) (hv.2 x))
  have hT := relativeMongeAmpereEnergy_tendsto_of_antitone omega θ hφ hφb
    (relativePSH_convexComb hφb hu hv ht0 ht1) hwr hanti hlim
  refine ge_of_tendsto' hT fun j => ?_
  have hub := truncation_bounded hφb hu.2 j
  have hvb := truncation_bounded hφb hv.2 j
  have hconc := relativeEnergyOfMinimalType_concave omega θ hφp (hut j).1 (hvt j).1 hφb hub hvb
    ht0 ht1 (hwr j).1
  have hEu : relativeMongeAmpereEnergy θ φ u hφ hu ≤
      (relativeEnergyOfMinimalType θ φ (truncation φ u j) hφp (hut j).1 : EReal) := by
    rw [← relativeMongeAmpereEnergy_eq_of_bounded omega θ hφ (hut j) hφb hub]
    exact relativeMongeAmpereEnergy_mono θ hφ hu (hut j) (le_truncation φ u j)
  have hEv : relativeMongeAmpereEnergy θ φ v hφ hv ≤
      (relativeEnergyOfMinimalType θ φ (truncation φ v j) hφp (hvt j).1 : EReal) := by
    rw [← relativeMongeAmpereEnergy_eq_of_bounded omega θ hφ (hvt j) hφb hvb]
    exact relativeMongeAmpereEnergy_mono θ hφ hv (hvt j) (le_truncation φ v j)
  rw [relativeMongeAmpereEnergy_eq_of_bounded omega θ hφ (hwr j) hφb
    (isBoundedPotential_convexComb hub hvb ht0.le ht1.le)]
  calc (t : EReal) * relativeMongeAmpereEnergy θ φ u hφ hu +
        ((1 - t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ v hφ hv
      ≤ (t : EReal) * (relativeEnergyOfMinimalType θ φ (truncation φ u j) hφp (hut j).1 : EReal) +
        ((1 - t : ℝ) : EReal) *
          (relativeEnergyOfMinimalType θ φ (truncation φ v j) hφp (hvt j).1 : EReal) :=
        add_le_add (mul_le_mul_of_nonneg_left hEu (EReal.coe_nonneg.mpr ht0.le))
          (mul_le_mul_of_nonneg_left hEv (EReal.coe_nonneg.mpr (by linarith)))
    _ = ((t * relativeEnergyOfMinimalType θ φ (truncation φ u j) hφp (hut j).1 +
          (1 - t) * relativeEnergyOfMinimalType θ φ (truncation φ v j) hφp (hvt j).1 : ℝ) :
          EReal) := by
        rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    _ ≤ _ := EReal.coe_le_coe_iff.mpr hconc

/-- **`E^1(X, θ; φ)` is convex** (bounded model potential). -/
theorem relativeFiniteEnergy_convexComb (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsModelPotential θ φ)
    (hφb : IsBoundedPotential φ) (hu : RelativePSH θ φ u) (hv : RelativePSH θ φ v) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hu1 : RelativeFiniteEnergy θ φ u hφ)
    (hv1 : RelativeFiniteEnergy θ φ v hφ) : RelativeFiniteEnergy θ φ (convexComb t u v) hφ := by
  have hw := relativePSH_convexComb hφb hu hv ht0 ht1
  rw [relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb hu] at hu1
  rw [relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb hv] at hv1
  rw [relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb hw]
  refine lt_of_lt_of_le ?_ (relativeMongeAmpereEnergy_concave omega θ hφ hφb hu hv ht0 ht1)
  have hu0 := relativeMongeAmpereEnergy_le_zero θ hφ hu
  have hv0 := relativeMongeAmpereEnergy_le_zero θ hφ hv
  rw [← EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top hu0) hu1.ne',
    ← EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top hv0) hv1.ne',
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  exact EReal.bot_lt_coe _

end SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyConcavity

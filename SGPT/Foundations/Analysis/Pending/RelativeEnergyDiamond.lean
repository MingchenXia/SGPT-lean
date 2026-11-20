import SGPT.Foundations.Analysis.Pending.FiniteEnergyCharacterization
import SGPT.Foundations.Analysis.Pending.MongeAmpereEnergyConcavity
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
import SGPT.Foundations.Analysis.Pending.RooftopContactGeneral
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

set_option autoImplicit false

/-!
# The diamond inequality for the Monge--Ampère energy

Let `(X, ω)` be a compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form and `E = E_θ^φ`
the Monge--Ampère energy relative to a reference `φ`. For two potentials `u`, `v` write
`u ∨ v = max(u, v)` and `u ∧ v = P_θ(min(u, v))` for the rooftop envelope.

* `relativeEnergyOfMinimalType_add_le_max_add_rooftop` — **for bounded `θ`-PSH `φ`, `u`, `v`,
  `E(u) + E(v) ≤ E(u ∨ v) + E(u ∧ v)`** (Xia, SGPT, Corollary 3.1.7, bounded case).
* `relativeMongeAmpereEnergy_add_le_max_add_rooftop` — the same for the extended energy, a bounded
  model potential `φ` and `u, v ∈ E(X, θ; φ)`, in `[-∞, 0]` (Xia's Step 1: decreasing truncations).

Proof of the bounded case. Put `f_t = (1 - t) u + t v`, `A_t = u ∨ f_t` (from `u` to `u ∨ v`) and
`B_t = f_t ∧ v` (from `u ∧ v` to `v`), and `g(t) = ∫ (v - u)⁺ θ_{f_t}^n`. For `s < t` the comparison
inequalities (Xia (3.33)) give
* `E(A_t) - E(A_s) ≥ ∫ (A_t - A_s) θ_{A_t}^n = (t - s) g(t)`: `A_t - A_s = (t - s)(v - u)⁺`, and on
  `{u < v}` the measure of `A_t = max(f_t, u)` is that of `f_t` (plurifine locality of the maximum);
* `E(B_t) - E(B_s) ≤ ∫ (B_t - B_s) θ_{B_s}^n ≤ (t - s) g(s)`: `θ_{B_s}^n` is carried by the two
  contact sets, `B_t - B_s ≤ 0` on `{B_s = v}`, `B_t - B_s ≤ (t - s)(v - u)⁺` on `{B_s = f_s}`, and
  there `θ_{B_s}^n ≤ θ_{f_s}^n`.
Summing over `t_i = i / N`, the two Riemann sums of `g` differ by the telescoping sum
`(g(1) - g(0)) / N`, so `E(u ∨ v) - E(u) - (E(v) - E(u ∧ v)) ≥ (g(1) - g(0)) / N` for every `N`.
Unlike Xia's proof (Lemmas 3.1.10, 3.1.11), no differentiability of the energy along the two paths
and no convergence in capacity is needed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RelativeEnergyDiamond

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar RelativeEnergy
  BoundedMongeAmpereEnergy MongeAmpereEnergyDecreasing FiniteEnergyCharacterization DiagonalMass
  ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### The two paths -/

section Paths

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The real affine path `(1 - t) u + t v` through the real values of `u` and `v`. -/
def path (u v : M → EReal) (t : ℝ) : M → EReal :=
  fun x => (((1 - t) * (u x).toReal + t * (v x).toReal : ℝ) : EReal)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem path_zero {u v : M → EReal} (hub : IsBoundedPotential u) : path u v 0 = u := by
  funext x
  simp only [path, sub_zero, one_mul, zero_mul, add_zero]
  exact EReal.coe_toReal (hub.ne_top x) (hub.ne_bot x)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem path_one {u v : M → EReal} (hvb : IsBoundedPotential v) : path u v 1 = v := by
  funext x
  simp only [path, sub_self, zero_mul, one_mul, zero_add]
  exact EReal.coe_toReal (hvb.ne_top x) (hvb.ne_bot x)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem path_eq_convexComb {u v : M → EReal} (hub : IsBoundedPotential u)
    (hvb : IsBoundedPotential v) (t : ℝ) : path u v t = convexComb (1 - t) u v := by
  funext x
  rw [convexComb_apply, ← EReal.coe_toReal (hub.ne_top x) (hub.ne_bot x),
    ← EReal.coe_toReal (hvb.ne_top x) (hvb.ne_bot x)]
  simp only [path]
  norm_cast
  ring_nf

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem toReal_path (u v : M → EReal) (t : ℝ) (x : M) :
    (path u v t x).toReal = (1 - t) * (u x).toReal + t * (v x).toReal :=
  EReal.toReal_coe _

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem isBoundedPotential_path {u v : M → EReal} (hub : IsBoundedPotential u)
    (hvb : IsBoundedPotential v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsBoundedPotential (path u v t) := by
  obtain ⟨a₁, b₁, h₁⟩ := hub
  obtain ⟨a₂, b₂, h₂⟩ := hvb
  refine ⟨min a₁ a₂, max b₁ b₂, fun x => ⟨?_, ?_⟩⟩
  · have hu1 : a₁ ≤ (u x).toReal := by
      have := (h₁ x).1
      rw [← EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top b₁) (h₁ x).2)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a₁) (h₁ x).1)] at this
      exact_mod_cast this
    have hv1 : a₂ ≤ (v x).toReal := by
      have := (h₂ x).1
      rw [← EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top b₂) (h₂ x).2)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a₂) (h₂ x).1)] at this
      exact_mod_cast this
    simp only [path]
    norm_cast
    have h1 : min a₁ a₂ ≤ (u x).toReal := (min_le_left _ _).trans hu1
    have h2 : min a₁ a₂ ≤ (v x).toReal := (min_le_right _ _).trans hv1
    nlinarith [ht.1, ht.2]
  · have hu1 : (u x).toReal ≤ b₁ := by
      have := (h₁ x).2
      rw [← EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top b₁) (h₁ x).2)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a₁) (h₁ x).1)] at this
      exact_mod_cast this
    have hv1 : (v x).toReal ≤ b₂ := by
      have := (h₂ x).2
      rw [← EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top b₂) (h₂ x).2)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a₂) (h₂ x).1)] at this
      exact_mod_cast this
    simp only [path]
    norm_cast
    have h1 : (u x).toReal ≤ max b₁ b₂ := hu1.trans (le_max_left _ _)
    have h2 : (v x).toReal ≤ max b₁ b₂ := hv1.trans (le_max_right _ _)
    nlinarith [ht.1, ht.2]

theorem isThetaPshPotential_path {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential θ v) (hub : IsBoundedPotential u)
    (hvb : IsBoundedPotential v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsThetaPshPotential θ (path u v t) := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0, path_zero hub]; exact hu
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1, path_one hvb]; exact hv
  rw [path_eq_convexComb hub hvb]
  exact isThetaPshPotential_convexComb hu hv (by linarith) (by linarith)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The upper path `u ∨ f_t`, from `u` to `u ∨ v`. -/
def upperPath (u v : M → EReal) (t : ℝ) : M → EReal := fun x => max (u x) (path u v t x)

/-- The lower path `f_t ∧ v`, from `u ∧ v` to `v`. -/
def lowerPath (θ : SmoothRealForm n M 2) (u v : M → EReal) (t : ℝ) : M → EReal :=
  rooftopEnvelope θ (fun x => min (path u v t x) (v x))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem upperPath_zero {u v : M → EReal} (hub : IsBoundedPotential u) : upperPath u v 0 = u := by
  funext x
  simp only [upperPath, path_zero hub, max_self]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem upperPath_one {u v : M → EReal} (hvb : IsBoundedPotential v) :
    upperPath u v 1 = fun x => max (u x) (v x) := by
  funext x
  simp only [upperPath, path_one hvb]

theorem lowerPath_zero {θ : SmoothRealForm n M 2} {u v : M → EReal} (hub : IsBoundedPotential u) :
    lowerPath θ u v 0 = rooftopEnvelope θ (fun x => min (u x) (v x)) := by
  simp only [lowerPath, path_zero hub]

/-- The rooftop envelope of a `θ`-PSH potential is the potential itself. -/
theorem rooftopEnvelope_self {θ : SmoothRealForm n M 2} {v : M → EReal}
    (hv : IsThetaPshPotential θ v) : rooftopEnvelope θ v = v := by
  refine le_antisymm ?_ (self_le_rooftopEnvelope hv)
  refine (rooftopEnvelope_le_iff hv.1.quasiPlurisubharmonic.upperSemicontinuous).2 ?_
  intro w hw hwv
  exact ThetaPlurisubharmonic.le_of_quasiEverywhere_le hw.1 hv.1 hwv

theorem lowerPath_one {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hv : IsThetaPshPotential θ v) (hvb : IsBoundedPotential v) : lowerPath θ u v 1 = v := by
  have : (fun x => min (path u v 1 x) (v x)) = v := by
    rw [path_one hvb]; funext x; exact min_self (v x)
  rw [lowerPath, this, rooftopEnvelope_self hv]

theorem isThetaPshPotential_upperPath {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential θ v) (hub : IsBoundedPotential u)
    (hvb : IsBoundedPotential v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsThetaPshPotential θ (upperPath u v t) :=
  ⟨ThetaPlurisubharmonic.max hu.1 (isThetaPshPotential_path hu hv hub hvb ht).1,
    hu.2.mono fun _ => le_max_left _ _⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem isBoundedPotential_upperPath {u v : M → EReal} (hub : IsBoundedPotential u)
    (hvb : IsBoundedPotential v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsBoundedPotential (upperPath u v t) := by
  obtain ⟨a₁, b₁, h₁⟩ := hub
  obtain ⟨a₂, b₂, h₂⟩ := isBoundedPotential_path ⟨a₁, b₁, h₁⟩ hvb ht
  exact ⟨a₁, max b₁ b₂, fun x => ⟨(h₁ x).1.trans (le_max_left _ _),
    max_le ((h₁ x).2.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
      ((h₂ x).2.trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _)))⟩⟩

/-- The rooftop `u ∧ v = P_θ(min(u, v))` of two bounded `θ`-PSH potentials is a bounded `θ`-PSH
potential. -/
theorem rooftop_of_bounded [Nonempty M] [CompactSpace M] {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v) :
    IsThetaPshPotential θ.val (rooftopEnvelope θ.val (fun x => min (u x) (v x))) ∧
      IsBoundedPotential (rooftopEnvelope θ.val (fun x => min (u x) (v x))) := by
  have h := relativeEInfinity_rooftop_add_const_of_sameSingularityType θ u u v hu hu hv
    (SameSingularityTypeOn.refl _ univ) (sameSingularityType_of_bounded hvb hub) 0
  have e : (fun x => min (u x) (v x + ((0 : ℝ) : EReal))) = fun x => min (u x) (v x) := by
    funext x; simp
  rw [e] at h
  exact ⟨h.1, isBoundedPotential_of_sameSingularityType hub h.2⟩

theorem relativeEInfinity_lowerPath [Nonempty M] [CompactSpace M] {θ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsThetaPshPotential θ.val (lowerPath θ.val u v t) ∧ IsBoundedPotential (lowerPath θ.val u v t) :=
  rooftop_of_bounded (isThetaPshPotential_path hu hv hub hvb ht) hv
    (isBoundedPotential_path hub hvb ht) hvb

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem coe_toReal_of_bounded {u : M → EReal} (hub : IsBoundedPotential u) (x : M) :
    (((u x).toReal : ℝ) : EReal) = u x :=
  EReal.coe_toReal (hub.ne_top x) (hub.ne_bot x)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The real value of the upper path: `u ∨ f_t = u + t (v - u)⁺`. -/
theorem toReal_upperPath {u v : M → EReal} (hub : IsBoundedPotential u) {t : ℝ} (ht : 0 ≤ t)
    (x : M) : (upperPath u v t x).toReal =
      (u x).toReal + t * max ((v x).toReal - (u x).toReal) 0 := by
  have e : upperPath u v t x =
      ((max (u x).toReal ((1 - t) * (u x).toReal + t * (v x).toReal) : ℝ) : EReal) := by
    rw [EReal.coe_strictMono.monotone.map_max, coe_toReal_of_bounded hub x]
    rfl
  rw [e, EReal.toReal_coe]
  rcases le_total (u x).toReal (v x).toReal with h | h
  · rw [max_eq_right (by nlinarith), max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (by nlinarith), max_eq_right (by linarith)]
    ring

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A bounded potential has bounded real values. -/
theorem exists_abs_toReal_le {u : M → EReal} (hub : IsBoundedPotential u) :
    ∃ C : ℝ, ∀ x, |(u x).toReal| ≤ C := by
  obtain ⟨a, b, hab⟩ := hub
  refine ⟨max |a| |b|, fun x => abs_le.mpr ⟨?_, ?_⟩⟩
  · have h : a ≤ (u x).toReal := by
      have := (hab x).1
      rw [← coe_toReal_of_bounded ⟨a, b, hab⟩ x] at this
      exact_mod_cast this
    linarith [neg_abs_le a, le_max_left |a| |b|]
  · have h : (u x).toReal ≤ b := by
      have := (hab x).2
      rw [← coe_toReal_of_bounded ⟨a, b, hab⟩ x] at this
      exact_mod_cast this
    linarith [le_abs_self b, le_max_right |a| |b|]

end Paths

/-! ### The bounded case -/

section Bounded

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

open Classical in
/-- The diagonal measure `θ_g^n`, and `0` for a function which is not `θ`-PSH. -/
def measureOf (θ : ClosedRealOneOneForm n M) (g : M → EReal) : Measure M :=
  if h : ThetaPlurisubharmonic θ.val g then
    globalMixedMeasure (fun _ : Fin n => θ) (fun _ => g) (fun _ => h) else 0

omit [BorelSpace M] in
theorem measureOf_eq {θ : ClosedRealOneOneForm n M} {g : M → EReal}
    (h : ThetaPlurisubharmonic θ.val g) :
    measureOf θ g = globalMixedMeasure (fun _ : Fin n => θ) (fun _ => g) (fun _ => h) := by
  rw [measureOf, dif_pos h]

open Classical in
/-- The energy (3.29) relative to `φ`, and `0` for a function which is not a `θ`-PSH potential. -/
def energyOf (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsThetaPshPotential θ.val φ)
    (g : M → EReal) : ℝ :=
  if h : IsThetaPshPotential θ.val g then relativeEnergyOfMinimalType θ φ g hφ h else 0

omit [BorelSpace M] in
theorem energyOf_eq {θ : ClosedRealOneOneForm n M} {φ g : M → EReal}
    {hφ : IsThetaPshPotential θ.val φ} (h : IsThetaPshPotential θ.val g) :
    energyOf θ φ hφ g = relativeEnergyOfMinimalType θ φ g hφ h := by
  rw [energyOf, dif_pos h]

/-- `g(t) = ∫ (v - u)⁺ θ_{f_t}^n` along the affine path `f_t = (1 - t) u + t v`. -/
def gap (θ : ClosedRealOneOneForm n M) (u v : M → EReal) (t : ℝ) : ℝ :=
  ∫ x, max ((v x).toReal - (u x).toReal) 0 ∂(measureOf θ (path u v t))

omit [CompactSpace M] in
theorem measurable_posPart_sub {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (hv : ThetaPlurisubharmonic θ v) :
    Measurable fun x => max ((v x).toReal - (u x).toReal) 0 :=
  ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv).ereal_toReal.sub
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu).ereal_toReal).max measurable_const

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem posPart_sub_nonneg (u v : M → EReal) (x : M) :
    0 ≤ max ((v x).toReal - (u x).toReal) 0 := le_max_right _ _

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] in
/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable_of_abs_le {μ : Measure M} [IsFiniteMeasure μ] {f : M → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- **The upper path.** For `0 ≤ s ≤ t ≤ 1`, `t > 0`:
`E(u ∨ f_t) - E(u ∨ f_s) ≥ (t - s) ∫ (v - u)⁺ θ_{f_t}^n`. -/
theorem sub_mul_gap_le_energyOf_upperPath (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφb : IsBoundedPotential φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (t - s) * gap θ u v t ≤
      energyOf θ φ hφ (upperPath u v t) - energyOf θ φ hφ (upperPath u v s) := by
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs, hst.trans ht1⟩
  have hAt := isThetaPshPotential_upperPath hu hv hub hvb htI
  have hAs := isThetaPshPotential_upperPath hu hv hub hvb hsI
  have hf := isThetaPshPotential_path hu hv hub hvb htI
  rw [energyOf_eq hAt, energyOf_eq hAs]
  refine le_trans ?_ (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hAt hAs hφb
    (isBoundedPotential_upperPath hub hvb htI) (isBoundedPotential_upperPath hub hvb hsI)).1
  set h : M → ℝ := fun x => max ((v x).toReal - (u x).toReal) 0 with hh
  have hpt : ∀ x, (upperPath u v t x).toReal - (upperPath u v s x).toReal = (t - s) * h x := by
    intro x
    rw [toReal_upperPath hub ht0.le, toReal_upperPath hub hs]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sub_nonneg.mpr hst)
  -- the two measures agree on `{u < v}`, where `h` lives
  set S : Set M := {x | u x < v x} with hS
  have hSm : MeasurableSet S :=
    measurableSet_lt (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1)
      (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1)
  have hzero : ∀ x, x ∉ S → h x = 0 := by
    intro x hx
    have hvu : v x ≤ u x := not_lt.mp hx
    have : (v x).toReal ≤ (u x).toReal :=
      EReal.toReal_le_toReal hvu (hvb.ne_bot x) (hub.ne_top x)
    simp only [hh]
    exact max_eq_right (by linarith)
  have hmax : ∀ _i : Fin n, ThetaPlurisubharmonic θ.val
      (fun x => max (path u v t x) (u x)) := fun _ =>
    ThetaPlurisubharmonic.max hf.1 hu.1
  have hloc := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq (θ := fun _ => θ)
    (u := fun _ => path u v t) (w := fun _ => u) (fun _ => hf.1) (fun _ => hu.1) hmax
  have hST : S ⊆ {x | ∀ _i : Fin n, u x < path u v t x} := by
    intro x hx _
    have hux : (u x).toReal < (v x).toReal := by
      have h1 : u x < v x := hx
      rw [← coe_toReal_of_bounded hub x, ← coe_toReal_of_bounded hvb x] at h1
      exact_mod_cast h1
    show u x < (((1 - t) * (u x).toReal + t * (v x).toReal : ℝ) : EReal)
    rw [← coe_toReal_of_bounded hub x]
    exact_mod_cast (by nlinarith : (u x).toReal < (1 - t) * (u x).toReal + t * (v x).toReal)
  have hA : globalMixedMeasure (fun _ : Fin n => θ) (fun _ => upperPath u v t) (fun _ => hAt.1) =
      globalMixedMeasure (fun _ : Fin n => θ) (fun _ x => max (path u v t x) (u x)) hmax :=
    BoundedIntegrationByParts.globalMixedMeasure_congr' rfl
      (by funext _ x; exact max_comm _ _) _ _
  have hres : (globalMixedMeasure (fun _ : Fin n => θ) (fun _ => upperPath u v t)
      (fun _ => hAt.1)).restrict S =
      (globalMixedMeasure (fun _ : Fin n => θ) (fun _ => path u v t) (fun _ => hf.1)).restrict S := by
    rw [← Measure.restrict_restrict_of_subset hST, hA, hloc,
      Measure.restrict_restrict_of_subset hST]
  rw [gap, measureOf_eq hf.1, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← hres,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

/-- **The lower path.** For `0 ≤ s ≤ t ≤ 1`:
`E(f_t ∧ v) - E(f_s ∧ v) ≤ (t - s) ∫ (v - u)⁺ θ_{f_s}^n`. -/
theorem energyOf_lowerPath_sub_le [Nonempty M] (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφb : IsBoundedPotential φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    energyOf θ φ hφ (lowerPath θ.val u v t) - energyOf θ φ hφ (lowerPath θ.val u v s) ≤
      (t - s) * gap θ u v s := by
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hst, ht1⟩
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs, hst.trans ht1⟩
  obtain ⟨hBt, hBtb⟩ := relativeEInfinity_lowerPath hu hv hub hvb htI
  obtain ⟨hBs, hBsb⟩ := relativeEInfinity_lowerPath hu hv hub hvb hsI
  have hft := isThetaPshPotential_path hu hv hub hvb htI
  have hfs := isThetaPshPotential_path hu hv hub hvb hsI
  have hftb := isBoundedPotential_path hub hvb htI
  have hfsb := isBoundedPotential_path hub hvb hsI
  rw [energyOf_eq hBt, energyOf_eq hBs]
  refine (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hBt hBs hφb hBtb hBsb).2.trans ?_
  set h : M → ℝ := fun x => max ((v x).toReal - (u x).toReal) 0 with hh
  set C1 : Set M := {x | lowerPath θ.val u v s x = path u v s x} with hC1
  have hC1m : MeasurableSet C1 :=
    measurableSet_eq_fun (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hBs.1)
      (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hfs.1)
  set μB := globalMixedMeasure (fun _ : Fin n => θ) (fun _ => lowerPath θ.val u v s)
    (fun _ => hBs.1) with hμB
  have : IsFiniteMeasure μB := globalMixedMeasure_isFiniteMeasure_of_bounded _ fun _ => hBsb
  set μf := globalMixedMeasure (fun _ : Fin n => θ) (fun _ => path u v s) (fun _ => hfs.1)
    with hμf
  have : IsFiniteMeasure μf := globalMixedMeasure_isFiniteMeasure_of_bounded _ fun _ => hfsb
  have hN : μB {x | lowerPath θ.val u v s x ≠ path u v s x ∧ lowerPath θ.val u v s x ≠ v x} = 0 :=
    RooftopContactGeneral.diagonalPotentialMeasure_rooftopEnvelope_min_noncontact_eq_zero_general
      omega θ hfs hv hBs
  have hobs := RooftopEnvelopeLatticeMass.rooftopEnvelope_min_le θ hft hv
  have hobs' := RooftopEnvelopeLatticeMass.rooftopEnvelope_min_le θ hfs hv
  have hcontact : ∀ᵐ x ∂μB, lowerPath θ.val u v s x ≠ path u v s x →
      lowerPath θ.val u v s x = v x := by
    rw [ae_iff]
    convert hN using 2
    ext x
    simp only [mem_ofPred_eq, Classical.not_imp]
  have hae : ∀ᵐ x ∂μB, (lowerPath θ.val u v t x).toReal - (lowerPath θ.val u v s x).toReal ≤
      (t - s) * C1.indicator h x := by
    filter_upwards [hcontact] with x hx
    have h1 : (lowerPath θ.val u v t x).toReal ≤ (path u v t x).toReal :=
      EReal.toReal_le_toReal (hobs.1 x) (hBtb.ne_bot x) (hftb.ne_top x)
    have h2 : (lowerPath θ.val u v t x).toReal ≤ (v x).toReal :=
      EReal.toReal_le_toReal (hobs.2 x) (hBtb.ne_bot x) (hvb.ne_top x)
    rw [toReal_path] at h1
    by_cases hc : lowerPath θ.val u v s x = path u v s x
    · rw [indicator_of_mem (show x ∈ C1 from hc)]
      have h3 : (lowerPath θ.val u v s x).toReal =
          (1 - s) * (u x).toReal + s * (v x).toReal := by rw [hc, toReal_path]
      simp only [hh]
      rcases le_total (u x).toReal (v x).toReal with huv | huv
      · rw [max_eq_left (by linarith)]; nlinarith
      · rw [max_eq_right (by linarith)]; nlinarith
    · rw [indicator_of_notMem (show x ∉ C1 from hc), mul_zero]
      have h3 : (lowerPath θ.val u v s x).toReal = (v x).toReal := by rw [hx hc]
      linarith
  obtain ⟨Ct, hCt⟩ := exists_abs_toReal_le hBtb
  obtain ⟨Cs, hCs⟩ := exists_abs_toReal_le hBsb
  obtain ⟨Cu, hCu⟩ := exists_abs_toReal_le hub
  obtain ⟨Cv, hCv⟩ := exists_abs_toReal_le hvb
  have hhm : Measurable h := measurable_posPart_sub hu.1 hv.1
  have hhb : ∀ x, |h x| ≤ Cv + Cu := fun x => by
    rw [abs_of_nonneg (posPart_sub_nonneg u v x)]
    refine max_le ?_ (by linarith [(abs_nonneg _).trans (hCu x), (abs_nonneg _).trans (hCv x)])
    linarith [le_abs_self (v x).toReal, neg_abs_le (u x).toReal, hCu x, hCv x]
  have hBint : Integrable (fun x => (lowerPath θ.val u v t x).toReal -
      (lowerPath θ.val u v s x).toReal) μB :=
    integrable_of_abs_le
      ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hBt.1).ereal_toReal.sub
        (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hBs.1).ereal_toReal)
      (C := Ct + Cs) fun x => (abs_sub _ _).trans (add_le_add (hCt x) (hCs x))
  have hIint : Integrable (fun x => (t - s) * C1.indicator h x) μB :=
    ((integrable_of_abs_le hhm hhb).indicator hC1m).const_mul (t - s)
  refine (integral_mono_ae hBint hIint hae).trans ?_
  rw [integral_const_mul, integral_indicator hC1m]
  refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr hst)
  have hle : μB.restrict C1 ≤ μf.restrict C1 := by
    refine Measure.le_iff.2 fun E hE => ?_
    rw [Measure.restrict_apply hE, Measure.restrict_apply hE]
    exact MaxMassDecomposition.contact_measure_le omega hBs hfs hobs'.1 hE
  have hnn : ∀ μ : Measure M, 0 ≤ᵐ[μ] h := fun μ => Eventually.of_forall (posPart_sub_nonneg u v)
  calc ∫ x in C1, h x ∂μB ≤ ∫ x in C1, h x ∂μf :=
        integral_mono_measure hle (hnn _) (integrable_of_abs_le hhm hhb).integrableOn
    _ ≤ ∫ x, h x ∂μf := setIntegral_le_integral (integrable_of_abs_le hhm hhb) (hnn _)
    _ = gap θ u v s := by rw [gap, measureOf_eq hfs.1]

/-- **The diamond inequality for bounded potentials** (Xia, SGPT, Corollary 3.1.7, bounded case):
for bounded `θ`-PSH `φ`, `u`, `v` on a compact Kähler manifold,
`E(u) + E(v) ≤ E(u ∨ v) + E(u ∧ v)`, `E = E_θ^φ` the energy (3.29), `u ∧ v = P_θ(min(u, v))`. -/
theorem relativeEnergyOfMinimalType_add_le_max_add_rooftop [Nonempty M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hφb : IsBoundedPotential φ)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v)
    (hm : IsThetaPshPotential θ.val (fun x => max (u x) (v x)))
    (hw : IsThetaPshPotential θ.val (rooftopEnvelope θ.val (fun x => min (u x) (v x)))) :
    relativeEnergyOfMinimalType θ φ u hφ hu + relativeEnergyOfMinimalType θ φ v hφ hv ≤
      relativeEnergyOfMinimalType θ φ _ hφ hm + relativeEnergyOfMinimalType θ φ _ hφ hw := by
  set Em := relativeEnergyOfMinimalType θ φ _ hφ hm
  set Ew := relativeEnergyOfMinimalType θ φ _ hφ hw
  set Eu := relativeEnergyOfMinimalType θ φ u hφ hu
  set Ev := relativeEnergyOfMinimalType θ φ v hφ hv
  have eA0 : energyOf θ φ hφ (upperPath u v 0) = Eu := by rw [upperPath_zero hub, energyOf_eq hu]
  have eA1 : energyOf θ φ hφ (upperPath u v 1) = Em := by rw [upperPath_one hvb, energyOf_eq hm]
  have eB0 : energyOf θ φ hφ (lowerPath θ.val u v 0) = Ew := by
    rw [lowerPath_zero hub, energyOf_eq hw]
  have eB1 : energyOf θ φ hφ (lowerPath θ.val u v 1) = Ev := by
    rw [lowerPath_one hv hvb, energyOf_eq hv]
  have key : ∀ N : ℕ, 0 < N → (gap θ u v 1 - gap θ u v 0) / N ≤ (Em - Eu) - (Ev - Ew) := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    set a : ℕ → ℝ := fun i => energyOf θ φ hφ (upperPath u v ((i : ℝ) / N)) with ha_def
    set b : ℕ → ℝ := fun i => energyOf θ φ hφ (lowerPath θ.val u v ((i : ℝ) / N)) with hb_def
    set c : ℕ → ℝ := fun i => gap θ u v ((i : ℝ) / N) with hc_def
    have h0 : ((0 : ℕ) : ℝ) / N = 0 := by simp
    have h1 : ((N : ℕ) : ℝ) / N = 1 := div_self hNr.ne'
    have ha : a N - a 0 = Em - Eu := by simp only [ha_def, h0, h1, eA0, eA1]
    have hb : b N - b 0 = Ev - Ew := by simp only [hb_def, h0, h1, eB0, eB1]
    have hc : c N - c 0 = gap θ u v 1 - gap θ u v 0 := by simp only [hc_def, h0, h1]
    have hstep : ∀ i ∈ Finset.range N, ((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N = 1 / N := by
      intro i _
      push_cast
      ring
    have hI : ∀ i ∈ Finset.range N, 0 ≤ (i : ℝ) / N ∧ (i : ℝ) / N ≤ ((i + 1 : ℕ) : ℝ) / N ∧
        0 < ((i + 1 : ℕ) : ℝ) / N ∧ ((i + 1 : ℕ) : ℝ) / N ≤ 1 := by
      intro i hi
      have hiN : i + 1 ≤ N := Finset.mem_range.mp hi
      refine ⟨by positivity, div_le_div_of_nonneg_right (by push_cast; linarith) hNr.le,
        by positivity, (div_le_one hNr).2 (by exact_mod_cast hiN)⟩
    have stepA : ∀ i ∈ Finset.range N, 1 / (N : ℝ) * c (i + 1) ≤ a (i + 1) - a i := by
      intro i hi
      obtain ⟨hs, hst, ht0, ht1⟩ := hI i hi
      have := sub_mul_gap_le_energyOf_upperPath omega θ hφ hφb hu hv hub hvb hs hst ht0 ht1
      rwa [hstep i hi] at this
    have stepB : ∀ i ∈ Finset.range N, b (i + 1) - b i ≤ 1 / (N : ℝ) * c i := by
      intro i hi
      obtain ⟨hs, hst, -, ht1⟩ := hI i hi
      have := energyOf_lowerPath_sub_le omega θ hφ hφb hu hv hub hvb hs hst ht1
      rwa [hstep i hi] at this
    have hsa := Finset.sum_range_sub a N
    have hsb := Finset.sum_range_sub b N
    have hsc := Finset.sum_range_sub c N
    have hA := Finset.sum_le_sum stepA
    have hB := Finset.sum_le_sum stepB
    have hdiff : ∑ i ∈ Finset.range N, 1 / (N : ℝ) * c (i + 1) -
        ∑ i ∈ Finset.range N, 1 / (N : ℝ) * c i = 1 / N * (c N - c 0) := by
      rw [← Finset.sum_sub_distrib, ← hsc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [div_eq_mul_one_div, mul_comm, ← hc, ← hdiff, ← ha, ← hb, ← hsa, ← hsb]
    linarith
  have hlim : Tendsto (fun N : ℕ => (gap θ u v 1 - gap θ u v 0) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h0 : 0 ≤ (Em - Eu) - (Ev - Ew) :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => key N hN⟩)
  linarith

end Bounded

/-! ### A bounded model potential -/

section Model

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
theorem relativeEnergyOfMinimalType_congr {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    {hφ : IsThetaPshPotential θ.val φ} (huv : u = v) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    relativeEnergyOfMinimalType θ φ u hφ hu = relativeEnergyOfMinimalType θ φ v hφ hv := by
  subst huv
  rfl

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem truncation_max (φ u v : M → EReal) (k : ℕ) :
    (fun x => max (truncation φ u k x) (truncation φ v k x)) =
      truncation φ (fun x => max (u x) (v x)) k := by
  funext x
  simp only [truncation]
  exact (sup_sup_distrib_right _ _ _).symm

/-- The sum of two energies converges along sums of convergent sequences in `[-∞, 0]`. -/
theorem tendsto_add_of_ne_top {a b : ℕ → EReal} {A B : EReal} (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    Tendsto (fun k => a k + b k) atTop (𝓝 (A + B)) :=
  (EReal.continuousAt_add (p := (A, B)) (Or.inl hA) (Or.inr hB)).tendsto.comp (ha.prodMk_nhds hb)

/-- **The diamond inequality for the extended energy** (Xia, SGPT, Corollary 3.1.7) for a bounded
model potential `φ`: if `u, v ∈ PSH(X, θ; φ)` and the rooftop `u ∧ v = P_θ(min(u, v))` is a
`θ`-PSH potential, then `E(u) + E(v) ≤ E(u ∨ v) + E(u ∧ v)` in `[-∞, 0]`. -/
theorem relativeMongeAmpereEnergy_add_le_max_add_rooftop [Nonempty M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ) (hu : RelativePSH θ φ u)
    (hv : RelativePSH θ φ v) (hm : RelativePSH θ φ (fun x => max (u x) (v x)))
    (hw : RelativePSH θ φ (rooftopEnvelope θ.val (fun x => min (u x) (v x)))) :
    relativeMongeAmpereEnergy θ φ u hφ hu + relativeMongeAmpereEnergy θ φ v hφ hv ≤
      relativeMongeAmpereEnergy θ φ _ hφ hm + relativeMongeAmpereEnergy θ φ _ hφ hw := by
  have hφp := hφ.plurisubharmonic
  set uC : ℕ → M → EReal := truncation φ u with huC
  set vC : ℕ → M → EReal := truncation φ v with hvC
  have hpu : ∀ k, IsThetaPshPotential θ.val (uC k) := fun k =>
    isThetaPshPotential_truncation hφp.1 hu.1.1 hφb hu.2 k
  have hpv : ∀ k, IsThetaPshPotential θ.val (vC k) := fun k =>
    isThetaPshPotential_truncation hφp.1 hv.1.1 hφb hv.2 k
  have hbu : ∀ k, IsBoundedPotential (uC k) := truncation_bounded hφb hu.2
  have hbv : ∀ k, IsBoundedPotential (vC k) := truncation_bounded hφb hv.2
  set wC : ℕ → M → EReal := fun k => rooftopEnvelope θ.val (fun x => min (uC k x) (vC k x))
    with hwC
  have hpw : ∀ k, IsThetaPshPotential θ.val (wC k) ∧ IsBoundedPotential (wC k) := fun k =>
    rooftop_of_bounded (hpu k) (hpv k) (hbu k) (hbv k)
  have hwle : ∀ k, wC k ≤ uC k ∧ wC k ≤ vC k := fun k =>
    RooftopEnvelopeLatticeMass.rooftopEnvelope_min_le θ (hpu k) (hpv k)
  have hrw : ∀ k, RelativePSH θ φ (wC k) := fun k =>
    ⟨(hpw k).1, (hwle k).1.trans (truncation_le hu.2 k)⟩
  have hpm : ∀ k, IsThetaPshPotential θ.val (fun x => max (uC k x) (vC k x)) := fun k => by
    rw [huC, hvC, truncation_max]
    exact isThetaPshPotential_truncation hφp.1 hm.1.1 hφb hm.2 k
  -- the bounded diamond at every level
  have hk : ∀ k, ((relativeEnergyOfMinimalType θ φ (uC k) hφp (hpu k) +
      relativeEnergyOfMinimalType θ φ (vC k) hφp (hpv k) : ℝ) : EReal) ≤
      ((relativeEnergyOfMinimalType θ φ _ hφp (hpm k) +
        relativeEnergyOfMinimalType θ φ (wC k) hφp (hpw k).1 : ℝ) : EReal) := fun k =>
    EReal.coe_le_coe_iff.mpr (relativeEnergyOfMinimalType_add_le_max_add_rooftop omega θ hφp hφb
      (hpu k) (hpv k) (hbu k) (hbv k) (hpm k) (hpw k).1)
  -- the four limits
  have hTu := tendsto_relativeEnergyOfMinimalType_truncation omega θ hφ hu hφb
  have hTv := tendsto_relativeEnergyOfMinimalType_truncation omega θ hφ hv hφb
  have hTm := tendsto_relativeEnergyOfMinimalType_truncation omega θ hφ hm hφb
  have hTm' : Tendsto (fun k => (relativeEnergyOfMinimalType θ φ _ hφp (hpm k) : EReal)) atTop
      (𝓝 (relativeMongeAmpereEnergy θ φ _ hφ hm)) := by
    refine hTm.congr fun k => ?_
    rw [relativeEnergyOfMinimalType_congr (truncation_max φ u v k).symm]
  -- the rooftops decrease to the rooftop
  have hanti : ∀ x, Antitone fun k => wC k x := fun x i j hij =>
    rooftopEnvelope_mono (fun y => min_le_min (truncation_antitone φ u y hij)
      (truncation_antitone φ v y hij)) x
  have hwk : ∀ k, rooftopEnvelope θ.val (fun x => min (u x) (v x)) ≤ wC k := fun k =>
    rooftopEnvelope_mono fun y => min_le_min (le_truncation φ u k y) (le_truncation φ v k y)
  have hinf : (fun x => ⨅ k, wC k x) = rooftopEnvelope θ.val (fun x => min (u x) (v x)) := by
    refine le_antisymm ?_ fun x => le_iInf fun k => hwk k x
    have hpsh : ThetaPlurisubharmonic θ.val (fun x => ⨅ k, wC k x) :=
      ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone (fun k => (hpw k).1.1) hanti
    have hpot : IsThetaPshPotential θ.val (fun x => ⨅ k, wC k x) :=
      ⟨hpsh, hw.1.2.mono fun x => le_iInf fun k => hwk k x⟩
    refine le_rooftopEnvelope hpot (quasiEverywhere_of_forall fun x => le_min ?_ ?_)
    · exact ge_of_tendsto (tendsto_truncation hφb x)
        (Eventually.of_forall fun k => (iInf_le _ k).trans ((hwle k).1 x))
    · exact ge_of_tendsto (tendsto_truncation hφb x)
        (Eventually.of_forall fun k => (iInf_le _ k).trans ((hwle k).2 x))
  have hlimw : ∀ x, Tendsto (fun k => wC k x) atTop
      (𝓝 (rooftopEnvelope θ.val (fun y => min (u y) (v y)) x)) := fun x => by
    rw [← congrFun hinf x]
    exact tendsto_atTop_iInf (hanti x)
  have hTw := relativeMongeAmpereEnergy_tendsto_of_antitone omega θ hφ hφb hw hrw hanti hlimw
  have hTw' : Tendsto (fun k => (relativeEnergyOfMinimalType θ φ (wC k) hφp (hpw k).1 : EReal))
      atTop (𝓝 (relativeMongeAmpereEnergy θ φ _ hφ hw)) := by
    refine hTw.congr fun k => ?_
    rw [relativeMongeAmpereEnergy_eq_of_bounded omega θ hφ (hrw k) hφb (hpw k).2]
  have hne : ∀ (g : M → EReal) (hg : RelativePSH θ φ g), relativeMongeAmpereEnergy θ φ g hφ hg ≠ ⊤ :=
    fun g hg => ne_top_of_le_ne_top EReal.zero_ne_top (relativeMongeAmpereEnergy_le_zero θ hφ hg)
  have hL := tendsto_add_of_ne_top hTu hTv (hne _ hu) (hne _ hv)
  have hR := tendsto_add_of_ne_top hTm' hTw' (hne _ hm) (hne _ hw)
  refine le_of_tendsto_of_tendsto' hL hR fun k => ?_
  have := hk k
  rwa [EReal.coe_add, EReal.coe_add] at this

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The maximum of two relative potentials is a relative potential. -/
theorem relativePSH_max {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    (hu : RelativePSH θ φ u) (hv : RelativePSH θ φ v) :
    RelativePSH θ φ (fun x => max (u x) (v x)) :=
  ⟨⟨ThetaPlurisubharmonic.max hu.1.1 hv.1.1, hu.1.2.mono fun _ => le_max_left _ _⟩,
    fun x => max_le (hu.2 x) (hv.2 x)⟩

/-- The rooftop of two full-mass potentials is a relative potential (it even has full mass,
`FiniteGeodesicsFullMassAnyDim.relativeFullMass_rooftop`), so the diamond inequality applies to
`E(X, θ; φ)`. -/
theorem relativePSH_rooftop_of_relativeFullMass [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : RelativeFullMass θ φ u hφ) (hv : RelativeFullMass θ φ v hφ) :
    RelativePSH θ φ (rooftopEnvelope θ.val (fun x => min (u x) (v x))) :=
  (FiniteGeodesicsFullMassAnyDim.relativeFullMass_rooftop omega θ φ u v hφ hu hv).1.relativePSH

end Model


end

end SGPT.Foundations.Analysis.Pending.RelativeEnergyDiamond

import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

set_option autoImplicit false

/-!
# Xia's geodesic rays with the singularity-type order `⪯`

Xia (SGPT, Definition 4.2.2, PDF 159) considers geodesic rays in his class `E(X, θ; φ)`, whose
members are `⪯ φ` (Definition 3.1.5), and writes `R(X, θ; φ)` for those emanating from `φ`.
`RelativeGeodesicRays.IsRelativeGeodesicRay` asks the slices to lie in the normalized class
`{η ≤ φ}`; Xia's rays may have `sup_X ℓ_t = C t` with `C > 0` (proof of his Theorem 4.3.4).

* `IsRelativeGeodesicRayPreceq`, `IsFiniteEnergyRayPreceq`, `IsBoundedRayPreceq` (slices in Xia's
  `E`, `E¹`, `E^∞`) and `IsRayFromModel`, `IsFiniteEnergyRayFromModel`, `IsBoundedRayFromModel`
  (Xia's `R`, `R¹`, `R^∞`: moreover `ℓ_0 = φ`).
* `rayShift ℓ A B = (ℓ_t + A t + B)`: affine shifts of rays are rays (`isRelativeGeodesicRayPreceq_rayShift`);
  a `⪯` ray with a linear bound `ℓ_t ≤ φ + A t + B` becomes a normalized ray after the shift by
  `-(A t + B)` (`isRelativeGeodesicRay_rayShift_neg`).
* Bounded model potential: `energy_ray_preceq` (the energy is affine along `⪯` rays),
  `relativeFiniteEnergyPreceq_ray_zero`, `toReal_energy_ray_preceq`, `radialEnergy_eq_preceq` (the radial
  energy, Xia Definition 4.3.6, is the slope), `energy_rayFromModel` (`E(ℓ_t) = t E(ℓ)` on `R¹`),
  `rayD1_eq_radialEnergy_sub_preceq` (Xia (4.38)).
* With a linear bound (`HasLinearBound`; Xia's Proposition 4.2.4 gives it, but that is not
  formalized here): the Darvas distance of rays is unchanged by the common shift
  (`rayD1_rayShift_neg`), `exists_tendsto_rayD1_preceq`, and `rayD1_isMetric_preceq` (Xia Theorem 4.3.4).
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RelativePreceqRays

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar RelativeEnergy
  BoundedMongeAmpereEnergy FiniteEnergyCharacterization DiagonalMass RelativeDarvasDistance
  FiniteGeodesicEnergyAffineE1 RelativeGeodesicRays RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [MeasurableSpace M] [CompactSpace M]

/-! ### Definitions -/

/-- **A geodesic ray in Xia's `E(X, θ; φ)`** (SGPT Definition 4.2.2, with `⪯`): slices in
`E(X, θ; φ)` for `t ≥ 0`, and the restriction to every `[a, b]` is the Perron geodesic. -/
def IsRelativeGeodesicRayPreceq (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) (ℓ : ℝ → M → EReal) : Prop :=
  (∀ t, 0 ≤ t → RelativeFullMassPreceq θ φ (ℓ t) hφ) ∧
    ∀ a b : ℝ, 0 ≤ a → a < b → ∀ s ∈ Ioo (0 : ℝ) 1,
      ℓ (a + s * (b - a)) = finiteGeodesic θ.val (ℓ a) (ℓ b) s

/-- Slices in Xia's `E¹(X, θ; φ)` for `t > 0`. -/
def IsFiniteEnergyRayPreceq (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) (ℓ : ℝ → M → EReal) : Prop :=
  IsRelativeGeodesicRayPreceq θ φ hφ ℓ ∧ ∀ t, 0 < t → RelativeFiniteEnergyPreceq θ φ (ℓ t) hφ

/-- Slices in `E^∞(X, θ; φ)` for `t ≥ 0`. -/
def IsBoundedRayPreceq (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) (ℓ : ℝ → M → EReal) : Prop :=
  IsRelativeGeodesicRayPreceq θ φ hφ ℓ ∧ ∀ t, 0 ≤ t → RelativeEInfinity θ φ (ℓ t)

/-- **Xia's `R(X, θ; φ)`**: geodesic rays in `E(X, θ; φ)` emanating from `φ`. -/
def IsRayFromModel (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (ℓ : ℝ → M → EReal) : Prop :=
  IsRelativeGeodesicRayPreceq θ φ hφ ℓ ∧ ℓ 0 = φ

/-- **Xia's `R¹(X, θ; φ)`**. -/
def IsFiniteEnergyRayFromModel (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) (ℓ : ℝ → M → EReal) : Prop :=
  IsFiniteEnergyRayPreceq θ φ hφ ℓ ∧ ℓ 0 = φ

/-- **Xia's `R^∞(X, θ; φ)`**. -/
def IsBoundedRayFromModel (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) (ℓ : ℝ → M → EReal) : Prop :=
  IsBoundedRayPreceq θ φ hφ ℓ ∧ ℓ 0 = φ

/-- A linear bound `ℓ_t ≤ φ + A t + B` for `t ≥ 0` (Xia's Proposition 4.2.4 and Proposition 3.1.4
give it with `B = 0` for every ray of `R(X, θ; φ)`). -/
def HasLinearBound (φ : M → EReal) (ℓ : ℝ → M → EReal) : Prop :=
  ∃ A B : ℝ, ∀ t, 0 ≤ t → ∀ x, ℓ t x ≤ φ x + ((A * t + B : ℝ) : EReal)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M] in
/-- Two linear bounds can be taken with common constants. -/
theorem HasLinearBound.common {φ : M → EReal} {ℓ ℓ' : ℝ → M → EReal} (h : HasLinearBound φ ℓ)
    (h' : HasLinearBound φ ℓ') : ∃ A B : ℝ, (∀ t, 0 ≤ t → ∀ x, ℓ t x ≤ φ x + ((A * t + B : ℝ) : EReal)) ∧
      ∀ t, 0 ≤ t → ∀ x, ℓ' t x ≤ φ x + ((A * t + B : ℝ) : EReal) := by
  obtain ⟨A, B, hAB⟩ := h
  obtain ⟨A', B', hAB'⟩ := h'
  have key : ∀ (a b : ℝ) (f : ℝ → M → EReal), (∀ t, 0 ≤ t → ∀ x, f t x ≤ φ x + ((a * t + b : ℝ) : EReal)) →
      a ≤ max A A' → b ≤ max B B' →
      ∀ t, 0 ≤ t → ∀ x, f t x ≤ φ x + ((max A A' * t + max B B' : ℝ) : EReal) :=
    fun a b f hf ha hb t ht x => (hf t ht x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2
      (add_le_add (mul_le_mul_of_nonneg_right ha ht) hb)))
  exact ⟨max A A', max B B', key A B ℓ hAB (le_max_left _ _) (le_max_left _ _),
    key A' B' ℓ' hAB' (le_max_right _ _) (le_max_right _ _)⟩

/-- The affine shift `t ↦ ℓ_t + A t + B` of a ray. -/
def rayShift (ℓ : ℝ → M → EReal) (A B : ℝ) : ℝ → M → EReal :=
  fun t x => ℓ t x + ((A * t + B : ℝ) : EReal)

/-! ### Normalized rays, affine shifts -/

section Shift

variable [BorelSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}
  {ℓ : ℝ → M → EReal}

omit [BorelSpace M] in
theorem isRelativeGeodesicRayPreceq_of_isRelativeGeodesicRay
    (h : IsRelativeGeodesicRay θ φ hφ ℓ) : IsRelativeGeodesicRayPreceq θ φ hφ ℓ :=
  ⟨fun t ht => preceq_of_relativeFullMass (h.1 t ht), h.2⟩

omit [BorelSpace M] in
theorem isFiniteEnergyRayPreceq_of_isFiniteEnergyRay (h : IsFiniteEnergyRay θ φ hφ ℓ) :
    IsFiniteEnergyRayPreceq θ φ hφ ℓ :=
  ⟨isRelativeGeodesicRayPreceq_of_isRelativeGeodesicRay h.1,
    fun t ht => preceq_of_relativeFiniteEnergy (h.2 t ht)⟩

omit [BorelSpace M] in
theorem isBoundedRayPreceq_of_isBoundedRay (h : IsBoundedRay θ φ hφ ℓ) :
    IsBoundedRayPreceq θ φ hφ ℓ :=
  ⟨isRelativeGeodesicRayPreceq_of_isRelativeGeodesicRay h.1, h.2⟩

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
/-- The restriction property is preserved by affine shifts. -/
theorem rayShift_geodesic {ℓ : ℝ → M → EReal} {θ' : SmoothRealForm n M 2}
    (h : ∀ a b : ℝ, 0 ≤ a → a < b → ∀ s ∈ Ioo (0 : ℝ) 1,
      ℓ (a + s * (b - a)) = finiteGeodesic θ' (ℓ a) (ℓ b) s) (A B : ℝ) :
    ∀ a b : ℝ, 0 ≤ a → a < b → ∀ s ∈ Ioo (0 : ℝ) 1,
      rayShift ℓ A B (a + s * (b - a)) =
        finiteGeodesic θ' (rayShift ℓ A B a) (rayShift ℓ A B b) s := by
  intro a b ha hab s hs
  have hcov := finiteGeodesic_affineCovariance θ' (ℓ a) (ℓ b) (A * (b - a)) (A * a + B) s
  have eb : A * (b - a) + (A * a + B) = A * b + B := by ring
  rw [eb] at hcov
  show (fun x => ℓ (a + s * (b - a)) x + ((A * (a + s * (b - a)) + B : ℝ) : EReal)) =
    finiteGeodesic θ' (fun x => ℓ a x + ((A * a + B : ℝ) : EReal))
      (fun x => ℓ b x + ((A * b + B : ℝ) : EReal)) s
  rw [hcov, h a b ha hab s hs]
  funext x
  congr 2
  ring

theorem IsRelativeGeodesicRayPreceq.rayShift (h : IsRelativeGeodesicRayPreceq θ φ hφ ℓ) (A B : ℝ) :
    IsRelativeGeodesicRayPreceq θ φ hφ (rayShift ℓ A B) :=
  ⟨fun t ht => (h.1 t ht).add_const (A * t + B), rayShift_geodesic h.2 A B⟩

theorem IsFiniteEnergyRayPreceq.rayShift (omega : KahlerBackground n M)
    (h : IsFiniteEnergyRayPreceq θ φ hφ ℓ) (A B : ℝ) :
    IsFiniteEnergyRayPreceq θ φ hφ (rayShift ℓ A B) :=
  ⟨h.1.rayShift A B, fun t ht => (h.2 t ht).add_const omega (A * t + B)⟩

theorem IsBoundedRayPreceq.rayShift (h : IsBoundedRayPreceq θ φ hφ ℓ) (A B : ℝ) :
    IsBoundedRayPreceq θ φ hφ (rayShift ℓ A B) :=
  ⟨h.1.rayShift A B, fun t ht => RelativeEInfinity.add_const (h.2 t ht) (A * t + B)⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
theorem le_of_rayShift_neg {A B t : ℝ} {x : M} (h : ℓ t x ≤ φ x + ((A * t + B : ℝ) : EReal)) :
    rayShift ℓ (-A) (-B) t x ≤ φ x := by
  show ℓ t x + (((-A) * t + -B : ℝ) : EReal) ≤ φ x
  rw [add_coe_le_iff, show -((-A) * t + -B) = A * t + B by ring]
  exact h

/-- **A `⪯` ray with a linear bound becomes a normalized ray** after the shift by `-(A t + B)`. -/
theorem isRelativeGeodesicRay_rayShift_neg (h : IsRelativeGeodesicRayPreceq θ φ hφ ℓ) {A B : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ℓ t x ≤ φ x + ((A * t + B : ℝ) : EReal)) :
    IsRelativeGeodesicRay θ φ hφ (rayShift ℓ (-A) (-B)) :=
  ⟨fun t ht => (h.1 t ht).relativeFullMass_add fun x => le_of_rayShift_neg (hb t ht x),
    rayShift_geodesic h.2 (-A) (-B)⟩

theorem isFiniteEnergyRay_rayShift_neg (omega : KahlerBackground n M)
    (h : IsFiniteEnergyRayPreceq θ φ hφ ℓ) {A B : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ℓ t x ≤ φ x + ((A * t + B : ℝ) : EReal)) :
    IsFiniteEnergyRay θ φ hφ (rayShift ℓ (-A) (-B)) :=
  ⟨isRelativeGeodesicRay_rayShift_neg h.1 hb, fun t ht =>
    (h.2 t ht).relativeFiniteEnergy_add omega fun x => le_of_rayShift_neg (hb t ht.le x)⟩

theorem isBoundedRay_rayShift_neg (h : IsBoundedRayPreceq θ φ hφ ℓ) {A B : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, ℓ t x ≤ φ x + ((A * t + B : ℝ) : EReal)) :
    IsBoundedRay θ φ hφ (rayShift ℓ (-A) (-B)) :=
  ⟨isRelativeGeodesicRay_rayShift_neg h.1 hb, fun t ht => RelativeEInfinity.add_const (h.2 t ht) _⟩

end Shift

/-! ### The energy along `⪯` rays (bounded model potential) -/

section Energy

variable [BorelSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ} {ℓ : ℝ → M → EReal}

/-- **The energy is affine along `⪯` rays** (bounded model potential), in `[-∞, +∞)`. -/
theorem energy_ray_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hℓ : IsRelativeGeodesicRayPreceq θ φ hφ ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    energy θ φ hφ (ℓ (a + s * (b - a))) =
      ((1 - s : ℝ) : EReal) * energy θ φ hφ (ℓ a) + ((s : ℝ) : EReal) * energy θ φ hφ (ℓ b) := by
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0
    simp only [zero_mul, add_zero, sub_zero, EReal.coe_one, one_mul, EReal.coe_zero, zero_mul]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · subst h1
    simp only [one_mul, add_sub_cancel, sub_self, EReal.coe_zero, zero_mul, EReal.coe_one, zero_add]
  rw [hℓ.2 a b ha hab s ⟨h0, h1⟩]
  exact energy_finiteGeodesic_of_relativeFullMassPreceq omega hφb (hℓ.1 a ha)
    (hℓ.1 b (ha.trans hab.le)) ⟨h0, h1⟩

/-- The initial slice of a `⪯` finite-energy ray has finite energy (bounded model potential). -/
theorem relativeFiniteEnergyPreceq_ray_zero (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) :
    RelativeFiniteEnergyPreceq θ φ (ℓ 0) hφ := by
  refine (relativeFiniteEnergyPreceq_iff_bot_lt_energy omega hφb
    (hℓ.1.1 0 le_rfl).relativePSHPreceq).2 ?_
  by_contra hbot
  rw [not_lt, le_bot_iff] at hbot
  have h := energy_ray_preceq omega hφb hℓ.1 le_rfl zero_lt_one (s := 1 / 2) ⟨by norm_num, by norm_num⟩
  have e : (0 : ℝ) + 1 / 2 * (1 - 0) = 1 / 2 := by norm_num
  rw [e, hbot, EReal.coe_mul_bot_of_pos (by norm_num), EReal.bot_add] at h
  have hb := bot_lt_energy_of_preceq omega hφb (hℓ.2 (1 / 2) (by norm_num))
  rw [h] at hb
  exact lt_irrefl _ hb

theorem relativeFiniteEnergyPreceq_ray (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    RelativeFiniteEnergyPreceq θ φ (ℓ t) hφ := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h]; exact relativeFiniteEnergyPreceq_ray_zero omega hφb hℓ
  · exact hℓ.2 t h

theorem toReal_energy_ray_combination_preceq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (energy θ φ hφ (ℓ (a + s * (b - a)))).toReal =
      (1 - s) * (energy θ φ hφ (ℓ a)).toReal + s * (energy θ φ hφ (ℓ b)).toReal := by
  have h := energy_ray_preceq omega hφb hℓ.1 ha hab hs
  rw [← coe_toReal_energy_of_preceq omega hφb (relativeFiniteEnergyPreceq_ray omega hφb hℓ ha),
    ← coe_toReal_energy_of_preceq omega hφb
      (relativeFiniteEnergyPreceq_ray omega hφb hℓ (ha.trans hab.le)),
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
  rw [h, EReal.toReal_coe]

/-- **The energy is affine along `⪯` finite-energy rays** (bounded model potential):
`E(ℓ_t) = E(ℓ_0) + t (E(ℓ_1) - E(ℓ_0))` for `t ≥ 0`. -/
theorem toReal_energy_ray_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    (energy θ φ hφ (ℓ t)).toReal = (energy θ φ hφ (ℓ 0)).toReal +
      t * ((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal) := by
  rcases le_or_gt t 1 with h1 | h1
  · have h := toReal_energy_ray_combination_preceq omega hφb hℓ le_rfl zero_lt_one (s := t) ⟨ht, h1⟩
    rw [show (0 : ℝ) + t * (1 - 0) = t by ring] at h
    rw [h]; ring
  · have htpos : 0 < t := zero_lt_one.trans h1
    have h := toReal_energy_ray_combination_preceq omega hφb hℓ le_rfl htpos (s := 1 / t)
      ⟨by positivity, (div_le_one htpos).2 h1.le⟩
    rw [show (0 : ℝ) + 1 / t * (t - 0) = 1 by
      rw [sub_zero, zero_add, one_div, inv_mul_cancel₀ htpos.ne']] at h
    rw [h]
    field_simp
    ring

/-- **The radial energy of a `⪯` finite-energy ray** (Xia Definition 4.3.6; bounded model
potential) is the slope `E(ℓ_1) - E(ℓ_0)`; the limit exists. -/
theorem tendsto_radialEnergy_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) :
    Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * energy θ φ hφ (ℓ t)) atTop
      (𝓝 (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal : ℝ) : EReal)) := by
  set e0 := (energy θ φ hφ (ℓ 0)).toReal
  set m := (energy θ φ hφ (ℓ 1)).toReal - e0
  have hlim : Tendsto (fun t : ℝ => t⁻¹ * e0 + m) atTop (𝓝 m) := by
    simpa using (tendsto_inv_atTop_zero.mul_const e0).add_const m
  refine (EReal.tendsto_coe.2 hlim).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← coe_toReal_energy_of_preceq omega hφb (relativeFiniteEnergyPreceq_ray omega hφb hℓ ht.le),
    ← EReal.coe_mul, toReal_energy_ray_preceq omega hφb hℓ ht.le]
  congr 1
  field_simp
  ring

theorem radialEnergy_eq_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ) :
    radialEnergy θ φ hφ ℓ =
      (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal : ℝ) : EReal) :=
  (tendsto_radialEnergy_preceq omega hφb hℓ).limUnder_eq

/-- On Xia's `R¹(X, θ; φ)`, `E(ℓ_t) = t E(ℓ)` (bounded model potential). -/
theorem energy_rayFromModel (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (hℓ : IsFiniteEnergyRayFromModel θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    energy θ φ hφ (ℓ t) = ((t : ℝ) : EReal) * radialEnergy θ φ hφ ℓ := by
  rw [radialEnergy_eq_preceq omega hφb hℓ.1,
    ← coe_toReal_energy_of_preceq omega hφb (relativeFiniteEnergyPreceq_ray omega hφb hℓ.1 ht),
    toReal_energy_ray_preceq omega hφb hℓ.1 ht, hℓ.2, energy_self omega hφb, ← EReal.coe_mul]
  congr 1
  simp

/-- **Xia (4.38) for `⪯` rays** (Proposition 4.3.6; bounded model potential): for finite-energy
rays with `ℓ_t ≤ ℓ'_t` for all `t ≥ 0`, `d₁(ℓ, ℓ') = E(ℓ') - E(ℓ)`. No linear bound is needed. -/
theorem rayD1_eq_radialEnergy_sub_preceq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') (hle : ∀ t, 0 ≤ t → ℓ t ≤ ℓ' t) :
    rayD1 θ φ hφ ℓ ℓ' = radialEnergy θ φ hφ ℓ' - radialEnergy θ φ hφ ℓ := by
  set e0 := (energy θ φ hφ (ℓ 0)).toReal
  set e0' := (energy θ φ hφ (ℓ' 0)).toReal
  set m := (energy θ φ hφ (ℓ 1)).toReal - e0
  set m' := (energy θ φ hφ (ℓ' 1)).toReal - e0'
  have hlim : Tendsto (fun t : ℝ => (e0' - e0) / t + (m' - m)) atTop (𝓝 (m' - m)) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id).add_const (m' - m)
  have hT : Tendsto (fun t => ((relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t : ℝ) : EReal)) atTop
      (𝓝 ((m' - m : ℝ) : EReal)) := by
    refine EReal.tendsto_coe.2 (hlim.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [relativeD1_eq_sub_of_le (relativeFiniteEnergyPreceq_ray omega hφb hℓ ht.le).1.plurisubharmonic
      (hle t ht.le), toReal_energy_ray_preceq omega hφb hℓ' ht.le,
      toReal_energy_ray_preceq omega hφb hℓ ht.le]
    field_simp
    ring
  rw [rayD1, hT.limUnder_eq, radialEnergy_eq_preceq omega hφb hℓ, radialEnergy_eq_preceq omega hφb hℓ',
    ← EReal.coe_sub]

/-! ### The Darvas distance of `⪯` rays with a linear bound -/

/-- `d₁(ℓ_t, ℓ'_t)` is unchanged by a common affine shift (bounded model potential). -/
theorem relativeD1_rayShift (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') (A B : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    relativeD1 θ φ hφ (rayShift ℓ A B t) (rayShift ℓ' A B t) = relativeD1 θ φ hφ (ℓ t) (ℓ' t) :=
  relativeD1_add_const omega hφb (relativeFiniteEnergyPreceq_ray omega hφb hℓ ht)
    (relativeFiniteEnergyPreceq_ray omega hφb hℓ' ht) (A * t + B)

theorem rayD1_rayShift (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') (A B : ℝ) :
    rayD1 θ φ hφ (rayShift ℓ A B) (rayShift ℓ' A B) = rayD1 θ φ hφ ℓ ℓ' := by
  have h : (fun t : ℝ => ((relativeD1 θ φ hφ (rayShift ℓ A B t) (rayShift ℓ' A B t) / t : ℝ) : EReal))
      =ᶠ[atTop] fun t : ℝ => ((relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [relativeD1_rayShift omega hφb hℓ hℓ' A B ht]
  unfold rayD1 limUnder
  rw [Filter.map_congr h]

/-- **Convexity of `d₁` along `⪯` rays with a linear bound** (Xia Proposition 4.3.5; bounded model
potential). -/
theorem convexOn_relativeD1_ray_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') (hb : HasLinearBound φ ℓ)
    (hb' : HasLinearBound φ ℓ') :
    ConvexOn ℝ (Ici 0) fun t => relativeD1 θ φ hφ (ℓ t) (ℓ' t) := by
  obtain ⟨A, B, hA, hA'⟩ := hb.common hb'
  refine (convexOn_relativeD1_ray omega hφb (isFiniteEnergyRay_rayShift_neg omega hℓ hA)
    (isFiniteEnergyRay_rayShift_neg omega hℓ' hA')).congr fun t ht => ?_
  exact relativeD1_rayShift omega hφb hℓ hℓ' (-A) (-B) ht

/-- **The Darvas distance of two `⪯` rays exists and is finite** (Xia Definition 4.3.5; bounded
model potential), for finite-energy rays with a common initial point and linear bounds:
`d₁(ℓ_t, ℓ'_t)/t` increases to a finite `L ≥ 0` and `rayD1 ℓ ℓ' = L`. -/
theorem exists_tendsto_rayD1_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRayPreceq θ φ hφ ℓ)
    (hℓ' : IsFiniteEnergyRayPreceq θ φ hφ ℓ') (hb : HasLinearBound φ ℓ)
    (hb' : HasLinearBound φ ℓ') (h0 : ℓ 0 = ℓ' 0) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun t => relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t) atTop (𝓝 L) ∧
      (∀ t, 0 < t → relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t ≤ L) ∧ rayD1 θ φ hφ ℓ ℓ' = (L : EReal) := by
  obtain ⟨A, B, hA, hA'⟩ := hb.common hb'
  have h0' : rayShift ℓ (-A) (-B) 0 = rayShift ℓ' (-A) (-B) 0 := by
    show (fun x => ℓ 0 x + (((-A) * 0 + -B : ℝ) : EReal)) =
      fun x => ℓ' 0 x + (((-A) * 0 + -B : ℝ) : EReal)
    rw [h0]
  obtain ⟨L, hL0, hT, hle, hL⟩ := exists_tendsto_rayD1 omega hφb
    (isFiniteEnergyRay_rayShift_neg omega hℓ hA) (isFiniteEnergyRay_rayShift_neg omega hℓ' hA') h0'
  refine ⟨L, hL0, hT.congr' ?_, fun t ht => ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [relativeD1_rayShift omega hφb hℓ hℓ' (-A) (-B) ht]
  · rw [← relativeD1_rayShift omega hφb hℓ hℓ' (-A) (-B) ht.le]
    exact hle t ht
  · rw [← rayD1_rayShift omega hφb hℓ hℓ' (-A) (-B)]
    exact hL

/-- **The Darvas metric on `⪯` rays** (Xia Theorem 4.3.4; bounded model potential): on the
finite-energy `⪯` rays with a given initial point `p` and a linear bound, `d₁` is finite,
nonnegative, symmetric, satisfies the triangle inequality, and `d₁(ℓ, ℓ') = 0` forces `ℓ_t = ℓ'_t`
for every `t ≥ 0`. For `p = φ` these are Xia's rays `R¹(X, θ; φ)`, for which his Proposition 4.2.4
gives the linear bound. -/
theorem rayD1_isMetric_preceq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (p : M → EReal) :
    (∀ ℓ ℓ', IsFiniteEnergyRayPreceq θ φ hφ ℓ → IsFiniteEnergyRayPreceq θ φ hφ ℓ' →
      HasLinearBound φ ℓ → HasLinearBound φ ℓ' → ℓ 0 = p → ℓ' 0 = p →
      0 ≤ rayD1 θ φ hφ ℓ ℓ' ∧ rayD1 θ φ hφ ℓ ℓ' < ⊤) ∧
    (∀ ℓ, IsFiniteEnergyRayPreceq θ φ hφ ℓ → HasLinearBound φ ℓ → rayD1 θ φ hφ ℓ ℓ = 0) ∧
    (∀ ℓ ℓ', rayD1 θ φ hφ ℓ ℓ' = rayD1 θ φ hφ ℓ' ℓ) ∧
    (∀ ℓ ℓ' ℓ'', IsFiniteEnergyRayPreceq θ φ hφ ℓ → IsFiniteEnergyRayPreceq θ φ hφ ℓ' →
      IsFiniteEnergyRayPreceq θ φ hφ ℓ'' → HasLinearBound φ ℓ → HasLinearBound φ ℓ' →
      HasLinearBound φ ℓ'' → ℓ 0 = p → ℓ' 0 = p → ℓ'' 0 = p →
      rayD1 θ φ hφ ℓ ℓ'' ≤ rayD1 θ φ hφ ℓ ℓ' + rayD1 θ φ hφ ℓ' ℓ'') ∧
    (∀ ℓ ℓ', IsFiniteEnergyRayPreceq θ φ hφ ℓ → IsFiniteEnergyRayPreceq θ φ hφ ℓ' →
      HasLinearBound φ ℓ → HasLinearBound φ ℓ' → ℓ 0 = p → ℓ' 0 = p →
      rayD1 θ φ hφ ℓ ℓ' = 0 → ∀ t, 0 ≤ t → ℓ t = ℓ' t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ ℓ' hℓ hℓ' hb hb' h0 h0'
    obtain ⟨L, hL0, -, -, hL⟩ := exists_tendsto_rayD1_preceq omega hφb hℓ hℓ' hb hb' (h0.trans h0'.symm)
    rw [hL]
    exact ⟨EReal.coe_nonneg.mpr hL0, EReal.coe_lt_top L⟩
  · intro ℓ hℓ hb
    obtain ⟨L, -, hT, -, hL⟩ := exists_tendsto_rayD1_preceq omega hφb hℓ hℓ hb hb rfl
    have hT0 : Tendsto (fun t => relativeD1 θ φ hφ (ℓ t) (ℓ t) / t) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [relativeD1_self (relativeFiniteEnergyPreceq_ray omega hφb hℓ ht).1.plurisubharmonic,
        zero_div]
    rw [hL, tendsto_nhds_unique hT hT0, EReal.coe_zero]
  · intro ℓ ℓ'
    unfold rayD1
    congr 1
    funext t
    rw [relativeD1_comm]
  · intro ℓ ℓ' ℓ'' hℓ hℓ' hℓ'' hb hb' hb'' h0 h0' h0''
    obtain ⟨L1, -, hT1, -, hL1⟩ :=
      exists_tendsto_rayD1_preceq omega hφb hℓ hℓ'' hb hb'' (h0.trans h0''.symm)
    obtain ⟨L2, -, hT2, -, hL2⟩ :=
      exists_tendsto_rayD1_preceq omega hφb hℓ hℓ' hb hb' (h0.trans h0'.symm)
    obtain ⟨L3, -, hT3, -, hL3⟩ :=
      exists_tendsto_rayD1_preceq omega hφb hℓ' hℓ'' hb' hb'' (h0'.trans h0''.symm)
    rw [hL1, hL2, hL3, ← EReal.coe_add, EReal.coe_le_coe_iff]
    refine le_of_tendsto_of_tendsto hT1 (hT2.add hT3) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← add_div]
    exact div_le_div_of_nonneg_right (relativeD1_triangle_of_preceq omega hφb
      (relativeFiniteEnergyPreceq_ray omega hφb hℓ ht.le)
      (relativeFiniteEnergyPreceq_ray omega hφb hℓ'' ht.le)
      (relativeFiniteEnergyPreceq_ray omega hφb hℓ' ht.le)) ht.le
  · intro ℓ ℓ' hℓ hℓ' hb hb' h0 h0' hzero t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, h0, h0']
    obtain ⟨L, -, -, hle, hL⟩ :=
      exists_tendsto_rayD1_preceq omega hφb hℓ hℓ' hb hb' (h0.trans h0'.symm)
    rw [hL, EReal.coe_eq_zero] at hzero
    have h1 := hle t h
    rw [hzero, div_le_iff₀ h, zero_mul] at h1
    exact eq_of_relativeD1_eq_zero_of_preceq omega hφb (relativeFiniteEnergyPreceq_ray omega hφb hℓ ht)
      (relativeFiniteEnergyPreceq_ray omega hφb hℓ' ht)
      (le_antisymm h1 (relativeD1_nonneg_of_preceq omega hφb
        (relativeFiniteEnergyPreceq_ray omega hφb hℓ ht)
        (relativeFiniteEnergyPreceq_ray omega hφb hℓ' ht)))

end Energy

end

end SGPT.Foundations.Analysis.Pending.RelativePreceqRays

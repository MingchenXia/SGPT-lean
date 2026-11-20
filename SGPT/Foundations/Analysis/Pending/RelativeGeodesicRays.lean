import SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyAffineE1

set_option autoImplicit false

/-!
# Geodesic rays, the radial energy and the Darvas distance of rays (bounded model potential)

Let `(X, ω)` be a connected compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form and `φ` a
model potential.

* `IsRelativeGeodesicRay` (Xia, SGPT, Definition 4.2.2): a family `(ℓ_t)_{t ≥ 0}` in the full-mass
  class `E(X, θ; φ)` whose restriction to every compact interval `[a, b]`, reparametrized to
  `[0, 1]`, is the Perron geodesic from `ℓ_a` to `ℓ_b`; `IsFiniteEnergyRay` (slices in
  `E¹(X, θ; φ)` for `t > 0`) and `IsBoundedRay` (slices in `E^∞(X, θ; φ)`).
* `radialEnergy` (Xia Definition 4.3.6): `E(ℓ) = lim_{t → ∞} t⁻¹ E(ℓ_t)`.
* `rayD1` (Xia Definition 4.3.5): `d₁(ℓ, ℓ') = lim_{t → ∞} t⁻¹ d₁(ℓ_t, ℓ'_t)`.

For a **bounded** model potential `φ`:

* `toReal_energy_ray` — the energy is affine along finite-energy rays,
  `E(ℓ_t) = E(ℓ_0) + t (E(ℓ_1) - E(ℓ_0))` (from `FiniteGeodesicEnergyAffineE1`), and the initial
  slice has finite energy too (`relativeFiniteEnergy_ray_zero`); `radialEnergy_eq`: the radial
  energy is the slope `E(ℓ_1) - E(ℓ_0)`.
* `convexOn_relativeD1_ray` — `t ↦ d₁(ℓ_t, ℓ'_t)` is convex on `[0, ∞)` (Xia Proposition 4.3.5):
  the geodesic between the rooftops `ℓ_a ∧ ℓ'_a` and `ℓ_b ∧ ℓ'_b` lies below the rooftops in between,
  so `t ↦ E(ℓ_t ∧ ℓ'_t)` is concave.
* `exists_tendsto_rayD1` — for rays with the same initial point, `d₁(ℓ_t, ℓ'_t)/t` increases to a
  finite limit (finiteness by the triangle inequality through `φ`, where `d₁(ℓ_t, φ) = -E(ℓ_t)` is
  affine); `rayD1_isMetric`: `d₁` is a metric on the finite-energy rays with a given initial point
  (Xia Theorem 4.3.4).
* `rayD1_eq_radialEnergy_sub` — for ordered finite-energy rays, `d₁(ℓ, ℓ') = E(ℓ') - E(ℓ)`
  (Xia Proposition 4.3.6, (4.38)).
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RelativeGeodesicRays

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar RelativeEnergy
  BoundedMongeAmpereEnergy MongeAmpereEnergyDecreasing FiniteEnergyCharacterization DiagonalMass
  RelativeEnergyDiamond RelativeDarvasDistance FiniteGeodesicEnergyAffineE1

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [MeasurableSpace M] [CompactSpace M]

/-! ### Definitions -/

/-- **A geodesic ray in `E(X, θ; φ)`** (Xia, SGPT, Definition 4.2.2): every slice `ℓ_t`, `t ≥ 0`, lies
in the full-mass class, and for `0 ≤ a < b` the restriction to `[a, b]`, reparametrized to `[0, 1]`,
is the Perron geodesic from `ℓ_a` to `ℓ_b`. -/
def IsRelativeGeodesicRay (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) (ℓ : ℝ → M → EReal) : Prop :=
  (∀ t, 0 ≤ t → RelativeFullMass θ φ (ℓ t) hφ) ∧
    ∀ a b : ℝ, 0 ≤ a → a < b → ∀ s ∈ Ioo (0 : ℝ) 1,
      ℓ (a + s * (b - a)) = finiteGeodesic θ.val (ℓ a) (ℓ b) s

/-- A geodesic ray with finite energy: `ℓ_t ∈ E¹(X, θ; φ)` for `t > 0` (the space `R¹`). -/
def IsFiniteEnergyRay (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (ℓ : ℝ → M → EReal) : Prop :=
  IsRelativeGeodesicRay θ φ hφ ℓ ∧ ∀ t, 0 < t → RelativeFiniteEnergy θ φ (ℓ t) hφ

/-- A bounded geodesic ray: `ℓ_t ∈ E^∞(X, θ; φ)` for `t ≥ 0` (the space `R^∞`). -/
def IsBoundedRay (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (ℓ : ℝ → M → EReal) : Prop :=
  IsRelativeGeodesicRay θ φ hφ ℓ ∧ ∀ t, 0 ≤ t → RelativeEInfinity θ φ (ℓ t)

/-- **The radial energy** (Xia, SGPT, Definition 4.3.6): `E(ℓ) = lim_{t → ∞} t⁻¹ E(ℓ_t)`. -/
def radialEnergy (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (ℓ : ℝ → M → EReal) : EReal :=
  limUnder atTop fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * energy θ φ hφ (ℓ t)

/-- **The Darvas distance of two rays** (Xia, SGPT, Definition 4.3.5):
`d₁(ℓ, ℓ') = lim_{t → ∞} t⁻¹ d₁(ℓ_t, ℓ'_t)`. -/
def rayD1 (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (ℓ ℓ' : ℝ → M → EReal) : EReal :=
  limUnder atTop fun t : ℝ => ((relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t : ℝ) : EReal)

/-! ### The energy along rays -/

section Energy

variable [BorelSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

omit [ConnectedSpace M] in
/-- The energy of the model potential vanishes (bounded model potential). -/
theorem energy_self (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ) :
    energy θ φ hφ φ = 0 := by
  rw [energy_eq (hφ := hφ) ⟨hφ.plurisubharmonic, le_rfl⟩,
    relativeMongeAmpereEnergy_eq_of_bounded omega θ hφ ⟨hφ.plurisubharmonic, le_rfl⟩ hφb hφb,
    relativeEnergyOfMinimalType_self]
  rfl

omit [ConnectedSpace M] in
/-- The model potential has finite energy (bounded model potential). -/
theorem relativeFiniteEnergy_self (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ) :
    RelativeFiniteEnergy θ φ φ hφ :=
  (relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb ⟨hφ.plurisubharmonic, le_rfl⟩).2 (by
    change ⊥ < energy θ φ hφ φ
    rw [energy_self omega hφb]
    exact EReal.bot_lt_zero)

/-- **The energy is affine along geodesic rays** (bounded model potential), in `[-∞, 0]`:
`E(ℓ_{a + s (b - a)}) = (1 - s) E(ℓ_a) + s E(ℓ_b)` for `0 ≤ a < b` and `0 ≤ s ≤ 1`. -/
theorem energy_ray (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsRelativeGeodesicRay θ φ hφ ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    energy θ φ hφ (ℓ (a + s * (b - a))) =
      ((1 - s : ℝ) : EReal) * energy θ φ hφ (ℓ a) + ((s : ℝ) : EReal) * energy θ φ hφ (ℓ b) := by
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0
    simp only [zero_mul, add_zero, sub_zero, EReal.coe_one, one_mul, EReal.coe_zero, zero_mul]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · subst h1
    simp only [one_mul, add_sub_cancel, sub_self, EReal.coe_zero, zero_mul, EReal.coe_one, zero_add]
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have hfa := hℓ.1 a ha
  have hfb := hℓ.1 b (ha.trans hab.le)
  have hsub := FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass
    omega θ φ (ℓ a) (ℓ b) hφ hfa hfb
  have hUt := relativePSH_finiteGeodesic hsub.2.2.1 hfa.relativePSH hfb.relativePSH hsI
  rw [hℓ.2 a b ha hab s hsI, energy_eq hUt, energy_eq hfa.relativePSH, energy_eq hfb.relativePSH]
  exact relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFullMass omega θ hφ hφb hfa hfb
    hfa.relativePSH hfb.relativePSH hsI hUt

/-- The initial slice of a finite-energy ray has finite energy (bounded model potential): if it had
energy `-∞`, so would `ℓ_{1/2}`. -/
theorem relativeFiniteEnergy_ray_zero (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) : RelativeFiniteEnergy θ φ (ℓ 0) hφ := by
  have hr0 := (hℓ.1.1 0 le_rfl).relativePSH
  refine (relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb hr0).2 ?_
  rw [← energy_eq]
  by_contra hbot
  rw [not_lt, le_bot_iff] at hbot
  have h := energy_ray omega hφb hℓ.1 le_rfl zero_lt_one (s := 1 / 2) ⟨by norm_num, by norm_num⟩
  have e : (0 : ℝ) + 1 / 2 * (1 - 0) = 1 / 2 := by norm_num
  rw [e, hbot, EReal.coe_mul_bot_of_pos (by norm_num), EReal.bot_add] at h
  have hb := bot_lt_energy omega hφb (hℓ.2 (1 / 2) (by norm_num))
  rw [h] at hb
  exact lt_irrefl _ hb

theorem relativeFiniteEnergy_ray (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    RelativeFiniteEnergy θ φ (ℓ t) hφ := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h]; exact relativeFiniteEnergy_ray_zero omega hφb hℓ
  · exact hℓ.2 t h

/-- The energy along a finite-energy ray, as a real number. -/
theorem toReal_energy_ray_combination (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (energy θ φ hφ (ℓ (a + s * (b - a)))).toReal =
      (1 - s) * (energy θ φ hφ (ℓ a)).toReal + s * (energy θ φ hφ (ℓ b)).toReal := by
  have h := energy_ray omega hφb hℓ.1 ha hab hs
  have hfa := relativeFiniteEnergy_ray omega hφb hℓ ha
  have hfb := relativeFiniteEnergy_ray omega hφb hℓ (ha.trans hab.le)
  rw [← coe_toReal_energy hfa.1.relativePSH (bot_lt_energy omega hφb hfa),
    ← coe_toReal_energy hfb.1.relativePSH (bot_lt_energy omega hφb hfb), ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_add] at h
  rw [h, EReal.toReal_coe]

/-- **The energy is affine along finite-energy rays** (bounded model potential):
`E(ℓ_t) = E(ℓ_0) + t (E(ℓ_1) - E(ℓ_0))` for `t ≥ 0`. -/
theorem toReal_energy_ray (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    (energy θ φ hφ (ℓ t)).toReal = (energy θ φ hφ (ℓ 0)).toReal +
      t * ((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal) := by
  rcases le_or_gt t 1 with h1 | h1
  · have h := toReal_energy_ray_combination omega hφb hℓ le_rfl zero_lt_one (s := t) ⟨ht, h1⟩
    rw [show (0 : ℝ) + t * (1 - 0) = t by ring] at h
    rw [h]; ring
  · have htpos : 0 < t := zero_lt_one.trans h1
    have h := toReal_energy_ray_combination omega hφb hℓ le_rfl htpos (s := 1 / t)
      ⟨by positivity, (div_le_one htpos).2 h1.le⟩
    rw [show (0 : ℝ) + 1 / t * (t - 0) = 1 by
      rw [sub_zero, zero_add, one_div, inv_mul_cancel₀ htpos.ne']] at h
    rw [h]
    field_simp
    ring

/-- **The radial energy is the slope** of the energy along a finite-energy ray (bounded model
potential): `t⁻¹ E(ℓ_t) → E(ℓ_1) - E(ℓ_0)`. -/
theorem tendsto_radialEnergy (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) :
    Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * energy θ φ hφ (ℓ t)) atTop
      (𝓝 (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal : ℝ) : EReal)) := by
  set e0 := (energy θ φ hφ (ℓ 0)).toReal
  set m := (energy θ φ hφ (ℓ 1)).toReal - e0
  have hlim : Tendsto (fun t : ℝ => t⁻¹ * e0 + m) atTop (𝓝 m) := by
    simpa using (tendsto_inv_atTop_zero.mul_const e0).add_const m
  refine (EReal.tendsto_coe.2 hlim).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hf := relativeFiniteEnergy_ray omega hφb hℓ ht.le
  rw [← coe_toReal_energy hf.1.relativePSH (bot_lt_energy omega hφb hf), ← EReal.coe_mul,
    toReal_energy_ray omega hφb hℓ ht.le]
  congr 1
  field_simp
  ring

theorem radialEnergy_eq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) :
    radialEnergy θ φ hφ ℓ =
      (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal : ℝ) : EReal) :=
  (tendsto_radialEnergy omega hφb hℓ).limUnder_eq

/-- For a ray emanating from the model potential, `E(ℓ_t) = t E(ℓ)` (bounded model potential). -/
theorem energy_ray_of_zero_eq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (h0 : ℓ 0 = φ) {t : ℝ} (ht : 0 ≤ t) :
    energy θ φ hφ (ℓ t) = ((t : ℝ) : EReal) * radialEnergy θ φ hφ ℓ := by
  have hf := relativeFiniteEnergy_ray omega hφb hℓ ht
  rw [radialEnergy_eq omega hφb hℓ, ← coe_toReal_energy hf.1.relativePSH (bot_lt_energy omega hφb hf),
    toReal_energy_ray omega hφb hℓ ht, h0, energy_self omega hφb, ← EReal.coe_mul]
  congr 1
  simp

end Energy

/-! ### `d₁` along pairs of rays -/

section Distance

variable [BorelSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- **The energy of the rooftops is concave along two finite-energy rays** (bounded model
potential): the geodesic between `ℓ_a ∧ ℓ'_a` and `ℓ_b ∧ ℓ'_b` lies below `ℓ_c ∧ ℓ'_c`. -/
theorem toReal_energy_rooftop_ray_concave (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ')
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (1 - s) * (energy θ φ hφ (rooftop θ (ℓ a) (ℓ' a))).toReal +
        s * (energy θ φ hφ (rooftop θ (ℓ b) (ℓ' b))).toReal ≤
      (energy θ φ hφ (rooftop θ (ℓ (a + s * (b - a))) (ℓ' (a + s * (b - a))))).toReal := by
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst h0; simp
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · subst h1; simp
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  have hb0 : 0 ≤ b := ha.trans hab.le
  have hfa := relativeFiniteEnergy_ray omega hφb hℓ ha
  have hfb := relativeFiniteEnergy_ray omega hφb hℓ hb0
  have hfa' := relativeFiniteEnergy_ray omega hφb hℓ' ha
  have hfb' := relativeFiniteEnergy_ray omega hφb hℓ' hb0
  set c := a + s * (b - a) with hc
  have hc0 : 0 ≤ c := by rw [hc]; nlinarith
  have hfc := relativeFiniteEnergy_ray omega hφb hℓ hc0
  have hfc' := relativeFiniteEnergy_ray omega hφb hℓ' hc0
  have hra := relativeFiniteEnergy_rooftop omega hfa hfa'
  have hrb := relativeFiniteEnergy_rooftop omega hfb hfb'
  have hrc := relativeFiniteEnergy_rooftop omega hfc hfc'
  have hsub := FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeFiniteEnergy
    omega θ φ _ _ hφ hra hrb
  set η := finiteGeodesic θ.val (rooftop θ (ℓ a) (ℓ' a)) (rooftop θ (ℓ b) (ℓ' b)) with hη
  have hηpot := hsub.2.2.1.thetaPshPotential hsI
  have hηrel := relativePSH_finiteGeodesic hsub.2.2.1 hra.1.relativePSH hrb.1.relativePSH hsI
  have hle1 : η s ≤ ℓ c := by
    rw [hc, hℓ.1.2 a b ha hab s hsI]
    exact finiteGeodesic_mono (rooftop_le_left hfa.1.plurisubharmonic hfa'.1.plurisubharmonic)
      (rooftop_le_left hfb.1.plurisubharmonic hfb'.1.plurisubharmonic) s
  have hle2 : η s ≤ ℓ' c := by
    rw [hc, hℓ'.1.2 a b ha hab s hsI]
    exact finiteGeodesic_mono (rooftop_le_right hfa.1.plurisubharmonic hfa'.1.plurisubharmonic)
      (rooftop_le_right hfb.1.plurisubharmonic hfb'.1.plurisubharmonic) s
  have hlec : η s ≤ rooftop θ (ℓ c) (ℓ' c) :=
    (le_rooftop_iff hfc.1.plurisubharmonic hfc'.1.plurisubharmonic hηpot).2 ⟨hle1, hle2⟩
  have hE := relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFiniteEnergy omega θ hφ hφb hra hrb
    hra.1.relativePSH hrb.1.relativePSH hsI hηrel
  have hmono := energy_mono (hφ := hφ) hηrel hrc.1.relativePSH hlec
  rw [energy_eq hηrel, hE] at hmono
  rw [← energy_eq, ← energy_eq,
    ← coe_toReal_energy hra.1.relativePSH (bot_lt_energy omega hφb hra),
    ← coe_toReal_energy hrb.1.relativePSH (bot_lt_energy omega hφb hrb),
    ← coe_toReal_energy hrc.1.relativePSH (bot_lt_energy omega hφb hrc),
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hmono
  exact hmono

/-- The Darvas distance along two finite-energy rays, at time `t`. -/
theorem relativeD1_ray_three_point (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ')
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    relativeD1 θ φ hφ (ℓ (a + s * (b - a))) (ℓ' (a + s * (b - a))) ≤
      (1 - s) * relativeD1 θ φ hφ (ℓ a) (ℓ' a) + s * relativeD1 θ φ hφ (ℓ b) (ℓ' b) := by
  have h1 := toReal_energy_ray_combination omega hφb hℓ ha hab hs
  have h2 := toReal_energy_ray_combination omega hφb hℓ' ha hab hs
  have h3 := toReal_energy_rooftop_ray_concave omega hφb hℓ hℓ' ha hab hs
  simp only [relativeD1]
  rw [h1, h2]
  nlinarith

/-- **Convexity of `d₁` along two finite-energy rays** (Xia, SGPT, Proposition 4.3.5, for rays and a
bounded model potential): `t ↦ d₁(ℓ_t, ℓ'_t)` is convex on `[0, ∞)`. -/
theorem convexOn_relativeD1_ray (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ') :
    ConvexOn ℝ (Ici 0) fun t => relativeD1 θ φ hφ (ℓ t) (ℓ' t) := by
  refine ⟨convex_Ici 0, fun x hx y hy p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have h := relativeD1_ray_three_point omega hφb hℓ hℓ' (mem_Ici.mp hx) hxy (s := q)
      ⟨hq, by linarith⟩
    rw [show x + q * (y - x) = p * x + q * y by linear_combination (-x) * hpq,
      show 1 - q = p by linarith] at h
    exact h
  · subst hxy
    rw [← add_mul, hpq, one_mul, ← add_mul, hpq, one_mul]
  · have h := relativeD1_ray_three_point omega hφb hℓ hℓ' (mem_Ici.mp hy) hxy (s := p)
      ⟨hp, by linarith⟩
    rw [show y + p * (x - y) = p * x + q * y by linear_combination (-y) * hpq,
      show 1 - p = q by linarith] at h
    linarith

/-- `d₁` vanishes at time `0` for rays with a common initial point, and is nonnegative. -/
theorem relativeD1_ray_nonneg (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ')
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ relativeD1 θ φ hφ (ℓ t) (ℓ' t) :=
  relativeD1_nonneg omega hφb (relativeFiniteEnergy_ray omega hφb hℓ ht)
    (relativeFiniteEnergy_ray omega hφb hℓ' ht)

/-- For rays with a common initial point, `t ↦ d₁(ℓ_t, ℓ'_t)/t` is nondecreasing on `(0, ∞)`. -/
theorem relativeD1_ray_div_mono (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ')
    (h0 : ℓ 0 = ℓ' 0) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    relativeD1 θ φ hφ (ℓ s) (ℓ' s) / s ≤ relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t := by
  have hconv := convexOn_relativeD1_ray omega hφb hℓ hℓ'
  have hD0 : relativeD1 θ φ hφ (ℓ 0) (ℓ' 0) = 0 := by
    rw [h0]; exact relativeD1_self (relativeFiniteEnergy_ray omega hφb hℓ' le_rfl).1.plurisubharmonic
  have h := hconv.secant_mono (a := 0) (x := s) (y := t) (mem_Ici.2 le_rfl) (mem_Ici.2 hs.le)
    (mem_Ici.2 (hs.le.trans hst)) hs.ne' (hs.trans_le hst).ne' hst
  simpa only [hD0, sub_zero] using h

/-- `d₁(ℓ_t, φ) = -E(ℓ_t)` along a ray (bounded model potential). -/
theorem relativeD1_ray_reference (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    relativeD1 θ φ hφ (ℓ t) φ = -(energy θ φ hφ (ℓ t)).toReal := by
  have hf := relativeFiniteEnergy_ray omega hφb hℓ ht
  rw [relativeD1_eq_sub_of_le hf.1.plurisubharmonic hf.1.le_reference, energy_self omega hφb,
    EReal.toReal_zero, zero_sub]

/-- An upper bound for `d₁(ℓ_t, ℓ'_t)/t`, through the model potential: for `t > 0`,
`d₁(ℓ_t, ℓ'_t)/t ≤ -(E(ℓ_0) + E(ℓ'_0))/t - (E(ℓ) + E(ℓ'))` with the radial energies as slopes. -/
theorem relativeD1_ray_div_le (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ')
    {t : ℝ} (ht : 0 < t) :
    relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t ≤
      -((energy θ φ hφ (ℓ 0)).toReal + (energy θ φ hφ (ℓ' 0)).toReal) / t -
        (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal) +
          ((energy θ φ hφ (ℓ' 1)).toReal - (energy θ φ hφ (ℓ' 0)).toReal)) := by
  have hf := relativeFiniteEnergy_ray omega hφb hℓ ht.le
  have hf' := relativeFiniteEnergy_ray omega hφb hℓ' ht.le
  have htri := relativeD1_triangle omega hφb hf hf' (relativeFiniteEnergy_self omega hφb)
  rw [relativeD1_comm θ φ hφ φ, relativeD1_ray_reference omega hφb hℓ ht.le,
    relativeD1_ray_reference omega hφb hℓ' ht.le, toReal_energy_ray omega hφb hℓ ht.le,
    toReal_energy_ray omega hφb hℓ' ht.le] at htri
  rw [div_le_iff₀ ht]
  have e : (-((energy θ φ hφ (ℓ 0)).toReal + (energy θ φ hφ (ℓ' 0)).toReal) / t -
      (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal) +
        ((energy θ φ hφ (ℓ' 1)).toReal - (energy θ φ hφ (ℓ' 0)).toReal))) * t =
      -((energy θ φ hφ (ℓ 0)).toReal + (energy θ φ hφ (ℓ' 0)).toReal) -
        t * (((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal) +
          ((energy θ φ hφ (ℓ' 1)).toReal - (energy θ φ hφ (ℓ' 0)).toReal)) := by
    field_simp
  rw [e]
  linarith

/-- **The Darvas distance of two rays exists and is finite** (Xia, SGPT, Definition 4.3.5 and the
finiteness in Theorem 4.3.4; bounded model potential): for finite-energy rays with a common initial
point, `d₁(ℓ_t, ℓ'_t)/t` increases to a finite limit `L ≥ 0`, and `rayD1 ℓ ℓ' = L`. -/
theorem exists_tendsto_rayD1 (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ')
    (h0 : ℓ 0 = ℓ' 0) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun t => relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t) atTop (𝓝 L) ∧
      (∀ t, 0 < t → relativeD1 θ φ hφ (ℓ t) (ℓ' t) / t ≤ L) ∧ rayD1 θ φ hφ ℓ ℓ' = (L : EReal) := by
  classical
  set D : ℝ → ℝ := fun t => relativeD1 θ φ hφ (ℓ t) (ℓ' t) with hD
  set F : ℝ → ℝ := fun t => if 0 < t then D t / t else 0 with hF
  have hF0 : ∀ t, 0 ≤ F t := fun t => by
    simp only [hF]
    split_ifs with ht
    · exact div_nonneg (relativeD1_ray_nonneg omega hφb hℓ hℓ' ht.le) ht.le
    · exact le_rfl
  have hmono : Monotone F := by
    intro s t hst
    by_cases hs : 0 < s
    · have ht : 0 < t := hs.trans_le hst
      simp only [hF, if_pos hs, if_pos ht]
      exact relativeD1_ray_div_mono omega hφb hℓ hℓ' h0 hs hst
    · simp only [hF, if_neg hs]
      exact hF0 t
  set c0 := (energy θ φ hφ (ℓ 0)).toReal + (energy θ φ hφ (ℓ' 0)).toReal
  set m := ((energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal) +
    ((energy θ φ hφ (ℓ' 1)).toReal - (energy θ φ hφ (ℓ' 0)).toReal)
  have hbdd : BddAbove (range F) := by
    refine ⟨|c0| - m, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h1 : F t ≤ F (max t 1) := hmono (le_max_left _ _)
    have hpos : 0 < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have h2 := relativeD1_ray_div_le omega hφb hℓ hℓ' hpos
    simp only [hF, if_pos hpos] at h1
    have h3 : -c0 / max t 1 ≤ |c0| := by
      rw [div_le_iff₀ hpos]
      nlinarith [neg_abs_le c0, le_max_right t 1, abs_nonneg c0]
    linarith
  have hT := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ t, F t
  have hev : ∀ᶠ t in atTop, F t = D t / t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [hF, if_pos ht]
  have hT' : Tendsto (fun t => D t / t) atTop (𝓝 L) := hT.congr' hev
  have hle : ∀ t, 0 < t → D t / t ≤ L := fun t ht => by
    have := le_ciSup hbdd t
    simp only [hF, if_pos ht] at this
    exact this
  refine ⟨L, (hF0 1).trans (le_ciSup hbdd 1), hT', hle, ?_⟩
  exact (EReal.tendsto_coe.2 hT').limUnder_eq

/-- The ray distance is at most `-(E(ℓ) + E(ℓ'))` (radial energies), in particular finite. -/
theorem rayD1_le (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ')
    (h0 : ℓ 0 = ℓ' 0) : rayD1 θ φ hφ ℓ ℓ' ≤ -radialEnergy θ φ hφ ℓ - radialEnergy θ φ hφ ℓ' := by
  obtain ⟨L, -, hT, -, hL⟩ := exists_tendsto_rayD1 omega hφb hℓ hℓ' h0
  set c0 := (energy θ φ hφ (ℓ 0)).toReal + (energy θ φ hφ (ℓ' 0)).toReal
  set m1 := (energy θ φ hφ (ℓ 1)).toReal - (energy θ φ hφ (ℓ 0)).toReal
  set m2 := (energy θ φ hφ (ℓ' 1)).toReal - (energy θ φ hφ (ℓ' 0)).toReal
  have hB : Tendsto (fun t : ℝ => -c0 / t - (m1 + m2)) atTop (𝓝 (-(m1 + m2))) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id).sub_const (m1 + m2)
  have hLle : L ≤ -(m1 + m2) := le_of_tendsto_of_tendsto hT hB
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        exact relativeD1_ray_div_le omega hφb hℓ hℓ' ht)
  rw [hL, radialEnergy_eq omega hφb hℓ, radialEnergy_eq omega hφb hℓ', ← EReal.coe_neg,
    ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

/-- **The Darvas metric on rays** (Xia, SGPT, Theorem 4.3.4; bounded model potential): on the
finite-energy rays with a given initial point `p`, `d₁` is finite, nonnegative, symmetric, satisfies
the triangle inequality, and `d₁(ℓ, ℓ') = 0` forces `ℓ_t = ℓ'_t` for every `t ≥ 0`. -/
theorem rayD1_isMetric (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    (p : M → EReal) :
    (∀ ℓ ℓ', IsFiniteEnergyRay θ φ hφ ℓ → IsFiniteEnergyRay θ φ hφ ℓ' → ℓ 0 = p → ℓ' 0 = p →
      0 ≤ rayD1 θ φ hφ ℓ ℓ' ∧ rayD1 θ φ hφ ℓ ℓ' < ⊤) ∧
    (∀ ℓ, IsFiniteEnergyRay θ φ hφ ℓ → rayD1 θ φ hφ ℓ ℓ = 0) ∧
    (∀ ℓ ℓ', rayD1 θ φ hφ ℓ ℓ' = rayD1 θ φ hφ ℓ' ℓ) ∧
    (∀ ℓ ℓ' ℓ'', IsFiniteEnergyRay θ φ hφ ℓ → IsFiniteEnergyRay θ φ hφ ℓ' →
      IsFiniteEnergyRay θ φ hφ ℓ'' → ℓ 0 = p → ℓ' 0 = p → ℓ'' 0 = p →
      rayD1 θ φ hφ ℓ ℓ'' ≤ rayD1 θ φ hφ ℓ ℓ' + rayD1 θ φ hφ ℓ' ℓ'') ∧
    (∀ ℓ ℓ', IsFiniteEnergyRay θ φ hφ ℓ → IsFiniteEnergyRay θ φ hφ ℓ' → ℓ 0 = p → ℓ' 0 = p →
      rayD1 θ φ hφ ℓ ℓ' = 0 → ∀ t, 0 ≤ t → ℓ t = ℓ' t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ ℓ' hℓ hℓ' h0 h0'
    obtain ⟨L, hL0, -, -, hL⟩ := exists_tendsto_rayD1 omega hφb hℓ hℓ' (h0.trans h0'.symm)
    rw [hL]
    exact ⟨EReal.coe_nonneg.mpr hL0, EReal.coe_lt_top L⟩
  · intro ℓ hℓ
    obtain ⟨L, -, hT, -, hL⟩ := exists_tendsto_rayD1 omega hφb hℓ hℓ rfl
    have hT0 : Tendsto (fun t => relativeD1 θ φ hφ (ℓ t) (ℓ t) / t) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [relativeD1_self (relativeFiniteEnergy_ray omega hφb hℓ ht).1.plurisubharmonic, zero_div]
    rw [hL, tendsto_nhds_unique hT hT0, EReal.coe_zero]
  · intro ℓ ℓ'
    unfold rayD1
    congr 1
    funext t
    rw [relativeD1_comm]
  · intro ℓ ℓ' ℓ'' hℓ hℓ' hℓ'' h0 h0' h0''
    obtain ⟨L1, -, hT1, -, hL1⟩ := exists_tendsto_rayD1 omega hφb hℓ hℓ'' (h0.trans h0''.symm)
    obtain ⟨L2, -, hT2, -, hL2⟩ := exists_tendsto_rayD1 omega hφb hℓ hℓ' (h0.trans h0'.symm)
    obtain ⟨L3, -, hT3, -, hL3⟩ := exists_tendsto_rayD1 omega hφb hℓ' hℓ'' (h0'.trans h0''.symm)
    rw [hL1, hL2, hL3, ← EReal.coe_add, EReal.coe_le_coe_iff]
    refine le_of_tendsto_of_tendsto hT1 (hT2.add hT3) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← add_div]
    exact div_le_div_of_nonneg_right (relativeD1_triangle omega hφb
      (relativeFiniteEnergy_ray omega hφb hℓ ht.le) (relativeFiniteEnergy_ray omega hφb hℓ'' ht.le)
      (relativeFiniteEnergy_ray omega hφb hℓ' ht.le)) ht.le
  · intro ℓ ℓ' hℓ hℓ' h0 h0' hzero t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, h0, h0']
    obtain ⟨L, -, -, hle, hL⟩ := exists_tendsto_rayD1 omega hφb hℓ hℓ' (h0.trans h0'.symm)
    rw [hL, EReal.coe_eq_zero] at hzero
    have h1 := hle t h
    rw [hzero, div_le_iff₀ h, zero_mul] at h1
    exact eq_of_relativeD1_eq_zero omega hφb (relativeFiniteEnergy_ray omega hφb hℓ ht)
      (relativeFiniteEnergy_ray omega hφb hℓ' ht)
      (le_antisymm h1 (relativeD1_ray_nonneg omega hφb hℓ hℓ' ht))

/-- **(4.38)** (Xia, SGPT, Proposition 4.3.6; bounded model potential): for finite-energy rays with
`ℓ_t ≤ ℓ'_t` for all `t ≥ 0`, `d₁(ℓ, ℓ') = E(ℓ') - E(ℓ)`. -/
theorem rayD1_eq_radialEnergy_sub (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {ℓ ℓ' : ℝ → M → EReal} (hℓ : IsFiniteEnergyRay θ φ hφ ℓ) (hℓ' : IsFiniteEnergyRay θ φ hφ ℓ')
    (hle : ∀ t, 0 ≤ t → ℓ t ≤ ℓ' t) :
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
    rw [relativeD1_eq_sub_of_le (relativeFiniteEnergy_ray omega hφb hℓ ht.le).1.plurisubharmonic
      (hle t ht.le), toReal_energy_ray omega hφb hℓ' ht.le, toReal_energy_ray omega hφb hℓ ht.le]
    field_simp
    ring
  rw [rayD1, hT.limUnder_eq, radialEnergy_eq omega hφb hℓ, radialEnergy_eq omega hφb hℓ', ← EReal.coe_sub]

end Distance


end

end SGPT.Foundations.Analysis.Pending.RelativeGeodesicRays

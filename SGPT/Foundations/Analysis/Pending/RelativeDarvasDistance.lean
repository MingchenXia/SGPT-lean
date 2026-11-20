import SGPT.Foundations.Analysis.Pending.RelativeEnergyDiamond

set_option autoImplicit false

/-!
# The Darvas distance `d₁` on the finite-energy class (bounded model potential)

Let `(X, ω)` be a connected compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form, `φ` a
model potential and `E = E_θ^φ` the extended Monge--Ampère energy. For `u, v ∈ E¹(X, θ; φ)`,

  `d₁(u, v) = E(u) + E(v) - 2 E(u ∧ v)`,   `u ∧ v = P_θ(min(u, v))` the rooftop envelope

(Xia, SGPT, Definition 4.3.1; `relativeD1`, defined for every model potential). For a **bounded**
model potential `φ` (for instance `θ` Kähler and `φ = V_θ = 0`):

* `relativeD1_eq_sub_of_le` — `d₁(u, v) = E(v) - E(u)` when `u ≤ v` (Xia (4.15));
* `relativeD1_nonneg`, `relativeD1_comm`, `relativeD1_self`, and the Pythagorean identity
  `relativeD1_eq_add_rooftop`: `d₁(u, v) = d₁(u, u ∧ v) + d₁(v, u ∧ v)`;
* `relativeD1_rooftop_le` — the contraction `d₁(u ∧ w, v ∧ w) ≤ d₁(u, v)` (Xia Proposition 4.3.1),
  from the diamond inequality (`RelativeEnergyDiamond`);
* `relativeD1_triangle` — the triangle inequality (Xia Lemma 4.3.1, Step 2);
* `eq_of_relativeD1_eq_zero` — separation (Xia Lemma 4.3.1, Step 1), by the domination principle;
* `relativeD1_isMetric` — so `d₁` is a metric on `E¹(X, θ; φ)`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct GlobalNonPluripolar RelativeEnergy
  BoundedMongeAmpereEnergy MongeAmpereEnergyDecreasing FiniteEnergyCharacterization DiagonalMass
  RelativeEnergyDiamond

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Definitions -/

/-- The rooftop envelope `u ∧ v = P_θ(min(u, v))`. -/
def rooftop (θ : ClosedRealOneOneForm n M) (u v : M → EReal) : M → EReal :=
  rooftopEnvelope θ.val (fun x => min (u x) (v x))

theorem rooftop_comm (θ : ClosedRealOneOneForm n M) (u v : M → EReal) :
    rooftop θ u v = rooftop θ v u := by
  unfold rooftop
  congr 1
  funext x
  exact min_comm _ _

variable [MeasurableSpace M] [CompactSpace M]

/-- The extended energy (Xia (3.30)) as a function of the potential alone. -/
def energy (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (u : M → EReal) : EReal :=
  sInf (relativeEnergyMajorantValues θ φ u hφ)

theorem energy_eq {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} {hφ : IsModelPotential θ φ}
    (hu : RelativePSH θ φ u) : energy θ φ hφ u = relativeMongeAmpereEnergy θ φ u hφ hu := rfl

/-- **The Darvas distance** `d₁(u, v) = E(u) + E(v) - 2 E(u ∧ v)` (Xia, SGPT, Definition 4.3.1),
read in `ℝ`; on `E¹(X, θ; φ)` all three energies are finite. -/
def relativeD1 (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (u v : M → EReal) : ℝ :=
  (energy θ φ hφ u).toReal + (energy θ φ hφ v).toReal - 2 * (energy θ φ hφ (rooftop θ u v)).toReal

theorem relativeD1_comm (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (u v : M → EReal) : relativeD1 θ φ hφ u v = relativeD1 θ φ hφ v u := by
  rw [relativeD1, relativeD1, rooftop_comm]
  ring

/-! ### The rooftop envelope -/

section Rooftop

omit [MeasurableSpace M] [CompactSpace M] in
/-- The rooftop of two `θ`-PSH potentials, when it is a `θ`-PSH potential, is the largest
`θ`-PSH potential below both. -/
theorem le_rooftop_iff {θ : ClosedRealOneOneForm n M} {u v s : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hs : IsThetaPshPotential θ.val s) : s ≤ rooftop θ u v ↔ s ≤ u ∧ s ≤ v := by
  have hle := RooftopEnvelopeLatticeMass.rooftopEnvelope_min_le θ hu hv
  constructor
  · intro h
    exact ⟨h.trans hle.1, h.trans hle.2⟩
  · rintro ⟨h1, h2⟩
    exact le_rooftopEnvelope hs (quasiEverywhere_of_forall fun x => le_min (h1 x) (h2 x))

omit [MeasurableSpace M] [CompactSpace M] in
theorem rooftop_le_left {θ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) : rooftop θ u v ≤ u :=
  (RooftopEnvelopeLatticeMass.rooftopEnvelope_min_le θ hu hv).1

omit [MeasurableSpace M] [CompactSpace M] in
theorem rooftop_le_right {θ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) : rooftop θ u v ≤ v :=
  (RooftopEnvelopeLatticeMass.rooftopEnvelope_min_le θ hu hv).2

omit [MeasurableSpace M] [CompactSpace M] in
/-- Two `θ`-PSH potentials with the same `θ`-PSH potentials below them are equal. -/
theorem eq_of_forall_le_iff {θ : ClosedRealOneOneForm n M} {r r' : M → EReal}
    (hr : IsThetaPshPotential θ.val r) (hr' : IsThetaPshPotential θ.val r')
    (h : ∀ s, IsThetaPshPotential θ.val s → (s ≤ r ↔ s ≤ r')) : r = r' :=
  le_antisymm ((h r hr).1 le_rfl) ((h r' hr').2 le_rfl)

omit [MeasurableSpace M] [CompactSpace M] in
/-- `u ∧ v = u` when `u ≤ v`. -/
theorem rooftop_eq_left_of_le {θ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (huv : u ≤ v) : rooftop θ u v = u := by
  have e : (fun x => min (u x) (v x)) = u := funext fun x => min_eq_left (huv x)
  rw [rooftop, e, rooftopEnvelope_self hu]

omit [MeasurableSpace M] [CompactSpace M] in
/-- `u ∧ v = v` when `v ≤ u`. -/
theorem rooftop_eq_right_of_le {θ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hv : IsThetaPshPotential θ.val v) (hvu : v ≤ u) : rooftop θ u v = v := by
  rw [rooftop_comm]
  exact rooftop_eq_left_of_le hv hvu

omit [MeasurableSpace M] [CompactSpace M] in
theorem rooftop_mono {θ : ClosedRealOneOneForm n M} {u u' v v' : M → EReal} (hu : u ≤ u')
    (hv : v ≤ v') : rooftop θ u v ≤ rooftop θ u' v' :=
  rooftopEnvelope_mono fun x => min_le_min (hu x) (hv x)

end Rooftop

/-! ### Energies on the finite-energy class -/

section Energy

variable [BorelSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

omit [BorelSpace M] in
theorem energy_le_zero {u : M → EReal} (hu : RelativePSH θ φ u) : energy θ φ hφ u ≤ 0 :=
  relativeMongeAmpereEnergy_le_zero θ hφ hu

omit [BorelSpace M] in
theorem energy_ne_top {u : M → EReal} (hu : RelativePSH θ φ u) : energy θ φ hφ u ≠ ⊤ :=
  ne_top_of_le_ne_top EReal.zero_ne_top (energy_le_zero hu)

omit [BorelSpace M] in
theorem energy_mono {u v : M → EReal} (hu : RelativePSH θ φ u) (hv : RelativePSH θ φ v)
    (huv : u ≤ v) : energy θ φ hφ u ≤ energy θ φ hφ v :=
  relativeMongeAmpereEnergy_mono θ hφ hu hv huv

omit [BorelSpace M] in
theorem coe_toReal_energy {u : M → EReal} (hu : RelativePSH θ φ u) (hb : ⊥ < energy θ φ hφ u) :
    (((energy θ φ hφ u).toReal : ℝ) : EReal) = energy θ φ hφ u :=
  EReal.coe_toReal (energy_ne_top hu) hb.ne'

omit [BorelSpace M] in
theorem toReal_energy_mono {u v : M → EReal} (hu : RelativePSH θ φ u)
    (hb : ⊥ < energy θ φ hφ u) (hv : RelativePSH θ φ v) (huv : u ≤ v) :
    (energy θ φ hφ u).toReal ≤ (energy θ φ hφ v).toReal :=
  EReal.toReal_le_toReal (energy_mono hu hv huv) hb.ne' (energy_ne_top hv)

/-- A finite-energy potential has finite energy (bounded model potential). -/
theorem bot_lt_energy (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ) {u : M → EReal}
    (hu : RelativeFiniteEnergy θ φ u hφ) : ⊥ < energy θ φ hφ u :=
  (relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb hu.1.relativePSH).1 hu

/-- The rooftop of two finite-energy potentials has finite energy. -/
theorem relativeFiniteEnergy_rooftop [ConnectedSpace M] (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ) :
    RelativeFiniteEnergy θ φ (rooftop θ u v) hφ :=
  FiniteGeodesicsFullMassAnyDim.relativeFiniteEnergy_rooftop_of_kahler omega θ φ u v hφ hu hv

end Energy

/-! ### Elementary properties of `d₁` -/

section Basic

variable {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- **Xia (4.15).** `d₁(u, v) = E(v) - E(u)` when `u ≤ v`. -/
theorem relativeD1_eq_sub_of_le {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (huv : u ≤ v) :
    relativeD1 θ φ hφ u v = (energy θ φ hφ v).toReal - (energy θ φ hφ u).toReal := by
  rw [relativeD1, rooftop_eq_left_of_le hu huv]
  ring

theorem relativeD1_self {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    relativeD1 θ φ hφ u u = 0 := by
  rw [relativeD1_eq_sub_of_le hu le_rfl, sub_self]

/-- **The Pythagorean identity** `d₁(u, v) = d₁(u, u ∧ v) + d₁(v, u ∧ v)`. -/
theorem relativeD1_eq_add_rooftop {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hw : IsThetaPshPotential θ.val (rooftop θ u v)) :
    relativeD1 θ φ hφ u v =
      relativeD1 θ φ hφ u (rooftop θ u v) + relativeD1 θ φ hφ v (rooftop θ u v) := by
  rw [relativeD1_comm θ φ hφ u (rooftop θ u v), relativeD1_comm θ φ hφ v (rooftop θ u v),
    relativeD1_eq_sub_of_le hw (rooftop_le_left hu hv),
    relativeD1_eq_sub_of_le hw (rooftop_le_right hu hv), relativeD1]
  ring

variable [BorelSpace M] [ConnectedSpace M]

/-- `d₁ ≥ 0` on `E¹(X, θ; φ)`, for a bounded model potential. -/
theorem relativeD1_nonneg (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {u v : M → EReal} (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ) :
    0 ≤ relativeD1 θ φ hφ u v := by
  have hw := relativeFiniteEnergy_rooftop omega hu hv
  have hb := bot_lt_energy omega hφb hw
  have h1 := toReal_energy_mono hw.1.relativePSH hb hu.1.relativePSH
    (rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic)
  have h2 := toReal_energy_mono hw.1.relativePSH hb hv.1.relativePSH
    (rooftop_le_right hu.1.plurisubharmonic hv.1.plurisubharmonic)
  rw [relativeD1]
  linarith

end Basic

/-! ### Contraction and the triangle inequality -/

section Metric

variable [BorelSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
  {hφ : IsModelPotential θ φ}

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- `(u ∧ w) ∧ (v ∧ w) = (u ∧ v) ∧ w`. -/
theorem rooftop_rooftop_rooftop {u v w : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hw : IsThetaPshPotential θ.val w)
    (huw : IsThetaPshPotential θ.val (rooftop θ u w)) (hvw : IsThetaPshPotential θ.val (rooftop θ v w))
    (huv : IsThetaPshPotential θ.val (rooftop θ u v))
    (h1 : IsThetaPshPotential θ.val (rooftop θ (rooftop θ u w) (rooftop θ v w)))
    (h2 : IsThetaPshPotential θ.val (rooftop θ (rooftop θ u v) w)) :
    rooftop θ (rooftop θ u w) (rooftop θ v w) = rooftop θ (rooftop θ u v) w := by
  refine eq_of_forall_le_iff h1 h2 fun s hs => ?_
  rw [le_rooftop_iff huw hvw hs, le_rooftop_iff huv hw hs, le_rooftop_iff hu hw hs,
    le_rooftop_iff hv hw hs, le_rooftop_iff hu hv hs]
  tauto

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- `(u ∧ w) ∧ v = v ∧ w` when `v ≤ u`. -/
theorem rooftop_rooftop_of_le {u v w : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hw : IsThetaPshPotential θ.val w)
    (huw : IsThetaPshPotential θ.val (rooftop θ u w))
    (h1 : IsThetaPshPotential θ.val (rooftop θ (rooftop θ u w) v))
    (h2 : IsThetaPshPotential θ.val (rooftop θ v w)) (hvu : v ≤ u) :
    rooftop θ (rooftop θ u w) v = rooftop θ v w := by
  refine eq_of_forall_le_iff h1 h2 fun s hs => ?_
  rw [le_rooftop_iff huw hv hs, le_rooftop_iff hu hw hs, le_rooftop_iff hv hw hs]
  constructor
  · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h', h⟩
  · rintro ⟨h', h⟩; exact ⟨⟨h'.trans hvu, h⟩, h'⟩

/-- **The contraction for ordered pairs** (Xia, proof of Proposition 4.3.1, Step 1): for
`v ≤ u` in `E¹(X, θ; φ)` and `w ∈ E¹(X, θ; φ)`, `d₁(u ∧ w, v ∧ w) ≤ d₁(u, v)`, by the diamond
inequality applied to `u ∧ w` and `v`. -/
theorem relativeD1_rooftop_le_of_le (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {u v w : M → EReal} (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hw : RelativeFiniteEnergy θ φ w hφ) (hvu : v ≤ u) :
    relativeD1 θ φ hφ (rooftop θ u w) (rooftop θ v w) ≤ relativeD1 θ φ hφ u v := by
  have huw := relativeFiniteEnergy_rooftop omega hu hw
  have hvw := relativeFiniteEnergy_rooftop omega hv hw
  have hpu := hu.1.plurisubharmonic
  have hpv := hv.1.plurisubharmonic
  have hpw := hw.1.plurisubharmonic
  have hle : rooftop θ v w ≤ rooftop θ u w := rooftop_mono hvu le_rfl
  rw [relativeD1_comm, relativeD1_eq_sub_of_le hvw.1.plurisubharmonic hle, relativeD1_comm,
    relativeD1_eq_sub_of_le hpv hvu]
  -- the diamond inequality for `a = u ∧ w` and `v`
  set a := rooftop θ u w with ha
  have hav : rooftop θ a v = rooftop θ v w :=
    rooftop_rooftop_of_le hpu hpv hpw huw.1.plurisubharmonic
      (by
        have := relativeFiniteEnergy_rooftop omega huw hv
        exact this.1.plurisubharmonic)
      hvw.1.plurisubharmonic hvu
  have hm := relativePSH_max huw.1.relativePSH hv.1.relativePSH
  have hd := relativeMongeAmpereEnergy_add_le_max_add_rooftop omega θ hφ hφb huw.1.relativePSH
    hv.1.relativePSH hm (by
      show RelativePSH θ φ (rooftop θ a v)
      rw [hav]; exact hvw.1.relativePSH)
  have hma : (fun x => max (a x) (v x)) ≤ u := fun x =>
    max_le (rooftop_le_left hpu hpw x) (hvu x)
  have hmu := energy_mono (hφ := hφ) hm hu.1.relativePSH hma
  change energy θ φ hφ a + energy θ φ hφ v ≤ energy θ φ hφ _ + energy θ φ hφ (rooftop θ a v) at hd
  rw [hav] at hd
  have hd' : energy θ φ hφ a + energy θ φ hφ v ≤ energy θ φ hφ u + energy θ φ hφ (rooftop θ v w) :=
    hd.trans (add_le_add hmu le_rfl)
  rw [← coe_toReal_energy huw.1.relativePSH (bot_lt_energy omega hφb huw),
    ← coe_toReal_energy hv.1.relativePSH (bot_lt_energy omega hφb hv),
    ← coe_toReal_energy hu.1.relativePSH (bot_lt_energy omega hφb hu),
    ← coe_toReal_energy hvw.1.relativePSH (bot_lt_energy omega hφb hvw),
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hd'
  linarith

/-- **The contraction** (Xia, SGPT, Proposition 4.3.1): for `u, v, w ∈ E¹(X, θ; φ)`,
`d₁(u ∧ w, v ∧ w) ≤ d₁(u, v)` (bounded model potential). -/
theorem relativeD1_rooftop_le (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {u v w : M → EReal} (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hw : RelativeFiniteEnergy θ φ w hφ) :
    relativeD1 θ φ hφ (rooftop θ u w) (rooftop θ v w) ≤ relativeD1 θ φ hφ u v := by
  have huv := relativeFiniteEnergy_rooftop omega hu hv
  have huw := relativeFiniteEnergy_rooftop omega hu hw
  have hvw := relativeFiniteEnergy_rooftop omega hv hw
  have huvw := relativeFiniteEnergy_rooftop omega huv hw
  have h1 := relativeFiniteEnergy_rooftop omega huw hvw
  have hpu := hu.1.plurisubharmonic
  have hpv := hv.1.plurisubharmonic
  have hpw := hw.1.plurisubharmonic
  have e : rooftop θ (rooftop θ u w) (rooftop θ v w) = rooftop θ (rooftop θ u v) w :=
    rooftop_rooftop_rooftop hpu hpv hpw huw.1.plurisubharmonic hvw.1.plurisubharmonic
      huv.1.plurisubharmonic h1.1.plurisubharmonic huvw.1.plurisubharmonic
  rw [relativeD1_eq_add_rooftop huw.1.plurisubharmonic hvw.1.plurisubharmonic h1.1.plurisubharmonic,
    e, relativeD1_eq_add_rooftop hpu hpv huv.1.plurisubharmonic]
  exact add_le_add
    (relativeD1_rooftop_le_of_le omega hφb hu huv hw (rooftop_le_left hpu hpv))
    (relativeD1_rooftop_le_of_le omega hφb hv huv hw (rooftop_le_right hpu hpv))

/-- **The triangle inequality** (Xia, SGPT, Lemma 4.3.1, Step 2): for `u, v, w ∈ E¹(X, θ; φ)`,
`d₁(u, v) ≤ d₁(u, w) + d₁(w, v)` (bounded model potential). -/
theorem relativeD1_triangle (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {u v w : M → EReal} (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hw : RelativeFiniteEnergy θ φ w hφ) :
    relativeD1 θ φ hφ u v ≤ relativeD1 θ φ hφ u w + relativeD1 θ φ hφ w v := by
  have hpu := hu.1.plurisubharmonic
  have hpv := hv.1.plurisubharmonic
  have hpw := hw.1.plurisubharmonic
  have huv := relativeFiniteEnergy_rooftop omega hu hv
  have huw := relativeFiniteEnergy_rooftop omega hu hw
  have hvw := relativeFiniteEnergy_rooftop omega hv hw
  have hwu := relativeFiniteEnergy_rooftop omega hw hu
  have hvwu := relativeFiniteEnergy_rooftop omega hvw hu
  -- `E(w) - E(v ∧ w) ≥ E(w ∧ u) - E((v ∧ w) ∧ u)` by the contraction with `u`
  have hc := relativeD1_rooftop_le omega hφb hw hvw hu
  have hle1 : rooftop θ v w ≤ w := rooftop_le_right hpv hpw
  have hle2 : rooftop θ (rooftop θ v w) u ≤ rooftop θ w u := rooftop_mono hle1 le_rfl
  rw [relativeD1_comm θ φ hφ (rooftop θ w u),
    relativeD1_eq_sub_of_le hvwu.1.plurisubharmonic hle2, relativeD1_comm θ φ hφ w,
    relativeD1_eq_sub_of_le hvw.1.plurisubharmonic hle1] at hc
  -- `E((v ∧ w) ∧ u) ≤ E(u ∧ v)`
  have hle3 : rooftop θ (rooftop θ v w) u ≤ rooftop θ u v :=
    (le_rooftop_iff hpu hpv hvwu.1.plurisubharmonic).2
      ⟨rooftop_le_right hvw.1.plurisubharmonic hpu,
        (rooftop_le_left hvw.1.plurisubharmonic hpu).trans (rooftop_le_left hpv hpw)⟩
  have hm := toReal_energy_mono hvwu.1.relativePSH (bot_lt_energy omega hφb hvwu)
    huv.1.relativePSH hle3
  rw [relativeD1, relativeD1, relativeD1, rooftop_comm θ w v, rooftop_comm θ w u] at *
  linarith

omit [ConnectedSpace M] in
/-- **The comparison with the smaller measure** (bounded potentials): for bounded `θ`-PSH `φ`, `u`,
`v` with `v ≤ u`, `∫ (u - v) θ_v^n ≤ (n + 1) (E^φ(u) - E^φ(v))` (every term of the cocycle sum is
`≥ 0`, and the first is `∫ (u - v) θ_v^n`). -/
theorem integral_le_mul_relativeEnergyOfMinimalType_sub (omega : KahlerBackground n M)
    {u v : M → EReal} (hφ' : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u)
    (hvb : IsBoundedPotential v) (hvu : v ≤ u) :
    ∫ x, ((u x).toReal - (v x).toReal) ∂(diagonalPotentialMeasure θ v hv) ≤
      ((n : ℝ) + 1) * (relativeEnergyOfMinimalType θ φ u hφ' hu -
        relativeEnergyOfMinimalType θ φ v hφ' hv) := by
  rw [relativeEnergyOfMinimalType_sub omega θ hφ' hu hv hφb hub hvb,
    relativeEnergyOfMinimalType_mul θ hv hu hvb hub, Finset.sum_range_succ']
  have h0 : layMeasure θ n 0 u v (fun _ => v) hu.1 hv.1 (fun _ => hv.1) =
      diagonalPotentialMeasure θ v hv :=
    BoundedIntegrationByParts.globalMixedMeasure_congr' rfl (by funext i; simp [lay]) _ _
  rw [h0]
  have hnn : ∀ j ∈ Finset.range n, 0 ≤ ∫ x, ((u x).toReal - (v x).toReal) ∂(layMeasure θ n (j + 1)
      u v (fun _ => v) hu.1 hv.1 (fun _ => hv.1)) := fun j _ =>
    integral_nonneg fun x => sub_nonneg.mpr (EReal.toReal_le_toReal (hvu x) (hvb.ne_bot x)
      (hub.ne_top x))
  linarith [Finset.sum_nonneg hnn]

omit [ConnectedSpace M] in
/-- For `v ≤ u` in `E¹(X, θ; φ)` with `E(u) = E(v)` (bounded model potential), `θ_v^n` does not
charge `{v < u}`. -/
theorem measure_lt_eq_zero_of_energy_eq (omega : KahlerBackground n M)
    (hφb : IsBoundedPotential φ) {u v : M → EReal} (hu : RelativeFiniteEnergy θ φ u hφ)
    (hv : RelativeFiniteEnergy θ φ v hφ) (hvu : v ≤ u)
    (he : (energy θ φ hφ u).toReal = (energy θ φ hφ v).toReal) :
    diagonalPotentialMeasure θ v hv.1.plurisubharmonic {x | v x < u x} = 0 := by
  classical
  have hφp := hφ.plurisubharmonic
  have hru := hu.1.relativePSH
  have hrv := hv.1.relativePSH
  set μ := diagonalPotentialMeasure θ v hv.1.plurisubharmonic with hμ
  have : IsFiniteMeasure μ := GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega _
  obtain ⟨a, b, hab⟩ := hφb
  -- truncations
  set uk : ℕ → M → EReal := truncation φ u with huk
  set vk : ℕ → M → EReal := truncation φ v with hvk
  have hpu : ∀ k, IsThetaPshPotential θ.val (uk k) := fun k =>
    isThetaPshPotential_truncation hφp.1 hru.1.1 ⟨a, b, hab⟩ hru.2 k
  have hpv : ∀ k, IsThetaPshPotential θ.val (vk k) := fun k =>
    isThetaPshPotential_truncation hφp.1 hrv.1.1 ⟨a, b, hab⟩ hrv.2 k
  have hbu : ∀ k, IsBoundedPotential (uk k) := truncation_bounded ⟨a, b, hab⟩ hru.2
  have hbv : ∀ k, IsBoundedPotential (vk k) := truncation_bounded ⟨a, b, hab⟩ hrv.2
  have hvuk : ∀ k, vk k ≤ uk k := fun k x => max_le_max (hvu x) le_rfl
  -- the energy differences tend to `0`
  have hTu := tendsto_relativeEnergyOfMinimalType_truncation omega θ hφ hru ⟨a, b, hab⟩
  have hTv := tendsto_relativeEnergyOfMinimalType_truncation omega θ hφ hrv ⟨a, b, hab⟩
  have hfu : relativeMongeAmpereEnergy θ φ u hφ hru =
      (((energy θ φ hφ u).toReal : ℝ) : EReal) :=
    (coe_toReal_energy hru (bot_lt_energy omega ⟨a, b, hab⟩ hu)).symm
  have hfv : relativeMongeAmpereEnergy θ φ v hφ hrv =
      (((energy θ φ hφ v).toReal : ℝ) : EReal) :=
    (coe_toReal_energy hrv (bot_lt_energy omega ⟨a, b, hab⟩ hv)).symm
  rw [hfu] at hTu
  rw [hfv] at hTv
  have hTu' := (EReal.tendsto_coe.mp hTu)
  have hTv' := (EReal.tendsto_coe.mp hTv)
  have hD : Tendsto (fun k => ((n : ℝ) + 1) * (relativeEnergyOfMinimalType θ φ (uk k) hφp (hpu k) -
      relativeEnergyOfMinimalType θ φ (vk k) hφp (hpv k))) atTop (𝓝 0) := by
    have := (hTu'.sub hTv').const_mul ((n : ℝ) + 1)
    rwa [he, sub_self, mul_zero] at this
  -- the bounded comparison at each level
  have hk : ∀ k, ∫ x, ((uk k x).toReal - (vk k x).toReal) ∂(diagonalPotentialMeasure θ (vk k) (hpv k)) ≤
      ((n : ℝ) + 1) * (relativeEnergyOfMinimalType θ φ (uk k) hφp (hpu k) -
        relativeEnergyOfMinimalType θ φ (vk k) hφp (hpv k)) := fun k =>
    integral_le_mul_relativeEnergyOfMinimalType_sub omega hφp (hpu k) (hpv k) ⟨a, b, hab⟩ (hbu k)
      (hbv k) (hvuk k)
  -- a fixed level set `{φ - k₀ < v}`
  have hlevel : ∀ k₀ : ℕ, μ ({x | φ x - ((k₀ : ℝ) : EReal) < v x} ∩ {x | v x < u x}) = 0 := by
    intro k₀
    set A : Set M := {x | φ x - ((k₀ : ℝ) : EReal) < v x} with hA
    have hAm : MeasurableSet A := measurableSet_lt_truncation hφp.1 hrv.1.1 k₀
    -- on `A` the values are finite
    have hvfin : ∀ x ∈ A, v x ≠ ⊥ := fun x hx => ne_bot_of_gt hx
    have hufin : ∀ x ∈ A, u x ≠ ⊥ := fun x hx => ne_bot_of_le_ne_bot (hvfin x hx) (hvu x)
    have hutop : ∀ x, u x ≠ ⊤ := fun x =>
      ne_top_of_le_ne_top (EReal.coe_ne_top b) ((hru.2 x).trans (hab x).2)
    set f : M → ℝ := A.indicator fun x => (u x).toReal - (v x).toReal with hf
    have hf0 : ∀ x, 0 ≤ f x := by
      intro x
      by_cases hx : x ∈ A
      · rw [hf, indicator_of_mem hx]
        exact sub_nonneg.mpr (EReal.toReal_le_toReal (hvu x) (hvfin x hx) (hutop x))
      · rw [hf, indicator_of_notMem hx]
    have hfb : ∀ x, |f x| ≤ (b - a) + k₀ := by
      intro x
      rw [abs_of_nonneg (hf0 x)]
      by_cases hx : x ∈ A
      · rw [hf, indicator_of_mem hx]
        have h1 : (u x).toReal ≤ b := by
          have := (hru.2 x).trans (hab x).2
          rw [← EReal.coe_toReal (hutop x) (hufin x hx)] at this
          exact EReal.coe_le_coe_iff.mp this
        have h2 : a - k₀ < (v x).toReal := by
          have h := (EReal.sub_le_sub (hab x).1 le_rfl :
            (a : EReal) - ((k₀ : ℝ) : EReal) ≤ φ x - ((k₀ : ℝ) : EReal)).trans_lt hx
          rw [← EReal.coe_sub, ← EReal.coe_toReal (ne_top_of_le_ne_top (hutop x) (hvu x))
            (hvfin x hx)] at h
          exact_mod_cast h
        linarith
      · rw [hf, indicator_of_notMem hx]
        have : (0 : ℝ) ≤ b - a := by
          have := (hab x).1.trans (hab x).2
          have : a ≤ b := by exact_mod_cast this
          linarith
        positivity
    have hfm : Measurable f :=
      (((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hru.1.1).ereal_toReal).sub
        ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hrv.1.1).ereal_toReal)).indicator hAm
    have hfi : Integrable f μ := integrable_of_abs_le hfm hfb
    -- `∫ f dμ ≤ D_k` for every `k ≥ k₀`
    have hle : ∀ k, k₀ ≤ k → ∫ x, f x ∂μ ≤ ((n : ℝ) + 1) *
        (relativeEnergyOfMinimalType θ φ (uk k) hφp (hpu k) -
          relativeEnergyOfMinimalType θ φ (vk k) hφp (hpv k)) := by
      intro k hkk
      refine le_trans ?_ (hk k)
      set ν := diagonalPotentialMeasure θ (vk k) (hpv k) with hν
      have : IsFiniteMeasure ν := globalMixedMeasure_isFiniteMeasure_of_bounded _ fun _ => hbv k
      set Ak : Set M := {x | φ x - ((k : ℝ) : EReal) < v x} with hAk
      have hAAk : A ⊆ Ak := fun x hx => lt_of_le_of_lt (EReal.sub_le_sub le_rfl
        (EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hkk))) hx
      have hres : ν.restrict Ak = μ.restrict Ak :=
        diagonalPotentialMeasure_truncation_restrict θ hφp hrv.1 k (hpv k)
      have hresA : ν.restrict A = μ.restrict A := by
        rw [← Measure.restrict_restrict_of_subset hAAk, hres, Measure.restrict_restrict_of_subset hAAk]
      obtain ⟨Cu, hCu⟩ := exists_abs_toReal_le (hbu k)
      obtain ⟨Cv, hCv⟩ := exists_abs_toReal_le (hbv k)
      have hgm : Measurable fun x => (uk k x).toReal - (vk k x).toReal :=
        ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable (hpu k).1).ereal_toReal).sub
          ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable (hpv k).1).ereal_toReal)
      have hgi : Integrable (fun x => (uk k x).toReal - (vk k x).toReal) ν :=
        integrable_of_abs_le hgm (C := Cu + Cv) fun x =>
          (abs_sub _ _).trans (add_le_add (hCu x) (hCv x))
      have hg0 : ∀ x, 0 ≤ (uk k x).toReal - (vk k x).toReal := fun x =>
        sub_nonneg.mpr (EReal.toReal_le_toReal (hvuk k x) ((hbv k).ne_bot x) ((hbu k).ne_top x))
      calc ∫ x, f x ∂μ = ∫ x in A, ((u x).toReal - (v x).toReal) ∂μ := integral_indicator hAm
        _ ≤ ∫ x in A, ((uk k x).toReal - (vk k x).toReal) ∂μ := by
            refine setIntegral_mono_on (hfi.integrableOn.congr_fun ?_ hAm) ?_ hAm ?_
            · intro x hx; rw [hf, indicator_of_mem hx]
            · have := hgi.integrableOn (s := A)
              rwa [IntegrableOn, hresA] at this
            · intro x hx
              have hvx : vk k x = v x := truncation_eq_of_lt (hAAk hx)
              rw [hvx]
              exact sub_le_sub_right (EReal.toReal_le_toReal (le_max_left _ _) (hufin x hx)
                ((hbu k).ne_top x)) _
        _ = ∫ x in A, ((uk k x).toReal - (vk k x).toReal) ∂ν := by rw [hresA]
        _ ≤ ∫ x, ((uk k x).toReal - (vk k x).toReal) ∂ν :=
            setIntegral_le_integral hgi (Eventually.of_forall hg0)
    have hint0 : ∫ x, f x ∂μ ≤ 0 :=
      ge_of_tendsto hD (eventually_atTop.2 ⟨k₀, hle⟩)
    have hzero : f =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg hf0 hfi).1 (le_antisymm hint0 (integral_nonneg hf0))
    refine measure_mono_null ?_ (ae_iff.mp hzero)
    rintro x ⟨hxA, hxlt⟩
    change ¬ f x = 0
    rw [hf, indicator_of_mem hxA]
    have : (v x).toReal < (u x).toReal := by
      have h := hxlt
      change v x < u x at h
      rw [← EReal.coe_toReal (ne_top_of_le_ne_top (hutop x) (hvu x)) (hvfin x hxA),
        ← EReal.coe_toReal (hutop x) (hufin x hxA)] at h
      exact EReal.coe_lt_coe_iff.mp h
    linarith
  -- the union over the levels, and the poles
  have hcover : {x | v x < u x} ⊆
      (⋃ k₀ : ℕ, ({x | φ x - ((k₀ : ℝ) : EReal) < v x} ∩ {x | v x < u x})) ∪ {x | v x = ⊥} := by
    intro x hx
    by_cases hbot : v x = ⊥
    · exact Or.inr hbot
    refine Or.inl (mem_iUnion.2 ?_)
    have hvtop : v x ≠ ⊤ := ne_top_of_lt hx
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (b - (v x).toReal)
    refine ⟨k₀, ?_, hx⟩
    show φ x - ((k₀ : ℝ) : EReal) < v x
    calc φ x - ((k₀ : ℝ) : EReal) ≤ (b : EReal) - ((k₀ : ℝ) : EReal) :=
          EReal.sub_le_sub (hab x).2 le_rfl
      _ = ((b - k₀ : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ < (((v x).toReal : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
      _ = v x := EReal.coe_toReal hvtop hbot
  refine measure_mono_null hcover (measure_union_null (measure_iUnion_null hlevel) ?_)
  exact diagonalPotentialMeasure_pole_null θ hv.1.plurisubharmonic

/-- **Separation for ordered pairs**: `v ≤ u` in `E¹(X, θ; φ)` and `E(u) = E(v)` force `u = v`
(bounded model potential), by the domination principle. -/
theorem eq_of_le_of_energy_eq (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {u v : M → EReal} (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (hvu : v ≤ u) (he : (energy θ φ hφ u).toReal = (energy θ φ hφ v).toReal) : u = v :=
  le_antisymm (FiniteGeodesicsFullMassAnyDim.le_of_relativeFullMass_of_measure_lt_eq_zero omega hv.1
    hu.1 (measure_lt_eq_zero_of_energy_eq omega hφb hu hv hvu he)) hvu

/-- **Separation** (Xia, SGPT, Lemma 4.3.1, Step 1): `d₁(u, v) = 0` forces `u = v` on
`E¹(X, θ; φ)` (bounded model potential). -/
theorem eq_of_relativeD1_eq_zero (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ)
    {u v : M → EReal} (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (h : relativeD1 θ φ hφ u v = 0) : u = v := by
  have hw := relativeFiniteEnergy_rooftop omega hu hv
  have hpu := hu.1.plurisubharmonic
  have hpv := hv.1.plurisubharmonic
  have hb := bot_lt_energy omega hφb hw
  have h1 := toReal_energy_mono hw.1.relativePSH hb hu.1.relativePSH (rooftop_le_left hpu hpv)
  have h2 := toReal_energy_mono hw.1.relativePSH hb hv.1.relativePSH (rooftop_le_right hpu hpv)
  rw [relativeD1] at h
  have e1 : (energy θ φ hφ u).toReal = (energy θ φ hφ (rooftop θ u v)).toReal := by linarith
  have e2 : (energy θ φ hφ v).toReal = (energy θ φ hφ (rooftop θ u v)).toReal := by linarith
  exact (eq_of_le_of_energy_eq omega hφb hu hw (rooftop_le_left hpu hpv) e1).trans
    (eq_of_le_of_energy_eq omega hφb hv hw (rooftop_le_right hpu hpv) e2).symm

/-- **`d₁` is a metric on `E¹(X, θ; φ)`** (Xia, SGPT, Lemma 4.3.1), for a bounded model potential
on a connected compact Kähler manifold. -/
theorem relativeD1_isMetric (omega : KahlerBackground n M) (hφb : IsBoundedPotential φ) :
    (∀ u v, RelativeFiniteEnergy θ φ u hφ → RelativeFiniteEnergy θ φ v hφ →
      0 ≤ relativeD1 θ φ hφ u v) ∧
    (∀ u, RelativeFiniteEnergy θ φ u hφ → relativeD1 θ φ hφ u u = 0) ∧
    (∀ u v, relativeD1 θ φ hφ u v = relativeD1 θ φ hφ v u) ∧
    (∀ u v w, RelativeFiniteEnergy θ φ u hφ → RelativeFiniteEnergy θ φ v hφ →
      RelativeFiniteEnergy θ φ w hφ →
      relativeD1 θ φ hφ u v ≤ relativeD1 θ φ hφ u w + relativeD1 θ φ hφ w v) ∧
    (∀ u v, RelativeFiniteEnergy θ φ u hφ → RelativeFiniteEnergy θ φ v hφ →
      relativeD1 θ φ hφ u v = 0 → u = v) :=
  ⟨fun _ _ hu hv => relativeD1_nonneg omega hφb hu hv,
    fun _ hu => relativeD1_self hu.1.plurisubharmonic,
    fun u v => relativeD1_comm θ φ hφ u v,
    fun _ _ _ hu hv hw => relativeD1_triangle omega hφb hu hv hw,
    fun _ _ hu hv h => eq_of_relativeD1_eq_zero omega hφb hu hv h⟩

end Metric

end

end SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance

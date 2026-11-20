import SGPT.BDivisor.BlowupModelNef
import SGPT.BDivisor.MassPushforwardClassVolume

/-!
# The volume of a b-divisor over the book's models

Source: `chap:bdiv`, `def:volb`: the volume of a pseudo-effective Weil b-divisor `𝔻` is
`vol 𝔻 = lim_{π : Y → X} vol 𝔻_Y`; "the right-hand side is a decreasing net due to
`prop:cones_modif2`, hence the limit always exists"; the volume of a non-pseudo-effective Weil
b-divisor is `0`; `𝔻` is big if `vol 𝔻 > 0`.

For a model system `S` we put `vol 𝔻 = ⨅_{π ∈ S} vol 𝔻_π` for pseudo-effective `𝔻` and `0`
otherwise (`WeilBDivisorOn.vol`); the class volume on a model is `def:volcohclass`
(`SGPT.BDivisor.Modification.classVolume`). Along a system whose dominations satisfy
`vol (g_* β) ≥ vol β` (`PushforwardVolumeMonotone`), the net `π ↦ vol 𝔻_π` is decreasing and
converges to `vol 𝔻` (`tendsto_vol`).

**On the book's models the hypothesis is a theorem.** For `X` connected compact Kähler, every
blow-up model is compact connected Kähler (Blanchard), so `prop:cones_modif2`, item 2
(`SGPT.BDivisor.sourceClassVolume_le_classPushforward`) applies along every domination of blow-up
models (`pushforwardVolumeMonotone_blowup`): the book's decreasing net exists and converges to
`vol 𝔻` for every pseudo-effective `𝔻` (`antitone_classVolume_blowup`, `tendsto_vol_blowup`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor

open Set Filter
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

namespace WeilBDivisorOn

section General

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]
  {S : ModelSystem n X} {hn : 0 < n}

/-- **The volume of a b-divisor** (`def:volb`): `⨅_π vol 𝔻_π` for pseudo-effective `𝔻` (the limit
of the decreasing net `π ↦ vol 𝔻_π`, `tendsto_vol`), and `0` otherwise. -/
def vol (𝔻 : WeilBDivisorOn S hn) : ℝ≥0∞ := by
  classical
  exact if 𝔻.IsPseudoeffective then ⨅ π : S.Model, Modification.classVolume π.1 (𝔻.onModel π)
    else 0

/-- A b-divisor is **big** if `vol 𝔻 > 0` (`def:volb`). -/
def IsBig (𝔻 : WeilBDivisorOn S hn) : Prop := 0 < 𝔻.vol

theorem vol_of_isPseudoeffective {𝔻 : WeilBDivisorOn S hn} (h : 𝔻.IsPseudoeffective) :
    𝔻.vol = ⨅ π : S.Model, Modification.classVolume π.1 (𝔻.onModel π) := by
  classical
  rw [vol, if_pos h]

theorem vol_of_not_isPseudoeffective {𝔻 : WeilBDivisorOn S hn} (h : ¬ 𝔻.IsPseudoeffective) :
    𝔻.vol = 0 := by
  classical
  rw [vol, if_neg h]

theorem vol_le_classVolume (𝔻 : WeilBDivisorOn S hn) (π : S.Model) :
    𝔻.vol ≤ Modification.classVolume π.1 (𝔻.onModel π) := by
  by_cases h : 𝔻.IsPseudoeffective
  · rw [vol_of_isPseudoeffective h]
    exact iInf_le (fun π : S.Model => Modification.classVolume π.1 (𝔻.onModel π)) π
  · rw [vol_of_not_isPseudoeffective h]
    exact zero_le

variable (S hn) in
/-- `prop:cones_modif2`, item 2, along the dominations of a model system: `vol (g_* β) ≥ vol β`
for every domination `g` and every pseudo-effective class `β`. -/
def PushforwardVolumeMonotone : Prop :=
  ∀ (π π' : S.Model) (h : π ≤ π') (β : RealBottChern n π'.1.carrier),
    ClassPseudoeffectiveViaPotentials β →
      Modification.classVolume π'.1 β ≤
        Modification.classVolume π.1
          (Modification.classPushforwardOfLE hn (show π.1 ≤ π'.1 from h) β)

theorem antitone_classVolume (hmono : PushforwardVolumeMonotone S hn)
    {𝔻 : WeilBDivisorOn S hn} (h𝔻 : 𝔻.IsPseudoeffective) :
    Antitone fun π : S.Model => Modification.classVolume π.1 (𝔻.onModel π) := by
  intro π π' h
  have hβ := (isPseudoeffective_iff 𝔻).mp h𝔻 π'
  have := hmono π π' h (𝔻.onModel π') hβ
  rwa [𝔻.pushforward_onModel h] at this

theorem tendsto_vol (hmono : PushforwardVolumeMonotone S hn) {𝔻 : WeilBDivisorOn S hn}
    (h𝔻 : 𝔻.IsPseudoeffective) :
    Tendsto (fun π : S.Model => Modification.classVolume π.1 (𝔻.onModel π)) atTop
      (𝓝 𝔻.vol) := by
  rw [vol_of_isPseudoeffective h𝔻]
  exact tendsto_atTop_iInf (antitone_classVolume hmono h𝔻)

end General

section Blowup

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] {hn : 0 < m + 1}

/-- **`prop:cones_modif2`, item 2, along the book's models**: for `X` connected compact Kähler,
`vol (g_* β) ≥ vol β` along every domination `g` of blow-up models and every pseudo-effective
class `β`. (No hypothesis on the models: they are Kähler by Blanchard's theorem.) -/
theorem pushforwardVolumeMonotone_blowup (hK : Nonempty (KahlerBackground (m + 1) X)) :
    PushforwardVolumeMonotone (ModelSystem.blowup (m + 1) X) hn := by
  intro π π' h β hβ
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  have : BorelSpace π.1.carrier := ⟨rfl⟩
  let : MeasurableSpace π'.1.carrier := borel π'.1.carrier
  have : BorelSpace π'.1.carrier := ⟨rfl⟩
  obtain ⟨ω⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
  obtain ⟨ω'⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π'
  exact sourceClassVolume_le_classPushforward
    (Modification.Dominates.isAnalyticModification (show π.1 ≤ π'.1 from h)) ω ω' hβ

/-- **`def:volb`: the net `π ↦ vol 𝔻_π` over the book's models is decreasing.** -/
theorem antitone_classVolume_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {𝔻 : BlowupWeilBDivisor (m + 1) X hn} (h𝔻 : 𝔻.IsPseudoeffective) :
    Antitone fun π : (ModelSystem.blowup (m + 1) X).Model =>
      Modification.classVolume π.1 (𝔻.onModel π) :=
  antitone_classVolume (pushforwardVolumeMonotone_blowup hK) h𝔻

/-- **`def:volb`: the limit `lim_π vol 𝔻_π` over the book's models exists and equals `vol 𝔻`**,
for every pseudo-effective b-divisor `𝔻` over the connected compact Kähler manifold `X`. -/
theorem tendsto_vol_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {𝔻 : BlowupWeilBDivisor (m + 1) X hn} (h𝔻 : 𝔻.IsPseudoeffective) :
    Tendsto (fun π : (ModelSystem.blowup (m + 1) X).Model =>
      Modification.classVolume π.1 (𝔻.onModel π)) atTop (𝓝 𝔻.vol) :=
  tendsto_vol (pushforwardVolumeMonotone_blowup hK) h𝔻

end Blowup

end WeilBDivisorOn

end SGPT.BDivisor

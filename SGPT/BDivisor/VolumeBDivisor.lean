import SGPT.BDivisor.NefBDivisor
import SGPT.Envelopes.SourceClassVolumeModification
import SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres

/-!
# The volume of a b-divisor

Source: `chap:bdiv`, `def:volb`: the volume of a pseudo-effective Weil b-divisor `𝔻` is
`vol 𝔻 = lim_{π : Y → X} vol 𝔻_Y`; "the right-hand side is a decreasing net due to
`prop:cones_modif2`, hence the limit always exists"; the volume of a non-pseudo-effective Weil
b-divisor is `0`; `𝔻` is big if `vol 𝔻 > 0`.

The volume of a class on a model is the project's `def:volcohclass`
(`SGPT.PSH.VariableComplexAtlas.sourceClassVolume`: `vol α = vol T_min`), computed with the Borel
`σ`-algebra of the model; models of a connected manifold are connected
(`Modification.instConnectedSpace`).

We define `vol 𝔻` as the infimum `⨅_π vol 𝔻_π` (for pseudo-effective `𝔻`). The book's limit is the
limit of the net `π ↦ vol 𝔻_π` along the directed set of models. The net is decreasing exactly when
`vol (g_* β) ≥ vol β` along every domination `g` (`prop:cones_modif2`, item 2; recorded here as
the predicate `PushforwardVolumeMonotone`), and then it converges to the infimum
(`tendsto_vol`). Item 2 of `prop:cones_modif2` is not yet formalized (it needs the push-forward
half of `prop:nppmassinv`), so the identification of `vol 𝔻` with the book's limit is conditional
on it.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor

open Set Filter
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace Modification

/-- The model of a modification of a connected manifold is connected. -/
instance instConnectedSpace [ConnectedSpace X] (π : Modification n X) :
    ConnectedSpace π.carrier := by
  apply connectedSpace_iff_univ.mpr
  have hc := AnalyticModificationConnectedFibres.isConnected_preimage_of_isConnected
    π.isAnalyticModification (⟨univ, isOpen_univ⟩ : TopologicalSpace.Opens X) isConnected_univ
  change IsConnected (π.map ⁻¹' (univ : Set X)) at hc
  simpa only [preimage_univ] using hc

variable [ConnectedSpace X]

/-- The volume `vol α` of a class `α ∈ H^{1,1}(Y_π, ℝ)` on a model (`def:volcohclass`, with the
Borel `σ`-algebra of `Y_π`). -/
def classVolume (π : Modification n X) (α : RealBottChern n π.carrier) : ℝ≥0∞ :=
  @SGPT.PSH.VariableComplexAtlas.sourceClassVolume n π.carrier _ _ _ (borel π.carrier) _ _ α

end Modification

namespace WeilBDivisor

variable {hn : 0 < n} [ConnectedSpace X]

/-- **The volume of a Weil b-divisor** (`def:volb`): `⨅_π vol 𝔻_π` for pseudo-effective `𝔻` (the
limit of the net `π ↦ vol 𝔻_π` when it is decreasing, `tendsto_vol`), and `0` otherwise. -/
def vol (𝔻 : WeilBDivisor n X hn) : ℝ≥0∞ := by
  classical
  exact if 𝔻.IsPseudoeffective then ⨅ π, Modification.classVolume π (𝔻.onModel π) else 0

/-- A Weil b-divisor is **big** if `vol 𝔻 > 0` (`def:volb`). -/
def IsBig (𝔻 : WeilBDivisor n X hn) : Prop := 0 < 𝔻.vol

theorem vol_of_isPseudoeffective {𝔻 : WeilBDivisor n X hn} (h : 𝔻.IsPseudoeffective) :
    𝔻.vol = ⨅ π, Modification.classVolume π (𝔻.onModel π) := by
  classical
  rw [vol, if_pos h]

theorem vol_of_not_isPseudoeffective {𝔻 : WeilBDivisor n X hn} (h : ¬ 𝔻.IsPseudoeffective) :
    𝔻.vol = 0 := by
  classical
  rw [vol, if_neg h]

/-- The volume of a b-divisor is at most the volume of each of its classes. -/
theorem vol_le_classVolume (𝔻 : WeilBDivisor n X hn) (π : Modification n X) :
    𝔻.vol ≤ Modification.classVolume π (𝔻.onModel π) := by
  by_cases h : 𝔻.IsPseudoeffective
  · rw [vol_of_isPseudoeffective h]
    exact iInf_le _ π
  · rw [vol_of_not_isPseudoeffective h]
    exact zero_le

theorem vol_le_root (𝔻 : WeilBDivisor n X hn) :
    𝔻.vol ≤ Modification.classVolume Modification.root 𝔻.root :=
  vol_le_classVolume 𝔻 Modification.root

variable (n X hn) in
/-- `prop:cones_modif2`, item 2, along the dominations of the model system: for every domination
`g : Y_{π'} → Y_π` and every pseudo-effective class `β` on `Y_{π'}`,
`vol (g_* β) ≥ vol β`. (Stated as a predicate; not proved here.) -/
def PushforwardVolumeMonotone : Prop :=
  ∀ (π π' : Modification n X) (h : π ≤ π') (β : RealBottChern n π'.carrier),
    ClassPseudoeffectiveViaPotentials β →
      Modification.classVolume π' β ≤
        Modification.classVolume π (Modification.classPushforwardOfLE hn h β)

/-- Under `prop:cones_modif2`, item 2, the net `π ↦ vol 𝔻_π` is decreasing. -/
theorem antitone_classVolume (hmono : PushforwardVolumeMonotone n X hn)
    {𝔻 : WeilBDivisor n X hn} (h𝔻 : 𝔻.IsPseudoeffective) :
    Antitone fun π => Modification.classVolume π (𝔻.onModel π) := by
  intro π π' h
  have hβ := (isPseudoeffective_iff 𝔻).mp h𝔻 π'
  have := hmono π π' h (𝔻.onModel π') hβ
  rwa [𝔻.pushforward_onModel h] at this

/-- **`vol 𝔻` is the limit of the decreasing net `π ↦ vol 𝔻_π`** (`def:volb`), granted
`prop:cones_modif2`, item 2. -/
theorem tendsto_vol (hmono : PushforwardVolumeMonotone n X hn) {𝔻 : WeilBDivisor n X hn}
    (h𝔻 : 𝔻.IsPseudoeffective) :
    Tendsto (fun π => Modification.classVolume π (𝔻.onModel π)) atTop (𝓝 𝔻.vol) := by
  rw [vol_of_isPseudoeffective h𝔻]
  exact tendsto_atTop_iInf (antitone_classVolume hmono h𝔻)

end WeilBDivisor

end SGPT.BDivisor

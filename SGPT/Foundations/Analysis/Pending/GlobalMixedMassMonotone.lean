import SGPT.Foundations.Analysis.Pending.MixedMass
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

set_option autoImplicit false

/-!
# Monotonicity of total mixed non-pluripolar mass in every dimension

`Pending.MixedMass.globalMixedMass_mono` proves that the total mixed
non-pluripolar mass is monotone in the singularity order, for locally
nondegenerate theta-PSH potentials on a compact manifold with a Kähler
background.  Its hypothesis `0 < n` is not used by the proof; it was kept only
for the existing callers.  This module records the statement without it
(`globalMixedMass_mono_of_isThetaPshPotential`), so that the dimension `0`
case is covered as well, and the form of the source (Copy-4, item
`it:monotone`; Darvas--Di Nezza--Lu, Theorem 2.4): on a *connected* compact
Kähler manifold the potentials need only be theta-PSH and not identically
`-∞`, because the identity principle
(`Pending.ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot`)
upgrades them to locally nondegenerate potentials
(`globalMixedMass_mono_of_connected`).

The mass `globalMixedMass θ u` is the total mass of the actual global mixed
non-pluripolar measure `⟨θ_{1,u_1} ∧ ⋯ ∧ θ_{n,u_n}⟩` (blueprint
`mmass:mass`), with `ddᶜ = i∂∂̄ / (2π)` (`LocalCurrents`), the normalization of
`ana:geometric-setting`.  In dimension `0` both sides are the mass of the
same measure, since a family indexed by `Fin 0` is unique.

Blueprint: `ana:mass-monotonicity`.  No statement of an existing declaration is
changed.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar MixedMass

noncomputable section

/-- If `f ≤ g + C` everywhere and `f` is somewhere different from `-∞`, then so
is `g`. -/
theorem exists_ne_bot_of_moreSingularOn {X : Type*} {f g : X → EReal}
    (hfg : MoreSingularOn f g univ) (hf : ∃ x, f x ≠ ⊥) : ∃ x, g x ≠ ⊥ := by
  obtain ⟨C, hC⟩ := hfg
  obtain ⟨x, hx⟩ := hf
  refine ⟨x, fun hgx => hx ?_⟩
  have h := hC x (mem_univ x)
  rw [hgx, EReal.bot_add] at h
  exact le_bot_iff.mp h

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u v : Fin n → M → EReal}

/-- **Monotonicity of total mixed mass in the singularity order**, in every
dimension (including `n = 0`), for locally nondegenerate theta-PSH potentials
on a compact manifold with a Kähler background.  This is
`MixedMass.globalMixedMass_mono` without its unused hypothesis `0 < n`. -/
theorem globalMixedMass_mono_of_isThetaPshPotential (omega : KahlerBackground n M)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, MoreSingularOn (u i) (v i) univ) :
    globalMixedMass θ u (fun i => (hu i).1) ≤
      globalMixedMass θ v (fun i => (hv i).1) :=
  MassFromBoundedDifference.globalMixedMeasure_univ_le_of_moreSingular hu hv huv
    fun _ _ ha hb _ ht hab hba =>
      (MixedMassBoundedDifference.globalMixedMeasure_univ_eq_of_le_add omega ha hb ht hab
        hba).le

/-- **Monotonicity of non-pluripolar mass** (blueprint `ana:mass-monotonicity`;
Copy-4 `it:monotone`, Darvas--Di Nezza--Lu Theorem 2.4).  Let `M` be a
connected compact Kähler manifold of dimension `n` (any `n`, including `0`),
`θ_j` smooth closed real `(1,1)`-forms, and `u_j, v_j` theta-PSH and not
identically `-∞`.  If `u_j ⪯ v_j` (that is `u_j ≤ v_j + C_j`) for every `j`,
then `∫⟨θ_{1,u_1} ∧ ⋯ ∧ θ_{n,u_n}⟩ ≤ ∫⟨θ_{1,v_1} ∧ ⋯ ∧ θ_{n,v_n}⟩`.

That `v_j` is not identically `-∞` follows from the hypotheses on `u_j`, so it
is not assumed. -/
theorem globalMixedMass_mono_of_connected [ConnectedSpace M] (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hv : ∀ i, ThetaPlurisubharmonic (θ i).val (v i))
    (hune : ∀ i, ∃ x, u i x ≠ ⊥)
    (huv : ∀ i, MoreSingularOn (u i) (v i) univ) :
    globalMixedMass θ u hu ≤ globalMixedMass θ v hv :=
  globalMixedMass_mono_of_isThetaPshPotential (θ := θ) omega
    (fun i => ⟨hu i, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
      (hu i) (hune i)⟩)
    (fun i => ⟨hv i, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
      (hv i) (exists_ne_bot_of_moreSingularOn (huv i) (hune i))⟩)
    huv

/-- The real encoding of the connected form, for callers working with real
masses; it loses nothing because both masses are finite. -/
theorem globalMixedMassReal_mono_of_connected [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hv : ∀ i, ThetaPlurisubharmonic (θ i).val (v i))
    (hune : ∀ i, ∃ x, u i x ≠ ⊥)
    (huv : ∀ i, MoreSingularOn (u i) (v i) univ) :
    globalMixedMassReal θ u hu ≤ globalMixedMassReal θ v hv :=
  ENNReal.toReal_mono (globalMixedMass_lt_top omega hv).ne
    (globalMixedMass_mono_of_connected omega hu hv hune huv)

end

end SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

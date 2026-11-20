import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeOrderInfimum
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteRooftopChains
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility

set_option autoImplicit false

/-! # Literal I-model rooftop chains and genuine tails from an actual lower seed -/

open Set

namespace SGPT.Foundations.Analysis.Pending.IModelRooftopLowerSeed

open FirstPass FirstPass.PositiveClasses FirstPass.IEnvelope
  ActualIEnvelopeOrderInfimum RelativeDarvasDistance
  SingularModelDarvasFiniteRooftopChains ThetaPshDecreasingLimit

noncomputable section


variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- A natural genuine common lower seed internally produces rooftop
regularity and the literal multiplier-ideal fixed-point equality. -/
theorem isIModelPotential_rooftop_of_common_lower
    (θ : ClosedRealOneOneForm n M) {u v s : M → EReal}
    (hu : IsIModelPotential θ.val u) (hv : IsIModelPotential θ.val v)
    (hs : IsThetaPshPotential θ.val s) (hsu : s ≤ u) (hsv : s ≤ v) :
    IsIModelPotential θ.val (rooftop θ u v) := by
  have hu0 : u ≤ 0 := by
    rw [hu.envelope_eq]
    exact iSingularityEnvelope_le_zero θ.val u
  have hne : (rooftopCompetitors θ.val (fun x => min (u x) (v x))).Nonempty :=
    ⟨s, mem_rooftopCompetitors_of_le hs (fun x => le_min (hsu x) (hsv x))⟩
  have hbound : ∃ C : ℝ, ∀ g ∈ rooftopCompetitors θ.val
      (fun x => min (u x) (v x)), ∀ x, g x ≤ (C : EReal) := by
    refine ⟨0, ?_⟩
    intro g hg x
    have hgu : g ≤ u := hg.1.1.le_of_quasiEverywhere_le hu.plurisubharmonic.1
      (hg.2.mono fun y hy => hy.trans (min_le_left _ _))
    exact (hgu x).trans (hu0 x)
  have hr : IsThetaPshPotential θ.val (rooftop θ u v) :=
    isThetaPshPotential_rooftop_of_nonempty hne hbound
  have hr0 : rooftop θ u v ≤ 0 :=
    (rooftop_le_left hu.plurisubharmonic hv.plurisubharmonic).trans hu0
  have hIr : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val (rooftop θ u v)) :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hr.1.hasSmoothLocalPotentials (rooftop θ u v) hr
  have hIu : iSingularityEnvelope θ.val (rooftop θ u v) ≤ u :=
    (iSingularityEnvelope_le_of_iOrderOnManifold θ hu.plurisubharmonic
      (iOrderOnManifold_of_le hu.plurisubharmonic.1.quasiPlurisubharmonic
        (rooftop_le_left hu.plurisubharmonic hv.plurisubharmonic))).trans_eq hu.envelope_eq.symm
  have hIv : iSingularityEnvelope θ.val (rooftop θ u v) ≤ v :=
    (iSingularityEnvelope_le_of_iOrderOnManifold θ hv.plurisubharmonic
      (iOrderOnManifold_of_le hv.plurisubharmonic.1.quasiPlurisubharmonic
        (rooftop_le_right hu.plurisubharmonic hv.plurisubharmonic))).trans_eq hv.envelope_eq.symm
  exact ⟨hr, le_antisymm
    (le_iSingularityEnvelope hr hr0 (IEquivalentOnManifold.refl (rooftop θ u v)))
    ((le_rooftop_iff hu.plurisubharmonic hv.plurisubharmonic hIr).mpr ⟨hIu, hIv⟩)⟩


/-- The finite rooftop recursion internally retains both its literal
I-model property and the common genuine seed at every stage. -/
theorem isIModelPotential_finiteTailRooftop_and_lower
    (θ : ClosedRealOneOneForm n M) {u : ℕ → M → EReal} {s : M → EReal}
    (hu : ∀ j, IsIModelPotential θ.val (u j))
    (hs : IsThetaPshPotential θ.val s) (i : ℕ)
    (hbelow : ∀ j, s ≤ u (i + j)) (k : ℕ) :
    IsIModelPotential θ.val (finiteTailRooftop θ u i k) ∧
      s ≤ finiteTailRooftop θ u i k := by
  induction k with
  | zero => simpa only [finiteTailRooftop, Nat.add_zero] using And.intro (hu i) (hbelow 0)
  | succ k ih =>
      refine ⟨isIModelPotential_rooftop_of_common_lower θ ih.1 (hu (i + k + 1))
        hs ih.2 (by simpa only [Nat.add_assoc] using hbelow (k + 1)), ?_⟩
      exact (le_rooftop_iff ih.1.plurisubharmonic (hu (i + k + 1)).plurisubharmonic hs).mpr
        ⟨ih.2, by simpa only [Nat.add_assoc] using hbelow (k + 1)⟩

/-- The actual decreasing rooftop tail has internally produced raw PSH
and local nondegeneracy from its genuine seed, before the I-model infimum lemma. -/
theorem isIModelPotential_iInf_finiteTailRooftop_of_common_lower
    (θ : ClosedRealOneOneForm n M) {u : ℕ → M → EReal} {s : M → EReal}
    (hu : ∀ j, IsIModelPotential θ.val (u j))
    (hs : IsThetaPshPotential θ.val s) (i : ℕ)
    (hbelow : ∀ j, s ≤ u (i + j)) :
    IsIModelPotential θ.val (⨅ k, finiteTailRooftop θ u i k) := by
  have hQ (k : ℕ) : IsIModelPotential θ.val (finiteTailRooftop θ u i k) :=
    (isIModelPotential_finiteTailRooftop_and_lower θ hu hs i hbelow k).1
  have hsQ (k : ℕ) : s ≤ finiteTailRooftop θ u i k :=
    (isIModelPotential_finiteTailRooftop_and_lower θ hu hs i hbelow k).2
  have hanti : Antitone (finiteTailRooftop θ u i) := by
    apply antitone_nat_of_succ_le
    intro k
    exact rooftop_le_left (hQ k).plurisubharmonic (hu (i + k + 1)).plurisubharmonic
  have hraw := thetaPlurisubharmonic_iInf_of_antitone
    (fun k => (hQ k).plurisubharmonic.1) (fun x _ _ hij => hanti hij x)
  have hτ : IsThetaPshPotential θ.val (⨅ k, finiteTailRooftop θ u i k) := by
    constructor
    · have heq : (⨅ k, finiteTailRooftop θ u i k) =
          (fun x => ⨅ k, finiteTailRooftop θ u i k x) := by
        funext x
        exact iInf_apply
      rw [heq]
      exact hraw
    · exact hs.2.mono (le_iInf hsQ)
  exact isIModelPotential_iInf_of_isThetaPshPotential θ hQ hτ

end

end SGPT.Foundations.Analysis.Pending.IModelRooftopLowerSeed

import SGPT.Foundations.Analysis.Pending.ActualDecreasingModelMixedMass
import SGPT.Foundations.Analysis.Pending.ThetaPshAntitoneSupNondegenerate
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.ModelRaySupremum

set_option autoImplicit false

/-! # Actual infima of decreasing model sequences

SGPT PDF0111--0112 Proposition 3.1.11, fixed-background sequence scope.
Actual model normalization and Hartogs noncollapse produce a genuine
infimum. Actual envelope monotonicity and the self-competitor produce its
fixed equality. The mass consumers keep positive infimum mass as a natural
hypothesis; no positive mass is inferred from positive stage masses.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualDecreasingModelInfimum

open FirstPass FirstPass.PositiveClasses DiagonalMass MixedMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual model normalization internally rules out collapse of the raw
decreasing infimum and hence produces its genuine theta-PSH witness. -/
theorem isThetaPshPotential_iInf_of_antitone_model
    {θ : ClosedRealOneOneForm n M} {u : ℕ → M → EReal}
    (hu : ∀ k, IsModelPotential θ (u k)) (hanti : Antitone u) :
    IsThetaPshPotential θ.val (⨅ k, u k) := by
  have hreach : ∀ k, ∃ x : M, ((-1 : ℝ) : EReal) ≤ u k x := by
    intro k
    have hlt : ((-1 : ℝ) : EReal) < ⨆ x, u k x := by
      rw [ModelRaySupremum.iSup_model_eq_zero (hu k)]
      norm_num
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp hlt
    exact ⟨x, hx.le⟩
  have hantiPoint : ∀ x, Antitone fun k => u k x :=
    fun x _ _ hab => hanti hab x
  have hne := ThetaPshAntitoneSupNondegenerate.exists_ne_bot_iInf_of_forall_exists_le
    (fun k => (hu k).plurisubharmonic) hantiPoint hreach
  have hraw := ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
    (fun k => (hu k).plurisubharmonic.1) hantiPoint
  have heq : (⨅ k, u k) = (fun x => ⨅ k, u k x) := by
    funext x
    exact iInf_apply
  rw [heq]
  exact ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot hraw hne

/-- The produced genuine infimum is fixed by the actual singularity
envelope, without an idempotence or fixed-point certificate. -/
theorem singularityEnvelope_iInf_of_antitone_model
    {θ : ClosedRealOneOneForm n M} {u : ℕ → M → EReal}
    (hu : ∀ k, IsModelPotential θ (u k)) (hanti : Antitone u) :
    (⨅ k, u k) = singularityEnvelope θ.val (⨅ k, u k) := by
  have hU := isThetaPshPotential_iInf_of_antitone_model hu hanti
  have hU0 : (⨅ k, u k) ≤ 0 := by
    exact (iInf_le u 0).trans (by
      rw [(hu 0).envelope_eq]
      exact singularityEnvelope_le_zero θ.val (u 0))
  apply le_antisymm (self_le_singularityEnvelope hU hU0)
  apply le_iInf
  intro k
  have hmore : MoreSingularOn (⨅ j, u j) (u k) univ :=
    MoreSingularOn.of_le fun x _ => iInf_le u k x
  simpa only [← (hu k).envelope_eq] using singularityEnvelope_mono (θ := θ.val) hmore

variable [BorelSpace M]

/-- Actual diagonal masses converge to the internally produced infimum
on its natural positive-mass domain. Pointwise convergence is also produced. -/
theorem tendsto_diagonalPotentialMass_iInf_of_antitone_model
    (omega : KahlerBackground n M) {θ : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} (hu : ∀ k, IsModelPotential θ (u k))
    (hanti : Antitone u)
    (hpos : 0 < diagonalPotentialMass θ (⨅ k, u k)
      (isThetaPshPotential_iInf_of_antitone_model hu hanti)) :
    Tendsto (fun k => diagonalPotentialMass θ (u k) (hu k).plurisubharmonic) atTop
      (𝓝 (diagonalPotentialMass θ (⨅ k, u k)
        (isThetaPshPotential_iInf_of_antitone_model hu hanti))) := by
  apply ActualDecreasingModelMixedMass.tendsto_diagonalPotentialMass_of_antitone_model
    omega θ u hu hanti (isThetaPshPotential_iInf_of_antitone_model hu hanti) hpos
  intro x
  simpa only [iInf_apply] using
    tendsto_atTop_iInf (show Antitone (fun k => u k x) from fun _ _ hab => hanti hab x)

/-- Actual independent mixed masses converge to the produced infima when
each actual diagonal infimum mass is positive. No limit witnesses are inputs. -/
theorem tendsto_globalMixedMass_iInf_of_antitone_model
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} (hu : ∀ k i, IsModelPotential (θ i) (u k i))
    (hanti : ∀ i, Antitone (fun k => u k i))
    (hpos : ∀ i, 0 < diagonalPotentialMass (θ i) (⨅ k, u k i)
      (isThetaPshPotential_iInf_of_antitone_model (fun k => hu k i) (hanti i))) :
    Tendsto (fun k => globalMixedMass θ (u k) (fun i => (hu k i).plurisubharmonic.1))
      atTop (𝓝 (globalMixedMass θ (fun i => ⨅ k, u k i)
        (fun i => (isThetaPshPotential_iInf_of_antitone_model
          (fun k => hu k i) (hanti i)).1))) := by
  apply ActualDecreasingModelMixedMass.tendsto_globalMixedMass_of_antitone_model
    omega hu hanti
    (fun i => isThetaPshPotential_iInf_of_antitone_model (fun k => hu k i) (hanti i)) hpos
  intro i x
  simpa only [iInf_apply] using tendsto_atTop_iInf
    (show Antitone (fun k => u k i x) from fun _ _ hab => hanti i hab x)

end

end SGPT.Foundations.Analysis.Pending.ActualDecreasingModelInfimum

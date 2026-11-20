import SGPT.Foundations.Analysis.Pending.ActualMixedMassOrderedContinuity
import SGPT.Foundations.Analysis.Pending.DecreasingContactMassLimit
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondModel
import SGPT.Foundations.Analysis.Pending.RelativeFullMass

set_option autoImplicit false

/-! # Actual mixed mass of decreasing model sequences

SGPT PDF0112--0113 Proposition 3.1.12, fixed-background sequence positive
limit scope, and its use in PDF0236. Actual model contact and decreasing
contact semicontinuity internally produce diagonal limits; the actual
ordered mixed-mass consumer then produces independent mixed-mass limits.
The varying-background/net and zero-mass scopes remain separate.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualDecreasingModelMixedMass

open FirstPass FirstPass.PositiveClasses DiagonalMass MixedMass
  GlobalMixedMassMonotone ActualMixedMassOrderedContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem contact_mass_eq_mass_of_model (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsModelPotential θ u) :
    diagonalPotentialMeasure θ u hu.plurisubharmonic {x | u x = 0} =
      diagonalPotentialMass θ u hu.plurisubharmonic := by
  have hu0 : u ≤ 0 := by
    rw [hu.envelope_eq]
    exact singularityEnvelope_le_zero θ.val u
  have hnull := RooftopMassDiamondModel.measure_lt_zero_eq_zero_of_model
    omega θ hu.plurisubharmonic hu.envelope_eq
  have hrestrict : (diagonalPotentialMeasure θ u hu.plurisubharmonic).restrict {x | u x = 0} =
      diagonalPotentialMeasure θ u hu.plurisubharmonic := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply measure_mono_null ?_ hnull
    intro x hx
    change u x ≠ 0 at hx
    exact lt_of_le_of_ne (hu0 x) hx
  have h := congrArg (fun μ : Measure M => μ univ) hrestrict
  simpa only [Measure.restrict_apply_univ, diagonalPotentialMass] using h

/-- Actual contact semicontinuity produces the diagonal mass limit of a
decreasing model sequence with a genuine positive-mass pointwise limit. -/
theorem tendsto_diagonalPotentialMass_of_antitone_model
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (u : ℕ → M → EReal) (hu : ∀ k, IsModelPotential θ (u k))
    (hanti : Antitone u) {v : M → EReal} (hv : IsThetaPshPotential θ.val v)
    (_hpos : 0 < diagonalPotentialMass θ v hv)
    (hlim : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (v x))) :
    Tendsto (fun k => diagonalPotentialMass θ (u k) (hu k).plurisubharmonic) atTop
      (𝓝 (diagonalPotentialMass θ v hv)) := by
  have hle (k : ℕ) : v ≤ u k := fun x =>
    (show Antitone (fun j => u j x) from fun a b hab => hanti hab x).le_of_tendsto
      (hlim x) k
  have hu0 (k : ℕ) : u k ≤ 0 := by
    rw [(hu k).envelope_eq]
    exact singularityEnvelope_le_zero θ.val (u k)
  have hcontact := DecreasingContactMassLimit.contactMeasure_limsup_le_of_antitone_of_tendsto
    omega θ u (fun k => (hu k).plurisubharmonic) (fun k x => hu0 k x) v hv hanti hlim
  have hfun : (fun k => diagonalPotentialMeasure θ (u k) (hu k).plurisubharmonic
      {x | u k x = 0}) = fun k => diagonalPotentialMass θ (u k) (hu k).plurisubharmonic :=
    funext fun k => contact_mass_eq_mass_of_model omega (hu k)
  rw [hfun] at hcontact
  have hlow : diagonalPotentialMass θ v hv ≤
      liminf (fun k => diagonalPotentialMass θ (u k) (hu k).plurisubharmonic) atTop :=
    le_liminf_of_le (h := Eventually.of_forall fun k =>
      diagonalPotentialMass_mono_of_kahler
      omega hv (hu k).plurisubharmonic (MoreSingularOn.of_le fun x _ => hle k x)
    )
  exact tendsto_of_le_liminf_of_limsup_le hlow
    (hcontact.trans (measure_mono (subset_univ _)))

/-- Actual diagonal limits and pointwise orders are produced from each
decreasing model sequence before the independent mixed-mass limit is derived. -/
theorem tendsto_globalMixedMass_of_antitone_model
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} (hu : ∀ k i, IsModelPotential (θ i) (u k i))
    (hanti : ∀ i, Antitone (fun k => u k i)) {v : Fin n → M → EReal}
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hpos : ∀ i, 0 < diagonalPotentialMass (θ i) (v i) (hv i))
    (hlim : ∀ i x, Tendsto (fun k => u k i x) atTop (𝓝 (v i x))) :
    Tendsto (fun k => globalMixedMass θ (u k) (fun i => (hu k i).plurisubharmonic.1)) atTop
      (𝓝 (globalMixedMass θ v (fun i => (hv i).1))) := by
  apply tendsto_globalMixedMass_of_le_of_diagonal_tendsto omega atTop hv
    (fun k i => (hu k i).plurisubharmonic)
  · intro k i x
    exact (show Antitone (fun j => u j i x) from fun a b hab => hanti i hab x).le_of_tendsto
      (hlim i x) k
  · exact hpos
  · intro i
    exact tendsto_diagonalPotentialMass_of_antitone_model omega (θ i) (fun k => u k i)
      (fun k => hu k i) (hanti i) (hv i) (hpos i) (hlim i)

end

end SGPT.Foundations.Analysis.Pending.ActualDecreasingModelMixedMass

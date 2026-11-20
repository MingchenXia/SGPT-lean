import SGPT.Foundations.Analysis.Pending.NaturalThetaPshHartogsRecovery
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedContinuity
import SGPT.Foundations.Analysis.Pending.SingularModelUniformTruncationFullMass

set_option autoImplicit false

/-! # Actual canonical local-L1 extended singular energy USC

Original canonical tails internally recover the original potential and
their extended energies. Uniform original energy lower bounds then
internally produce fullmass/E1 of the original limit via own truncations.
No limit E1, compactness, maximizer or prescribed MA certificate is assumed.
Complete mathematical blueprint and proofs preceded SOURCE.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualSingularEnergyCanonicalL1Usc

open FirstPass FirstPass.PositiveClasses DiagonalMass RelativeEnergy
  RelativeDarvasDistance RelativePreceqClasses MongeAmpereEnergyDecreasing

noncomputable section

/-- The literal original upper-regularized canonical potential tail. -/
def canonicalTailSup {M : Type*} [TopologicalSpace M]
    (u : ℕ → M → EReal) (N : ℕ) : M → EReal :=
  uscRegularization (⨆ j : ℕ, u (j + N))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ v : M → EReal}
  {hφ : IsModelPotential θ φ} {u : ℕ → M → EReal}

/-- Genuine canonical Hartogs recovery and actual extended decreasing
energy continuity produce the original tail energies without limit E1. -/
theorem canonical_tail_energy_tendsto (omega : KahlerBackground n M)
    (hu : ∀ j, RelativePSHPreceq θ φ (u j)) (hv : IsThetaPshPotential θ.val v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    {C : ℝ} (hC : ∀ j x, u j x ≤ (C : EReal)) :
    RelativePSHPreceq θ φ v ∧
    (∀ x, v x ≤ φ x + (C : EReal)) ∧
    (∀ N, IsThetaPshPotential θ.val (canonicalTailSup u N)) ∧
    (∀ N x, canonicalTailSup u N x ≤ φ x + (C : EReal)) ∧
    Antitone (canonicalTailSup u) ∧
    (⨅ N : ℕ, canonicalTailSup u N) = v ∧
    (∀ x, Tendsto (fun N : ℕ => canonicalTailSup u N x) atTop (𝓝 (v x))) ∧
    Tendsto (fun N : ℕ => energy θ φ hφ (canonicalTailSup u N)) atTop (𝓝 (energy θ φ hφ v)) ∧
    (∀ N : ℕ, energy θ φ hφ (u N) ≤ energy θ φ hφ (canonicalTailSup u N)) := by
  have hraw : ∀ j x, u j x ≤ φ x + (C : EReal) := fun j x =>
    RelativePreceqStatements.le_add_const_of_moreSingularOn_of_singularityEnvelope_eq
      (hu j).1 hφ.envelope_eq.symm (hu j).2 (hC j) x
  have hvbound : v ≤ fun x => φ x + (C : EReal) :=
    ThetaPshL1Order.le_of_manifoldL1LocallyTendsto (fun j => (hu j).1) hv
      (hφ.plurisubharmonic.add_const C) hlim hraw
  have hvφ : RelativePSHPreceq θ φ v := ⟨hv, C, fun x _ => hvbound x⟩
  obtain ⟨hU, hanti, heq, hpoint⟩ :=
    NaturalThetaPshHartogsRecovery.usc_tailSup_iInf_eq_and_tendsto
      (fun j => (hu j).1) hv hlim hC
  have hUbound : ∀ N x, canonicalTailSup u N x ≤ φ x + (C : EReal) := by
    intro N
    exact uscRegularization_le (hφ.plurisubharmonic.add_const C).1.quasiPlurisubharmonic.upperSemicontinuous
      (iSup_le fun j => hraw (j + N))
  have hU0φ : MoreSingularOn (canonicalTailSup u 0) φ univ :=
    ⟨C, fun x _ => hUbound 0 x⟩
  have hE := SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone
    omega θ hφ hU hU0φ (fun x N L hNL => hanti hNL x) hpoint
  have hdom : ∀ N, energy θ φ hφ (u N) ≤ energy θ φ hφ (canonicalTailSup u N) := by
    intro N
    apply energy_mono_of_le
    have hself : u N ≤ (⨆ j : ℕ, u (j + N)) := by
      simpa only [Nat.zero_add] using le_iSup (fun j : ℕ => u (j + N)) 0
    exact hself.trans (le_uscRegularization _)
  exact ⟨hvφ, hvbound, hU, hUbound, hanti, heq, hpoint, hE, hdom⟩

/-- Actual extended energy is internally upper semicontinuous along the
original bounded canonical local-L1 sequence, including minus infinity. -/
theorem limsup_energy_le_of_manifoldL1LocallyTendsto (omega : KahlerBackground n M)
    (hu : ∀ j, RelativePSHPreceq θ φ (u j)) (hv : IsThetaPshPotential θ.val v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    {C : ℝ} (hC : ∀ j x, u j x ≤ (C : EReal)) :
    Filter.limsup (fun j : ℕ => energy θ φ hφ (u j)) atTop ≤ energy θ φ hφ v := by
  obtain ⟨_hvφ, _hvbound, _hU, _hUbound, _hanti, _heq, _hpoint, hE, hdom⟩ :=
    canonical_tail_energy_tendsto (hφ := hφ) omega hu hv hlim hC
  have h := Filter.limsup_le_limsup (f := atTop) (Eventually.of_forall hdom)
  rwa [hE.limsup_eq] at h

/-- Uniform actual extended-energy lower bounds internally produce
full mass and E1 of the original canonical local-L1 limit by own truncations. -/
theorem relativeFiniteEnergy_of_manifoldL1LocallyTendsto_of_uniform_energy_lower
    (omega : KahlerBackground n M)
    (hu : ∀ j, RelativePSHPreceq θ φ (u j)) (hv : IsThetaPshPotential θ.val v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    (hu0 : ∀ j x, u j x ≤ 0) {L : ℝ}
    (hL : ∀ j : ℕ, (L : EReal) ≤ energy θ φ hφ (u j)) :
    (∀ x, v x ≤ φ x) ∧ (L : EReal) ≤ energy θ φ hφ v ∧
      RelativeFiniteEnergy θ φ v hφ := by
  obtain ⟨_hvφ, hvbound, _hU, _hUbound, _hanti, _heq, _hpoint, hE, hdom⟩ :=
    canonical_tail_energy_tendsto (hφ := hφ) omega hu hv hlim
      (C := 0) (by simpa only [EReal.coe_zero] using hu0)
  have hvle : v ≤ φ := by
    intro x
    simpa only [EReal.coe_zero, add_zero] using hvbound x
  have hEv : (L : EReal) ≤ energy θ φ hφ v :=
    ge_of_tendsto' hE fun N => (hL N).trans (hdom N)
  have htrunc : ∀ j : ℕ, L ≤ relativeEnergyOfMinimalType θ φ
      (truncation φ v j) hφ.plurisubharmonic
      (SingularModelEnergyTruncation.relativeEInfinity_truncation hφ.plurisubharmonic hv
        (MoreSingularOn.of_le fun x _ => hvle x) j).1 := by
    intro j
    have hty := SingularModelEnergyTruncation.relativeEInfinity_truncation
      hφ.plurisubharmonic hv (MoreSingularOn.of_le fun x _ => hvle x) j
    have hletrunc : v ≤ truncation φ v j := fun x => le_max_left (v x) _
    have hh := hEv.trans (energy_mono_of_le hletrunc)
    rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ hty] at hh
    exact EReal.coe_le_coe_iff.mp hh
  exact ⟨hvle, hEv,
    SingularModelUniformTruncationFullMass.relativeFiniteEnergy_of_uniform_truncation_energy_lower
      omega hv hvle htrunc⟩

end

end SGPT.Foundations.Analysis.Pending.ActualSingularEnergyCanonicalL1Usc

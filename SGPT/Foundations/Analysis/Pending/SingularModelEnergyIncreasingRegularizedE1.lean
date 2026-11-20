import SGPT.Foundations.Analysis.Pending.SingularModelEnergyUniformTruncationTail
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingRegularizedContinuity
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondEnvelopeMax

set_option autoImplicit false

/-!
# Actual increasing E1 energy at genuine regularized suprema

Xia SGPT PDF0127--0128. The actual uniform truncation tail and genuine
finite-type regularized continuity produce the actual normalized E1 limit.
No pointwise convergence or same-type premise on the sequence is used.
Chart almost-everywhere and directed-net bridges remain separate producers.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingRegularizedE1

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
open RelativePreceqClasses MongeAmpereEnergyDecreasing
open SingularModelEnergyTruncation SingularModelEnergyUniformTruncationTail
open SingularModelEnergyIncreasingRegularizedContinuity SingularModelFiniteRealEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual real model energy is continuous along regularized increasing
normalized E1 sequences, without a same-type assumption on the sequence. -/
theorem toReal_energy_tendsto_of_monotone_regularized (omega : KahlerBackground n M)
    {u : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergy θ φ (u j) hφ)
    (hv : RelativeFiniteEnergy θ φ v hφ)
    (hm : ∀ x, Monotone fun j => u j x)
    (hreg : uscRegularization (⨆ j, u j) = v) :
    Tendsto (fun j => (energy θ φ hφ (u j)).toReal) atTop
      (𝓝 (energy θ φ hφ v).toReal) := by
  have huv : ∀ j, u j ≤ v := fun j x =>
    (le_iSup (fun k => u k) j x).trans (by rw [← hreg]; exact le_uscRegularization _ x)
  have hT (j C : ℕ) := relativeEInfinity_truncation hφ.plurisubharmonic
    (hu j).1.plurisubharmonic (preceq_of_relativePSH (hu j).1.relativePSH).2 C
  have hV (C : ℕ) := relativeEInfinity_truncation hφ.plurisubharmonic
    hv.1.plurisubharmonic (preceq_of_relativePSH hv.1.relativePSH).2 C
  have hVE1 (C : ℕ) : RelativeFiniteEnergyPreceq θ φ (truncation φ v C) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega (hV C)
  have hCconv (C : ℕ) :
      Tendsto (fun j => (energy θ φ hφ (truncation φ (u j) C)).toReal)
        atTop (𝓝 (energy θ φ hφ (truncation φ v C)).toReal) := by
    have hmC : ∀ x, Monotone fun j => truncation φ (u j) C x :=
      fun x j k hjk => max_le_max (hm x hjk) le_rfl
    have hCreg : uscRegularization (⨆ j, truncation φ (u j) C) = truncation φ v C := by
      have hsup : (⨆ j, truncation φ (u j) C) =
          fun x => max ((⨆ j, u j) x) (φ x - ((C : ℝ) : EReal)) := by
        funext x
        simp only [truncation, iSup_apply]
        exact iSup_sup.symm
      rw [hsup, uscRegularization_max, hreg,
        uscRegularization_eq
          (hφ.plurisubharmonic.sub_const (C : ℝ)).1.quasiPlurisubharmonic.upperSemicontinuous]
      rfl
    have h := energy_tendsto_of_monotone_regularized_sameType omega θ hφ
      (hV C).1 (hV C).2 (fun j => (hT j C).1) (hT 0 C).2 hmC hCreg
    exact (EReal.tendsto_toReal
      (energy_ne_top_of_preceq (hVE1 C).1.relativePSHPreceq)
      (SingularModelFiniteEnergyPreceq.bot_lt_energy omega (hVE1 C)).ne').comp h
  apply tendsto_order.2
  constructor
  · intro a ha
    let ε := (energy θ φ hφ v).toReal - a
    have hε : 0 < ε := sub_pos.mpr ha
    obtain ⟨C, hC⟩ := uniform_energy_truncation_error_of_monotone omega hu hm 0
      (half_pos hε)
    have hupper : (energy θ φ hφ v).toReal ≤
        (energy θ φ hφ (truncation φ v C)).toReal :=
      toReal_energy_mono omega (preceq_of_relativeFiniteEnergy hv) (hVE1 C)
        (fun x => le_max_left _ _)
    have hclose := (hCconv C).eventually_const_lt
      (show (energy θ φ hφ (truncation φ v C)).toReal - ε / 2 <
        (energy θ φ hφ (truncation φ v C)).toReal by linarith)
    filter_upwards [hclose] with j hj
    have herr := hC C le_rfl j (Nat.zero_le j)
    have herr' := (le_abs_self
      ((energy θ φ hφ (truncation φ (u j) C)).toReal -
        (energy θ φ hφ (u j)).toReal)).trans_lt herr
    dsimp only [ε] at herr' hj
    linarith
  · intro b hb
    exact Eventually.of_forall fun j => lt_of_le_of_lt
      (toReal_energy_mono omega (preceq_of_relativeFiniteEnergy (hu j))
        (preceq_of_relativeFiniteEnergy hv) (huv j)) hb

/-- The actual extended energies of the same genuine regularized increasing
E1 sequence converge by the produced finite-energy realification. -/
theorem energy_tendsto_of_monotone_regularized (omega : KahlerBackground n M)
    {u : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergy θ φ (u j) hφ)
    (hv : RelativeFiniteEnergy θ φ v hφ)
    (hm : ∀ x, Monotone fun j => u j x)
    (hreg : uscRegularization (⨆ j, u j) = v) :
    Tendsto (fun j => energy θ φ hφ (u j)) atTop (𝓝 (energy θ φ hφ v)) := by
  have h := EReal.tendsto_coe.mpr (toReal_energy_tendsto_of_monotone_regularized omega hu hv hm hreg)
  have he (j : ℕ) := SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (preceq_of_relativeFiniteEnergy (hu j))
  have hev := SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (preceq_of_relativeFiniteEnergy hv)
  simpa only [he, hev] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingRegularizedE1

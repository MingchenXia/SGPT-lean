import SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalFoundation
import SGPT.Foundations.Analysis.Pending.ActualSingularEnergyCanonicalL1Usc
import SGPT.Foundations.Analysis.Pending.ActualCanonicalL1SmoothVolumeIntegralContinuity

set_option autoImplicit false

/-! # Actual variational optimality of a genuine canonical L1 limit

Original sequence, original genuine canonical L1 limit, actual energy and
smooth-volume functional. Limit E1 and normalization are internally produced.
No compactness, abstract gluing, optimizer or prescribed-measure certificate.
This analytic sequence-limit implication is not unconditional existence.
Complete mathematical statements and proofs preceded substantive SOURCE.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalLimitMaximizer

open FirstPass FirstPass.PositiveClasses DiagonalMass RelativeEnergy
  RelativeDarvasDistance RelativePreceqClasses ActualSmoothVolumeVariationalFoundation IntegrationCurrent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ v : M → EReal}
  {hφ : IsModelPotential θ φ} {u : ℕ → M → EReal} {A L : ℝ}

/-- Actual canonical L1 convergence and genuine real energy lower bounds
internally produce limit E1 and the true functional maximizing inequality. -/
theorem le_functional_of_manifoldL1LocallyTendsto
    (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ)
    (hu0 : ∀ j x, u j x ≤ 0) (hv : IsThetaPshPotential θ.val v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    (hA : ∀ j, A ≤ (energy θ φ hφ (u j)).toReal)
    (hF : Tendsto (fun j => smoothVolumeFunctional omega θ φ hφ (u j)) atTop (𝓝 L)) :
    (∀ x, v x ≤ φ x) ∧ RelativeFiniteEnergyPreceq θ φ v hφ ∧
      L ≤ smoothVolumeFunctional omega θ φ hφ v := by
  have huP : ∀ j, RelativePSHPreceq θ φ (u j) := fun j => (hu j).1.relativePSHPreceq
  have hAext : ∀ j, (A : EReal) ≤ energy θ φ hφ (u j) := by
    intro j
    rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hu j)]
    exact EReal.coe_le_coe_iff.mpr (hA j)
  obtain ⟨hvφ, _hElower, hvF⟩ :=
    ActualSingularEnergyCanonicalL1Usc.relativeFiniteEnergy_of_manifoldL1LocallyTendsto_of_uniform_energy_lower
      omega huP hv hlim hu0 hAext
  have hvPre : RelativeFiniteEnergyPreceq θ φ v hφ := preceq_of_relativeFiniteEnergy hvF
  obtain ⟨_huI, _hvI, hI⟩ :=
    ActualCanonicalL1SmoothVolumeIntegralContinuity.integrable_and_integral_toReal_tendsto_of_manifoldL1LocallyTendsto
      (kahlerVolume omega) (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
      θ.val (fun j => (hu j).1.plurisubharmonic) hv hlim
  have hEreal : Tendsto (fun j => (energy θ φ hφ (u j)).toReal) atTop
      (𝓝 (L + smoothVolumeCoefficient omega θ φ hφ *
        (∫ x, (v x).toReal ∂kahlerVolume omega))) := by
    have hc : Tendsto (fun _j : ℕ => smoothVolumeCoefficient omega θ φ hφ) atTop
        (𝓝 (smoothVolumeCoefficient omega θ φ hφ)) := tendsto_const_nhds
    have hh := hF.add (hc.mul hI)
    have hid : (fun j => smoothVolumeFunctional omega θ φ hφ (u j) +
        smoothVolumeCoefficient omega θ φ hφ * (∫ x, (u j x).toReal ∂kahlerVolume omega)) =
        (fun j => (energy θ φ hφ (u j)).toReal) := by
      funext j
      unfold smoothVolumeFunctional
      ring
    rw [hid] at hh
    exact hh
  have hEext : Tendsto (fun j => energy θ φ hφ (u j)) atTop
      (𝓝 ((L + smoothVolumeCoefficient omega θ φ hφ *
        (∫ x, (v x).toReal ∂kahlerVolume omega) : ℝ) : EReal)) := by
    have hh := EReal.tendsto_coe.mpr hEreal
    have hid : (fun j => ((energy θ φ hφ (u j)).toReal : EReal)) =
        (fun j => energy θ φ hφ (u j)) := by
      funext j
      exact SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hu j)
    rw [hid] at hh
    exact hh
  have hUSC := ActualSingularEnergyCanonicalL1Usc.limsup_energy_le_of_manifoldL1LocallyTendsto
    (hφ := hφ) omega huP hv hlim (C := 0) (by simpa only [EReal.coe_zero] using hu0)
  rw [hEext.limsup_eq, ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hvPre] at hUSC
  have hreal := EReal.coe_le_coe_iff.mp hUSC
  refine ⟨hvφ, hvPre, ?_⟩
  unfold smoothVolumeFunctional
  linarith

/-- A genuine canonical L1 maximizing-sequence limit internally yields
an actual normalized original optimizer; existence of that limit is explicit. -/
theorem exists_normalized_optimum_of_manifoldL1LocallyTendsto
    (omega : KahlerBackground n M)
    (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ)
    (hu0 : ∀ j x, u j x ≤ 0) (hv : IsThetaPshPotential θ.val v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u atTop v)
    (hA : ∀ j, A ≤ (energy θ φ hφ (u j)).toReal)
    (hF : Tendsto (fun j => smoothVolumeFunctional omega θ φ hφ (u j)) atTop (𝓝 L))
    (hupper : ∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
      smoothVolumeFunctional omega θ φ hφ a ≤ L) :
    smoothVolumeFunctional omega θ φ hφ v = L ∧
      ∃ b : ℝ,
        RelativeFiniteEnergyPreceq θ φ (fun x => v x + (b : EReal)) hφ ∧
        (⨆ x, v x + (b : EReal)) = 0 ∧
        (∀ x, v x + (b : EReal) ≤ φ x) ∧
        smoothVolumeFunctional omega θ φ hφ (fun x => v x + (b : EReal)) = L ∧
        (∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
          smoothVolumeFunctional omega θ φ hφ a ≤
            smoothVolumeFunctional omega θ φ hφ (fun x => v x + (b : EReal))) := by
  obtain ⟨_hvφ, hvF, hL⟩ := le_functional_of_manifoldL1LocallyTendsto omega hu hu0 hv hlim hA hF
  have heq : smoothVolumeFunctional omega θ φ hφ v = L := le_antisymm (hupper v hvF) hL
  obtain ⟨b, hwF, hw0, hwφ, hwvalue, _hwpoint⟩ := exists_normalized_translate omega hvF
  have hwL : smoothVolumeFunctional omega θ φ hφ (fun x => v x + (b : EReal)) = L :=
    hwvalue.trans heq
  refine ⟨heq, b, hwF, hw0, hwφ, hwL, ?_⟩
  intro a ha
  rw [hwL]
  exact hupper a ha

end

end SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalLimitMaximizer

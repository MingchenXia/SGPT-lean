import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCappedGap

set_option autoImplicit false

/-!
# Finite-energy characterization within a singular model's full-mass class

Xia SGPT PDF0121--0122, Proposition 3.1.17. Actual same-type truncation
energy bounds, actual full-mass gap transfer, and monotone convergence
characterize finite canonical gap integral by energy greater than negative
infinity. Full mass is the source domain; no finite-energy-to-full-mass
implication is asserted here.
-/

open Set Filter MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativeEnergyIntegrability SingularModelEnergyTruncation
  SingularModelEnergyEndpointBounds SingularModelEnergyTruncationGap
  SingularModelEnergyCappedGap SingularModelEnergyCocycle
  GlobalNonPluripolar DiagonalMass MongeAmpereEnergyDecreasing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual canonical positive gap integrals bound both sides of a genuine
same-type truncation's finite energy, including a singular reference. -/
theorem neg_energy_le_integral_gap_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hule : u ≤ φ) (j : ℕ) :
    -relativeEnergyOfMinimalType θ φ (truncation φ u j) hφ
      (relativeEInfinity_truncation hφ hu
        (MoreSingularOn.of_le fun x _ => hule x) j).1 ≤
        ∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
          ∂diagonalPotentialMeasure θ (truncation φ u j)
            (relativeEInfinity_truncation hφ hu
              (MoreSingularOn.of_le fun x _ => hule x) j).1 ∧
    (∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
      ∂diagonalPotentialMeasure θ (truncation φ u j)
        (relativeEInfinity_truncation hφ hu
          (MoreSingularOn.of_le fun x _ => hule x) j).1) ≤
      -(((n : ℝ) + 1) * relativeEnergyOfMinimalType θ φ (truncation φ u j) hφ
        (relativeEInfinity_truncation hφ hu
          (MoreSingularOn.of_le fun x _ => hule x) j).1) := by
  let huφ : MoreSingularOn u φ univ := MoreSingularOn.of_le fun x _ => hule x
  let htj := relativeEInfinity_truncation hφ hu huφ j
  have hs : (∫ x, canonicalERealDiffToReal (truncation φ u j x) (φ x)
      ∂diagonalPotentialMeasure θ (truncation φ u j) htj.1) =
      -(∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
        ∂diagonalPotentialMeasure θ (truncation φ u j) htj.1) := by
    rw [← integral_neg]
    congr 1
    funext x
    exact canonicalERealDiffToReal_swap _ _
  have h1 := integral_le_energy omega θ hφ htj.1 htj.2
  have h2 := energy_mul_le_integral omega θ hφ htj.1 htj.2
    (FiniteEnergyCharacterization.truncation_le hule j)
  rw [hs] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- Within the actual full-mass class, the canonical gap lower integral is
finite exactly when the defining extended energy is greater than negative infinity. -/
theorem relativeFiniteEnergyIntegral_lt_top_iff_bot_lt_energy
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ u : M → EReal} (hφ : IsModelPotential θ φ)
    (hfull : RelativeFullMass θ φ u hφ) :
    relativeFiniteEnergyIntegral θ φ u hfull.plurisubharmonic < ⊤ ↔
      ⊥ < energy θ φ hφ u := by
  let hu := hfull.plurisubharmonic
  let hule := hfull.le_reference
  let huφ : MoreSingularOn u φ univ := MoreSingularOn.of_le fun x _ => hule x
  let htj := fun j => relativeEInfinity_truncation hφ.plurisubharmonic hu huφ j
  let E := fun j => relativeEnergyOfMinimalType θ φ (truncation φ u j)
    hφ.plurisubharmonic (htj j).1
  let I := fun j => ∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
    ∂diagonalPotentialMeasure θ u hu
  have hb (j : ℕ) : -E j ≤ I j ∧ I j ≤ -(((n : ℝ) + 1) * E j) := by
    have h := neg_energy_le_integral_gap_le omega θ hφ.plurisubharmonic hu hule j
    rw [integral_canonicalDiff_truncation_eq omega θ hφ hfull j] at h
    exact h
  have hE : energy θ φ hφ u = ⨅ j, (E j : EReal) :=
    energy_eq_iInf_truncation omega θ hφ hu huφ
  have hI : relativeFiniteEnergyIntegral θ φ u hu = ⨆ j, ENNReal.ofReal (I j) :=
    relativeFiniteEnergyIntegral_eq_iSup_integral omega θ hφ.plurisubharmonic hu hule
  constructor
  · intro hfin
    have hbound (j : ℕ) : I j ≤ (relativeFiniteEnergyIntegral θ φ u hu).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp
        (hI ▸ le_iSup (fun j => ENNReal.ofReal (I j)) j)
    rw [hE]
    refine lt_of_lt_of_le (EReal.bot_lt_coe
      (-(relativeFiniteEnergyIntegral θ φ u hu).toReal)) (le_iInf fun j => ?_)
    exact EReal.coe_le_coe_iff.mpr (by linarith [(hb j).1, hbound j])
  · intro hbot
    have htop : energy θ φ hφ u ≠ ⊤ :=
      RelativePreceqClasses.energy_ne_top_of_preceq ⟨hu, huφ⟩
    let e := (energy θ φ hφ u).toReal
    have he : energy θ φ hφ u = (e : EReal) := (EReal.coe_toReal htop hbot.ne').symm
    have hbelow (j : ℕ) : e ≤ E j := by
      apply EReal.coe_le_coe_iff.mp
      rw [← he, hE]
      exact iInf_le _ j
    rw [hI]
    refine lt_of_le_of_lt (b := ENNReal.ofReal (-(((n : ℝ) + 1) * e)))
      (iSup_le fun j => ENNReal.ofReal_le_ofReal ?_)
      ENNReal.ofReal_lt_top
    have hnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    have h := mul_le_mul_of_nonneg_left (hbelow j) hnonneg
    linarith [(hb j).2]

/-- Xia's finite-energy characterization for an arbitrary singular model
reference, on the normalized full-mass source domain. -/
theorem relativeFiniteEnergy_iff_bot_lt_energy (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) (hfull : RelativeFullMass θ φ u hφ) :
    RelativeFiniteEnergy θ φ u hφ ↔ ⊥ < energy θ φ hφ u := by
  have hiff := relativeFiniteEnergyIntegral_lt_top_iff_bot_lt_energy omega θ hφ hfull
  constructor
  · rintro ⟨_, hu, hfin⟩
    exact hiff.mp hfin
  · intro hbot
    exact ⟨hfull, hfull.plurisubharmonic, hiff.mpr hbot⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergy

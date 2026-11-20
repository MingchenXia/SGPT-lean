import SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncationGap

set_option autoImplicit false

/-!
# Actual monotone canonical gap integrals for singular references

Xia SGPT PDF0121--0122, Proposition 3.1.17. The pole-safe canonical gaps
of genuine truncations are actual caps of the canonical absolute gap.
Monotone convergence against the actual fixed diagonal measure identifies
the finite-energy lower integral with the supremum of real gap integrals.
-/

open Set Filter MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyCappedGap

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativeEnergyIntegrability SingularModelEnergyTruncation
  SingularModelEnergyEndpointBounds GlobalNonPluripolar DiagonalMass
  MongeAmpereEnergyDecreasing

noncomputable section

/-- The pole-safe truncation gap is precisely the finite cap of the absolute gap. -/
theorem ofReal_canonicalDiff_truncation_eq_min {X : Type*} {φ u : X → EReal}
    (hφ : ∀ x, φ x ≠ ⊤) (hu : ∀ x, u x ≠ ⊤) (hule : u ≤ φ) (j : ℕ) (x : X) :
    ENNReal.ofReal (canonicalERealDiffToReal (φ x) (truncation φ u j x)) =
      min (ENNReal.ofReal (j : ℝ)) (canonicalERealAbsDiff (φ x) (u x)) := by
  by_cases hpb : φ x = ⊥
  · have hub : u x = ⊥ := bot_unique (hpb ▸ hule x)
    simp [truncation, hpb, hub]
  · rw [← EReal.coe_toReal (hφ x) hpb]
    by_cases hub : u x = ⊥
    · rw [hub, canonicalERealAbsDiff_bot_right (EReal.coe_ne_bot _), min_top_right]
      change ENNReal.ofReal (canonicalERealDiffToReal ((φ x).toReal : EReal)
        (max (u x) (φ x - ((j : ℝ) : EReal)))) = _
      rw [hub, ← EReal.coe_toReal (hφ x) hpb, ← EReal.coe_sub,
        max_eq_right bot_le, canonicalERealDiffToReal_coe_coe]
      simp only [EReal.toReal_coe]
      congr 1
      ring
    · rw [← EReal.coe_toReal (hu x) hub]
      have horder : (u x).toReal ≤ (φ x).toReal :=
        EReal.toReal_le_toReal (hule x) hub (hφ x)
      rw [canonicalERealAbsDiff_coe_coe, abs_of_nonneg (sub_nonneg.mpr horder)]
      change ENNReal.ofReal (canonicalERealDiffToReal ((φ x).toReal : EReal)
        (max (u x) (φ x - ((j : ℝ) : EReal)))) = _
      rw [← EReal.coe_toReal (hu x) hub, ← EReal.coe_toReal (hφ x) hpb, ← EReal.coe_sub]
      simp only [EReal.toReal_coe]
      by_cases hc : (u x).toReal ≤ (φ x).toReal - (j : ℝ)
      · rw [max_eq_right (EReal.coe_le_coe_iff.mpr hc), canonicalERealDiffToReal_coe_coe,
          min_eq_left (ENNReal.ofReal_le_ofReal (by linarith))]
        congr 1
        ring
      · rw [max_eq_left (EReal.coe_le_coe_iff.mpr (le_of_not_ge hc)),
          canonicalERealDiffToReal_coe_coe,
          min_eq_right (ENNReal.ofReal_le_ofReal (by linarith))]

/-- The increasing finite caps recover the canonical absolute gap, including poles. -/
theorem iSup_ofReal_canonicalDiff_truncation {X : Type*} {φ u : X → EReal}
    (hφ : ∀ x, φ x ≠ ⊤) (hu : ∀ x, u x ≠ ⊤) (hule : u ≤ φ) (x : X) :
    (⨆ j : ℕ, ENNReal.ofReal (canonicalERealDiffToReal (φ x) (truncation φ u j x))) =
      canonicalERealAbsDiff (φ x) (u x) := by
  simp only [ofReal_canonicalDiff_truncation_eq_min hφ hu hule, ENNReal.ofReal_natCast]
  apply iSup_eq_of_tendsto
  · intro i j hij
    exact min_le_min (Nat.cast_le.mpr hij) le_rfl
  · simpa only [min_top_left] using
      ENNReal.tendsto_nat_nhds_top.min (tendsto_const_nhds (x := canonicalERealAbsDiff (φ x) (u x)))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual finite-energy lower integral is the supremum of actual, integrable
canonical truncation-gap integrals against the fixed genuine endpoint measure. -/
theorem relativeFiniteEnergyIntegral_eq_iSup_integral (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hule : u ≤ φ) :
    relativeFiniteEnergyIntegral θ φ u hu =
      ⨆ j : ℕ, ENNReal.ofReal (∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
        ∂diagonalPotentialMeasure θ u hu) := by
  let huφ : MoreSingularOn u φ univ := MoreSingularOn.of_le fun x _ => hule x
  let htj := fun j => relativeEInfinity_truncation hφ hu huφ j
  let g := fun j x => canonicalERealDiffToReal (φ x) (truncation φ u j x)
  let μ := diagonalPotentialMeasure θ u hu
  have hgint (j : ℕ) : Integrable (g j) μ :=
    integrable_canonicalDiff_globalMixedMeasure omega hφ.1 (htj j).1.1
      (htj j).2.symm (fun _ => hu.1)
  have hgnn (j : ℕ) (x : M) : 0 ≤ g j x := by
    have h := canonicalDiff_nonpos_of_le_of_sameType
      (htj j).1.1.quasiPlurisubharmonic.ne_top hφ.1.quasiPlurisubharmonic.ne_top
      (htj j).2 (FiniteEnergyCharacterization.truncation_le hule j) x
    dsimp only [g]
    rw [canonicalERealDiffToReal_swap]
    linarith
  have hgm (j : ℕ) : Measurable (fun x => ENNReal.ofReal (g j x)) :=
    (measurable_canonicalERealDiffToReal.comp
      ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hφ.1).prodMk
        (GlobalSlotComparison.ThetaPlurisubharmonic.measurable (htj j).1.1))).ennreal_ofReal
  have hgmono : Monotone (fun j x => ENNReal.ofReal (g j x)) := by
    intro i j hij x
    dsimp only [g]
    simp only [ofReal_canonicalDiff_truncation_eq_min
      hφ.1.quasiPlurisubharmonic.ne_top hu.1.quasiPlurisubharmonic.ne_top hule]
    exact min_le_min (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hij)) le_rfl
  change (∫⁻ x, canonicalERealAbsDiff (φ x) (u x) ∂μ) = _
  calc
    _ = ∫⁻ x, ⨆ j : ℕ, ENNReal.ofReal (g j x) ∂μ := by
      congr 1
      funext x
      exact (iSup_ofReal_canonicalDiff_truncation
        hφ.1.quasiPlurisubharmonic.ne_top hu.1.quasiPlurisubharmonic.ne_top hule x).symm
    _ = ⨆ j : ℕ, ∫⁻ x, ENNReal.ofReal (g j x) ∂μ := lintegral_iSup hgm hgmono
    _ = ⨆ j : ℕ, ENNReal.ofReal (∫ x, g j x ∂μ) := by
      congr 1
      funext j
      exact (ofReal_integral_eq_lintegral_ofReal (hgint j)
        (Eventually.of_forall (hgnn j))).symm

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyCappedGap

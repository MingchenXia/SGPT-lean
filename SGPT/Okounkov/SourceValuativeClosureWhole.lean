import SGPT.Okounkov.SourceValuativeKahlerApproximation
import SGPT.Okounkov.ValuativeTestCurve
import SGPT.Foundations.Analysis.Pending.PositiveMassCurrentBelow
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceValuativeClosure
open Set Filter MeasureTheory
open scoped Topology Pointwise ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending DiagonalMass ThetaPshConvexCombination
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.PartialBody SGPT.Okounkov.Valuative

/-- Original comparison sets are monotone under actual I-order. -/
theorem valuationsBelow_mono_of_iOrder {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) {u v : F.carrier → EReal}
    (hI : IOrderOnManifold (n := m + 1) u v) :
    valuationsBelow F θ u ⊆ valuationsBelow F θ v := by
  rintro _ ⟨ψ, hψ, hψu, hx⟩
  exact ⟨ψ, hψ, hψu.trans hI, hx⟩

/-- POSITIVE ORIGINAL I-volume, not original NPP mass, internally makes
the actual class big through the genuine positive-mass I-envelope reader. -/
theorem isBig_of_positive_iVolume {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hpos : letI : MeasurableSpace F.carrier := borel F.carrier
      haveI : BorelSpace F.carrier := ⟨rfl⟩
      letI : Nonempty F.carrier := PartialBody.nonempty_carrier F
      0 < iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ) :
    SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  obtain ⟨u, hu, _hI, hpu⟩ := exists_positive_mass_iEquivalent_reader F hφ hpos
  exact (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr
    (BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos
      (Nat.succ_pos m) F.omega θ hu hpu)

/-- Whole eq:DeltaTequalallval, on the EXACT original positive-I-volume
domain. No positive original NPP mass, prescribed valuation, reader,
approximation, volume convergence or dS certificate is supplied. -/
theorem generalPartialBody_eq_closure_valuationsBelow {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hpos : letI : MeasurableSpace F.carrier := borel F.carrier
      haveI : BorelSpace F.carrier := ⟨rfl⟩
      letI : Nonempty F.carrier := PartialBody.nonempty_carrier F
      0 < iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ) :
    generalPartialBody F θ φ = closure (valuationsBelow F θ φ) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  have hbig := isBig_of_positive_iVolume F hφ hpos
  have hbigN := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  obtain ⟨u, hu, hI, hpu⟩ := exists_positive_mass_iEquivalent_reader F hφ hpos
  have hbody := generalPartialBody_eq_of_iEquivalent F hφ hu hbig hI
  have hsets := valuationsBelow_eq_of_iEquivalent F θ hI
  rw [hbody, hsets]
  refine Subset.antisymm ?_ (closure_valuationsBelow_subset_generalPartialBody F hu hbig)
  obtain ⟨δ, hδ, s, hstrict, hsu⟩ :=
    PositiveMassCurrentBelow.exists_strict_thetaPsh_potential_le F.omega θ hbigN hu hpu
  have hs : IsThetaPshPotential θ.val s := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hstrict
      (KahlerDomination.isSemipositive_smul F.omega.isSemipositive hδ.le)
    simpa only [sub_add_cancel] using h
  let q : ℕ → ℚ := fun j => 1 - ((j : ℚ) + 2)⁻¹
  have hq0 (j : ℕ) : 0 < q j := by
    have hi : ((j : ℚ) + 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j; linarith)
    exact sub_pos.mpr hi
  have hq1 (j : ℕ) : q j < 1 := by
    have hi : (0 : ℚ) < ((j : ℚ) + 2)⁻¹ := by positivity
    dsimp only [q]
    linarith
  have hqR0 (j : ℕ) : (0 : ℝ) < q j := by exact_mod_cast hq0 j
  have hqR1 (j : ℕ) : (q j : ℝ) < 1 := by exact_mod_cast hq1 j
  have hqcast (j : ℕ) : (q j : ℝ) = 1 - ((j : ℝ) + 2)⁻¹ := by
    dsimp only [q]
    push_cast
    ring
  have hqLim : Tendsto (fun j => (q j : ℝ)) atTop (𝓝 1) := by
    simp_rw [hqcast]
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_zero] using hc.sub sourceCurrentMinorant_weight_tendsto
  have hKM (j : ℕ) : IsKahlerCurrentPotential θ (convexComb (q j : ℝ) u s) := by
    have hu0 : IsThetaPshPotential (θ - (0 : ℝ) • F.omega.form).val u := by
      simpa only [zero_smul, sub_zero] using hu
    have hlow := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul
      F.omega (hqR0 j) (hqR1 j) hu0 hstrict
    refine ⟨KahlerBackground.smul (mul_pos (sub_pos.mpr (hqR1 j)) hδ) F.omega, ?_⟩
    simpa only [KahlerBackground.smul_form, mul_zero, zero_add] using hlow
  have hMle (j : ℕ) : convexComb (q j : ℝ) u s ≤ u := by
    have hself : convexComb (q j : ℝ) u u = u := by
      funext y
      dsimp only [convexComb]
      rw [SGPT.Okounkov.TranscendentalDensity.ereal_add_smul_self (hqR0 j).le (sub_nonneg.mpr (hqR1 j).le),
        show (q j : ℝ) + (1 - (q j : ℝ)) = 1 by ring, EReal.coe_one, one_mul]
    have h := convexComb_mono (hqR0 j).le (hqR1 j).le (le_refl u) hsu
    rwa [hself] at h
  intro x hx
  let z := flagValuation F s
  have hz : z ∈ generalPartialBody F θ s :=
    SourceCurrentValuation.flagValuation_mem_generalPartialBody F hs
  have hmem (j : ℕ) : (q j : ℝ) • x + (1 - (q j : ℝ)) • z ∈
      closure (valuationsBelow F θ u) := by
    have hmix := convexComb_mem_generalPartialBody hu hs (hq0 j) (hq1 j) hx hz
    rw [generalPartialBody_eq_closure_valuationsBelow_of_kahler F (hKM j)] at hmix
    exact closure_mono (valuationsBelow_mono_of_iOrder F θ
      (iOrderOnManifold_of_le hu.1.quasiPlurisubharmonic (hMle j))) hmix
  have hcont : Continuous (fun a : ℝ => a • x + (1 - a) • z) := by fun_prop
  have hlim : Tendsto (fun j => (q j : ℝ) • x + (1 - (q j : ℝ)) • z) atTop (𝓝 x) := by
    simpa only [Function.comp_def, sub_self, one_smul, zero_smul, add_zero] using
      (hcont.tendsto 1).comp hqLim
  exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall hmem)

/-- WHOLE original thm:Deltapartialint: BOTH complete printed formulas,
exact original positive-I-volume currents and arbitrary REAL valuation
points, all source dimensions, no target-shaped additional assumptions. -/
theorem source_Deltapartialint {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hpos : letI : MeasurableSpace F.carrier := borel F.carrier
      haveI : BorelSpace F.carrier := ⟨rfl⟩
      letI : Nonempty F.carrier := PartialBody.nonempty_carrier F
      0 < iVolume θ (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ) :
    generalPartialBody F θ φ = closure (valuationsBelow F θ φ) ∧
      tradOkounkovBody F θ = closure (classValuations F θ) :=
  ⟨generalPartialBody_eq_closure_valuationsBelow F hφ hpos,
    tradOkounkovBody_eq_closure_classValuations F θ (isBig_of_positive_iVolume F hφ hpos)⟩

end SGPT.Okounkov.SourceValuativeClosure

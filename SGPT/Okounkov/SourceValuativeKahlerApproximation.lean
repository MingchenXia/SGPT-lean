import SGPT.Okounkov.SourceValuativeMixtureOrder

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceValuativeClosure
open Set Filter Metric MeasureTheory
open scoped Topology Pointwise ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending DiagonalMass ThetaPshConvexCombination
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.PartialBody SGPT.Okounkov.Valuative
open SGPT.Okounkov.TranscendentalBody

/-- An actual source-current witness arbitrarily close to ANY original
REAL body point. Its actual QEA, mass limits, affine barrier, global bound
and current mixture are all manufactured from the original Kähler input. -/
theorem exists_valuationBelow_close_of_kahler {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ) {x : Fin (m + 1) → ℝ}
    (hx : x ∈ generalPartialBody F θ φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : F.carrier → EReal, ∃ _hψ : IsThetaPshPotential θ.val ψ,
      IOrderOnManifold (n := m + 1) ψ φ ∧ dist (flagValuation F ψ) x < ε := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  have hφ := isThetaPshPotential_of_isKahlerCurrentPotential hK
  have hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr
      (isBigClass_of_isKahlerCurrentPotential hK)
  obtain ⟨B, hB⟩ := (isCompact_tradOkounkovBody (F := F) θ).isBounded.exists_norm_le
  let C : ℝ := 2 * max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hdiam {y z : Fin (m + 1) → ℝ} (hy : y ∈ tradOkounkovBody F θ)
      (hz : z ∈ tradOkounkovBody F θ) : dist y z ≤ C := by
    calc
      dist y z = ‖y - z‖ := dist_eq_norm _ _
      _ ≤ ‖y‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ C := by dsimp [C]; linarith [hB y hy, hB z hz, le_max_left B 0]
  let a : ℝ := 2 * (C + 1) / ε + 2
  have ha : 1 < a := by
    have hp : 0 < 2 * (C + 1) / ε := div_pos (by linarith) hε
    dsimp [a]
    linarith
  have ha0 : 0 < a := zero_lt_one.trans ha
  let t : ℝ := a⁻¹
  have ht0 : 0 < t := inv_pos.mpr ha0
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ ha
  have htC : t * C < ε / 2 := by
    have hm : ε * a = 2 * (C + 1) + 2 * ε := by
      dsimp [a]
      field_simp
    have hdiv : C / a < ε / 2 := (div_lt_iff₀ ha0).mpr (by nlinarith)
    simpa only [t, div_eq_mul_inv, mul_comm] using hdiv
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hK
  obtain ⟨j, η, hη, _hηpos, hbar⟩ :=
    (kahlerQEA_eventually_affine_barrier F hK hU ha).exists
  have hUj := (hU.2 j).1.1
  obtain ⟨D, hD⟩ := (singularityLE_iff_exists_real _ _).mp
    (le_of_sourceQuasiEquisingularApproximation hU.1 j)
  have hφUj := iOrderOnManifold_of_le_add hUj.1.quasiPlurisubharmonic hD
  have hxj := (generalPartialBody_subset_of_iOrder hφ hUj hφUj hbig).1 hx
  have hxcl := generalPartialBody_subset_closure_valuations_of_analytic
    (hU.2 j).1 (hU.2 j).2 hxj
  obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp hxcl (ε / 2) (half_pos hε)
  obtain ⟨S, hS, hSUj, rfl⟩ := hy
  let V := iSingularityEnvelope θ.val (U j)
  have hV : IsThetaPshPotential θ.val V :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) (U j) hUj
  have hUjV := iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) (U j) hUj
  have hIS : IOrderOnManifold (n := m + 1) S V := hSUj.trans hUjV.1
  let W := iSingularityEnvelope θ.val φ
  have hW : IsThetaPshPotential θ.val W :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ
  have hφW := iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    (LocalPotentials.closedRealOneOne_hasLocalPotentials θ) φ hφ
  let ψ := convexComb t η S
  have hψ : IsThetaPshPotential θ.val ψ :=
    isThetaPshPotential_convexComb hη hS ht0 ht1
  have hIbar := iOrderOnManifold_convexComb hη hS hη hV
    (iOrderOnManifold_refl η) hIS ht0 ht1
  have hbarI : IOrderOnManifold (n := m + 1) (convexComb t η V) W :=
    iOrderOnManifold_of_le hW.1.quasiPlurisubharmonic hbar
  have hIφ : IOrderOnManifold (n := m + 1) ψ φ := hIbar.trans (hbarI.trans hφW.2)
  refine ⟨ψ, hψ, hIφ, ?_⟩
  have hν : flagValuation F ψ =
      t • flagValuation F η + (1 - t) • flagValuation F S :=
    flagValuation_add_smul hη hS ht0.le (sub_nonneg.mpr ht1.le)
  have hηb := generalPartialBody_subset_tradOkounkovBody hη hbig
    (SourceCurrentValuation.flagValuation_mem_generalPartialBody F hη)
  have hSb := generalPartialBody_subset_tradOkounkovBody hS hbig
    (SourceCurrentValuation.flagValuation_mem_generalPartialBody F hS)
  have hdist : dist (flagValuation F ψ) (flagValuation F S) < ε / 2 := by
    rw [dist_eq_norm, hν]
    have heq : t • flagValuation F η + (1 - t) • flagValuation F S - flagValuation F S =
        t • (flagValuation F η - flagValuation F S) := by module
    rw [heq, norm_smul, Real.norm_of_nonneg ht0.le]
    exact (mul_le_mul_of_nonneg_left
      (show ‖flagValuation F η - flagValuation F S‖ ≤ C by
        simpa only [dist_eq_norm] using hdiam hηb hSb) ht0.le).trans_lt htC
  have hyx' : dist (flagValuation F S) x < ε / 2 := by simpa only [dist_comm] using hyx
  calc
    dist (flagValuation F ψ) x ≤ dist (flagValuation F ψ) (flagValuation F S) +
        dist (flagValuation F S) x := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hdist hyx'
    _ = ε := by ring

/-- Whole Kähler-current forward closure statement, from actual original
current witnesses at arbitrary original real points, without any prescribed
valuation or convergence assumption. -/
theorem generalPartialBody_eq_closure_valuationsBelow_of_kahler {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ φ) :
    generalPartialBody F θ φ = closure (valuationsBelow F θ φ) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : Nonempty F.carrier := PartialBody.nonempty_carrier F
  have hφ := isThetaPshPotential_of_isKahlerCurrentPotential hK
  have hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mpr (isBigClass_of_isKahlerCurrentPotential hK)
  refine Subset.antisymm ?_ (closure_valuationsBelow_subset_generalPartialBody F hφ hbig)
  intro x hx
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨ψ, hψ, hI, hdist⟩ := exists_valuationBelow_close_of_kahler F hK hx hε
  exact ⟨flagValuation F ψ, ⟨ψ, hψ, hI, rfl⟩, by simpa only [dist_comm] using hdist⟩

end SGPT.Okounkov.SourceValuativeClosure

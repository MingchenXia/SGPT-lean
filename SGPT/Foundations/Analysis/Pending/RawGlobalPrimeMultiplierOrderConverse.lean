import SGPT.Foundations.Analysis.Pending.RawPrimeComparisonAllTruncationIntegrals
import SGPT.Foundations.Analysis.Pending.ManifoldPointTruncationCoordinateMembership
import SGPT.Foundations.Analysis.Pending.FiniteFamilyStrictTruncationStability
import SGPT.Foundations.Analysis.Pending.RawQuasiPshUniformStrictGenericNecessity
import SGPT.Foundations.Analysis.Pending.NormalCrossings

set_option autoImplicit false

/-! # Actual all-global-prime order returns the original raw multiplier ideal -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RawGlobalPrimeMultiplierOrderConverse

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  NormalCrossings InvertibleIdealQuotient

noncomputable section

private theorem holomorphic_adapted {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (x : X) (Φ : LocalHolomorphicEquivAt (n := n) ((chartAt (ComplexModel n) x) x))
    (h0 : Φ.toFun ((chartAt (ComplexModel n) x) x) = 0)
    {F : X → ℂ} (hF : HolomorphicAt n F x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun w => F ((chartAt (ComplexModel n) x).symm (Φ.invFun w))) z := by
  have hs := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff
    x Φ h0 (fun _ : Fin 1 => F) F).mp (isInSpanAt_self ⟨0, rfl⟩ hF)
  exact hs.1.mono fun _ hz => hz.differentiableAt

private theorem psh_generatorLog_of_near_holomorphic {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ) {p : ComplexModel n}
    (hG : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (G i) z) :
    PlurisubharmonicAt (generatorLog G) p := by
  obtain ⟨U, hsub, hU, hpU⟩ := _root_.mem_nhds_iff.mp (eventually_all.mpr hG)
  have hgen : HolomorphicGeneratorsAt G p :=
    ⟨U, hU, hpU, fun i z hz => (hsub hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    plurisubharmonicAt_scaled_generatorLog hgen zero_lt_one

/-- Actual whole-prime order on every same-source global modification returns
every original raw multiplier ideal inclusion, with no target certificate. -/
theorem multiplierIdeal_le_of_all_global_prime_orders
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (horder : ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] (π : Y → X),
      AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π →
      ∀ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
        V.dim = m → (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) →
          (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => v (π w)) z) ≤
            ⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => u (π w)) z)
    {c : ℝ} (hc : 0 < c) :
    (multiplierIdeal (n := m + 1) c u).Le (multiplierIdeal (n := m + 1) c v) := by
  intro x F hint
  classical
  let e := complexChartAt (n := m + 1) x
  have he : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  by_cases hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0
  · obtain ⟨q₀, hcq₀, hq₀F⟩ :=
      RawQuasiPshUniformStrictGenericNecessity.exists_gt_multiplierIntegrableAt
        (hu e (e.val x) he) hint.2
    let q₁ := (c + q₀) / 2
    let q₂ := (c + q₁) / 2
    have hcq₁ : c < q₁ := by dsimp [q₁]; linarith
    have hq₁q₀ : q₁ < q₀ := by dsimp [q₁]; linarith
    have hcq₂ : c < q₂ := by dsimp [q₂]; linarith
    have hq₂q₁ : q₂ < q₁ := by dsimp [q₂]; linarith
    have hq₁ : 0 < q₁ := hc.trans hcq₁
    have hq₂ : 0 < q₂ := hc.trans hcq₂
    let δ := q₂ / c - 1
    have hδ : 0 < δ := by
      have h : 1 < q₂ / c := (lt_div_iff₀ hc).mpr (by simpa using hcq₂)
      dsimp [δ]
      linarith
    have hq₂eq : c * (1 + δ) = q₂ := by
      dsimp [δ]
      field_simp
      ring
    obtain ⟨p, hpbig⟩ := exists_nat_gt (max (2 * q₂ / δ) 1)
    have hpr : (0 : ℝ) < p := lt_trans zero_lt_one ((le_max_right _ _).trans_lt hpbig)
    have hp : 0 < p := by exact_mod_cast hpr
    have hpbound : 2 * (c * (1 + δ)) / δ ≤ (p : ℝ) := by
      rw [hq₂eq]
      exact ((le_max_left _ _).trans_lt hpbig).le
    have hint₀ : (multiplierIdeal (n := m + 1) q₀ u).mem x F := ⟨hint.1, hq₀F⟩
    obtain ⟨s, G, hG, hfull, hreverse, htrunc⟩ :=
      RawPrimeComparisonAllTruncationIntegrals.exists_full_family_with_all_truncation_integrals
        hu hv x hp hq₁ hq₁q₀ (fun Y _ _ _ π hπ V hdim hreg _hcenter =>
          horder Y π hπ V hdim hreg) hFnon hint₀
    obtain ⟨Φ, _hsrc, h0⟩ := NormalCrossings.exists_centred_coordinates (n := m + 1) x
    let T : ComplexModel (m + 1) → X := fun z => e.val.symm (Φ.invFun z)
    let GT : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (T z)
    let FT : ComplexModel (m + 1) → ℂ := fun z => F (T z)
    have hGT (i : Fin s) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
        DifferentiableAt ℂ (GT i) z := holomorphic_adapted x Φ h0 (hG i)
    have hqq : q₂ / p < q₁ / p := (div_lt_div_iff_of_pos_right hpr).mpr hq₂q₁
    have hintGT : MultiplierIntegrableAt (generatorLog GT) (q₂ / p) FT 0 volume := by
      apply FiniteFamilyStrictTruncationStability.multiplierIntegrableAt_of_all_truncations
        GT hGT (div_pos hq₂ hpr) hqq
      intro N
      obtain ⟨t, Q, hQ, _hQfull, hQmem, hQtarget⟩ := htrunc N
      let QT : Fin t → ComplexModel (m + 1) → ℂ := fun i z => Q i (T z)
      have hQT (i : Fin t) : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
          DifferentiableAt ℂ (QT i) z := holomorphic_adapted x Φ h0 (hQ i)
      refine ⟨t, QT, hQT, ?_, ?_⟩
      · intro i
        obtain ⟨_hQi, _hGi, hm⟩ :=
          ManifoldPointTruncationCoordinateMembership.mem_coordinate_truncation_of_original_membership
            x Φ h0 (multiplierIdeal (n := m + 1) p v) G hG hfull N (hQmem i)
        exact hm
      · let QP : Fin t → ComplexModel (m + 1) → ℂ := fun i z => Q i (e.val.symm z)
        have hQP (i : Fin t) : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (QP i) z :=
          MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
            (mem_complexChartAt_source x) (hQ i)
        have hpsh := (psh_generatorLog_of_near_holomorphic QP hQP).quasiPlurisubharmonicAt
        have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
          Φ (f := fun z => F (e.val.symm z)) (c := q₁ / p) hpsh
        have hweq : (fun z => generatorLog QP (Φ.invFun z)) = generatorLog QT := by
          funext z
          simp only [generatorLog_eq_log_sum]
          rfl
        have hintP : MultiplierIntegrableAt (generatorLog QP) (q₁ / p)
            (fun z => F (e.val.symm z)) (e.val x) volume := by
          convert hQtarget.2 using 1
          funext z
          simp only [chartFunction, generatorLog_eq_log_sum]
          rfl
        have h := hcov.mpr hintP
        simpa only [h0, hweq] using h
    let GP : Fin s → ComplexModel (m + 1) → ℂ := fun i z => G i (e.val.symm z)
    have hGP (i : Fin s) : ∀ᶠ z in 𝓝 (e.val x), DifferentiableAt ℂ (GP i) z :=
      MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
        (mem_complexChartAt_source x) (hG i)
    have hpsh := (psh_generatorLog_of_near_holomorphic GP hGP).quasiPlurisubharmonicAt
    have hcov := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
      Φ (f := fun z => F (e.val.symm z)) (c := q₂ / p) hpsh
    have hweq : (fun z => generatorLog GP (Φ.invFun z)) = generatorLog GT := by
      funext z
      simp only [generatorLog_eq_log_sum]
      rfl
    have hintGP : MultiplierIntegrableAt (generatorLog GP) (q₂ / p)
        (fun z => F (e.val.symm z)) (e.val x) volume := by
      apply hcov.mp
      simpa only [h0, hweq] using hintGT
    have hintG : (multiplierIdeal (n := m + 1) (c * (1 + δ) / p) (generatorLog G)).mem x F := by
      refine ⟨hint.1, ?_⟩
      rw [hq₂eq]
      convert hintGP using 1
      funext z
      simp only [chartFunction, generatorLog_eq_log_sum]
      rfl
    exact hreverse c δ hc hδ hpbound F hintG
  · have hzero : ∀ᶠ z in 𝓝 x, F z = 0 := by
      simpa only [Filter.Frequently, not_not, not_ne_iff] using hFnon
    have ht : Tendsto e.val.symm (𝓝 (e.val x)) (𝓝 x) := by
      have h := (e.val.symm.continuousAt he).tendsto
      simpa only [e.val.left_inv (mem_complexChartAt_source x)] using h
    refine ⟨hint.1, ?_⟩
    have hzeroP : (fun z => F (e.val.symm z)) =ᶠ[𝓝 (e.val x)] (fun _ => 0) :=
      ht.eventually hzero
    exact (multiplierIntegrableAt_zero (chartFunction v e) hc (e.val x) volume).congr
      EventuallyEq.rfl hzeroP.symm

end
end SGPT.Foundations.Analysis.Pending.RawGlobalPrimeMultiplierOrderConverse

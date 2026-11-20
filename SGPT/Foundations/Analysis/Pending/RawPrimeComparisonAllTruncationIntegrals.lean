import SGPT.Foundations.Analysis.Pending.AnalyticModificationNumericalMultiplierDescent
import SGPT.Foundations.Analysis.Pending.RawMultiplierGlobalModification
import SGPT.Foundations.Analysis.Pending.RawManifoldFullMultiplierFamily
import SGPT.Foundations.Analysis.Pending.FiniteGermIdealPullbackGenerators
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison

set_option autoImplicit false

/-! # Original whole-prime order internally produces every original truncation integral -/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RawPrimeComparisonAllTruncationIntegrals

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus
  GermIdealOrder IdealWeightPowers RestrictedIdealExtension

noncomputable section

/-- Natural original raw data internally give every complete original
truncation family and its analytic-target integral, on same-source modifications. -/
theorem exists_full_family_with_all_truncation_integrals
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v) (x : X)
    {p : ℕ} (hp : 0 < p) {q₀ q₁ : ℝ} (hq₁ : 0 < q₁) (hgap : q₁ < q₀)
    (horder : ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] (π : Y → X),
      AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π →
      ∀ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
        V.dim = m → (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) →
        (∀ z ∈ V.carrier, π z = x) →
          (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => v (π w)) z) ≤
            ⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => u (π w)) z)
    {F : X → ℂ} (hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0)
    (hint : (multiplierIdeal (n := m + 1) q₀ u).mem x F) :
    ∃ (s : ℕ) (G : Fin s → X → ℂ),
      (∀ i, HolomorphicAt (m + 1) (G i) x) ∧
      (∀ H : X → ℂ, (multiplierIdeal (n := m + 1) p v).mem x H ↔
        IsInSpanAt (n := m + 1) (· ∈ range G) x H) ∧
      (∀ (c δ : ℝ), 0 < c → 0 < δ → 2 * (c * (1 + δ)) / δ ≤ (p : ℝ) →
        ∀ H : X → ℂ,
          (multiplierIdeal (n := m + 1) (c * (1 + δ) / p) (generatorLog G)).mem x H →
          (multiplierIdeal (n := m + 1) c v).mem x H) ∧
      ∀ N : ℕ,
        let 𝔟 := sumIdeal (multiplierIdeal (n := m + 1) p v)
          (idealPow (pointIdeal (m + 1) x) N)
        ∃ (t : ℕ) (Q : Fin t → X → ℂ),
          (∀ i, HolomorphicAt (m + 1) (Q i) x) ∧
          (∀ H : X → ℂ, 𝔟.mem x H ↔ IsInSpanAt (n := m + 1) (· ∈ range Q) x H) ∧
          (∀ i, 𝔟.mem x (Q i)) ∧
          (multiplierIdeal (n := m + 1) (q₁ / p) (generatorLog Q)).mem x F := by
  classical
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨s, G, hG, hfull, C, hC, hdom, _, hreverse⟩ :=
    RawManifoldFullMultiplierFamily.exists_full_family_before_all_whole_fiber_bounds.{u, u} hv x hp
  have hcoh := GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
    (Nat.zero_lt_succ m) hv hpr
  refine ⟨s, G, hG, hfull, hreverse, ?_⟩
  intro N
  dsimp only
  let 𝔟 := sumIdeal (multiplierIdeal (n := m + 1) p v)
    (idealPow (pointIdeal (m + 1) x) N)
  have hcohB : 𝔟.IsCoherent :=
    (PointSupportedIdealPrincipalization.truncation_properties x hcoh N).1
  obtain ⟨U, hU, hxU, t, Q, hQon, hQfull⟩ := hcohB x
  have hQ (i : Fin t) : HolomorphicAt (m + 1) (Q i) x := by
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact (hQon i z hz).mdifferentiableAt (hU.mem_nhds hz)
  have hQmem (i : Fin t) : 𝔟.mem x (Q i) :=
    (hQfull x hxU (Q i)).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hQ i))
  have hGspan (i : Fin s) : IsInSpanAt (n := m + 1) (· ∈ range Q) x (G i) := by
    have hGmem := (hfull (G i)).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩ (hG i))
    exact (hQfull x hxU (G i)).mp (le_sumIdeal_left hcoh x (G i) hGmem)
  obtain ⟨B, hB, hBdom⟩ :=
    IdealWeightComparison.exists_nhds_generatorNormSq_le_of_forall_isInSpanAt hGspan
  have hC' : C * ENNReal.ofReal B ≠ ⊤ := ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  have hdomQ : ∀ᶠ z in 𝓝 x, EReal.exp (((p : ℝ) : EReal) * v z) ≤
      (C * ENNReal.ofReal B) * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2) := by
    filter_upwards [hdom, hBdom] with z hz hBz
    have hBE : (∑ i, ENNReal.ofReal (‖G i z‖ ^ 2)) ≤
        ENNReal.ofReal B * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
        ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
        ← ENNReal.ofReal_mul hB.le]
      exact ENNReal.ofReal_le_ofReal hBz
    calc
      _ ≤ C * ∑ i, ENNReal.ofReal (‖G i z‖ ^ 2) := hz
      _ ≤ C * (ENNReal.ofReal B * ∑ i, ENNReal.ofReal (‖Q i z‖ ^ 2)) :=
        by simpa only [mul_comm] using mul_le_mul_right hBE C
      _ = _ := (mul_assoc _ _ _).symm
  obtain ⟨_hz, Y, tY, cY, mY, π, D, E, _hseq, hmod, hhol, _hproper, _hsurj,
      hpull, hE, hs, _hpre, _hiso, hreaders⟩ :=
    RawMultiplierGlobalModification.exists_principalization_with_global_modification hv x hpr N
  let _ := tY
  let _ := cY
  let _ := mY
  have hcomponents : ∀ y : Y, π y = x → ∀ i : Fin E.length, y ∈ E.get i →
      ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
        V.dim = m ∧ (∀ z ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier z m) ∧
        y ∈ V.carrier ∧ (∀ z ∈ V.carrier, π z = x) ∧
        ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ E.get i ∩ O = V.carrier ∩ O := by
    intro y _hy i hyE
    obtain ⟨V, hdim, _hcomp, hyV, _hsub, _hconn, hreg, hlocal, hcenter, _hreader⟩ :=
      hreaders i y hyE
    exact ⟨V, hdim, hreg, hyV, hcenter, hlocal y hyV⟩
  have hgen : ∀ y : Y, π y = x → ∀ H : Y → ℂ, D.ideal.mem y H ↔
      IsInSpanAt (n := m + 1) (· ∈ range (fun i z => Q i (π z))) y H := by
    intro y hy H
    have hQy (i : Fin t) : HolomorphicAt (m + 1) (Q i) (π y) := hy ▸ hQ i
    have hfully (a : X → ℂ) : 𝔟.mem (π y) a ↔
        IsInSpanAt (n := m + 1) (· ∈ range Q) (π y) a := by
      rw [hy]
      exact hQfull x hxU a
    have h := FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
      (Eventually.of_forall fun _ => hhol.contMDiffAt) 𝔟 Q hQy hfully H
    have hpull' : GermIdeal.pullback (m := m + 1) π 𝔟 = D.ideal := hpull
    simpa only [hpull', Function.comp_def] using h
  have htarget :=
    AnalyticModificationNumericalMultiplierDescent.multiplierIdeal_mem_of_principalized_raw_prime_comparison
      hmod x D E hE hs hcomponents Q hQ hgen hu hpr hq₁ hgap hC' hdomQ
        (horder Y π hmod) hFnon hint
  exact ⟨t, Q, hQ, hQfull x hxU, hQmem, htarget⟩

end
end SGPT.Foundations.Analysis.Pending.RawPrimeComparisonAllTruncationIntegrals

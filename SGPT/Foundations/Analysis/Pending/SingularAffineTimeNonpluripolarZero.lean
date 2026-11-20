import SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalMixedZero
import SGPT.Foundations.Analysis.Pending.NonPluripolarHolomorphic
import SGPT.Foundations.Analysis.Pending.BedfordTaylorStripCovariance

set_option autoImplicit false

/-! # Actual affine time coordinates preserve the singular Perron NP equation -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularAffineTimeNonpluripolarZero

open FirstPass FiniteGeodesicMaximality BedfordTaylorStripCovariance
  BedfordTaylor MixedNonPluripolar SingularPerronCanonicalMixedZero
  SingularPerronNonpluripolarZero

noncomputable section

variable {n : ℕ}

/-- The true inverse-affine image time domain. -/
def affineTimeDomain (a : ℂ) (δ : ℝ) (S : Opens ℂ) : Opens ℂ :=
  ⟨(fun t => a + δ • t) ⁻¹' S, S.isOpen.preimage (by fun_prop)⟩

/-- The actual summed-model affine time map preserving all base coordinates. -/
def affineTimeStripMap (a : ℂ) (δ : ℝ) (q : ComplexModel (n + 1)) : ComplexModel (n + 1) :=
  (stripModelEquiv n).symm ((stripModelEquiv n q).1, δ⁻¹ • ((stripModelEquiv n q).2 - a))

/-- The actual summed-model inverse affine time map. -/
def affineTimeStripInv (a : ℂ) (δ : ℝ) (q : ComplexModel (n + 1)) : ComplexModel (n + 1) :=
  (stripModelEquiv n).symm ((stripModelEquiv n q).1, a + δ • (stripModelEquiv n q).2)

private theorem affine_time_left (a : ℂ) {δ : ℝ} (hδ : δ ≠ 0) (s : ℂ) :
    a + δ • (δ⁻¹ • (s - a)) = s := by
  rw [smul_inv_smul₀ hδ]
  abel

private theorem affine_time_right (a : ℂ) {δ : ℝ} (hδ : δ ≠ 0) (t : ℂ) :
    δ⁻¹ • (a + δ • t - a) = t := by
  rw [add_sub_cancel_left, inv_smul_smul₀ hδ]

/-- The explicit ordinary affine strip maps internally produce all genuine biholomorphic-pair fields. -/
theorem isBiholomorphicPair_affineTimeStrip (A : Opens (ComplexModel n))
    (S : Opens ℂ) (a : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    IsBiholomorphicPair (stripLift A S S.isOpen)
      (stripLift A (affineTimeDomain a δ S) (affineTimeDomain a δ S).isOpen)
      (affineTimeStripMap a δ) (affineTimeStripInv a δ) := by
  have hf : ContDiff ℂ ∞ (affineTimeStripMap (n := n) a δ) := by
    exact (stripModelEquiv n).symm.contDiff.comp
      (((stripModelEquiv n).contDiff.fst).prodMk
        (((stripModelEquiv n).contDiff.snd.sub contDiff_const).const_smul δ⁻¹))
  have hg : ContDiff ℂ ∞ (affineTimeStripInv (n := n) a δ) := by
    exact (stripModelEquiv n).symm.contDiff.comp
      (((stripModelEquiv n).contDiff.fst).prodMk
        (contDiff_const.add (((stripModelEquiv n).contDiff.snd).const_smul δ)))
  have hd : δ ≠ 0 := ne_of_gt hδ
  refine ⟨hf.contDiffOn, hg.contDiffOn, ?_, ?_, ?_, ?_⟩
  · intro q hq
    change (stripModelEquiv n (affineTimeStripMap a δ q)).1 ∈ A ∧
      a + δ • (stripModelEquiv n (affineTimeStripMap a δ q)).2 ∈ S
    simp only [affineTimeStripMap, ContinuousLinearEquiv.apply_symm_apply]
    rw [affine_time_left a hd]
    exact hq
  · intro q hq
    change (stripModelEquiv n q).1 ∈ A ∧ a + δ • (stripModelEquiv n q).2 ∈ S at hq
    change (stripModelEquiv n (affineTimeStripInv a δ q)).1 ∈ A ∧
      (stripModelEquiv n (affineTimeStripInv a δ q)).2 ∈ S
    simpa only [affineTimeStripInv, ContinuousLinearEquiv.apply_symm_apply] using hq
  · intro q _
    apply (stripModelEquiv n).injective
    simp only [affineTimeStripMap, affineTimeStripInv, ContinuousLinearEquiv.apply_symm_apply]
    rw [affine_time_left a hd]
  · intro q _
    apply (stripModelEquiv n).injective
    simp only [affineTimeStripMap, affineTimeStripInv, ContinuousLinearEquiv.apply_symm_apply]
    rw [affine_time_right a hd]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

omit [CompactSpace M] in
private theorem affine_target_le_model {θ : SmoothRealForm n M 2}
    (e : ComplexChart n M) {A : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e A ρ) (S : Opens ℂ) (a : ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ s ∈ S, (δ⁻¹ • (s - a)).re ∈ Ioo (0 : ℝ) 1) :
    stripLift (⟨A, hρ.1⟩ : Opens (ComplexModel n)) (affineTimeDomain a δ S)
        (affineTimeDomain a δ S).isOpen ≤ modelStripOpens A hρ.1 := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  change (stripModelEquiv n q).2.re ∈ Ioo (0 : ℝ) 1
  have ht := htime (a + δ • (stripModelEquiv n q).2) hq.2
  simpa only [affine_time_right a (ne_of_gt hδ)] using ht

/-- Actual fixed-local-potential Perron PSH and the true holomorphic affine time map produce the singular corrected pullback PSH internally. -/
theorem plurisubharmonicOn_erealModel_affineTime
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {A : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e A ρ) (S : Opens ℂ) (a : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ s ∈ S, (δ⁻¹ • (s - a)).re ∈ Ioo (0 : ℝ) 1) :
    PlurisubharmonicOn
      (fun q => erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ (affineTimeStripMap a δ q))
      (stripLift (⟨A, hρ.1⟩ : Opens (ComplexModel n)) S S.isOpen) := by
  let h := isBiholomorphicPair_affineTimeStrip (⟨A, hρ.1⟩ : Opens (ComplexModel n)) S a hδ
  have hB := affine_target_le_model e hρ S a hδ htime
  exact HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    (stripLift (⟨A, hρ.1⟩ : Opens (ComplexModel n)) S S.isOpen).isOpen
    (h.holo.differentiableOn (by simp)) h.mapsTo
    ((isBoundaryMaximalPshOn_erealModel_of_subgeodesic hsub e hρ).2.1.mono hB)

/-- Genuine Perron canonical mixed NP zero, ordinary-open restriction and the explicit affine-time biholomorphism internally produce actual source-strip diagonal NP zero. -/
theorem mixedTruncationLimitMeasure_erealModel_affineTime_eq_zero
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {A : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e A ρ) (S : Opens ℂ) (a : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ s ∈ S, (δ⁻¹ • (s - a)).re ∈ Ioo (0 : ℝ) 1) :
    mixedTruncationLimitMeasure
      (stripLift (⟨A, hρ.1⟩ : Opens (ComplexModel n)) S S.isOpen)
      (fun _ q => erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ
        (affineTimeStripMap a δ q))
      (fun _ => plurisubharmonicOn_erealModel_affineTime hsub e hρ S a hδ htime) = 0 := by
  let h := isBiholomorphicPair_affineTimeStrip (⟨A, hρ.1⟩ : Opens (ComplexModel n)) S a hδ
  have hB := affine_target_le_model e hρ S a hδ htime
  let hv := (isBoundaryMaximalPshOn_erealModel_of_subgeodesic hsub e hρ).2.1
  have hzero : mixedTruncationLimitMeasure
      (stripLift (⟨A, hρ.1⟩ : Opens (ComplexModel n)) (affineTimeDomain a δ S)
        (affineTimeDomain a δ S).isOpen)
      (fun _ => erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (fun _ => hv.mono hB) = 0 := by
    rw [← mixedTruncationLimitMeasure_restrict_open hB (fun _ => hv),
      mixedTruncationLimitMeasure_erealModel_of_subgeodesic_eq_zero hsub e hρ,
      Measure.restrict_zero]
  rw [mixedTruncationLimitMeasure_comp_biholomorphic h (fun _ => hv.mono hB)
    (fun _ => plurisubharmonicOn_erealModel_affineTime hsub e hρ S a hδ htime),
    hzero, Measure.restrict_zero, Measure.map_zero]

end

end SGPT.Foundations.Analysis.Pending.SingularAffineTimeNonpluripolarZero

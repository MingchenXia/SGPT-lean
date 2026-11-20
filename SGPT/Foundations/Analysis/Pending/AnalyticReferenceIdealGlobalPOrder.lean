import SGPT.Foundations.Analysis.Pending.BoundedMultiplierPotentialComparison
import SGPT.Foundations.Analysis.Pending.CompactAnalyticBoundedMultiplierInclusion
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityInterpolation
import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderSqueeze
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.CollarWeightComparison

set_option autoImplicit false

/-! # Actual ideal order with analytic reference produces global P-order -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.AnalyticReferenceIdealGlobalPOrder

open FirstPass FirstPass.PositiveClasses FirstPass.QuasiEquisingularApproximation FirstPass.IEnvelope
  FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus RelativeEnergy
  SingularGlobalPOrder SingularCanonicalSingularityDistance
  SingularCanonicalOrderSqueeze ThetaPshConvexCombination SingularMinimalCanonicalRay
  PluripolarCapacityDichotomy EndpointMixedMassConvexCombination ThetaPshL1Topology

noncomputable section

private theorem moreSingularOn_dim_zero
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
    [IsComplexManifold 0 M] [CompactSpace M]
    {θ ζ : SmoothRealForm 0 M 2} {ψ Φ : M → EReal}
    (hψ : IsThetaPshPotential θ ψ) (hΦ : IsThetaPshPotential ζ Φ) (s : ℝ) :
    MoreSingularOn ψ (fun x => (s : EReal) * Φ x) univ := by
  apply IdealWeightComparison.moreSingularOn_univ_of_forall_moreSingularAt
  intro x
  have hψx : ψ x = ((ψ x).toReal : EReal) :=
    (EReal.coe_toReal (hψ.1.quasiPlurisubharmonic.ne_top x)
      (FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero hψ x)).symm
  have hΦx : Φ x = ((Φ x).toReal : EReal) :=
    (EReal.coe_toReal (hΦ.1.quasiPlurisubharmonic.ne_top x)
      (FiniteGeodesicsFullMassAnyDim.ne_bot_of_dim_zero hΦ x)).symm
  refine ⟨(ψ x).toReal - s * (Φ x).toReal,
    eventually_of_mem ((FiniteGeodesicsFullMassAnyDim.isOpen_singleton_of_dim_zero x).mem_nhds
      (mem_singleton x)) ?_⟩
  intro y hy
  subst y
  dsimp only
  rw [hψx, hΦx, ← EReal.coe_mul, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  simp only [EReal.toReal_coe]
  ring_nf
  exact le_rfl

/-- Actual ideal inclusion and analytic type internally produce every
strict scaled-reference comparison, including dimension zero. -/
theorem moreSingularOn_scaled_of_iOrderOnManifold
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    {θ ζ : ClosedRealOneOneForm n M} {ψ Φ : M → EReal}
    (hψ : IsThetaPshPotential θ.val ψ) (hΦ : IsThetaPshPotential ζ.val Φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) Φ)
    (hI : IOrderOnManifold (n := n) ψ Φ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    MoreSingularOn ψ (fun x => (s : EReal) * Φ x) univ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact moreSingularOn_dim_zero hψ hΦ s
  · obtain ⟨R, hR, hgap⟩ :=
      CompactAnalyticBoundedMultiplierInclusion.exists_pos_uniform_bounded_multiplier_gap hA
    obtain ⟨m, hmgt⟩ := exists_nat_gt (R / (1 - s))
    have hmR : (0 : ℝ) < m := (div_pos hR (sub_pos.mpr hs1)).trans hmgt
    have hm : 0 < m := by exact_mod_cast hmR
    have hscale : R < (m : ℝ) * (1 - s) :=
      (div_lt_iff₀ (sub_pos.mpr hs1)).mp hmgt
    let p : ℝ := s * m
    have hp : 0 < p := mul_pos hs0 hmR
    have hpgap : p + R ≤ m := by dsimp only [p]; nlinarith
    have hM := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold hI hmR
    have hB := hgap p hp m hpgap
    have hle : (multiplierIdeal (n := n) (m : ℝ) ψ).Le
        (AnalyticBoundedMultiplierIdeal.boundedMultiplierIdeal (n := n)
          (fun x => (p : EReal) * Φ x)) :=
      fun x f hf => hB x f (hM x f hf)
    have hpm : p / (m : ℝ) = s := by
      dsimp only [p]
      exact mul_div_cancel_right₀ s hmR.ne'
    simpa only [hpm] using
      BoundedMultiplierPotentialComparison.moreSingularOn_of_multiplierIdeal_le_boundedMultiplierIdeal
        hn hψ hm hle

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine common backgrounds, actual strict comparisons and actual
native interpolation internally produce the source global P-order. -/
theorem sourcePOrder_of_iOrderOnManifold_of_analytic_reference
    (omega : KahlerBackground n M) {ψ Φ : M → EReal}
    (hψ : IsGlobalQuasiPshPotential (n := n) ψ)
    (hΦ : IsGlobalQuasiPshPotential (n := n) Φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) Φ)
    (hI : IOrderOnManifold (n := n) ψ Φ) : SourcePOrder (n := n) ψ Φ := by
  obtain ⟨C, hC, hψβ, hΦβ, _, _⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega hψ hΦ
  let β : KahlerBackground n M := KahlerBackground.smul hC omega
  let A : ThetaPshL1 β.form.val := ⟨Φ, hΦβ⟩
  let W : ThetaPshL1 β.form.val :=
    ⟨fun x => max (ψ x) (Φ x), IsThetaPshPotential.max hψβ hΦβ⟩
  let := singularityPseudoMetricSpace omega β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omega β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  have hcoeff (m : ℕ) : 0 < 1 / ((m : ℝ) + 2) ∧ 1 / ((m : ℝ) + 2) < 1 := by
    have hm := Nat.cast_nonneg (α := ℝ) m
    have hden : 0 < (m : ℝ) + 2 := by linarith
    exact ⟨one_div_pos.mpr hden, (div_lt_one hden).mpr (by linarith)⟩
  let t : ℕ → Ioo (0 : ℝ) 1 := fun m => ⟨1 / ((m : ℝ) + 2), hcoeff m⟩
  have ht : Tendsto (fun m => (t m).val) atTop (𝓝 0) := by
    simpa only [t, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hVmin : IsThetaPshPotential β.form.val (thetaPshSupremum β.form.val) :=
    (isModelPotential_thetaPshSupremum omega β.form (isBigClass_kahler β)).plurisubharmonic
  have hVzero : thetaPshSupremum β.form.val = (fun _ => 0) :=
    le_antisymm (thetaPshSupremum_le_zero β.form.val)
      (le_thetaPshSupremum (isThetaPshPotential_zero β) le_rfl)
  let Q : ℕ → ThetaPshL1 β.form.val := fun m =>
    ⟨convexComb (1 - (t m).val) Φ (thetaPshSupremum β.form.val),
      isThetaPshPotential_convexComb_closed hΦβ hVmin
        (sub_nonneg.mpr (t m).property.2.le) (sub_le_self 1 (t m).property.1.le)⟩
  have hQA : Tendsto Q atTop (𝓝 A) :=
    SingularCanonicalSingularityInterpolation.tendsto_native_convexComb_minimal_zero
      omega β.form (isBigClass_kahler β) A atTop t ht
  have hQval (m : ℕ) : (Q m).val = fun x => ((1 - (t m).val : ℝ) : EReal) * Φ x := by
    funext x
    change ((1 - (t m).val : ℝ) : EReal) * Φ x +
      ((1 - (1 - (t m).val) : ℝ) : EReal) * thetaPshSupremum β.form.val x = _
    rw [hVzero]
    simp only [mul_zero, add_zero]
  have hAB : SourcePOrder (n := n) A.val W.val :=
    sourcePOrder_of_moreSingularOn omega β.form β.form A.property W.property
      (MoreSingularOn.of_le fun x _ => le_max_right _ _)
  have hBW (m : ℕ) : SourcePOrder (n := n) W.val (Q m).val := by
    have hs0 : 0 < 1 - (t m).val := sub_pos.mpr (t m).property.2
    have hs1 : 1 - (t m).val < 1 := sub_lt_self 1 (t m).property.1
    obtain ⟨D, hD⟩ := moreSingularOn_scaled_of_iOrderOnManifold hψβ hΦβ hA hI hs0 hs1
    have hf := ModelRaySupremum.iSup_ne_top_ne_bot hΦβ
    let K : ℝ := (⨆ x, Φ x).toReal
    have hK : (K : EReal) = ⨆ x, Φ x := EReal.coe_toReal hf.1 hf.2
    have hself : MoreSingularOn Φ (fun x => ((1 - (t m).val : ℝ) : EReal) * Φ x) univ := by
      simpa only [EReal.coe_one, one_mul] using
        CollarWeightComparison.moreSingularOn_const_mul
          (a := 1) (b := 1 - (t m).val) hs0.le hs1.le
          (fun x _ => hK.symm ▸ le_iSup Φ x)
    obtain ⟨E, hE⟩ := hself
    have hmax : MoreSingularOn W.val (Q m).val univ := by
      rw [hQval]
      refine ⟨max D E, ?_⟩
      intro x hx
      exact max_le
        ((hD x hx).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left D E))))
        ((hE x hx).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right D E))))
    exact sourcePOrder_of_moreSingularOn omega β.form β.form W.property (Q m).property hmax
  have hreal : Tendsto (fun m => dist A (Q m)) atTop (𝓝 0) := by
    simpa only [dist_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => A)
      atTop (𝓝 A)).dist hQA
  have he (m : ℕ) : singularityDistance omega β.form (isBigClass_kahler β) Φ (Q m).val =
      (dist A (Q m) : EReal) := by
    obtain ⟨r, _, _, _, hr⟩ := exists_tendsto_singularityDistance omega β.form
      (isBigClass_kahler β) A.property (Q m).property
    rw [dist_eq_singularityDistance_toReal, hr, EReal.toReal_coe]
  have hlim : Tendsto (fun m => singularityDistance omega β.form
      (isBigClass_kahler β) Φ (Q m).val) atTop (𝓝 0) := by
    simp_rw [he]
    exact EReal.tendsto_coe.mpr hreal
  have hzeroLim := (tendsto_singularityDistance_zero_of_sourcePOrder omega β.form
    (isBigClass_kahler β) (atTop : Filter ℕ) (fun _ => A.property)
    (fun _ => W.property) (fun m => (Q m).property) (fun _ => hAB) hBW hlim).1
  have hzero : singularityDistance omega β.form (isBigClass_kahler β) A.val W.val = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hzeroLim
  have hWA := (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent omega β.form
      (isBigClass_kahler β) A.property W.property).mp hzero
  exact (sourcePOrder_of_moreSingularOn omega β.form β.form hψβ W.property
    (MoreSingularOn.of_le fun x _ => le_max_left _ _)).trans omega hWA.2

end

end SGPT.Foundations.Analysis.Pending.AnalyticReferenceIdealGlobalPOrder

import SGPT.Foundations.Analysis.Pending.SingularNativeOrderSandwich
import SGPT.Foundations.Analysis.Pending.SingularConvexMixedMassContinuity
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassGeneral

set_option autoImplicit false

/-! # Actual negative-side continuity of the minimal background

SGPT PDF0244--0245 Lemma 6.2.7 Step 2. The true big-class strict potential,
actual convex lower barrier, endpoint mass polynomials and native sandwich
produce the original-background limit. The positive-side moving native
background assertion is separate.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularMinimalBackgroundNegative

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  ThetaPshL1Topology ThetaPshConvexCombination EndpointMixedMassConvexCombination
  RelativeEnergy GlobalNonPluripolar SingularMinimalCanonicalRay
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison
  SingularConvexMixedMassContinuity SingularNativeOrderSandwich

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The true big-class strict potential and actual local convexity produce
the smaller-class bigness and both pointwise minimal-potential barriers. -/
theorem exists_minimal_sub_smul_convex_barrier
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ψ : M → EReal,
      IsThetaPshPotential (θ - δ • omega.form).val ψ ∧ ψ ≤ 0 ∧
      ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) δ →
        IsBigClass (RealBottChern.ofRepresentative (θ - ε • omega.form)) ∧
        IsThetaPshPotential θ.val (thetaPshSupremum (θ - ε • omega.form).val) ∧
        convexComb (ε / δ) ψ (thetaPshSupremum θ.val) ≤
          thetaPshSupremum (θ - ε • omega.form).val ∧
        thetaPshSupremum (θ - ε • omega.form).val ≤ thetaPshSupremum θ.val := by
  obtain ⟨δ, hδ, ψ₀, hψ₀⟩ :=
    FiniteGeodesicsFullMassGeneral.bigWithRespectToViaPotentials_of_isBigClass omega θ hbig
  obtain ⟨C, hC⟩ := hψ₀.exists_global_upper_bound
  let ψ : M → EReal := fun x => ψ₀ x - (C : EReal)
  have hψ : IsThetaPshPotential (θ - δ • omega.form).val ψ := hψ₀.sub_const C
  have hψ0 : ψ ≤ 0 := sub_const_nonpositive_of_le hC
  have hψθ : IsThetaPshPotential θ.val ψ := by
    simpa only [sub_add_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      hψ (KahlerDomination.isSemipositive_smul omega.isSemipositive hδ.le)
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  refine ⟨δ, hδ, ψ, hψ, hψ0, fun ε hε => ?_⟩
  have ha0 : 0 < ε / δ := div_pos hε.1 hδ
  have ha1 : ε / δ < 1 := (div_lt_one hδ).mpr hε.2
  have hsmall : IsBigClass (RealBottChern.ofRepresentative (θ - ε • omega.form)) := by
    refine ⟨{
      representative := θ - ε • omega.form
      represents := rfl
      potential := ψ
      lowerBound := KahlerBackground.smul (sub_pos.mpr hε.2) omega
      strictlyPsh := ?_ }⟩
    have he : (θ - ε • omega.form) - (δ - ε) • omega.form = θ - δ • omega.form := by
      module
    simpa only [KahlerBackground.smul_form, he] using hψ
  have hVsmall : IsThetaPshPotential (θ - ε • omega.form).val
      (thetaPshSupremum (θ - ε • omega.form).val) :=
    (isModelPotential_thetaPshSupremum omega (θ - ε • omega.form) hsmall).plurisubharmonic
  have hVθ : IsThetaPshPotential θ.val
      (thetaPshSupremum (θ - ε • omega.form).val) := by
    simpa only [sub_add_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      hVsmall (KahlerDomination.isSemipositive_smul omega.isSemipositive hε.1.le)
  have hqθ : IsThetaPshPotential θ.val (convexComb (ε / δ) ψ (thetaPshSupremum θ.val)) :=
    isThetaPshPotential_convexComb_closed hψθ hV ha0.le ha1.le
  have hqsmall : IsThetaPshPotential (θ - ε • omega.form).val
      (convexComb (ε / δ) ψ (thetaPshSupremum θ.val)) := by
    refine ⟨?_, hqθ.2⟩
    have h := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul ha0 (sub_pos.mpr ha1)
      hψ.1 hV.1
    have he : (ε / δ) • (θ - δ • omega.form) + (1 - ε / δ) • θ =
        θ - ε • omega.form := by
      rw [smul_sub, smul_smul, div_mul_cancel₀ ε hδ.ne']
      module
    rw [he] at h
    exact h
  have hq0 : convexComb (ε / δ) ψ (thetaPshSupremum θ.val) ≤ 0 := by
    intro x
    change (ε / δ : ℝ) * ψ x + ((1 - ε / δ : ℝ) : EReal) *
      thetaPshSupremum θ.val x ≤ 0
    have h1 := mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr ha0.le) (hψ0 x)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_nonneg.mpr ha1.le))
      (thetaPshSupremum_le_zero θ.val x)
    exact add_nonpos h1 h2
  exact ⟨hsmall, hVθ, le_thetaPshSupremum hqsmall hq0,
    le_thetaPshSupremum hVθ (thetaPshSupremum_le_zero _)⟩

private theorem tendsto_native_convex_lower_zero
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {ψ : M → EReal} (hψ : IsThetaPshPotential θ.val ψ)
    (hψV : ψ ≤ thetaPshSupremum θ.val)
    {I : Type*} (F : Filter I) (t : I → Ioo (0 : ℝ) 1)
    (ht : Tendsto (fun i => (t i).val) F (𝓝 (0 : ℝ))) :
    let hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
    Tendsto (fun i => (⟨convexComb (t i).val ψ (thetaPshSupremum θ.val),
      isThetaPshPotential_convexComb_closed hψ hV (t i).property.1.le
        (t i).property.2.le⟩ : ThetaPshL1 θ.val)) F
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨thetaPshSupremum θ.val, hV⟩) := by
  let V := thetaPshSupremum θ.val
  have hV : IsThetaPshPotential θ.val V :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  let Q : I → ThetaPshL1 θ.val := fun i => ⟨convexComb (t i).val ψ V,
    isThetaPshPotential_convexComb_closed hψ hV (t i).property.1.le (t i).property.2.le⟩
  let a : I → Icc (0 : ℝ) 1 := fun i =>
    ⟨(t i).val, (t i).property.1.le, (t i).property.2.le⟩
  have ha : Tendsto a F (𝓝 (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)) :=
    tendsto_subtype_rng.mpr ht
  have hq0 : convexComb 0 ψ V = V := by
    funext x
    simp only [ThetaPshConvexCombination.convexComb, EReal.coe_zero, zero_mul,
      sub_zero, EReal.coe_one, one_mul, zero_add]
  have hM (j : Fin (n + 1)) :
      Tendsto (fun i => (endpointMixedMass θ V (Q i).val hV (Q i).property j).toReal) F
        (𝓝 (endpointMixedMass θ V V hV hV j).toReal) := by
    have h := ((continuous_toReal_endpointMixedMass_convexComb omega hψ hV j).tendsto
      (⟨0, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).comp ha
    simpa only [Function.comp_def, hq0] using h
  have hqle (i : I) : (Q i).val ≤ V := by
    have h := convexComb_mono (t i).property.1.le (t i).property.2.le hψV (le_refl V)
    have hself : convexComb (t i).val V V = V := by
      funext x
      change ((t i).val : EReal) * V x + (((1 - (t i).val : ℝ) : EReal)) * V x = V x
      induction V x using EReal.rec with
      | bot => simp only [EReal.coe_mul_bot_of_pos (t i).property.1,
          EReal.coe_mul_bot_of_pos (sub_pos.mpr (t i).property.2), EReal.bot_add]
      | top => simp only [EReal.coe_mul_top_of_pos (t i).property.1,
          EReal.coe_mul_top_of_pos (sub_pos.mpr (t i).property.2), EReal.top_add_top]
      | coe r =>
        simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
        ring
    exact h.trans_eq hself
  have hD : Tendsto (fun i => (singularityDistance omega θ hbig (Q i).val V).toReal)
      F (𝓝 (0 : ℝ)) := by
    apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega θ hbig F
      (fun i => (Q i).property) hV).mpr
    intro j
    refine ⟨hM j, ?_⟩
    have hmax (i : I) : (fun x => max ((Q i).val x) (V x)) = V :=
      funext fun x => max_eq_right (hqle i x)
    have he (i : I) : endpointMixedMass θ V (fun x => max ((Q i).val x) (V x)) hV
        (IsThetaPshPotential.max (Q i).property hV) j = endpointMixedMass θ V V hV hV j := by
      have h := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple
        (congrArg (fun f => endpointMixedPotential j f V) (hmax i))
        (endpointMixedPotential_thetaPlurisubharmonic θ j _ V
          (IsThetaPshPotential.max (Q i).property hV) hV)
        (endpointMixedPotential_thetaPlurisubharmonic θ j V V hV hV)
      exact congrArg (fun μ : MeasureTheory.Measure M => μ Set.univ) h
    change Tendsto (fun i => (endpointMixedMass θ V
      (fun x => max ((Q i).val x) (V x)) hV
      (IsThetaPshPotential.max (Q i).property hV) j).toReal) F
      (𝓝 (endpointMixedMass θ V V hV hV j).toReal)
    simpa only [he] using (tendsto_const_nhds : Tendsto
      (fun _ : I => (endpointMixedMass θ V V hV hV j).toReal) F
      (𝓝 (endpointMixedMass θ V V hV hV j).toReal))
  let : PseudoMetricSpace (ThetaPshL1 θ.val) := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hd : (fun i => dist (Q i) (⟨V, hV⟩ : ThetaPshL1 θ.val)) =
      fun i => (singularityDistance omega θ hbig (Q i).val V).toReal :=
    funext fun i => dist_eq_singularityDistance_toReal omega θ hbig (Q i) ⟨V, hV⟩
  change Tendsto Q F (𝓝 (⟨V, hV⟩ : ThetaPshL1 θ.val))
  exact tendsto_iff_dist_tendsto_zero.mpr (hd.symm ▸ hD)

/-- The smaller-background minimal potentials converge to the original
minimal potential in both actual defining distance readers on the raw
right-neighborhood filter. All eventual admissibility is internally produced. -/
theorem tendsto_singularityDistance_minimal_sub_smul_right
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    Tendsto (fun ε : ℝ => singularityDistance omega θ hbig
      (thetaPshSupremum (θ - ε • omega.form).val) (thetaPshSupremum θ.val))
      (𝓝[>] 0) (𝓝 (0 : EReal)) ∧
    Tendsto (fun ε : ℝ => (singularityDistance omega θ hbig
      (thetaPshSupremum (θ - ε • omega.form).val) (thetaPshSupremum θ.val)).toReal)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
  obtain ⟨δ, hδ, ψ, hψ, hψ0, hbar⟩ := exists_minimal_sub_smul_convex_barrier omega θ hbig
  let S := Ioo (0 : ℝ) δ
  have hS : S ∈ (𝓝[>] (0 : ℝ)) := by
    have hgt : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
    have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < δ :=
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
    filter_upwards [hgt, hlt] with ε hε0 hεδ
    exact ⟨hε0, hεδ⟩
  let G : Filter S := comap ((↑) : S → ℝ) (𝓝[>] (0 : ℝ))
  let V := thetaPshSupremum θ.val
  have hV : IsThetaPshPotential θ.val V :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hψθ : IsThetaPshPotential θ.val ψ := by
    simpa only [sub_add_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      hψ (KahlerDomination.isSemipositive_smul omega.isSemipositive hδ.le)
  let t : S → Ioo (0 : ℝ) 1 := fun ε =>
    ⟨ε.val / δ, div_pos ε.property.1 hδ, (div_lt_one hδ).mpr ε.property.2⟩
  have hcoord : Tendsto (fun ε : S => ε.val) G (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have ht : Tendsto (fun ε : S => (t ε).val) G (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using hcoord.div_const δ
  let Q : S → ThetaPshL1 θ.val := fun ε =>
    ⟨convexComb (t ε).val ψ V,
      isThetaPshPotential_convexComb_closed hψθ hV (t ε).property.1.le (t ε).property.2.le⟩
  let W : S → ThetaPshL1 θ.val := fun ε =>
    ⟨thetaPshSupremum (θ - ε.val • omega.form).val, (hbar ε.val ε.property).2.1⟩
  let U : ThetaPshL1 θ.val := ⟨V, hV⟩
  let : PseudoMetricSpace (ThetaPshL1 θ.val) := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hQ : Tendsto Q G (𝓝 U) :=
    tendsto_native_convex_lower_zero omega θ hbig hψθ
      (le_thetaPshSupremum hψθ hψ0) G t ht
  have hQU (ε : S) : POrderWith θ (Q ε).val (W ε).val :=
    pOrderWith_of_moreSingular (MoreSingularOn.of_le fun x _ => (hbar ε.val ε.property).2.2.1 x)
  have hWU (ε : S) : POrderWith θ (W ε).val U.val :=
    pOrderWith_of_moreSingular (MoreSingularOn.of_le fun x _ => (hbar ε.val ε.property).2.2.2 x)
  have hW : Tendsto W G (𝓝 U) :=
    tendsto_native_of_fixedPOrder_sandwich omega θ hbig G Q W (fun _ => U) U hQU hWU
      hQ tendsto_const_nhds
  have hd : (fun ε => dist (W ε) U) = fun ε : S =>
      (singularityDistance omega θ hbig
        (thetaPshSupremum (θ - ε.val • omega.form).val) V).toReal :=
    funext fun ε => dist_eq_singularityDistance_toReal omega θ hbig (W ε) U
  have hreal : Tendsto (fun ε : S => (singularityDistance omega θ hbig
      (thetaPshSupremum (θ - ε.val • omega.form).val) V).toReal) G (𝓝 (0 : ℝ)) :=
    hd ▸ tendsto_iff_dist_tendsto_zero.mp hW
  have hcoe : (fun ε : S => ((singularityDistance omega θ hbig
      (thetaPshSupremum (θ - ε.val • omega.form).val) V).toReal : EReal)) =
      fun ε : S => singularityDistance omega θ hbig
        (thetaPshSupremum (θ - ε.val • omega.form).val) V := by
    funext ε
    obtain ⟨m, _, _, _, he⟩ := exists_tendsto_singularityDistance omega θ hbig
      (W ε).property hV
    change ((singularityDistance omega θ hbig (W ε).val V).toReal : EReal) =
      singularityDistance omega θ hbig (W ε).val V
    rw [he, EReal.toReal_coe]
  have hextended : Tendsto (fun ε : S => singularityDistance omega θ hbig
      (thetaPshSupremum (θ - ε.val • omega.form).val) V) G (𝓝 (0 : EReal)) := by
    simpa only [hcoe, EReal.coe_zero] using EReal.tendsto_coe.mpr hreal
  have hrange : Set.range ((↑) : S → ℝ) ∈ (𝓝[>] (0 : ℝ)) := by
    simpa only [Subtype.range_val] using hS
  exact ⟨(Filter.tendsto_comap'_iff hrange).mp hextended,
    (Filter.tendsto_comap'_iff hrange).mp hreal⟩

end
end SGPT.Foundations.Analysis.Pending.SingularMinimalBackgroundNegative

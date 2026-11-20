import SGPT.PSH.SourceGlobalOrderSupremum
import SGPT.PSH.SourceSubgeodesicEndpoints
import SGPT.PSH.SourceRelativeGeodesics
import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

/-- The literal finite-interval affine-infimum coefficient, retaining every pole. -/
def sourceSubgeodesicLegendreCoefficient {X : Type*} (curve : ℝ → X → EReal)
    (τ : ℝ) (x : X) : EReal :=
  ⨅ t : Ioo (0 : ℝ) 1, curve (t : ℝ) x - ((t.val * τ : ℝ) : EReal)

private theorem coefficient_eq_sliceInfimum {X : Type*} (curve : ℝ → X → EReal)
    (τ : ℝ) :
    sourceSubgeodesicLegendreCoefficient curve τ =
      sourceSliceInfimum (affineTranslatedCurve curve (-τ) 0) := by
  funext x
  apply iInf_congr
  intro t
  change curve (t : ℝ) x - ((t.val * τ : ℝ) : EReal) =
    curve (t : ℝ) x + (((-τ) * t.val + 0 : ℝ) : EReal)
  rw [show (-τ) * t.val + 0 = -(t.val * τ) by ring, EReal.coe_neg, sub_eq_add_neg]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {omega : KahlerBackground n M}
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}

/-- Actual affine product-PSH and Kiselman produce the genuine coefficient class. -/
theorem SourceSubgeodesicFrom.legendreCoefficient_isThetaPSH
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (τ : ℝ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceSubgeodesicLegendreCoefficient curve τ) := by
  rw [coefficient_eq_sliceInfimum]
  exact (h.affineTranslated (-τ) 0).isThetaPSH_sliceInfimum

omit [ConnectedSpace M] in
private theorem coefficient_le_left
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (τ : ℝ) :
    sourceSubgeodesicLegendreCoefficient curve τ ≤ u₀ := by
  rw [coefficient_eq_sliceInfimum, sourceSliceInfimum_eq_native]
  have hn := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp
    (h.affineTranslated (-τ) 0)
  simpa only [EReal.coe_zero, add_zero] using SubgeodesicInfimum.sliceInfimum_le_left hn

omit [ConnectedSpace M] in
private theorem coefficient_add_le_right
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (τ : ℝ) :
    (fun x ↦ sourceSubgeodesicLegendreCoefficient curve τ x + (τ : EReal)) ≤ u₁ := by
  have hn := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp
    (h.affineTranslated (-τ) 0)
  have hh := SubgeodesicInfimum.sliceInfimum_le_right hn
  intro x
  have hx := add_le_add (hh x) (le_refl (τ : EReal))
  simpa only [← sourceSliceInfimum_eq_native, ← coefficient_eq_sliceInfimum,
    neg_add_cancel, add_zero, add_assoc, ← EReal.coe_add, zero_add, EReal.coe_zero] using hx

private theorem real_convex_support {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Ioo (0 : ℝ) 1) g) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    g c + derivWithin g (Ioi c) c * (t - c) ≤ g t := by
  have hci : c ∈ interior (Ioo (0 : ℝ) 1) := by simpa only [interior_Ioo] using hc
  rcases lt_trichotomy t c with htc | rfl | hct
  · have hs := (hg.slope_le_leftDeriv_of_mem_interior ht hci htc).trans
      (hg.leftDeriv_le_rightDeriv_of_mem_interior hci)
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr htc)).mp hs
    nlinarith
  · simp only [sub_self, mul_zero, add_zero, le_refl]
  · have hs := hg.rightDeriv_le_slope_of_mem_interior hci ht hct
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hct)).mp hs
    nlinarith

private theorem exists_coefficient_gt_of_real_convex_limit {g : ℝ → ℝ} {L r : ℝ}
    (hg : ConvexOn ℝ (Ioo (0 : ℝ) 1) g)
    (hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 L)) (hr : r < L) :
    ∃ τ : ℝ, (r : EReal) <
      ⨅ t : Ioo (0 : ℝ) 1, ((g (t : ℝ) - t.val * τ : ℝ) : EReal) := by
  have hid : Tendsto (fun c : ℝ ↦ c) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun c : ℝ ↦ g (1 / 2) - g c) (𝓝[>] (0 : ℝ))
      (𝓝 (g (1 / 2) - L)) := tendsto_const_nhds.sub hlim
  have hden : Tendsto (fun c : ℝ ↦ 1 / 2 - c) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hid)
  have hA : Tendsto (fun c : ℝ ↦ g c - c * ((g (1 / 2) - g c) / (1 / 2 - c)))
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa only [Pi.div_apply, zero_mul, sub_zero] using
      hlim.sub (hid.mul (hnum.div hden (by norm_num : (1 / 2 : ℝ) ≠ 0)))
  have hsmall : ∀ᶠ c : ℝ in 𝓝[>] 0, c ∈ Ioo 0 (1 / 2) :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨c, hc, hcr⟩ := (hsmall.and (hA.eventually (Ioi_mem_nhds hr))).exists
  have hc1 : c ∈ Ioo (0 : ℝ) 1 := ⟨hc.1, by linarith [hc.2]⟩
  let τ := derivWithin g (Ioi c) c
  have hs := hg.rightDeriv_le_slope_of_mem_interior
    (by simpa only [interior_Ioo] using hc1) (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1) hc.2
  rw [slope_def_field] at hs
  have hintercept : g c - c * ((g (1 / 2) - g c) / (1 / 2 - c)) ≤ g c - c * τ := by
    dsimp [τ]
    nlinarith [mul_le_mul_of_nonneg_left hs hc.1.le]
  refine ⟨τ, (EReal.coe_lt_coe (hcr.trans_le hintercept)).trans_le ?_⟩
  apply le_iInf
  intro t
  apply EReal.coe_le_coe
  have hh := real_convex_support hg hc1 t.property
  dsimp [τ]
  nlinarith

omit [ConnectedSpace M] in
private theorem coefficient_iSup_eq_left_of_limit
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) (x : M)
    (hx : sourceSubgeodesicLeftLimit curve x = u₀ x) :
    (⨆ τ : ℝ, sourceSubgeodesicLegendreCoefficient curve τ x) = u₀ x := by
  apply le_antisymm (iSup_le fun τ ↦ coefficient_le_left h τ x)
  by_cases hbot : u₀ x = ⊥
  · rw [hbot]
    exact bot_le
  have htop : u₀ x ≠ ⊤ := h.1.1 x
  have hleft := tendsto_sourceSubgeodesicLeftLimit h x
  rw [hx] at hleft
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h
  rcases hn.verticalTrace_convexity_dichotomy x with hall | ⟨hfinite, hg⟩
  · have hevent : (fun t ↦ curve t x) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ ↦ (⊥ : EReal)) := by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      exact hall t ht
    have hlimbot : Tendsto (fun t ↦ curve t x) (𝓝[>] (0 : ℝ)) (𝓝 ⊥) :=
      tendsto_const_nhds.congr' hevent.symm
    exact False.elim (hbot (tendsto_nhds_unique hleft hlimbot))
  · have hreal := (EReal.tendsto_toReal htop hbot).comp hleft
    apply le_of_forall_lt
    intro a ha
    obtain ⟨r, har, hru⟩ := EReal.lt_iff_exists_real_btwn.mp ha
    have hr : r < (u₀ x).toReal := by
      rw [← EReal.coe_toReal htop hbot] at hru
      exact EReal.coe_lt_coe_iff.mp hru
    obtain ⟨τ, hrτ⟩ := exists_coefficient_gt_of_real_convex_limit hg hreal hr
    have heq : (⨅ t : Ioo (0 : ℝ) 1,
        (((curve (t : ℝ) x).toReal - t.val * τ : ℝ) : EReal)) =
        sourceSubgeodesicLegendreCoefficient curve τ x := by
      apply iInf_congr
      intro t
      rw [EReal.coe_sub, EReal.coe_toReal (hfinite t.val t.property).1
        (hfinite t.val t.property).2]
    rw [heq] at hrτ
    exact har.trans_le (hrτ.le.trans
      (le_iSup (fun σ : ℝ ↦ sourceSubgeodesicLegendreCoefficient curve σ x) τ))

private theorem coefficient_uscSup_left
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    uscSup (sourceSubgeodesicLegendreCoefficient curve) = u₀ := by
  have hF := h.legendreCoefficient_isThetaPSH
  have hH : (ofFixedModel n M).IsThetaPSH θ
      (uscSup (sourceSubgeodesicLegendreCoefficient curve)) :=
    isThetaPSH_uscSup_of_majorant hF h.1.upperSemicontinuous h.1.1
      (coefficient_le_left h)
  apply le_antisymm
  · exact uscRegularization_le h.1.upperSemicontinuous
      (fun x ↦ iSup_le fun τ ↦ coefficient_le_left h τ x)
  · apply (sourceQuasiEverywhere_le_iff h.1 hH).mp
    apply (sourceQuasiEverywhere_iff_native _).mpr
    have hqe := (sourceQuasiEverywhere_iff_native _).mp
      (sourceSubgeodesicLeftLimit_quasiEverywhere h)
    apply hqe.mono
    intro x hx
    rw [← coefficient_iSup_eq_left_of_limit h x hx]
    exact le_uscRegularization (fun y ↦ ⨆ τ : ℝ,
      sourceSubgeodesicLegendreCoefficient curve τ y) x

private theorem coefficient_timeReversed {X : Type*} (curve : ℝ → X → EReal) (τ : ℝ) :
    sourceSubgeodesicLegendreCoefficient (timeReversedCurve curve) τ =
      fun x ↦ sourceSubgeodesicLegendreCoefficient curve (-τ) x + ((-τ : ℝ) : EReal) := by
  let e : Ioo (0 : ℝ) 1 ≃ Ioo (0 : ℝ) 1 :=
    { toFun := fun t ↦ ⟨1 - t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
      invFun := fun t ↦ ⟨1 - t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
      left_inv := fun t ↦ Subtype.ext (by dsimp; ring)
      right_inv := fun t ↦ Subtype.ext (by dsimp; ring) }
  funext x
  unfold sourceSubgeodesicLegendreCoefficient
  rw [SubgeodesicInfimumThetaPsh.iInf_add_coe]
  calc
    (⨅ t : Ioo (0 : ℝ) 1, timeReversedCurve curve t.val x - ((t.val * τ : ℝ) : EReal)) =
        ⨅ t : Ioo (0 : ℝ) 1,
          (curve (e t).val x - (((e t).val * (-τ) : ℝ) : EReal) + ((-τ : ℝ) : EReal)) := by
      apply iInf_congr
      intro t
      change curve (1 - t.val) x - ((t.val * τ : ℝ) : EReal) =
        curve (1 - t.val) x - (((1 - t.val) * (-τ) : ℝ) : EReal) + ((-τ : ℝ) : EReal)
      have hreal : -(t.val * τ) = -((1 - t.val) * (-τ)) + (-τ) := by ring
      have hs : -((t.val * τ : ℝ) : EReal) =
          -(((1 - t.val) * (-τ) : ℝ) : EReal) + ((-τ : ℝ) : EReal) := by
        exact_mod_cast hreal
      simpa only [sub_eq_add_neg, add_assoc] using
        congrArg (fun z : EReal ↦ curve (1 - t.val) x + z) hs
    _ = _ := e.iInf_comp (g := fun t : Ioo (0 : ℝ) 1 ↦
      curve t.val x - ((t.val * (-τ) : ℝ) : EReal) + ((-τ : ℝ) : EReal))

/-- Both literal spatial USC-sup endpoint identities, including every original pole. -/
theorem SourceSubgeodesicFrom.legendreCoefficient_endpoints
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    uscSup (sourceSubgeodesicLegendreCoefficient curve) = u₀ ∧
      uscSup (fun τ : ℝ ↦ fun x ↦
        sourceSubgeodesicLegendreCoefficient curve τ x + (τ : EReal)) = u₁ := by
  refine ⟨coefficient_uscSup_left h, ?_⟩
  have hn := (sourceSubgeodesicFrom_iff_native omega θ curve u₀ u₁).mp h
  have hrev := (sourceSubgeodesicFrom_iff_native omega θ (timeReversedCurve curve) u₁ u₀).mpr
    hn.timeReversed
  have hh := coefficient_uscSup_left hrev
  rw [show (fun τ : ℝ ↦ fun x ↦
      sourceSubgeodesicLegendreCoefficient curve τ x + (τ : EReal)) =
      (sourceSubgeodesicLegendreCoefficient (timeReversedCurve curve)) ∘ Neg.neg by
        funext τ x
        rw [Function.comp_apply, coefficient_timeReversed, neg_neg]]
  change uscRegularization (fun x ↦ ⨆ τ : ℝ,
    sourceSubgeodesicLegendreCoefficient (timeReversedCurve curve) (-τ) x) = u₁
  have heq : (fun x ↦ ⨆ τ : ℝ,
      sourceSubgeodesicLegendreCoefficient (timeReversedCurve curve) (-τ) x) =
      (fun x ↦ ⨆ τ : ℝ, sourceSubgeodesicLegendreCoefficient (timeReversedCurve curve) τ x) := by
    funext x
    exact (Equiv.neg ℝ).iSup_comp (g := fun τ : ℝ ↦
      sourceSubgeodesicLegendreCoefficient (timeReversedCurve curve) τ x)
  rw [heq]
  exact hh

/-- Every actual joining subgeodesic has TRUE GLOBAL P-equivalent endpoints,
including zero original masses. Positive common backgrounds are internal. -/
theorem SourceSubgeodesicFrom.sourcePEquivalent_endpoints
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    GlobalPComparison.sourcePEquivalent (n := n) u₀ u₁ := by
  let U := sourceSubgeodesicLegendreCoefficient curve
  let V := fun τ : ℝ ↦ fun x ↦ U τ x + (τ : EReal)
  have hU : ∀ τ, (ofFixedModel n M).IsThetaPSH θ (U τ) :=
    h.legendreCoefficient_isThetaPSH
  have hV : ∀ τ, (ofFixedModel n M).IsThetaPSH θ (V τ) :=
    fun τ ↦ sourceThetaPSH_add_const (hU τ) τ
  let T := atlasClosedFormToNative θ
  have hUn (τ : ℝ) : IsThetaPshPotential T.val (U τ) :=
    (isThetaPSH_iff_nativeThetaPotential θ (U τ)).mp (hU τ)
  have hVn (τ : ℝ) : IsThetaPshPotential T.val (V τ) :=
    (isThetaPSH_iff_nativeThetaPotential θ (V τ)).mp (hV τ)
  obtain ⟨C, hC⟩ := ((isThetaPSH_iff_nativeThetaPotential θ u₀).mp h.1).exists_global_upper_bound
  obtain ⟨D, hD⟩ := ((isThetaPSH_iff_nativeThetaPotential θ u₁).mp h.2.1).exists_global_upper_bound
  have hUB : ∃ C : ℝ, ∀ τ x, U τ x ≤ (C : EReal) :=
    ⟨C, fun τ x ↦ (coefficient_le_left h τ x).trans (hC x)⟩
  have hVB : ∃ D : ℝ, ∀ τ x, V τ x ≤ (D : EReal) :=
    ⟨D, fun τ x ↦ (coefficient_add_le_right h τ x).trans (hD x)⟩
  have hUV (τ : ℝ) : GlobalPComparison.sourcePOrder (n := n) (U τ) (V τ) := by
    apply SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega T T (hUn τ) (hVn τ)
    refine ⟨-τ, fun x _ ↦ ?_⟩
    simp only [V, add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero, le_refl]
  have hVU (τ : ℝ) : GlobalPComparison.sourcePOrder (n := n) (V τ) (U τ) :=
    SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega T T (hVn τ) (hUn τ)
      ⟨τ, fun _ _ ↦ le_rfl⟩
  have hleft := sourcePOrder_uscSup omega hU hV hUB hVB hUV
  have hright := sourcePOrder_uscSup omega hV hU hVB hUB hVU
  obtain ⟨he₀, he₁⟩ := h.legendreCoefficient_endpoints
  exact ⟨by simpa only [U, V, he₀, he₁] using hleft,
    by simpa only [U, V, he₀, he₁] using hright⟩

/-- Positive ORIGINAL masses and true GLOBAL equivalence manufacture the
model and both full-mass memberships for the literal all-competitor Perron curve. -/
theorem sourcePerron_isSubgeodesicFrom_of_sourcePEquivalent (omega : KahlerBackground n M)
    (h₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (h₁ : (ofFixedModel n M).IsThetaPSH θ u₁)
    (hpos₀ : 0 < sourcePotentialNonPluripolarMeasure θ u₀ h₀ univ)
    (hpos₁ : 0 < sourcePotentialNonPluripolarMeasure θ u₁ h₁ univ)
    (hequiv : GlobalPComparison.sourcePEquivalent (n := n) u₀ u₁) :
    SourceSubgeodesicFrom omega θ (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ := by
  let T := atlasClosedFormToNative θ
  have hn₀ : IsThetaPshPotential T.val u₀ := (isThetaPSH_iff_nativeThetaPotential θ u₀).mp h₀
  have hn₁ : IsThetaPshPotential T.val u₁ := (isThetaPSH_iff_nativeThetaPotential θ u₁).mp h₁
  have hfixed := (SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith
    omega T hn₀ hn₁ hpos₀ hpos₁).mp hequiv
  have heq : sourceSingularityEnvelope θ u₀ = sourceSingularityEnvelope θ u₁ := by
    simpa only [sourceSingularityEnvelope_eq_native] using
      POrder.pEquivalentWith_iff_envelope_eq.mp hfixed
  have hmodel := sourceOrdinaryEnvelope_model omega h₀ hpos₀
  have hfull₀ : SourceRelativeFullMass θ (sourceSingularityEnvelope θ u₀) u₀ hmodel :=
    (sourceRelativeFullMass_iff_envelope_eq (hφ := hmodel) omega h₀).mpr rfl
  have hfull₁ : SourceRelativeFullMass θ (sourceSingularityEnvelope θ u₀) u₁ hmodel :=
    (sourceRelativeFullMass_iff_envelope_eq (hφ := hmodel) omega h₁).mpr heq.symm
  exact sourcePerron_isSubgeodesicFrom_of_relativeFullMass omega hfull₀ hfull₁

/-- WHOLE original thm:geodexi, with its two original positive masses and
actual product-PSH/global-L1 joining curve. Dimension zero is included. -/
theorem sourceSubgeodesic_exists_iff_sourcePEquivalent (omega : KahlerBackground n M)
    (h₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (h₁ : (ofFixedModel n M).IsThetaPSH θ u₁)
    (hpos₀ : 0 < sourcePotentialNonPluripolarMeasure θ u₀ h₀ univ)
    (hpos₁ : 0 < sourcePotentialNonPluripolarMeasure θ u₁ h₁ univ) :
    (∃ curve : ℝ → M → EReal, SourceSubgeodesicFrom omega θ curve u₀ u₁) ↔
      GlobalPComparison.sourcePEquivalent (n := n) u₀ u₁ := by
  constructor
  · rintro ⟨curve, hcurve⟩
    exact hcurve.sourcePEquivalent_endpoints
  · intro hequiv
    exact ⟨sourcePerronGeodesic omega θ u₀ u₁,
      sourcePerron_isSubgeodesicFrom_of_sourcePEquivalent omega h₀ h₁ hpos₀ hpos₁ hequiv⟩

end SGPT.PSH.VariableComplexAtlas

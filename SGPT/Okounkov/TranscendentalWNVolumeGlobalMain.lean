import SGPT.Okounkov.TranscendentalWNVolumeGlobalBounds
import SGPT.Okounkov.TranscendentalWNCone2
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSet
import SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

/-!
# The first volume formula of the deformation to the normal cone (package WN-VF2)

Blueprint node `tok-wn:formula-volume` (chapter `claude-tok-wn`), route
`tok-wn-vf:punctured`, `tok-wn-vf:legendre-bounds`, `tok-wn-vf:global-legendre-ma` (chapter
`claude-tok-wn-vf`, sub-lemmas in `claude-tok-wn-vf2`); WN21 Theorem 1.6 (1), proved in §4.

* `twistEnvelope_mass`: `∫_X ⟨θ_{v_t}^n⟩ = vol(ξ_t)` (`v_t = V_{θ - tη} + t g`; the measures of
  `v_t` for `θ` and of `V_{θ - tη}` for `θ - tη` agree off `Z`, which neither charges).
* `partialLegendre_mass`: `∫_X ⟨θ_{û_λ}^n⟩ = vol(ξ_{max(c - λ, 0)})` for `λ ∈ [0, b]`
  (`|û_λ - v_t| ≤ C`, `tok-wn-vf:legendre-bounds`).
* `isGlobalLegendreMAData_affineTwist`: WN21's `u` satisfies the hypotheses of WN21
  Theorem 3.5 on `X × ℂ*` with `[a, b] = [0, b]` and the pluripolar set
  `A = E_nK(ξ) ∪ E_nK(ξ_c) ∪ Z`.
* `deformationVolume_of_globalLegendreMA`: `GlobalLegendreMAStatement (m + 1) →
  DeformationVolumeStatement F`: `vol(β) = (n + 1)((b - c) vol(ξ) + ∫₀^c vol(ξ_t) dt)`.
* `deformationVolume_of_local`, `deformationVolumeDifference_of_local`: the same from the local
  identity `PartialLegendreMALocalStatement (m + 1)` (`tok-wn:legendre-ma`, lane WN-LEG) and the
  measurability statement `LegendreMAMeasurableStatement (m + 1)`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Toric

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### Bigness along the segment -/

theorem isThetaPshPotential_thetaPshSupremum_sub_smul {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} {c : ℝ}
    (hξ : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ))
    (hξc : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
      c • RealBottChern.ofRepresentative E.curvature)) {t : ℝ} (ht : t ∈ Icc 0 c) :
    IsBigClass (RealBottChern.ofRepresentative (θ - t • E.curvature)) ∧
    IsThetaPshPotential (θ - t • E.curvature).val (thetaPshSupremum (θ - t • E.curvature).val) := by
  have h := isBigMeetingFirstDivisor_sub_smul_of_mem_Icc F hξ hξc ht
  rw [← ofRepresentative_sub_smul] at h
  have hbig := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp h.1
  exact ⟨hbig, MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _ hbig⟩

theorem legendreLevel_mem_Icc {c lam b : ℝ} (hc : 0 < c) (hlam : lam ∈ Icc 0 b) :
    legendreLevel c lam ∈ Icc 0 c :=
  ⟨legendreLevel_nonneg _ _, max_le (by linarith [hlam.1]) hc.le⟩

/-! ### Masses -/

section Masses

variable [MeasurableSpace F.carrier] [BorelSpace F.carrier]

/-- **`∫_X ⟨θ_{v_t}^n⟩ = vol(ξ_t)`** (`tok-wn:envelopes` (b)). -/
theorem twistEnvelope_mass {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (hE0 : ∀ x, E.weight x ≤ 0) {t : ℝ}
    (hV : IsThetaPshPotential (θ - t • E.curvature).val (thetaPshSupremum (θ - t • E.curvature).val))
    (hv : IsThetaPshPotential θ.val (twistEnvelope F θ E t)) :
    diagonalPotentialMass θ (twistEnvelope F θ E t) hv =
      SGPT.PSH.VariableComplexAtlas.sourceClassVolume
        (RealBottChern.ofRepresentative (θ - t • E.curvature)) := by
  have hEs : E.support = F.flag (1 : Fin (m + 2)) := hE.choose_spec.2.1
  have hZ : IsComplexAnalyticSubset (n := m + 1) E.support :=
    ResidualNef.isComplexAnalyticSubset_support E
  have hZi : interior E.support = ∅ := by rw [hEs]; exact interior_firstFlag F
  have hP := ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hZ hZi
  obtain ⟨hV', hvol⟩ := TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative F.omega
    (θ - t • E.curvature) hV
  rw [hvol]
  have huu' : ∀ x ∉ E.support, thetaPshSupremum (θ - t • E.curvature).val x =
      twistEnvelope F θ E t x + ((-(t * (E.weight x).toReal) : ℝ) : EReal) := by
    intro x hx
    have hwt : E.weight x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hE0 x)
    rw [twistEnvelope, (EReal.coe_toReal hwt hx).symm, ← EReal.coe_mul, EReal.toReal_coe,
      MeteredDivisorPositivity.add_coe_add_neg_coe]
  have h := globalMixedMeasure_restrict_compl_support E t
    (SmoothRealForm.GeometricallyEq.refl _) hv.1 hV'.1 huu'
  have h1 := congrArg (fun ν : Measure F.carrier => ν univ) h
  simp only [Measure.restrict_apply_univ] at h1
  unfold diagonalPotentialMass diagonalPotentialMeasure
  have hn1 := globalMixedMeasure_doesNotChargeManifoldPluripolar
    (θ := fun _ : Fin (m + 1) => θ) (u := fun _ => twistEnvelope F θ E t) (fun _ => hv.1) _ hP
  have hn2 := globalMixedMeasure_doesNotChargeManifoldPluripolar
    (θ := fun _ : Fin (m + 1) => θ - t • E.curvature)
    (u := fun _ => thetaPshSupremum (θ - t • E.curvature).val) (fun _ => hV'.1) _ hP
  rw [← compl_compl E.support] at hn1 hn2
  rw [← measure_congr (ae_eq_univ.mpr hn1), ← h1, measure_congr (ae_eq_univ.mpr hn2)]

omit [MeasurableSpace F.carrier] [BorelSpace F.carrier] in
/-- `v_{t'} ≤ v_t` for `0 ≤ t ≤ t'` (the obstacles `t g` decrease). -/
theorem twistEnvelope_antitone {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (hE0 : ∀ x, E.weight x ≤ 0) {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t')
    (hV : IsThetaPshPotential (θ - t • E.curvature).val (thetaPshSupremum (θ - t • E.curvature).val))
    (hV' : IsThetaPshPotential (θ - t' • E.curvature).val
      (thetaPshSupremum (θ - t' • E.curvature).val)) (x : F.carrier) :
    twistEnvelope F θ E t' x ≤ twistEnvelope F θ E t x := by
  have hEs : E.support = F.flag (1 : Fin (m + 2)) := hE.choose_spec.2.1
  rcases htt'.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hd : 0 < t' - t := sub_pos.mpr hlt
  -- `V_{θ - t'η} + (t' - t) g ≤ V_{θ - tη}`
  have hcomp : IsThetaPshPotential (θ - t • E.curvature).val
      (fun y => thetaPshSupremum (θ - t' • E.curvature).val y + ((t' - t : ℝ) : EReal) * E.weight y) := by
    have h := isThetaPshPotential_twistEnvelope F (θ := θ - t • E.curvature) hE0 hEs hd.le
      (by rwa [show θ - t • E.curvature - (t' - t) • E.curvature = θ - t' • E.curvature by
        rw [sub_sub, ← add_smul, add_sub_cancel]])
    convert h using 2
    simp only [twistEnvelope]
    rw [show θ - t • E.curvature - (t' - t) • E.curvature = θ - t' • E.curvature by
        rw [sub_sub, ← add_smul, add_sub_cancel]]
  have hle := le_thetaPshSupremum hcomp (fun y => by
    have h1 := thetaPshSupremum_le_zero (θ - t' • E.curvature).val y
    have h2 := ereal_coe_mul_nonpos hd.le (hE0 y)
    simpa using add_le_add h1 h2) x
  by_cases hx : E.weight x = ⊥
  · rcases ht.eq_or_lt with rfl | htpos
    · simp only [twistEnvelope, hx, EReal.coe_mul_bot_of_pos (lt_of_le_of_lt ht hlt), EReal.add_bot]
      exact bot_le
    · simp only [twistEnvelope, hx, EReal.coe_mul_bot_of_pos (htpos.trans hlt), EReal.add_bot]
      exact bot_le
  have hwt : E.weight x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hE0 x)
  set g := (E.weight x).toReal
  have hg : E.weight x = (g : EReal) := (EReal.coe_toReal hwt hx).symm
  simp only [twistEnvelope] at hle ⊢
  rw [hg, ← EReal.coe_mul] at hle ⊢
  rw [← EReal.coe_mul]
  have h := add_le_add hle (le_refl ((t * g : ℝ) : EReal))
  refine le_of_eq_of_le ?_ h
  rw [add_assoc, ← EReal.coe_add]
  congr 2; ring

end Masses

/-! ### Local boundedness off `E_nK(ξ) ∪ E_nK(ξ_c) ∪ Z` -/

/-- `(1 - t/c) V_θ + (t/c) V_{θ - cη} ≤ V_{θ - tη}` for `t ∈ [0, c]`. -/
theorem convexComb_le_thetaPshSupremum {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} {c : ℝ} (hc : 0 < c)
    (hV0 : IsThetaPshPotential θ.val (thetaPshSupremum θ.val))
    (hVc : IsThetaPshPotential (θ - c • E.curvature).val
      (thetaPshSupremum (θ - c • E.curvature).val))
    {t : ℝ} (ht : t ∈ Icc 0 c) (x : F.carrier) :
    ((1 - t / c : ℝ) : EReal) * thetaPshSupremum θ.val x +
        ((t / c : ℝ) : EReal) * thetaPshSupremum (θ - c • E.curvature).val x ≤
      thetaPshSupremum (θ - t • E.curvature).val x := by
  rcases ht.1.eq_or_lt with rfl | ht0
  · simp
  rcases ht.2.eq_or_lt with rfl | htc
  · simp [div_self hc.ne']
  have hs0 : 0 < t / c := div_pos ht0 hc
  have hs1 : 0 < 1 - t / c := by rw [sub_pos, div_lt_one hc]; exact htc
  have hs1' : 1 - t / c < 1 := by linarith
  have h := AmbientConvexCurrent.isThetaPshPotential_convexComb_forms hV0 hVc hs1 hs1'
  have hform : (1 - t / c) • θ + (1 - (1 - t / c)) • (θ - c • E.curvature) =
      θ - t • E.curvature := by
    rw [sub_sub_cancel, smul_sub, smul_smul, div_mul_cancel₀ t hc.ne', ← add_sub_assoc,
      ← add_smul, sub_add_cancel, one_smul]
  rw [hform] at h
  have hpot : IsThetaPshPotential (θ - t • E.curvature).val (fun x =>
      ((1 - t / c : ℝ) : EReal) * thetaPshSupremum θ.val x +
        ((t / c : ℝ) : EReal) * thetaPshSupremum (θ - c • E.curvature).val x) := by
    convert h using 2
    rw [ThetaPshConvexCombination.convexComb_apply, sub_sub_cancel]
  exact le_thetaPshSupremum hpot (fun x => by
    have h1 := ereal_coe_mul_nonpos hs1.le (thetaPshSupremum_le_zero θ.val x)
    have h2 := ereal_coe_mul_nonpos hs0.le (thetaPshSupremum_le_zero (θ - c • E.curvature).val x)
    simpa using add_le_add h1 h2) x


/-- The weight of a metrized divisor is locally bounded below off its support. -/
theorem weight_eventually_ge {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] (D : MeteredEffectiveQDivisor n M)
    {x : M} (hx : x ∉ D.support) : ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ((-C : ℝ) : EReal) ≤ D.weight y := by
  set e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W₁, hxW, hpot⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature D hx e hxe
  have hcont : ContinuousAt (fun ζ => (D.weight (e.val.symm ζ)).toReal) (e.val x) :=
    hpot.2.2.1.continuousOn.continuousAt (hpot.1.mem_nhds hxW)
  have hce : ContinuousAt e.val x := e.val.continuousAt hxe
  have h1 : ∀ᶠ y in 𝓝 x, (D.weight (e.val.symm (e.val y))).toReal >
      (D.weight (e.val.symm (e.val x))).toReal - 1 :=
    (hcont.comp hce).eventually (lt_mem_nhds (by
      show _ - 1 < (D.weight (e.val.symm (e.val x))).toReal; linarith))
  have hsupp : IsClosed D.support := (ResidualNef.isComplexAnalyticSubset_support D).isClosed
  refine ⟨-((D.weight (e.val.symm (e.val x))).toReal - 1), ?_⟩
  filter_upwards [h1, hsupp.isOpen_compl.mem_nhds hx, e.val.open_source.mem_nhds hxe]
    with y hy hyD hys
  rw [e.val.left_inv hys] at hy
  rw [neg_neg]
  rcases eq_or_ne (D.weight y) ⊤ with htop | htop
  · rw [htop]; exact le_top
  rw [← EReal.coe_toReal htop hyD]
  exact EReal.coe_le_coe_iff.mpr hy.le

/-- **The non-Kähler locus of a big class is analytic with empty interior.** -/
theorem nonKahlerLocus_analytic_interior {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] (hn : 0 < n)
    {α : RealBottChern n M} (hα : IsBigClass α) :
    IsComplexAnalyticSubset (n := n) (nonKahlerLocus α) ∧ interior (nonKahlerLocus α) = ∅ := by
  refine ⟨NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus hn α hα, ?_⟩
  obtain ⟨T, -, -, hpole⟩ := NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn α hα
  rw [← hpole]
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨y, hy, hyne⟩ := T.strictlyPsh.2 x _ isOpen_interior hx
  exact hyne (mem_poleSet.mp (interior_subset hy))


/-! ### WN21's `u` on `X × ℂ*` -/

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

theorem affineTwist_le_log {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hE0 : ∀ x, E.weight x ≤ 0)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 ≤ c) {w : F.carrier × ProjectiveLine → EReal}
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
    (x : F.carrier) {τ : ℂ} (hτ : τ ≠ 0) :
    affineTwist w b x τ ≤ ((b * Real.log (1 + ‖τ‖ ^ 2) : ℝ) : EReal) := by
  have hq := notMem_centre_affinePoint F x hτ
  have h1 := basePotential_le F hE hμ hEℰ hwμ hq
  have hW1 := baseExceptionalWeight_le_one F E hE0 (x, affinePoint τ)
  have hWpos := baseExceptionalWeight_pos F hE hq
  have h2 : ((c * Real.log (baseExceptionalWeight F E (x, affinePoint τ)) : ℝ) : EReal) ≤ 0 :=
    EReal.coe_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos hc (Real.log_nonpos hWpos.le hW1))
  simpa [affineTwist] using add_le_add (h1.trans h2) (le_refl ((b * Real.log (1 + ‖τ‖ ^ 2) : ℝ) : EReal))

theorem partialLegendre_affineTwist_le {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hE0 : ∀ x, E.weight x ≤ 0)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 ≤ c) {w : F.carrier × ProjectiveLine → EReal}
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal)) (lam : ℝ) (x : F.carrier) :
    partialLegendre (affineTwist w b) lam x ≤ ((b * Real.log 2 : ℝ) : EReal) := by
  refine (iInf_le _ (⟨1, one_ne_zero⟩ : puncturedPlane)).trans ?_
  have h := affineTwist_le_log F hE hE0 hμ hEℰ hc hwμ x one_ne_zero
  simp only [norm_one, one_pow] at h
  simp only [logNormSq, norm_one, one_pow, Real.log_one, mul_zero, EReal.coe_zero, sub_zero]
  norm_num at h ⊢
  exact h

/-- **WN21's `u` satisfies the hypotheses of WN21 Theorem 3.5** on `X × ℂ*`, with `[0, b]` and
`A = E_nK(ξ) ∪ E_nK(ξ_c) ∪ Z`. -/
theorem isGlobalLegendreMAData_affineTwist [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hE0 : ∀ x, E.weight x ≤ 0)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 < c) (hcb : c < b)
    (hξ : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ))
    (hξc : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
      c • RealBottChern.ofRepresentative E.curvature))
    {w : F.carrier × ProjectiveLine → EReal}
    (hw : IsThetaPshPotential (productLineForm θ b).val w)
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
    (hrot : ∀ a : ℂˣ, ‖(a : ℂ)‖ = 1 → ∀ q, w (lineRotation a q) = w q) :
    IsGlobalLegendreMAData θ.val (affineTwist w b) 0 b
      (nonKahlerLocus (RealBottChern.ofRepresentative θ) ∪
        nonKahlerLocus (RealBottChern.ofRepresentative (θ - c • E.curvature)) ∪ E.support) := by
  have hb : 0 < b := hc.trans hcb
  have hEs : E.support = F.flag (1 : Fin (m + 2)) := hE.choose_spec.2.1
  obtain ⟨hbig0, hV0⟩ := isThetaPshPotential_thetaPshSupremum_sub_smul F hξ hξc
    (⟨le_rfl, hc.le⟩ : (0 : ℝ) ∈ Icc 0 c)
  obtain ⟨hbigc, hVc⟩ := isThetaPshPotential_thetaPshSupremum_sub_smul F hξ hξc
    (⟨hc.le, le_rfl⟩ : c ∈ Icc 0 c)
  simp only [zero_smul, sub_zero] at hbig0 hV0
  obtain ⟨hA0, hA0i⟩ := nonKahlerLocus_analytic_interior (Nat.succ_pos m) hbig0
  obtain ⟨hAc, hAci⟩ := nonKahlerLocus_analytic_interior (Nat.succ_pos m) hbigc
  have hZ : IsComplexAnalyticSubset (n := m + 1) E.support :=
    ResidualNef.isComplexAnalyticSubset_support E
  have hZi : interior E.support = ∅ := by rw [hEs]; exact interior_firstFlag F
  refine
    { psh := isPullbackThetaPshPunctured_affineTwist hw.1
      circleInvariant := isCircleInvariant_affineTwist b hrot
      le := hb.le
      eq_bot_of_notMem := fun lam hlam x =>
        partialLegendre_eq_bot_of_le hb.le
          (fun x τ hτ => affineTwist_le_log F hE hE0 hμ hEℰ hc.le hwμ x hτ) hlam x
      pluripolar := manifoldLocallyPluripolar_union (manifoldLocallyPluripolar_union
        (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hA0 hA0i)
        (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hAc hAci))
        (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hZ hZi)
      locallyBounded := ?_ }
  intro lam hlam y hy
  simp only [mem_union, not_or] at hy
  obtain ⟨⟨hy0, hyc⟩, hyZ⟩ := hy
  obtain ⟨N₀, hN₀, a₀, _B₀, hb₀⟩ :=
    BigClassEnvelopeContact.exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus
      (Nat.succ_pos m) θ hbig0 hV0 hy0
  obtain ⟨Nc, hNc, ac, _Bc, hbc⟩ :=
    BigClassEnvelopeContact.exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus
      (Nat.succ_pos m) (θ - c • E.curvature) hbigc hVc hyc
  obtain ⟨Cg, hCg⟩ := weight_eventually_ge E hyZ
  set t := legendreLevel c lam with htdef
  have ht := legendreLevel_mem_Icc hc hlam
  obtain ⟨-, hVt⟩ := isThetaPshPotential_thetaPshSupremum_sub_smul F hξ hξc ht
  refine ⟨|a₀| + |ac| + c * |Cg| + |b * Real.log 2|, ?_⟩
  filter_upwards [hN₀, hNc, hCg] with y' hy'0 hy'c hy'g
  constructor
  · refine le_trans ?_ (twistEnvelope_le_partialLegendre F hE hE0 hμ hEℰ hc hcb hwμ hlam hVt y')
    have hconv := convexComb_le_thetaPshSupremum F hc hV0 hVc ht y'
    have hs0 : 0 ≤ t / c := div_nonneg ht.1 hc.le
    have hs1 : 0 ≤ 1 - t / c := by rw [sub_nonneg, div_le_one hc]; exact ht.2
    have h1 : (((1 - t / c) * a₀ : ℝ) : EReal) ≤ ((1 - t / c : ℝ) : EReal) * thetaPshSupremum θ.val y' := by
      rw [EReal.coe_mul]; exact mul_le_mul_of_nonneg_left (hb₀ y' hy'0).1 (EReal.coe_nonneg.mpr hs1)
    have h2 : (((t / c) * ac : ℝ) : EReal) ≤
        ((t / c : ℝ) : EReal) * thetaPshSupremum (θ - c • E.curvature).val y' := by
      rw [EReal.coe_mul]; exact mul_le_mul_of_nonneg_left (hbc y' hy'c).1 (EReal.coe_nonneg.mpr hs0)
    have h3 : ((t * (-Cg) : ℝ) : EReal) ≤ (t : EReal) * E.weight y' := by
      rw [EReal.coe_mul]; exact mul_le_mul_of_nonneg_left hy'g (EReal.coe_nonneg.mpr ht.1)
    have hsum := add_le_add (le_trans (add_le_add h1 h2) hconv) h3
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (le_of_le_of_eq hsum (by rw [twistEnvelope]))
    rw [← EReal.coe_add] at *
    have e1 : -(1 - t / c) * |a₀| ≤ (1 - t / c) * a₀ := by
      nlinarith [neg_abs_le a₀, abs_nonneg a₀]
    have e2 : -(t / c) * |ac| ≤ (t / c) * ac := by nlinarith [neg_abs_le ac, abs_nonneg ac]
    have e3 : -(t * |Cg|) ≤ t * (-Cg) := by nlinarith [neg_abs_le Cg, le_abs_self Cg, ht.1]
    have e4 : t * |Cg| ≤ c * |Cg| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
    have e5 : (1 - t / c) * |a₀| ≤ |a₀| := by nlinarith [abs_nonneg a₀]
    have e6 : (t / c) * |ac| ≤ |ac| := by
      have : t / c ≤ 1 := (div_le_one hc).mpr ht.2
      nlinarith [abs_nonneg ac]
    nlinarith [abs_nonneg (b * Real.log 2)]
  · refine (partialLegendre_affineTwist_le F hE hE0 hμ hEℰ hc.le hwμ lam y').trans
      (EReal.coe_le_coe_iff.mpr ?_)
    nlinarith [le_abs_self (b * Real.log 2), abs_nonneg a₀, abs_nonneg ac, abs_nonneg Cg]

end Deformation


/-! ### The first volume formula -/

/-- `t ↦ vol(ξ_t)` is antitone on `[0, c]`. -/
theorem classVolumeReal_sub_smul_antitone {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (hE0 : ∀ x, E.weight x ≤ 0) {c : ℝ}
    (hξ : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ))
    (hξc : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
      c • RealBottChern.ofRepresentative E.curvature)) :
    AntitoneOn (fun t => classVolumeReal F (RealBottChern.ofRepresentative θ -
      t • RealBottChern.ofRepresentative E.curvature)) (Icc 0 c) := by
  intro t ht t' ht' htt'
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  have hEs : E.support = F.flag (1 : Fin (m + 2)) := hE.choose_spec.2.1
  obtain ⟨-, hVt⟩ := isThetaPshPotential_thetaPshSupremum_sub_smul F hξ hξc ht
  obtain ⟨-, hVt'⟩ := isThetaPshPotential_thetaPshSupremum_sub_smul F hξ hξc ht'
  have hv := isThetaPshPotential_twistEnvelope F hE0 hEs ht.1 hVt
  have hv' := isThetaPshPotential_twistEnvelope F hE0 hEs ht'.1 hVt'
  have hmono := Pending.diagonalPotentialMass_mono_of_kahler F.omega hv' hv
    ⟨0, fun x _ => by
      simpa using twistEnvelope_antitone F hE hE0 ht.1 htt' hVt hVt' x⟩
  rw [twistEnvelope_mass F hE hE0 hVt' hv', twistEnvelope_mass F hE hE0 hVt hv] at hmono
  simp only [classVolumeReal]
  rw [← ofRepresentative_sub_smul, ← ofRepresentative_sub_smul]
  exact ENNReal.toReal_mono (TranscendentalVolumeConcavity.sourceClassVolume_lt_top F.omega _).ne
    hmono

/-- **`tok-wn:formula-volume`** (WN21 Theorem 1.6 (1)) from the global Monge–Ampère identity of
the partial Legendre transform (`tok-wn-vf:global-legendre-ma`). -/
theorem deformationVolume_of_globalLegendreMA (hglob : GlobalLegendreMAStatement.{u} (m + 1)) :
    DeformationVolumeStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc
  have := compactSpace_normalCone F hμ
  have hb : 0 < b := hc.trans hcb
  have hEs : E.support = F.flag (1 : Fin (m + 2)) := hE.choose_spec.2.1
  set Θt := deformationForm F hμ.contMDiff θ b c Eℰ with hΘt
  obtain ⟨hbigβ, -⟩ := betaBig F E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc hcb hξ hξc.1
  have hCc : (deformationCentre F)ᶜ.Nonempty := by
    rw [nonempty_compl]
    intro h
    have := interior_deformationCentre F
    rw [h, interior_univ] at this
    exact univ_nonempty.ne_empty this
  obtain ⟨q₀, hq₀⟩ := hCc
  obtain ⟨z₀, -, -⟩ := exists_preimage_of_notMem_centre F hμ hq₀
  have : Nonempty 𝒳 := ⟨z₀⟩
  have hũ : IsThetaPshPotential Θt.val (thetaPshSupremum Θt.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum Θt
      ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbigβ)
  obtain ⟨w, hw, hwμ⟩ := exists_basePotential F hE0 hμ hEℰ θ hc.le hũ
  have hrot := basePotential_rotation F hE hμ hEℰ hw hwμ
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  let _ : MeasurableSpace (F.carrier × ProjectiveLine) := borel _
  have : BorelSpace (F.carrier × ProjectiveLine) := ⟨rfl⟩
  rw [deformationVolumeReal_eq_comap F hμ hEℰ hũ hw hwμ]
  have hν := isPuncturedProductMAMeasure_comap (N := m + 1) (Y := F.carrier) hw.1
  have hdata := isGlobalLegendreMAData_affineTwist F hE hE0 hμ hEℰ hc hcb hξ hξc hw hwμ hrot
  rw [hglob F.carrier θ (affineTwist w b) 0 b _ hdata _ hν univ MeasurableSet.univ]
  -- the integrand
  set f : ℝ → ℝ := fun lam => classVolumeReal F (RealBottChern.ofRepresentative θ -
    legendreLevel c lam • RealBottChern.ofRepresentative E.curvature) with hfdef
  have hint : EqOn (fun lam => globalMixedMeasure (fun _ : Fin (m + 1) => θ)
      (fun _ => partialLegendre (affineTwist w b) lam)
      (fun _ => thetaPlurisubharmonic_partialLegendre hdata.psh hdata.circleInvariant lam) univ)
      (fun lam => ENNReal.ofReal (f lam)) (Icc 0 b) := by
    intro lam hlam
    have ht := legendreLevel_mem_Icc hc hlam
    obtain ⟨-, hVt⟩ := isThetaPshPotential_thetaPshSupremum_sub_smul F hξ hξc ht
    have hvt := isThetaPshPotential_twistEnvelope F hE0 hEs ht.1 hVt
    have hlow := twistEnvelope_le_partialLegendre F hE hE0 hμ hEℰ hc hcb hwμ hlam hVt
    obtain ⟨C, hC⟩ := partialLegendre_le_twistEnvelope_add F hE hE0 hμ hEℰ hc hcb hw hwμ hrot
      hlam hVt
    have hUpot : IsThetaPshPotential θ.val (partialLegendre (affineTwist w b) lam) := by
      refine ⟨thetaPlurisubharmonic_partialLegendre hdata.psh hdata.circleInvariant lam,
        fun x O hO hxO => ?_⟩
      obtain ⟨y, hy, hyne⟩ := hvt.2 x O hO hxO
      exact ⟨y, hy, fun h => hyne (le_bot_iff.mp (h ▸ hlow y))⟩
    have hmass := PluripolarCapacityDichotomy.diagonalPotentialMass_eq_of_le_add F.omega θ
      hUpot hvt (c₁ := 0) (fun x => by simpa using hlow x) hC
    change diagonalPotentialMass θ _ hUpot = _
    rw [hmass, twistEnvelope_mass F hE hE0 hVt hvt, ofRepresentative_sub_smul, hfdef]
    simp only [classVolumeReal]
    rw [ENNReal.ofReal_toReal (TranscendentalVolumeConcavity.sourceClassVolume_lt_top F.omega _).ne]
  rw [setLIntegral_congr_fun measurableSet_Icc hint]
  -- `f` is monotone on `[0, b]`, hence integrable
  have hanti := classVolumeReal_sub_smul_antitone F hE hE0 hξ hξc
  have hfmono : MonotoneOn f (Icc 0 b) := by
    intro x hx y hy hxy
    exact hanti (legendreLevel_mem_Icc hc hy) (legendreLevel_mem_Icc hc hx)
      (max_le_max (by linarith) le_rfl)
  have hfint : IntegrableOn f (Icc 0 b) := hfmono.integrableOn_isCompact isCompact_Icc
  have hfnn : ∀ lam, 0 ≤ f lam := fun lam => ENNReal.toReal_nonneg
  rw [← ofReal_integral_eq_lintegral_ofReal hfint (Eventually.of_forall fun lam => hfnn lam),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun lam => hfnn lam),
    ENNReal.toReal_natCast]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.le]
  have hfi0c : IntervalIntegrable f volume 0 c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hc.le).mpr
      (hfint.mono_set (Icc_subset_Icc le_rfl hcb.le))
  have hfic : IntervalIntegrable f volume c b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hcb.le).mpr
      (hfint.mono_set (Icc_subset_Icc hc.le le_rfl))
  rw [← intervalIntegral.integral_add_adjacent_intervals hfi0c hfic]
  have h1 : ∫ lam in c..b, f lam = (b - c) * classVolumeReal F (RealBottChern.ofRepresentative θ) := by
    rw [intervalIntegral.integral_congr (g := fun _ => classVolumeReal F
      (RealBottChern.ofRepresentative θ)) ?_, intervalIntegral.integral_const, smul_eq_mul]
    intro lam hlam
    rw [uIcc_of_le hcb.le] at hlam
    simp only [hfdef, legendreLevel, max_eq_right (sub_nonpos.mpr hlam.1), zero_smul, sub_zero]
  have h2 : ∫ lam in (0 : ℝ)..c, f lam = ∫ t in (0 : ℝ)..c, classVolumeReal F
      (RealBottChern.ofRepresentative θ - t • RealBottChern.ofRepresentative E.curvature) := by
    rw [intervalIntegral.integral_congr (g := fun lam => classVolumeReal F
      (RealBottChern.ofRepresentative θ - (c - lam) • RealBottChern.ofRepresentative E.curvature))
      ?_, intervalIntegral.integral_comp_sub_left (fun t => classVolumeReal F
        (RealBottChern.ofRepresentative θ - t • RealBottChern.ofRepresentative E.curvature)) c]
    · simp only [sub_self, sub_zero]
    · intro lam hlam
      rw [uIcc_of_le hc.le] at hlam
      simp only [hfdef, legendreLevel, max_eq_left (sub_nonneg.mpr hlam.2)]
  rw [h1, h2]
  ring

/-- **`tok-wn:formula-volume`** (WN21 Theorem 1.6 (1)), conditional on the local Monge–Ampère
identity of the partial Legendre transform (`tok-wn:legendre-ma`) and on the measurable
dependence of its integrand on `λ`. -/
theorem deformationVolume_of_local (hloc : PartialLegendreMALocalStatement (m + 1))
    (hmeas : LegendreMAMeasurableStatement (m + 1)) : DeformationVolumeStatement F :=
  deformationVolume_of_globalLegendreMA F
    (globalLegendreMA_of_local_of_measurable (Nat.succ_pos m) hloc hmeas)

/-- **`tok-wn:formula-volume`, second half** (WN21 Corollary 4.7), under the same hypotheses. -/
theorem deformationVolumeDifference_of_local (hloc : PartialLegendreMALocalStatement (m + 1))
    (hmeas : LegendreMAMeasurableStatement (m + 1)) : DeformationVolumeDifferenceStatement F :=
  deformationVolumeDifference_of_volume F (deformationVolume_of_local F hloc hmeas)


end SGPT.Okounkov.TranscendentalWN

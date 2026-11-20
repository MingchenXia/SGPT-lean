import SGPT.Okounkov.TranscendentalWNVolumeGlobalProduct
import SGPT.Okounkov.TranscendentalWNVolumeFibre
import SGPT.Okounkov.TranscendentalWNDeformationBig
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.ProperMappingInduction
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

/-!
# The deformation off the central and infinite fibres (package WN-VF2)

Blueprint node `tok-wn-vf:punctured` (chapter `claude-tok-wn-vf`, sub-lemmas in
`claude-tok-wn-vf2`); WN21 §4, Proposition 4.2 and the beginning of the proof of Theorem 1.6 (1).

Let `ũ = V_θ̃` on the deformation `𝒳` and `Θ = p₁^*θ + b p₂^*ω_FS` on `X × ℙ¹`
(`productLineForm`), so that `θ̃ = μ^*Θ - c η_ℰ` (`pullback_productLineForm_geometricallyEq`).

* `exists_basePotential`: `ũ + c log |s_ℰ|²` (which is `μ^*Θ`-psh off `ℰ` and `≤ 0`) extends
  across `ℰ` and descends to a `Θ`-psh potential `w` on `X × ℙ¹` with
  `w ∘ μ = ũ + c log |s_ℰ|²` off `ℰ` — WN21's `u - b log (1 + |τ|²)` (Proposition 4.2), now on all
  of `X × ℙ¹`.
* `basePotential_le`: `w ≤ c log W` off `Z × {0}`.
* `basePotential_rotation`: `w` is invariant under the rotations `[v₀ : v₁] ↦ [a v₀ : v₁]`,
  `|a| = 1` (by comparison with `ũ`: `w ∘ r_a ∘ μ - c log |s_ℰ|²` is a competitor for `V_θ̃`).
* `globalMixedMeasure_restrict_compl_support`: on the complement of the support of a metrized
  divisor `D`, the non-pluripolar measure of `u - s log |s_D|²` for `θ - s η_D` is that of `u`
  for `θ` (`-log |s_D|²` is a smooth local potential of `η_D` there).
* `deformationVolumeReal_eq_comap`: `vol(β) = ∫_𝒳 ⟨θ̃_ũ^{n+1}⟩ = ∫_{X × ℂ*} ⟨Θ_w^{n+1}⟩`: `ℰ` and `X × {0, ∞}` are
  analytic and not charged, and `μ` is an isomorphism over `(Z × {0})ᶜ`
  (`ModificationMassInvariance.globalMixedMeasure_restrict_preimage_eq_map`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Toric

/-! ### Change of representative off the support of a metrized divisor -/

section Gauge

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

theorem ereal_add_neg_add (a : EReal) (r s : ℝ) :
    (a + ((-s : ℝ) : EReal)) + ((r + s : ℝ) : EReal) = a + (r : EReal) := by
  induction a using EReal.rec with
  | bot => simp
  | top => rw [EReal.top_add_coe, EReal.top_add_coe, EReal.top_add_coe]
  | coe a => rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]; congr 1; ring

/-- **Gauge change off the support of a metrized divisor.**  If `θ' = θ - s η_D` and
`u' = u - s log |s_D|²` off `supp D`, the non-pluripolar measures of `(θ', u')` and `(θ, u)`
agree on `(supp D)ᶜ`. -/
theorem globalMixedMeasure_restrict_compl_support {θ θ' : ClosedRealOneOneForm n M}
    (D : MeteredEffectiveQDivisor n M) (s : ℝ)
    (hθ' : θ'.val.GeometricallyEq (θ - s • D.curvature).val) {u u' : M → EReal}
    (hu : ThetaPlurisubharmonic θ.val u) (hu' : ThetaPlurisubharmonic θ'.val u')
    (huu' : ∀ x ∉ D.support, u' x = u x + ((-(s * (D.weight x).toReal) : ℝ) : EReal)) :
    (globalMixedMeasure (fun _ : Fin n => θ') (fun _ => u') (fun _ => hu')).restrict D.supportᶜ =
      (globalMixedMeasure (fun _ : Fin n => θ) (fun _ => u) (fun _ => hu)).restrict D.supportᶜ := by
  have hDc : IsClosed D.support := (ResidualNef.isComplexAnalyticSubset_support D).isClosed
  refine ModificationMassInvariance.restrict_eq_of_locally_eq fun y hy => ?_
  obtain ⟨P, hyP⟩ := exists_patch_containing (fun _ : Fin n => hu) y
  obtain ⟨W₁, hyW₁, hpot⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature D hy P.chart
      (P.source_subset hyP)
  let D' : Opens (ComplexModel n) :=
    ⟨(P.domain : Set (ComplexModel n)) ∩ W₁ ∩ P.chart.val.symm ⁻¹' D.supportᶜ,
      (P.chart.val.continuousOn_symm.mono (fun z hz => P.domain_le_target hz.1)).isOpen_inter_preimage
        (P.domain.isOpen.inter hpot.1) hDc.isOpen_compl⟩
  have hD'P : D' ≤ P.domain := fun z hz => hz.1.1
  have hpot' : IsSmoothLocalPotential (-D.curvature).val P.chart (D' : Set (ComplexModel n))
      (fun ζ => (D.weight (P.chart.val.symm ζ)).toReal) :=
    hpot.mono D'.isOpen fun z hz => hz.1.2
  have hθform : θ - s • D.curvature = θ + s • (-D.curvature) := by
    rw [smul_neg, sub_eq_add_neg]
  let Q : Patch (fun _ : Fin n => θ') (fun _ => u') :=
    { chart := P.chart
      domain := D'
      domain_le_target := fun z hz => P.domain_le_target (hD'P hz)
      potential := fun i z => P.potential i z + s * (D.weight (P.chart.val.symm z)).toReal
      localPotential := fun i => by
        have h := FirstPass.LocalPotentials.localPotential_add
          (a := θ) (b := s • (-D.curvature))
          ((P.localPotential i).mono D'.isOpen hD'P)
          (FirstPass.LocalPotentials.localPotential_smul (a := -D.curvature) hpot' s)
        rw [← hθform] at h
        exact (hθ'.localPotential_iff _ _ _).mpr (by simpa only [smul_eq_mul] using h)
      plurisubharmonic := fun i => by
        refine SGPT.Siu.plurisubharmonicOn_congr_of_isOpen D'.isOpen
          ((P.plurisubharmonic i).mono hD'P) fun z hz => ?_
        change u (P.chart.val.symm z) + _ = u' (P.chart.val.symm z) + _
        rw [huu' _ hz.2]
        exact (ereal_add_neg_add _ _ _).symm }
  let P' := P.restrict D' hD'P
  have hsrc : (Q.source : Set M) = P'.source := rfl
  have hcorr : ∀ i, EqOn (Q.corrected i) (P'.corrected i) Q.domain := by
    intro i z hz
    change u' (P.chart.val.symm z) + _ = u (P.chart.val.symm z) + _
    rw [huu' _ hz.2]
    exact ereal_add_neg_add _ _ _
  have hcong : MixedNonPluripolar.mixedTruncationLimitMeasure Q.domain Q.corrected
      Q.plurisubharmonic = MixedNonPluripolar.mixedTruncationLimitMeasure Q.domain P'.corrected
        P'.plurisubharmonic :=
    MixedNonPluripolar.mixedTruncationLimitMeasure_congr _ _ hcorr
  have hmeas : patchMeasure Q = patchMeasure P' := by
    show Q.pushMeasure _ = P'.pushMeasure _
    rw [hcong]
    rfl
  refine ⟨P'.source, P'.source.isOpen, ⟨P.source_subset hyP, ⟨⟨hyP.2, ?_⟩, ?_⟩⟩, ?_, ?_⟩
  · exact hyW₁
  · change P.chart.val.symm (P.chart.val y) ∈ D.supportᶜ
    rw [P.chart.val.left_inv (P.source_subset hyP)]; exact hy
  · intro x hx
    have h := hx.2.2
    change P.chart.val.symm (P.chart.val x) ∈ D.supportᶜ at h
    rwa [P.chart.val.left_inv hx.1] at h
  · rw [← hsrc, globalMixedMeasure_restrict_patch (fun _ => hu') Q, hmeas, hsrc,
      globalMixedMeasure_restrict_patch (fun _ => hu) P']

end Gauge

/-! ### Pluripolar fibres of `Y × ℙ¹` -/

section Fibres

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

theorem projectiveZero_ne_projectiveInfinity : projectiveZero ≠ projectiveInfinity := by
  intro h
  have := projectiveLineHomeomorph.injective h
  exact OnePoint.coe_ne_infty _ this

theorem interior_singleton_projectiveLine (p : ProjectiveLine) : interior ({p} : Set ProjectiveLine) = ∅ := by
  by_contra hne
  have hopen : IsOpen ({p} : Set ProjectiveLine) := by
    obtain ⟨q, hq⟩ := nonempty_iff_ne_empty.mpr hne
    have hqp : q = p := mem_singleton_iff.mp (interior_subset hq)
    subst hqp
    have : interior ({q} : Set ProjectiveLine) = {q} :=
      Subset.antisymm interior_subset (singleton_subset_iff.mpr hq)
    rw [← this]; exact isOpen_interior
  rcases isClopen_iff.mp ⟨isClosed_singleton, hopen⟩ with h | h
  · exact singleton_ne_empty p h
  · have h0 : projectiveZero ∈ ({p} : Set ProjectiveLine) := h ▸ mem_univ _
    have h1 : projectiveInfinity ∈ ({p} : Set ProjectiveLine) := h ▸ mem_univ _
    exact projectiveZero_ne_projectiveInfinity ((mem_singleton_iff.mp h0).trans
      (mem_singleton_iff.mp h1).symm)

/-- **`Y × {p}` is pluripolar** in `Y × ℙ¹`. -/
theorem manifoldLocallyPluripolar_prod_singleton (p : ProjectiveLine) :
    ManifoldLocallyPluripolar (n := N + 1) ((univ : Set Y) ×ˢ ({p} : Set ProjectiveLine)) := by
  have hA : IsComplexAnalyticSubset (n := N + 1)
      ((Prod.snd : Y × ProjectiveLine → ProjectiveLine) ⁻¹' {p}) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_snd (n := N) (m := 1))
      (ProperMappingInduction.isComplexAnalyticSubset_of_finite (finite_singleton p))
  have hset : (univ : Set Y) ×ˢ ({p} : Set ProjectiveLine) =
      (Prod.snd : Y × ProjectiveLine → ProjectiveLine) ⁻¹' {p} := by
    ext q; simp
  rw [hset]
  refine ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hA ?_
  rw [← hset, interior_prod_eq, interior_singleton_projectiveLine, prod_empty]

end Fibres

/-! ### The base potential on `X × ℙ¹` -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- `μ^*Θ = θ̃ + c η_ℰ` (geometrically). -/
theorem pullback_productLineForm_geometricallyEq (hμ : IsNormalConeDeformation F μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ)
    (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) :
    (ClosedRealOneOneForm.pullback hμ.contMDiff (productLineForm θ b)).val.GeometricallyEq
      (deformationForm F hμ.contMDiff θ b c Eℰ + c • Eℰ.curvature).val := by
  intro e z hz
  unfold productLineForm deformationForm
  rw [NefCoreKahlerCurrent.pullback_add_smul]
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul, sub_add_cancel]
  have h1 := (pullback_comp_geometricallyEq' (contMDiff_fst (n := m + 1) (m := 1)) hμ.contMDiff
    θ.val e hz).symm
  have h2 := (pullback_comp_geometricallyEq' (contMDiff_snd (n := m + 1) (m := 1)) hμ.contMDiff
    projectiveNativeFSClosedForm.val e hz).symm
  simp only [ClosedRealOneOneForm.pullback_val] at h1 h2 ⊢
  rw [h1, h2]

/-- `θ̃ = μ^*Θ - c η_ℰ` (geometrically). -/
theorem deformationForm_geometricallyEq (hμ : IsNormalConeDeformation F μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ)
    (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) :
    (deformationForm F hμ.contMDiff θ b c Eℰ).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hμ.contMDiff (productLineForm θ b) - c • Eℰ.curvature).val := by
  intro e z hz
  have h := pullback_productLineForm_geometricallyEq F hμ θ b c Eℰ e hz
  simp only [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul] at h ⊢
  rw [h, add_sub_cancel_right]

theorem weight_le_zero_of_deformationMetric {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE0 : ∀ x, E.weight x ≤ 0) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) (z : 𝒳) : Eℰ.weight z ≤ 0 := by
  rw [hEℰ.weight_eq, ENNReal.log_le_zero_iff]
  exact ENNReal.ofReal_le_one.mpr (baseExceptionalWeight_le_one F E hE0 _)

/-- **The base potential** (WN21 Proposition 4.2, read on `X × ℙ¹`): `ũ + c log |s_ℰ|²` extends
across `ℰ` and descends to a `Θ`-psh potential `w` on `X × ℙ¹`. -/
theorem exists_basePotential {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE0 : ∀ x, E.weight x ≤ 0) (hμ : IsNormalConeDeformation F μ)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    {b c : ℝ} (hc : 0 ≤ c)
    (huT : IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ).val
      (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val)) :
    ∃ w : F.carrier × ProjectiveLine → EReal,
      IsThetaPshPotential (productLineForm θ b).val w ∧
      ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal) := by
  have := compactSpace_normalCone F hμ
  set Θt := deformationForm F hμ.contMDiff θ b c Eℰ with hΘt
  set uT := thetaPshSupremum Θt.val with huTdef
  obtain ⟨hA, hAi⟩ := isComplexAnalyticSubset_support_exceptional F hEℰ
  set v : 𝒳 → EReal := fun z => uT z + ((-(-c * (Eℰ.weight z).toReal) : ℝ) : EReal) with hvdef
  have hoff : ThetaPshOff (Θt - (-c) • Eℰ.curvature).val Eℰ.support v :=
    SGPT.Siu.thetaPshOff_sub_smul_weight huT.1 Eℰ (-c)
  have hv0 : ∀ z, v z ≤ 0 := by
    intro z
    have h1 := thetaPshSupremum_le_zero Θt.val z
    have h2 : (Eℰ.weight z).toReal ≤ 0 :=
      EReal.toReal_nonpos (weight_le_zero_of_deformationMetric F hE0 hEℰ z)
    have : ((-(-c * (Eℰ.weight z).toReal) : ℝ) : EReal) ≤ 0 :=
      EReal.coe_nonpos.mpr (by nlinarith)
    simpa [hvdef] using add_le_add h1 this
  have hbd : LocallyBoundedAboveOff Eℰ.support v := fun x =>
    ⟨univ, univ_mem, 0, fun y _ _ => by simpa using hv0 y⟩
  obtain ⟨hext, hoffeq, -⟩ :=
    TranscendentalLifting.thetaPsh_extend_across_analytic (Θt - (-c) • Eℰ.curvature) hA hAi hoff hbd
  have hform : Θt - (-c) • Eℰ.curvature = Θt + c • Eℰ.curvature := by
    rw [neg_smul, sub_neg_eq_add]
  rw [hform] at hext
  have hext' : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hμ.contMDiff (productLineForm θ b)).val
      (extensionAcross Eℰ.support v) :=
    ((pullback_productLineForm_geometricallyEq F hμ θ b c Eℰ).thetaPlurisubharmonic_iff _).mpr hext
  have hnd : LocallyNondegenerate (extensionAcross Eℰ.support v) := by
    intro x O hO hxO
    have hnot : ¬ O ⊆ Eℰ.support := fun hsub => by
      have := interior_maximal hsub hO
      rw [hAi] at this
      exact this hxO
    obtain ⟨x', hx'O, hx'A⟩ := not_subset.mp hnot
    obtain ⟨y, hy, hyfin⟩ := huT.2 x' (O ∩ Eℰ.supportᶜ) (hO.inter hA.isClosed.isOpen_compl)
      ⟨hx'O, hx'A⟩
    refine ⟨y, hy.1, ?_⟩
    rw [hoffeq y hy.2]
    intro hbot
    rw [hvdef, EReal.add_eq_bot_iff] at hbot
    rcases hbot with h | h
    · exact hyfin h
    · exact EReal.coe_ne_bot _ h
  obtain ⟨w, hw, hwμ⟩ := AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification
    (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hμ) (productLineForm θ b)
    (w := extensionAcross Eℰ.support v) ⟨hext', hnd⟩
  refine ⟨w, hw, fun z hz => ?_⟩
  rw [hwμ, hoffeq z (hEℰ.support_eq ▸ hz)]
  simp only [hvdef, neg_mul, neg_neg]


/-! ### Properties of the base potential -/

theorem exists_preimage_of_notMem_centre (hμ : IsNormalConeDeformation F μ)
    {q : F.carrier × ProjectiveLine} (hq : q ∉ deformationCentre F) :
    ∃ z, z ∉ exceptionalSet F μ ∧ μ z = q := by
  obtain ⟨z, hz, rfl⟩ := (isIsomorphismOver_normalCone F hμ).1.surjOn hq
  exact ⟨z, hz, rfl⟩

/-- **`w ≤ c log W` off `Z × {0}`** (`ũ ≤ 0`). -/
theorem basePotential_le {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hμ : IsNormalConeDeformation F μ)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} {w : F.carrier × ProjectiveLine → EReal}
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
    {q : F.carrier × ProjectiveLine} (hq : q ∉ deformationCentre F) :
    w q ≤ ((c * Real.log (baseExceptionalWeight F E q) : ℝ) : EReal) := by
  obtain ⟨z, hz, rfl⟩ := exists_preimage_of_notMem_centre F hμ hq
  obtain ⟨-, hwt⟩ := weight_eq_coe_of_notMem F hE hEℰ hz
  rw [hwμ z hz, hwt, EReal.toReal_coe]
  calc thetaPshSupremum _ z + ((c * Real.log (baseExceptionalWeight F E (μ z)) : ℝ) : EReal)
      ≤ 0 + ((c * Real.log (baseExceptionalWeight F E (μ z)) : ℝ) : EReal) :=
        add_le_add (thetaPshSupremum_le_zero _ z) le_rfl
    _ = _ := zero_add _

theorem projectiveTorusAction_projectiveZero (a : ℂˣ) :
    projectiveTorusAction a projectiveZero = projectiveZero := by
  have h := projectiveTorusAction_finite a 0
  rw [mul_zero] at h
  exact h

theorem projectiveTorusAction_inv_apply (a : ℂˣ) (p : ProjectiveLine) :
    projectiveTorusAction a⁻¹ (projectiveTorusAction a p) = p := by
  rw [← projectiveTorusAction_mul, inv_mul_cancel, projectiveTorusAction_one]

theorem lineRotation_mem_centre_iff (a : ℂˣ) (q : F.carrier × ProjectiveLine) :
    lineRotation a q ∈ deformationCentre F ↔ q ∈ deformationCentre F := by
  simp only [mem_deformationCentre_iff, lineRotation]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => by rw [h, projectiveTorusAction_projectiveZero]⟩
  rw [← projectiveTorusAction_inv_apply a q.2, h, projectiveTorusAction_projectiveZero]

theorem projectiveWeight_projectiveTorusAction {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) (i : Fin 2)
    (p : ProjectiveLine) : projectiveWeight i (projectiveTorusAction a p) = projectiveWeight i p := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [projectiveTorusAction, Projectivization.map_mk, projectiveWeight_mk]
  conv_rhs => rw [← Projectivization.mk_rep p, projectiveWeight_mk]
  fin_cases i <;> simp [projectiveTorusLinear, ha]

theorem baseExceptionalWeight_lineRotation (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) (q : F.carrier × ProjectiveLine) :
    baseExceptionalWeight F E (lineRotation a q) = baseExceptionalWeight F E q := by
  rw [baseExceptionalWeight_eq, baseExceptionalWeight_eq]
  simp only [lineRotation, projectiveWeight_projectiveTorusAction ha]

/-- **Rotation invariance of the base potential** (`tok-wn-vf:punctured`: circle invariance of
WN21's `u`). -/
theorem basePotential_rotation {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E)
    (hμ : IsNormalConeDeformation F μ)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} {w : F.carrier × ProjectiveLine → EReal}
    (hw : IsThetaPshPotential (productLineForm θ b).val w)
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal)) :
    ∀ a : ℂˣ, ‖(a : ℂ)‖ = 1 → ∀ q, w (lineRotation a q) = w q := by
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  set Θt := deformationForm F hμ.contMDiff θ b c Eℰ with hΘt
  obtain ⟨hA, hAi⟩ := isComplexAnalyticSubset_support_exceptional F hEℰ
  have hC : IsComplexAnalyticSubset (n := m + 1 + 1) (deformationCentre F) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (isClosedSubmanifold_deformationCentre F)
  -- one direction for every unit `a`
  have hle : ∀ a : ℂˣ, ‖(a : ℂ)‖ = 1 → ∀ q, w (lineRotation a q) ≤ w q := by
    intro a ha
    have hr : ThetaPlurisubharmonic (productLineForm θ b).val (fun q => w (lineRotation a q)) :=
      thetaPlurisubharmonic_comp_rotation hw.1 ha
    have hrμ : ThetaPlurisubharmonic (Θt + c • Eℰ.curvature).val
        (fun z => w (lineRotation a (μ z))) := by
      have h := GlobalPotentialPullback.thetaPlurisubharmonic_comp hμ.contMDiff hr
      rw [← ClosedRealOneOneForm.pullback_val] at h
      exact ((pullback_productLineForm_geometricallyEq F hμ θ b c Eℰ).thetaPlurisubharmonic_iff
        _).mp h
    have hoff := SGPT.Siu.thetaPshOff_sub_smul_weight hrμ Eℰ c
    rw [add_sub_cancel_right] at hoff
    set φ : 𝒳 → EReal := fun z => w (lineRotation a (μ z)) +
      ((-(c * (Eℰ.weight z).toReal) : ℝ) : EReal) with hφ
    have hφle : ∀ z ∉ Eℰ.support, φ z ≤ 0 := by
      intro z hz
      rw [hEℰ.support_eq] at hz
      have hq : μ z ∉ deformationCentre F := hz
      have hrq : lineRotation a (μ z) ∉ deformationCentre F :=
        fun h => hq ((lineRotation_mem_centre_iff F a _).mp h)
      have h1 := basePotential_le F hE hμ hEℰ hwμ hrq
      rw [baseExceptionalWeight_lineRotation F E ha] at h1
      obtain ⟨-, hwt⟩ := weight_eq_coe_of_notMem F hE hEℰ hz
      rw [hφ]
      simp only
      rw [hwt, EReal.toReal_coe]
      calc w (lineRotation a (μ z)) + ((-(c * Real.log (baseExceptionalWeight F E (μ z))) : ℝ) : EReal)
          ≤ ((c * Real.log (baseExceptionalWeight F E (μ z)) : ℝ) : EReal) +
              ((-(c * Real.log (baseExceptionalWeight F E (μ z))) : ℝ) : EReal) :=
            add_le_add h1 le_rfl
        _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
    -- a finite value off `ℰ`
    have hne : ∃ z ∉ Eℰ.support, φ z ≠ ⊥ := by
      have hCc : (deformationCentre F)ᶜ.Nonempty := by
        rw [nonempty_compl]
        intro h
        have := interior_deformationCentre F
        rw [h, interior_univ] at this
        exact univ_nonempty.ne_empty this
      obtain ⟨q₁, hq₁⟩ := hCc
      obtain ⟨q₂, hq₂C, hq₂⟩ := hw.2 q₁ _ (isClosed_deformationCentre F).isOpen_compl hq₁
      set q₀ := lineRotation a⁻¹ q₂
      have hq₀ : q₀ ∉ deformationCentre F :=
        fun h => hq₂C ((lineRotation_mem_centre_iff F a⁻¹ _).mp h)
      obtain ⟨z₀, hz₀, hμz₀⟩ := exists_preimage_of_notMem_centre F hμ hq₀
      refine ⟨z₀, hEℰ.support_eq ▸ hz₀, fun hbot => ?_⟩
      rw [hφ] at hbot
      simp only at hbot
      rw [EReal.add_eq_bot_iff] at hbot
      rcases hbot with h | h
      · apply hq₂
        rw [← h, hμz₀]
        simp only [q₀, lineRotation]
        rw [← projectiveTorusAction_mul, mul_inv_cancel, projectiveTorusAction_one]
      · exact EReal.coe_ne_bot _ h
    have hcomp := le_thetaPshSupremum_of_thetaPshOff Θt hA hAi hoff hφle hne
    have hoffC : ∀ q ∉ deformationCentre F, w (lineRotation a q) ≤ w q := by
      intro q hq
      obtain ⟨z, hz, rfl⟩ := exists_preimage_of_notMem_centre F hμ hq
      have h1 := hcomp z (hEℰ.support_eq ▸ hz)
      rw [hwμ z hz]
      have h2 := add_le_add h1 (le_refl ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
      rw [hφ] at h2
      simp only at h2
      have h3 : ∀ (A : EReal) (t : ℝ), A + ((-t : ℝ) : EReal) + (t : EReal) = A := fun A t => by
        simpa using MeteredDivisorPositivity.add_coe_add_neg_coe A (-t)
      rwa [h3] at h2
    exact le_of_le_off_analytic hC (interior_deformationCentre F) hw.1 hr hoffC
  intro a ha q
  refine le_antisymm (hle a ha q) ?_
  have h := hle a⁻¹ (by rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]) (lineRotation a q)
  simpa [lineRotation, projectiveTorusAction_inv_apply] using h


theorem affinePoint_eq (τ : ℂ) : affinePoint τ = projectiveLineHomeomorph ((τ : ℂ) : OnePoint ℂ) := by
  change projectiveLineHomeomorph (projectiveFiniteChart.symm
    (projectiveModelEquiv.symm (projectiveModelEquiv τ))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, projectiveFiniteChart_symm]

theorem compl_image_affineEmbedding_subset :
    (affineEmbedding '' ((univ : Set F.carrier) ×ˢ puncturedPlane))ᶜ ⊆
      (univ : Set F.carrier) ×ˢ ({projectiveZero} : Set ProjectiveLine) ∪
        (univ : Set F.carrier) ×ˢ ({projectiveInfinity} : Set ProjectiveLine) := by
  intro q hq
  by_contra hne
  simp only [mem_union, mem_prod, mem_univ, true_and, mem_singleton_iff, not_or] at hne
  apply hq
  obtain ⟨p', hp'⟩ := projectiveLineHomeomorph.surjective q.2
  induction p' using OnePoint.rec with
  | infty => exact absurd hp'.symm hne.2
  | coe τ =>
    have hτ : τ ≠ 0 := by
      rintro rfl; exact hne.1 hp'.symm
    refine ⟨(q.1, τ), ⟨mem_univ _, hτ⟩, ?_⟩
    change (q.1, affinePoint τ) = q
    rw [affinePoint_eq, hp']

/-- **`vol(β) = ∫_{X × ℂ*} ⟨Θ_w^{n+1}⟩`** (`tok-wn-vf:punctured`; WN21 §4, proof of Theorem 1.6 (1)):
the volume of `β` is the mass of the non-pluripolar measure of `w`, pulled back to `X × ℂ`
along `(x, τ) ↦ (x, [τ : 1])`, on `X × ℂ*`. -/
theorem deformationVolumeReal_eq_comap [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    [MeasurableSpace (F.carrier × ProjectiveLine)] [BorelSpace (F.carrier × ProjectiveLine)]
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ}
    (hũ : IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ).val
      (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val))
    {w : F.carrier × ProjectiveLine → EReal} (hw : IsThetaPshPotential (productLineForm θ b).val w)
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal)) :
    deformationVolumeReal F hμ
        (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ)) =
      ((globalMixedMeasure (fun _ : Fin (m + 1 + 1) => productLineForm θ b) (fun _ => w)
        (fun _ => hw.1)).comap affineEmbedding ((univ : Set F.carrier) ×ˢ puncturedPlane)).toReal := by
  unfold deformationVolumeReal
  let : MeasurableSpace 𝒳 := borel 𝒳
  have : BorelSpace 𝒳 := ⟨rfl⟩
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  obtain ⟨κ⟩ := nonempty_kahler_normalCone F hμ
  set Θt := deformationForm F hμ.contMDiff θ b c Eℰ with hΘt
  obtain ⟨hV, hvol⟩ := TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative κ Θt hũ
  rw [hvol]
  congr 1
  obtain ⟨hA, hAi⟩ := isComplexAnalyticSubset_support_exceptional F hEℰ
  -- `𝒳` is nonempty
  have hCc : (deformationCentre F)ᶜ.Nonempty := by
    rw [nonempty_compl]
    intro h
    have := interior_deformationCentre F
    rw [h, interior_univ] at this
    exact univ_nonempty.ne_empty this
  obtain ⟨q₀, hq₀⟩ := hCc
  obtain ⟨z₀, -, -⟩ := exists_preimage_of_notMem_centre F hμ hq₀
  have : Nonempty 𝒳 := ⟨z₀⟩
  -- step 1: `ℰ` is not charged
  have hnullE : globalMixedMeasure (fun _ : Fin (m + 1 + 1) => Θt)
      (fun _ => thetaPshSupremum Θt.val) (fun _ => hV.1) Eℰ.support = 0 :=
    globalMixedMeasure_doesNotChargeManifoldPluripolar _ _
      (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hA hAi)
  have h1 : DiagonalMass.diagonalPotentialMass Θt (thetaPshSupremum Θt.val) hV =
      (globalMixedMeasure (fun _ : Fin (m + 1 + 1) => Θt) (fun _ => thetaPshSupremum Θt.val)
        (fun _ => hV.1)).restrict Eℰ.supportᶜ univ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_congr (ae_eq_univ.mpr (by rw [compl_compl]; exact hnullE))).symm
  -- step 2: gauge change off `ℰ`
  have hwμpsh : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hμ.contMDiff (productLineForm θ b)).val (fun z => w (μ z)) := by
    have h := GlobalPotentialPullback.thetaPlurisubharmonic_comp hμ.contMDiff hw.1
    rwa [← ClosedRealOneOneForm.pullback_val] at h
  have huu' : ∀ x ∉ Eℰ.support, thetaPshSupremum Θt.val x =
      w (μ x) + ((-(c * (Eℰ.weight x).toReal) : ℝ) : EReal) := by
    intro x hx
    rw [hwμ x (hEℰ.support_eq ▸ hx), MeteredDivisorPositivity.add_coe_add_neg_coe]
  have h2 := globalMixedMeasure_restrict_compl_support Eℰ c
    (deformationForm_geometricallyEq F hμ θ b c Eℰ) hwμpsh hV.1 huu'
  -- step 3: naturality over `(Z × {0})ᶜ`
  have hN : IsOpen (deformationCentre F)ᶜ := (isClosed_deformationCentre F).isOpen_compl
  have hiso := isIsomorphismOver_normalCone F hμ
  have h3 := ModificationMassInvariance.globalMixedMeasure_restrict_preimage_eq_map
    hμ.contMDiff hN hiso (fun _ : Fin (m + 1 + 1) => hw.1) (fun _ => hwμpsh)
  have hsupp : Eℰ.supportᶜ = μ ⁻¹' (deformationCentre F)ᶜ := by
    rw [hEℰ.support_eq]; rfl
  have hs'm : AEMeasurable (ModificationMassInvariance.invOver μ (deformationCentre F)ᶜ)
      ((globalMixedMeasure (fun _ : Fin (m + 1 + 1) => productLineForm θ b) (fun _ => w)
        (fun _ => hw.1)).restrict (deformationCentre F)ᶜ) :=
    (ModificationMassInvariance.continuousOn_invOver hμ.contMDiff hN hiso).aemeasurable
      hN.measurableSet
  -- step 4: `X × {0, ∞}` is not charged
  have hP0 := manifoldLocallyPluripolar_prod_singleton (N := m + 1) (Y := F.carrier) projectiveZero
  have hPinf := manifoldLocallyPluripolar_prod_singleton (N := m + 1) (Y := F.carrier) projectiveInfinity
  set μX := globalMixedMeasure (fun _ : Fin (m + 1 + 1) => productLineForm θ b) (fun _ => w)
    (fun _ => hw.1) with hμX
  have hnullC : μX (deformationCentre F) = 0 := by
    refine measure_mono_null ?_ (globalMixedMeasure_doesNotChargeManifoldPluripolar _ _ hP0)
    intro q hq
    exact ⟨mem_univ _, ((mem_deformationCentre_iff F).mp hq).2⟩
  have hnullI : μX (affineEmbedding '' ((univ : Set F.carrier) ×ˢ puncturedPlane))ᶜ = 0 :=
    measure_mono_null (compl_image_affineEmbedding_subset F)
      (globalMixedMeasure_doesNotChargeManifoldPluripolar _ _
        (manifoldLocallyPluripolar_union hP0 hPinf))
  have hemb : MeasurableEmbedding (affineEmbedding (Y := F.carrier)) :=
    isOpenEmbedding_affineEmbedding.measurableEmbedding
  rw [h1, h2, hsupp, h3, Measure.map_apply_of_aemeasurable hs'm MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, hemb.comap_apply]
  rw [measure_congr (ae_eq_univ.mpr (by rw [compl_compl]; exact hnullC)),
    measure_congr (ae_eq_univ.mpr hnullI)]

end Deformation

end SGPT.Okounkov.TranscendentalWN

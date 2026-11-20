import SGPT.Okounkov.TranscendentalWNVolumeCompetitor
import SGPT.Okounkov.TranscendentalWNDeformationBeta
import SGPT.Okounkov.TranscendentalWNDeformationWeight
import SGPT.Okounkov.TranscendentalVolumeConcavityACVolume
import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent
import SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent

/-!
# Restricted volumes of the fibres and of the strict transform (package WN-VF)

Blueprint nodes `tok-wn:formula-fibre` and `tok-wn:formula-X-prime` (chapter `claude-tok-wn`)
with the sub-lemmas `tok-wn-vf:*` of `claude-tok-wn-vf`; WN21 Theorem 1.6 (2), (3).

Let `ũ = V_θ̃` (`thetaPshSupremum`, the envelope `P_θ̃(0)` with minimal singularities in `β`).

* `restrictedVolume_fibre` (`tok-wn:formula-fibre`): for `τ ≠ 0` and the section `s` of `μ` over
  `x ↦ (x, τ)`, `ũ ∘ s ≥ V_θ + b log N₀(τ)` (the competitor `V_θ ∘ π_X ∘ μ + b log N₀ ∘ π_{ℙ¹} ∘ μ
  - c log |s_ℰ|²`, `TranscendentalWNVolumeCompetitor`), hence `ũ ∘ s` has minimal
  singularities in `s^*β = ξ`, and so has the restriction of every potential with minimal
  singularities; since `X_τ` meets the Kähler locus of `β` (`BetaBigStatement`), the restricted
  volume is the mass of `ũ ∘ s` (`volconc:restricted-identification`), i.e. `vol(ξ)`.
* `restrictedVolume_strictTransform` (`tok-wn:formula-X-prime`): along the lift `ι'` of
  `x ↦ (x, 0)`, `ι'^*θ̃ = θ - cη` (`pullback_deformationForm_centralSection`), so
  `ũ ∘ ι' ≤ V_{θ - cη}`; conversely the competitor `(V_{θ - cη} + c g) ∘ π_X ∘ μ + b log N₁ ∘ π_{ℙ¹}
  ∘ μ - c log |s_ℰ|²` equals `V_{θ - cη}` on `X' \ ℰ ≅ X \ Z` (`N₁ = 1`, `log |s_ℰ|² = g` there),
  so `ũ ∘ ι' ≥ V_{θ - cη}` off `Z`, hence everywhere (two quasi-psh functions comparable off a
  nowhere dense analytic set).  Thus `ũ ∘ ι'` has minimal singularities in `ξ_c` and the
  restricted volume is `vol(ξ_c)`.

This route does not use the partial Legendre transform (WN21 Lemma 4.8 is replaced by the
explicit competitor).  Both results are **conditional on `BetaBigStatement F`**
(`tok-wn:beta-big`, WN21 Proposition 4.1, package WN-DEF), used only for the identification of
the restricted volume with the restricted mass of `ũ`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

/-! ### Generalities on envelopes -/

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Cohomologous forms have comparable envelopes**: if `{θ'} = {θ}` and `PSH(M, θ) ≠ ∅`, every
`θ'`-psh potential is `≤ V_θ + C`. -/
theorem le_thetaPshSupremum_add_of_class_eq [CompactSpace M] [Nonempty M]
    {θ θ' : ClosedRealOneOneForm n M}
    (h : RealBottChern.ofRepresentative θ' = RealBottChern.ofRepresentative θ)
    {u : M → EReal} (hu : IsThetaPshPotential θ'.val u) :
    ∃ C : ℝ, ∀ x, u x ≤ thetaPshSupremum θ.val x + (C : EReal) := by
  obtain ⟨g, hg, heq⟩ := (RealBottChern.ofRepresentative_eq_iff θ' θ).mp h
  have hug : IsThetaPshPotential θ.val (fun x => u x - (g x : EReal)) :=
    thetaPshPotential_sub_smooth hg heq hu
  obtain ⟨C, hC⟩ := FirstPass.thetaPshSupremum_minimalSingularities θ.val θ.2.1 θ.2.2
    hug.1.hasSmoothLocalPotentials ⟨_, hug⟩ _ hug
  have hgc : Continuous g := ProductTestForms.ChartSmooth.continuous hg
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hgc.continuousOn
  refine ⟨C + g x₀, fun x => ?_⟩
  have h1 := hC x (mem_univ x)
  have h2 : g x ≤ g x₀ := hx₀ (mem_univ x)
  have hu' : u x = (u x - (g x : EReal)) + (g x : EReal) := by
    rw [sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add, neg_add_cancel,
      EReal.coe_zero, add_zero]
  calc u x = (u x - (g x : EReal)) + (g x : EReal) := hu'
    _ ≤ (thetaPshSupremum θ.val x + (C : EReal)) + (g x₀ : EReal) :=
        add_le_add h1 (EReal.coe_le_coe_iff.mpr h2)
    _ = thetaPshSupremum θ.val x + ((C + g x₀ : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]

/-- **Comparison off an analytic set**: if `u, v ∈ PSH(M, θ)` and `v ≤ u` off a nowhere dense
analytic set `A`, then `v ≤ u` everywhere (`max(u, v) = u` off `A`, hence everywhere). -/
theorem le_of_le_off_analytic {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hAi : interior A = ∅) {θ : SmoothRealForm n M 2} {u v : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) (hv : ThetaPlurisubharmonic θ v)
    (hle : ∀ x ∉ A, v x ≤ u x) (x : M) : v x ≤ u x := by
  have hmax := BoundedGlobalProduct.ThetaPlurisubharmonic.max hu hv
  have heq := AnalyticModificationPotentialDescent.eq_of_eq_off_analytic_set hA hAi hmax hu
    (fun y hy => max_eq_left (hle y hy)) x
  exact (le_max_right (u x) (v x)).trans heq.le

end General

/-! ### The Kähler form along a section -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- Along a holomorphic `ι : X → 𝒳` with `π_X ∘ μ ∘ ι = id`, the Kähler form
`(π_X μ)^*ω + κ` of `𝒳` pulls back to a Kähler form. -/
theorem exists_kahlerBackground_pullback_isKahler (hμ : IsNormalConeDeformation F μ)
    {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hπ : ∀ x, (μ (ι x)).1 = x) :
    ∃ w : KahlerBackground (m + 1 + 1) 𝒳,
      (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler := by
  obtain ⟨κ⟩ := nonempty_kahler_normalCone F hμ
  set P := ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμ.contMDiff)
    F.omega.form with hPdef
  have hP : P.val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive _ F.omega.isSemipositive
  refine ⟨⟨P + (1 : ℝ) • κ.form,
    NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive κ hP one_pos⟩, ?_⟩
  have hX : (fun z => (μ z).1) ∘ ι = id := funext hπ
  have h1 : (ClosedRealOneOneForm.pullback hι P).val.GeometricallyEq F.omega.form.val := by
    intro e z hz
    rw [hPdef, ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
      ← pullback_comp_geometricallyEq' (contMDiff_deformationProjX F hμ.contMDiff) hι _ e hz,
      pullback_congr_map hX _ contMDiff_id]
    exact SmoothRealForm.pullback_id_geometricallyEq _ e hz
  have hgeq : (ClosedRealOneOneForm.pullback hι (P + (1 : ℝ) • κ.form)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hι κ.form + (1 : ℝ) • F.omega.form).val := by
    intro e z hz
    rw [NefCoreKahlerCurrent.pullback_add_smul]
    simp only [ClosedRealOneOneForm.coeff_add, one_smul]
    rw [h1 e hz]
    exact add_comm _ _
  exact hgeq.isKahler_iff.mpr (NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive F.omega
    (ClosedRealOneOneForm.pullback_isSemipositive hι κ.isSemipositive) one_pos)

/-- **The restricted volume along a section with minimal-singularity restriction.**  For a
holomorphic `ι : X → 𝒳` with `π_X ∘ μ ∘ ι = id`, a big class `β = {θ̃}` whose Kähler locus meets
`ι(X)`, and `V_{ι^*θ̃} ≤ V_θ̃ ∘ ι + C`, the restricted volume is `vol {ι^*θ̃}`. -/
theorem sectionRestrictedVolume_toReal_eq [CompactSpace 𝒳] (hμ : IsNormalConeDeformation F μ)
    {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hπ : ∀ x, (μ (ι x)).1 = x) (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative Θ))
    (hmeet : ∃ y, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative Θ))
    (hlow : ∃ C : ℝ, ∀ x, thetaPshSupremum (ClosedRealOneOneForm.pullback hι Θ).val x ≤
      thetaPshSupremum Θ.val (ι x) + (C : EReal)) :
    (sectionRestrictedVolume F ι hι (RealBottChern.ofRepresentative Θ)).toReal =
      classVolumeReal F (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hι Θ)) := by
  have : Nonempty 𝒳 := ⟨ι (Classical.arbitrary F.carrier)⟩
  obtain ⟨w, hw⟩ := exists_kahlerBackground_pullback_isKahler F hμ hι hπ
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  obtain ⟨hV, hR⟩ := TranscendentalVolumeConcavity.restrictedVolume_eq_restrictedMinimalMass hι w
    hw Θ ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig) hmeet
  set θ' := ClosedRealOneOneForm.pullback hι Θ with hθ'
  obtain ⟨hV', hvol⟩ := TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative
    F.omega θ' hV
  have hmass : diagonalPotentialMass θ' (fun y => thetaPshSupremum Θ.val (ι y)) hV =
      diagonalPotentialMass θ' (thetaPshSupremum θ'.val) hV' := by
    apply le_antisymm
    · exact diagonalPotentialMass_mono_of_kahler F.omega hV hV'
        (FirstPass.thetaPshSupremum_minimalSingularities θ'.val θ'.2.1 θ'.2.2
          hV.1.hasSmoothLocalPotentials ⟨_, hV⟩ _ hV)
    · obtain ⟨C, hC⟩ := hlow
      exact diagonalPotentialMass_mono_of_kahler F.omega hV' hV ⟨C, fun x _ => hC x⟩
  unfold sectionRestrictedVolume classVolumeReal
  rw [← TranscendentalVolumeConcavity.restrictedVolume_eq_classRestrictedVolume, hR, hmass,
    ← hvol]

/-! ### The fibres `X_τ`, `τ ≠ 0` -/

/-- The exceptional set of a metric of `𝒪(ℰ)` is analytic and nowhere dense. -/
theorem isComplexAnalyticSubset_support_exceptional [CompactSpace 𝒳]
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) :
    IsComplexAnalyticSubset (n := m + 1 + 1) Eℰ.support ∧ interior Eℰ.support = ∅ :=
  ⟨ResidualNef.isComplexAnalyticSubset_support Eℰ, by
    rw [hEℰ.support_eq]; exact interior_exceptionalSet F hμ⟩

omit [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- A section over `x ↦ (x, τ)`, `τ ≠ 0`, avoids `ℰ`. -/
theorem section_notMem_exceptionalSet {p : ProjectiveLine} (hp : p ≠ projectiveZero)
    {s : F.carrier → 𝒳} (hμs : ∀ x, μ (s x) = (x, p)) (x : F.carrier) :
    s x ∉ exceptionalSet F μ := by
  intro h
  have h' : μ (s x) ∈ deformationCentre F := h
  rw [hμs, mem_deformationCentre_iff] at h'
  exact hp h'.2

/-- **The lower bound on the fibres** (`tok-wn-vf:fibre-lower`): for `τ ≠ 0`, `0 < c < b` and the
section `s` of `μ` over `x ↦ (x, τ)`, `V_θ + b log N₀(τ) ≤ V_θ̃ ∘ s`. -/
theorem thetaPshSupremum_add_le_fibre {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hE0 : ∀ x, E.weight x ≤ 0)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hθ : IsThetaPshPotential θ.val (thetaPshSupremum θ.val)) {b c : ℝ} (hc : 0 < c)
    (hcb : c < b) {p : ProjectiveLine} (hp : p ≠ projectiveZero) {s : F.carrier → 𝒳}
    (hμs : ∀ x, μ (s x) = (x, p)) (x : F.carrier) :
    thetaPshSupremum θ.val x + ((b * Real.log (projectiveWeight 0 p) : ℝ) : EReal) ≤
      thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val (s x) := by
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  have hb : 0 < b := hc.trans hcb
  set w := deformationCompetitor F μ (thetaPshSupremum θ.val) (projectiveLogWeight 0) b c Eℰ
    with hwdef
  have hoff := thetaPshOff_deformationCompetitor F hμ hθ.1
    (thetaPlurisubharmonic_projectiveLogWeight 0) hb c Eℰ
  obtain ⟨hA, hAi⟩ := isComplexAnalyticSubset_support_exceptional F hEℰ
  have hsA : ∀ y, s y ∉ Eℰ.support := fun y => by
    rw [hEℰ.support_eq]; exact section_notMem_exceptionalSet F hp hμs y
  have hval : ∀ y, thetaPshSupremum θ.val y + ((b * Real.log (projectiveWeight 0 p) : ℝ) : EReal)
      ≤ w (s y) := by
    intro y
    obtain ⟨hWpos, hwt⟩ := weight_eq_coe_of_notMem F hE hEℰ
      (section_notMem_exceptionalSet F hp hμs y)
    have hW1 : baseExceptionalWeight F E (μ (s y)) ≤ 1 := baseExceptionalWeight_le_one F E hE0 _
    have hlog : Real.log (baseExceptionalWeight F E (μ (s y))) ≤ 0 := Real.log_nonpos hWpos.le hW1
    have h0 : (0 : EReal) ≤ ((-(c * Real.log (baseExceptionalWeight F E (μ (s y)))) : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (by nlinarith)
    rw [hwdef, deformationCompetitor, hwt, EReal.toReal_coe]
    rw [hμs] at h0 ⊢
    rw [projectiveLogWeight_zero_eq_coe hp, ← EReal.coe_mul]
    calc thetaPshSupremum θ.val y + ((b * Real.log (projectiveWeight 0 p) : ℝ) : EReal)
        = thetaPshSupremum θ.val y + ((b * Real.log (projectiveWeight 0 p) : ℝ) : EReal) + 0 :=
          (add_zero _).symm
      _ ≤ _ := add_le_add le_rfl h0
  have hle := le_thetaPshSupremum_of_thetaPshOff (deformationForm F hμ.contMDiff θ b c Eℰ) hA hAi
    hoff (fun z hz => deformationCompetitor_fibre_le_zero F hE hEℰ
      (fun y => thetaPshSupremum_le_zero _ y) hb hc.le hcb.le (hEℰ.support_eq ▸ hz)) ?_
  · exact (hval x).trans (hle (s x) (hsA x))
  · obtain ⟨y, -, hy⟩ := hθ.2 x univ isOpen_univ (mem_univ x)
    refine ⟨s y, hsA y, fun hbot => hy ?_⟩
    have h := hval y
    rw [hwdef, hbot, le_bot_iff, EReal.add_eq_bot_iff] at h
    rcases h with h | h
    · exact h
    · exact absurd h (EReal.coe_ne_bot _)

/-- **`tok-wn:formula-fibre`** (WN21 Theorem 1.6 (2)), conditional on `tok-wn:beta-big`
(`BetaBigStatement`, used for `X_τ ∩ K(β) ≠ ∅`): `vol_{𝒳|X_τ}(β) = vol(ξ)` for `τ ≠ 0`, and
potentials with minimal singularities restrict to potentials with minimal singularities. -/
theorem restrictedVolume_fibre (hbeta : BetaBigStatement F) : FibreRestrictedVolumeStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc p hp s hs hμs
  have := compactSpace_normalCone F hμ
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ with hΘ
  have hθbig := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξ.1
  have hθV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hθbig
  have hclass : RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hs Θ) =
      RealBottChern.ofRepresentative θ :=
    ofRepresentative_pullback_deformationForm_fibreSection F hμ hE hEℰ.weight_eq hEℰ.support_eq
      θ b c hp hs hμs
  have hV' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hs Θ).val
      (thetaPshSupremum (ClosedRealOneOneForm.pullback hs Θ).val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _
      (by rw [hclass]; exact hθbig)
  obtain ⟨C₁, hC₁⟩ := le_thetaPshSupremum_add_of_class_eq hclass hV'
  set r := b * Real.log (projectiveWeight 0 p) with hr
  have hlow : ∃ C : ℝ, ∀ x, thetaPshSupremum (ClosedRealOneOneForm.pullback hs Θ).val x ≤
      thetaPshSupremum Θ.val (s x) + (C : EReal) := by
    refine ⟨C₁ - r, fun x => ?_⟩
    have h2 := thetaPshSupremum_add_le_fibre F hE hE0 hμ hEℰ hθV hc hcb hp hμs x
    calc thetaPshSupremum (ClosedRealOneOneForm.pullback hs Θ).val x
        ≤ thetaPshSupremum θ.val x + (C₁ : EReal) := hC₁ x
      _ = thetaPshSupremum θ.val x + (r : EReal) + ((C₁ - r : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add, add_sub_cancel]
      _ ≤ thetaPshSupremum Θ.val (s x) + ((C₁ - r : ℝ) : EReal) := add_le_add h2 le_rfl
  obtain ⟨hbigβ, hfib, -, -⟩ := hbeta E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc hcb hξ hξc.1
  have hmeet : ∃ y, s y ∉ nonKahlerLocus (RealBottChern.ofRepresentative Θ) := by
    obtain ⟨z, hz, hzK⟩ := hfib p hp
    have hz2 : (μ z).2 = p := (Set.mem_prod.mp hz).2
    have hzC : μ z ∉ deformationCentre F := fun h =>
      hp (hz2 ▸ ((mem_deformationCentre_iff F).mp h).2)
    refine ⟨(μ z).1, ?_⟩
    have heq : z = s (μ z).1 := eq_of_map_eq_of_notMem F hμ hzC (by
      rw [hμs]; exact Prod.ext rfl hz2)
    rw [← heq]
    exact hzK
  refine ⟨?_, ?_⟩
  · rw [sectionRestrictedVolume_toReal_eq F hμ hs (fun x => by rw [hμs]) Θ hbigβ hmeet hlow,
      hclass]
  · intro w hw hwmin
    obtain ⟨C₂, hC₂⟩ := hwmin
    obtain ⟨C, hC⟩ := hlow
    have hle : ∀ x, thetaPshSupremum (ClosedRealOneOneForm.pullback hs Θ).val x ≤
        w (s x) + ((C₂ + C : ℝ) : EReal) := fun x =>
      calc thetaPshSupremum (ClosedRealOneOneForm.pullback hs Θ).val x
          ≤ thetaPshSupremum Θ.val (s x) + (C : EReal) := hC x
        _ ≤ w (s x) + (C₂ : EReal) + (C : EReal) := add_le_add (hC₂ (s x) (mem_univ _)) le_rfl
        _ = w (s x) + ((C₂ + C : ℝ) : EReal) := by rw [add_assoc, ← EReal.coe_add]
    refine ⟨⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hs hw.1, ?_⟩,
      ⟨C₂ + C, fun x _ => hle x⟩⟩
    refine (hV'.sub_const (C₂ + C)).2.mono fun x => ?_
    have h := add_le_add (hle x) (le_refl (((-(C₂ + C) : ℝ) : EReal)))
    rw [MeteredDivisorPositivity.add_coe_add_neg_coe] at h
    show thetaPshSupremum (ClosedRealOneOneForm.pullback hs Θ).val x - ((C₂ + C : ℝ) : EReal) ≤
      w (s x)
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact h

/-! ### The strict transform `X'` -/

/-- **Every lift of `x ↦ (x, 0)` parametrizes `X'`**: its range is the strict transform. -/
theorem range_eq_strictCentralFibre (hμ : IsNormalConeDeformation F μ) {ι : F.carrier → 𝒳}
    (hι : Continuous ι) (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) :
    range ι = strictCentralFibre F μ := by
  have hoff : ∀ x, x ∉ F.flag (1 : Fin (m + 2)) →
      ι x ∈ μ ⁻¹' (centralBase F \ deformationCentre F) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · simp [hμι, mem_centralBase_iff]
    · simpa [hμι, mem_deformationCentre_iff] using hx
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hdense : Dense (F.flag (1 : Fin (m + 2)))ᶜ := by
      rw [dense_iff_closure_eq, closure_compl, interior_firstFlag F, compl_empty]
    have hcl : x ∈ closure (F.flag (1 : Fin (m + 2)))ᶜ := hdense.closure_eq ▸ mem_univ x
    have himg : ι x ∈ closure (ι '' (F.flag (1 : Fin (m + 2)))ᶜ) :=
      mem_closure_image hι.continuousAt hcl
    refine closure_mono ?_ himg
    rintro _ ⟨y, hy, rfl⟩
    exact hoff y hy
  · have hcompact : IsCompact (range ι) := isCompact_range hι
    refine closure_minimal ?_ hcompact.isClosed
    intro z hz
    refine ⟨(μ z).1, ?_⟩
    have hz0 : (μ z).2 = projectiveZero := (mem_centralBase_iff F).mp hz.1
    have hzC : μ z ∉ deformationCentre F := hz.2
    exact (eq_of_map_eq_of_notMem F hμ hzC (by rw [hμι, ← hz0])).symm

omit [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- A lift of `x ↦ (x, 0)` meets `ℰ` exactly over `Z`. -/
theorem lift_mem_exceptionalSet_iff {ι : F.carrier → 𝒳}
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) (x : F.carrier) :
    ι x ∈ exceptionalSet F μ ↔ x ∈ F.flag (1 : Fin (m + 2)) := by
  show μ (ι x) ∈ deformationCentre F ↔ _
  rw [hμι, mem_deformationCentre_iff]
  simp

/-- **The strict-transform competitor is `≤ 0`**: `φ = V + c g` with `V ≤ 0`, `ℓ = log N₁`,
`0 < c ≤ b` (since `W ≥ e^g N₁`). -/
theorem deformationCompetitor_strict_le_zero {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ)
    {V : F.carrier → EReal} (hV : ∀ x, V x ≤ 0) {b c : ℝ} (hc : 0 < c) (hcb : c ≤ b)
    {z : 𝒳} (hz : z ∉ exceptionalSet F μ) :
    deformationCompetitor F μ (fun x => V x + (c : EReal) * E.weight x) (projectiveLogWeight 1)
      b c Eℰ z ≤ 0 := by
  have hb : 0 < b := hc.trans_le hcb
  refine deformationCompetitor_le_zero F hE hEℰ hz ?_
  obtain ⟨hWpos, -⟩ := weight_eq_coe_of_notMem F hE hEℰ hz
  set x := (μ z).1
  set p := (μ z).2
  by_cases hg : E.weight x = ⊥
  · simp only [hg, EReal.coe_mul_bot_of_pos hc, EReal.add_bot, EReal.bot_add, bot_le]
  by_cases hN : projectiveWeight 1 p = 0
  · have hbot : projectiveLogWeight 1 p = ⊥ := by
      rw [projectiveLogWeight, hN, ENNReal.ofReal_zero, ENNReal.log_zero]
    simp only [hbot, EReal.coe_mul_bot_of_pos hb, EReal.add_bot, bot_le]
  have hN1 : 0 < projectiveWeight 1 p := lt_of_le_of_ne (projectiveWeight_nonneg 1 p) (Ne.symm hN)
  set r := (E.weight x).toReal with hrdef
  have hgr : E.weight x = (r : EReal) := (EReal.coe_toReal (weight_ne_top F hE x) hg).symm
  have hexp : (EReal.exp (E.weight x)).toReal = Real.exp r := by
    rw [hgr, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos r).le]
  have hW : Real.exp r * projectiveWeight 1 p ≤ baseExceptionalWeight F E (μ z) := by
    rw [← hexp]; exact exp_mul_projectiveWeight_one_le_baseExceptionalWeight F E (μ z)
  have hlogW : r + Real.log (projectiveWeight 1 p) ≤ Real.log (baseExceptionalWeight F E (μ z)) := by
    have h := Real.log_le_log (mul_pos (Real.exp_pos r) hN1) hW
    rwa [Real.log_mul (Real.exp_pos r).ne' hN1.ne', Real.log_exp] at h
  have hlog1 : Real.log (projectiveWeight 1 p) ≤ 0 :=
    Real.log_nonpos (projectiveWeight_nonneg 1 p) (projectiveWeight_le_one 1 p)
  rw [hgr, projectiveLogWeight_eq_coe hN1, ← EReal.coe_mul, ← EReal.coe_mul]
  calc V x + ((c * r : ℝ) : EReal) + ((b * Real.log (projectiveWeight 1 p) : ℝ) : EReal)
      ≤ 0 + ((c * r : ℝ) : EReal) + ((b * Real.log (projectiveWeight 1 p) : ℝ) : EReal) :=
        add_le_add (add_le_add (hV x) le_rfl) le_rfl
    _ ≤ ((c * Real.log (baseExceptionalWeight F E (μ z)) : ℝ) : EReal) := by
        rw [zero_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
        nlinarith

/-- **The strict-transform competitor on `X' \ ℰ`**: at `ι'(x)`, `x ∉ Z`, it equals `V(x)`
(`N₁(0) = 1` and `log |s_ℰ|² ∘ ι' = g`). -/
theorem deformationCompetitor_strict_lift {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ)
    (V : F.carrier → EReal) (b c : ℝ) {ι : F.carrier → 𝒳}
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) {x : F.carrier}
    (hx : x ∉ F.flag (1 : Fin (m + 2))) :
    deformationCompetitor F μ (fun x => V x + (c : EReal) * E.weight x) (projectiveLogWeight 1)
      b c Eℰ (ι x) = V x := by
  have hwι : Eℰ.weight (ι x) = E.weight x := by
    rw [hEℰ.weight_eq]; exact weight_comp_centralSection F hE hμι x
  have hg : E.weight x ≠ ⊥ := by
    obtain ⟨-, -, hEsupp, -⟩ := hE
    intro h
    apply hx
    rw [← hEsupp]
    exact h
  set r := (E.weight x).toReal with hrdef
  have hgr : E.weight x = (r : EReal) := (EReal.coe_toReal (weight_ne_top F hE x) hg).symm
  unfold deformationCompetitor
  simp only [hwι, hμι]
  rw [projectiveLogWeight_one_projectiveZero, mul_zero, add_zero, hgr, EReal.toReal_coe,
    ← EReal.coe_mul]
  exact MeteredDivisorPositivity.add_coe_add_neg_coe _ _

/-- `{θ - c η} = {θ} - c {η}`. -/
theorem ofRepresentative_sub_smul {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (θ η : ClosedRealOneOneForm n M)
    (c : ℝ) :
    RealBottChern.ofRepresentative (θ - c • η) =
      RealBottChern.ofRepresentative θ - c • RealBottChern.ofRepresentative η := by
  rw [sub_eq_add_neg, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
    RealBottChern.ofRepresentative_smul, ← sub_eq_add_neg]

/-- **The minimal-singularity comparison on `X'`** (`tok-wn-vf:strict-lower`): for the lift `ι'`
of `x ↦ (x, 0)`, `V_{θ - cη} ≤ V_θ̃ ∘ ι'` everywhere on `X`. -/
theorem thetaPshSupremum_le_strict {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hμ : IsNormalConeDeformation F μ)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 < c) (hcb : c < b)
    (hVc : IsThetaPshPotential (θ - c • E.curvature).val (thetaPshSupremum (θ - c • E.curvature).val))
    (hVΘ : ThetaPlurisubharmonic (deformationForm F hμ.contMDiff θ b c Eℰ).val
      (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val))
    {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) (x : F.carrier) :
    thetaPshSupremum (θ - c • E.curvature).val x ≤
      thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val (ι x) := by
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  have hb : 0 < b := hc.trans hcb
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ with hΘ
  set θc := θ - c • E.curvature with hθc
  set V := thetaPshSupremum θc.val with hVdef
  -- `φ = V_{θ - cη} + c g ∈ PSH(X, θ)`
  have hφ : ThetaPlurisubharmonic θ.val (fun x => V x + (c : EReal) * E.weight x) := by
    have h2 := GlobalMultilinearExpansion.thetaPlurisubharmonic_smul hc
      (MeteredDivisorPositivity.thetaPlurisubharmonic_weight E)
    have h3 := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul one_pos one_pos hVc.1 h2
    simp only [one_smul, EReal.coe_one, one_mul] at h3
    rwa [hθc, sub_add_cancel] at h3
  set w := deformationCompetitor F μ (fun x => V x + (c : EReal) * E.weight x)
    (projectiveLogWeight 1) b c Eℰ with hwdef
  have hoff := thetaPshOff_deformationCompetitor F hμ hφ
    (thetaPlurisubharmonic_projectiveLogWeight 1) hb c Eℰ
  obtain ⟨hA, hAi⟩ := isComplexAnalyticSubset_support_exceptional F hEℰ
  have hιA : ∀ y, y ∉ F.flag (1 : Fin (m + 2)) → ι y ∉ Eℰ.support := fun y hy => by
    rw [hEℰ.support_eq, lift_mem_exceptionalSet_iff F hμι]; exact hy
  have hval : ∀ y, y ∉ F.flag (1 : Fin (m + 2)) → w (ι y) = V y := fun y hy =>
    deformationCompetitor_strict_lift F hE hEℰ V b c hμι hy
  -- a finite value off `Z`
  have hZc : (F.flag (1 : Fin (m + 2)))ᶜ.Nonempty := by
    rw [nonempty_compl]
    intro h
    have := interior_firstFlag F
    rw [h, interior_univ] at this
    exact univ_nonempty.ne_empty this
  obtain ⟨x₁, hx₁⟩ := hZc
  obtain ⟨x₀, hx₀Z, hx₀⟩ := hVc.2 x₁ _ F.firstDivisor.1.isOpen_compl hx₁
  have hle := le_thetaPshSupremum_of_thetaPshOff Θ hA hAi hoff
    (fun z hz => deformationCompetitor_strict_le_zero F hE hEℰ
      (fun y => thetaPshSupremum_le_zero _ y) hc hcb.le (hEℰ.support_eq ▸ hz))
    ⟨ι x₀, hιA x₀ hx₀Z, by show w (ι x₀) ≠ ⊥; rw [hval x₀ hx₀Z]; exact hx₀⟩
  -- the inequality off `Z`
  have hoffZ : ∀ y ∉ F.flag (1 : Fin (m + 2)), V y ≤ thetaPshSupremum Θ.val (ι y) := fun y hy => by
    rw [← hval y hy]; exact hle (ι y) (hιA y hy)
  -- both sides are `(θ - cη)`-psh
  have hcurv := pullback_curvature_geometricallyEq F hE hEℰ.weight_eq hEℰ.support_eq hι hμι
  have hgeq := pullback_deformationForm_centralSection F hμ.contMDiff θ b c Eℰ hι hμι hcurv
  have hu : ThetaPlurisubharmonic θc.val (fun y => thetaPshSupremum Θ.val (ι y)) :=
    (hgeq.thetaPlurisubharmonic_iff _).mp
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hVΘ)
  obtain ⟨-, -, hEsupp, -⟩ := hE
  exact le_of_le_off_analytic (hEsupp ▸ ResidualNef.isComplexAnalyticSubset_support E)
    (interior_firstFlag F) hu hVc.1 hoffZ x

/-- **`tok-wn:formula-X-prime`** (WN21 Theorem 1.6 (3)), conditional on `tok-wn:beta-big`
(`BetaBigStatement`, used for bigness of `β` and `X' ∩ K(β) ≠ ∅`):
`vol_{𝒳|X'}(β) = vol(ξ_c)`. -/
theorem restrictedVolume_strictTransform (hbeta : BetaBigStatement F) :
    StrictTransformRestrictedVolumeStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι
  have := compactSpace_normalCone F hμ
  have : Nonempty 𝒳 := ⟨ι (Classical.arbitrary _)⟩
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ with hΘ
  set θc := θ - c • E.curvature with hθc
  have hθc_class : RealBottChern.ofRepresentative θc =
      RealBottChern.ofRepresentative θ - c • RealBottChern.ofRepresentative E.curvature :=
    ofRepresentative_sub_smul θ E.curvature c
  have hVc : IsThetaPshPotential θc.val (thetaPshSupremum θc.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θc
      (by rw [hθc_class]; exact (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξc.1)
  obtain ⟨hbigβ, -, hstrict, -⟩ :=
    hbeta E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc hcb hξ hξc.1
  have hVΘ : IsThetaPshPotential Θ.val (thetaPshSupremum Θ.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum Θ
      ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbigβ)
  have hcurv := pullback_curvature_geometricallyEq F hE hEℰ.weight_eq hEℰ.support_eq hι hμι
  have hgeq := pullback_deformationForm_centralSection F hμ.contMDiff θ b c Eℰ hι hμι hcurv
  have hmeet : ∃ y, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative Θ) := by
    obtain ⟨z, hz, hzK⟩ := hstrict
    rw [← range_eq_strictCentralFibre F hμ hι.continuous hμι] at hz
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, hzK⟩
  have hlow : ∃ C : ℝ, ∀ x, thetaPshSupremum (ClosedRealOneOneForm.pullback hι Θ).val x ≤
      thetaPshSupremum Θ.val (ι x) + (C : EReal) := by
    refine ⟨0, fun x => ?_⟩
    rw [EReal.coe_zero, add_zero, thetaPshSupremum_geometricallyEq hgeq]
    exact thetaPshSupremum_le_strict F hE hμ hEℰ hc hcb hVc hVΘ.1 hι hμι x
  rw [sectionRestrictedVolume_toReal_eq F hμ hι (fun x => by rw [hμι]) Θ hbigβ hmeet hlow,
    RealBottChern.ofRepresentative_eq_of_geometricallyEq hgeq, hθc_class]

end Deformation

end SGPT.Okounkov.TranscendentalWN

import SGPT.Okounkov.TranscendentalWNVolumeExcFormula
import SGPT.Okounkov.TranscendentalWNKeyEasy
import SGPT.Okounkov.TranscendentalWNKeyGeometry
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-!
# The restricted volume along `ℰ`: reduction to the bundle Legendre identity (package WN-VF3)

Blueprint nodes `tok-wn-vf3:branch-concave`, `tok-wn-vf3:branch-minimal`,
`tok-wn-vf3:exceptional-mass`, `tok-wn-vf3:bundle-legendre-ma`, `tok-wn-vf3:reduction`
(chapter `claude-tok-wn-vf3`) and `tok-wn:formula-E` (chapter `claude-tok-wn`); source
D. Witt Nyström, arXiv:2103.03660 (WN21), Theorem 1.6 (4), proved at the end of §4.

WN21's proof of `vol_{𝒳|ℰ}(β) = n ∫₀^c vol_{X|Y}(α - t{Y}) dt` has three steps:

1. `vol_{𝒳|ℰ}(β) = ∫_ℰ ⟨(θ̃|_ℰ + dd^c ũ|_ℰ)^n⟩` (`ℰ` meets `K(β)`): here
   `exceptionalRestrictedVolume_eq_exceptionalMass`, from VOLCONC's
   `restrictedVolume_eq_restrictedMinimalMass` (Kähler restriction to the submanifold `ℰ`,
   `ℰ` connected by WN-KEY, `ℰ ∩ K(β) ≠ ∅` by `betaBig`);
2. the formula for `ũ|_ℰ` (`thetaPshSupremum_exceptional_eq_iSup`, file
   `TranscendentalWNVolumeExcFormula`), reindexed by `t = c - λ`:
   `ũ = sup_{t ∈ [0,c]} (W_t ∘ π_X + t log S₂ + (c - t) log S₁)` on the good part of `ℰ`,
   with `W_t = w_{c-t}` concave in `t` (`excBranch_concave`) and with minimal singularities in
   `ξ_t` (`excBranch_minimal`);
3. WN21 Theorem 3.5 on `ℰ \ (X' ∪ Z̃)`, the `ℂ*`-bundle `N_{Z|X} \ 0` over `Z`, in the fibre
   coordinate `log S₂ - log S₁` (`= log |z̃₁|² - g_Z`): the mass of such a function is
   `n ∫₀^c ∫_Z ⟨((θ - tη)|_Z + dd^c W_t|_Z)^{n-1}⟩ dt = n ∫₀^c R(ξ_t) dt`.

Step 3 is recorded as the statement `ExcBundleLegendreMAStatement` (**not proved here**: it
needs the bundle charts of `ℰ` over `Z`, WN21 Theorem 3.3 = `PartialLegendreMALocalStatement`
in those charts and the gluing of WN-VF2's `tok-wn-vf:global-legendre-ma` with a twist by the
normal bundle; `ℰ \ (X' ∪ Z̃)` is a product `Z × ℂ*` only when `N_{Z|X}` is trivial).
`exceptionalRestrictedVolume_of_bundleLegendre` proves

  `ExcLegendreInputStatement F → ExcBundleLegendreMAStatement F →
    ExceptionalRestrictedVolumeStatement F`

(`tok-wn:formula-E`), with steps 1–2 and all the bookkeeping proved.
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
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### Concavity and minimal singularities of the branches -/

section Branch

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The upper bound of the branches: `w_λ ≤ C` for `λ ∈ [0, c]`, and `w_λ = û_λ - (c - λ) g` off
`Z`, with `w_λ` `(θ - (c - λ) η)`-psh. -/
theorem excBranch_spec_of_family {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} {û : ℝ → F.carrier → EReal} (hû : IsExcLegendreFamily F E hμ Eℰ θ b c û)
    (hcb : c ≤ b) : ∃ C : ℝ, ∀ lam ∈ Icc 0 c,
      ThetaPlurisubharmonic (θ - (c - lam) • E.curvature).val (excBranch F E û c lam) ∧
        (∀ x, x ∉ E.support → excBranch F E û c lam x = excBranchOff F E û c lam x) ∧
        ∀ x, excBranch F E û c lam x ≤ (C : EReal) := by
  obtain ⟨C₀, hC₀⟩ := hû.upper
  obtain ⟨D, -, hsupp, -⟩ := id hE
  refine ⟨C₀, fun lam hl => ?_⟩
  have hlb : lam ∈ Icc 0 b := ⟨hl.1, hl.2.trans hcb⟩
  refine excBranch_spec hE (hû.psh lam hlb) fun y hy => ?_
  have hyZ : y ∉ F.flag (1 : Fin (m + 2)) := by rw [← hsupp]; exact hy
  have h1 := hC₀ lam hlb y hyZ
  rw [max_eq_left (by linarith [hl.2])] at h1
  have h2 := add_le_add h1 (le_refl (((-((c - lam) * (E.weight y).toReal)) : ℝ) : EReal))
  rw [← EReal.coe_add] at h2
  unfold excBranchOff
  refine h2.trans (le_of_eq ?_)
  congr 1; ring

/-- **The branches are concave in `λ`** on all of `X` (`tok-wn-vf3:branch-concave`): off `Z`,
`w_λ = û_λ - (c - λ) g` is concave as `û_λ` is; a convex combination of `w_{λ₁}`, `w_{λ₂}` is
`(θ - (c - λ_s) η)`-psh, so the chord inequality extends across the nowhere dense analytic set `Z`
(`le_of_le_off_analytic`). -/
theorem excBranch_concave {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} {û : ℝ → F.carrier → EReal} (hû : IsExcLegendreFamily F E hμ Eℰ θ b c û)
    (hcb : c ≤ b) (x : F.carrier) :
    IsConcaveFamilyAt (fun lam => excBranch F E û c lam) (Icc 0 c) x := by
  obtain ⟨C, hC⟩ := excBranch_spec_of_family F hE hû hcb
  obtain ⟨D, -, hsupp, -⟩ := id hE
  have hA : IsComplexAnalyticSubset (n := m + 1) E.support :=
    ResidualNef.isComplexAnalyticSubset_support E
  have hAi : interior E.support = ∅ := by rw [hsupp]; exact interior_firstFlag F
  intro l₁ hl₁ l₂ hl₂ s hs0 hs1
  simp only
  rcases hs0.eq_or_lt with rfl | hs0'
  · simp
  rcases hs1.eq_or_lt with rfl | hs1'
  · simp
  set ls := s * l₁ + (1 - s) * l₂ with hls
  have hlsI : ls ∈ Icc 0 c := ⟨by nlinarith [hl₁.1, hl₂.1], by nlinarith [hl₁.2, hl₂.2]⟩
  have hcomb := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul hs0' (by linarith : 0 < 1 - s)
    (hC l₁ hl₁).1 (hC l₂ hl₂).1
  have hform : s • (θ - (c - l₁) • E.curvature) + (1 - s) • (θ - (c - l₂) • E.curvature) =
      θ - (c - ls) • E.curvature := by
    rw [hls]; module
  rw [hform] at hcomb
  refine le_of_le_off_analytic hA hAi (hC ls hlsI).1 hcomb (fun y hy => ?_) x
  rw [(hC l₁ hl₁).2.1 y hy, (hC l₂ hl₂).2.1 y hy, (hC ls hlsI).2.1 y hy]
  unfold excBranchOff
  rw [ereal_coe_mul_add_coe hs0, ereal_coe_mul_add_coe (by linarith : (0 : ℝ) ≤ 1 - s),
    add_add_add_comm, ← EReal.coe_add]
  have hlb : ∀ l ∈ Icc 0 c, l ∈ Icc 0 b := fun l hl => ⟨hl.1, hl.2.trans hcb⟩
  refine add_le_add (hû.concave y l₁ (hlb l₁ hl₁) l₂ (hlb l₂ hl₂) s hs0 hs1) (le_of_eq ?_)
  congr 1
  rw [hls]; ring

/-- **The branches have minimal singularities** (`tok-wn-vf3:branch-minimal`): for `λ ∈ [0, c]`,
`V_{θ - (c - λ) η} ≤ w_λ ≤ V_{θ - (c - λ) η} + C`. -/
theorem excBranch_minimal {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} {û : ℝ → F.carrier → EReal} (hû : IsExcLegendreFamily F E hμ Eℰ θ b c û)
    (hcb : c ≤ b)
    (hV : ∀ lam ∈ Icc 0 c, IsThetaPshPotential (θ - (c - lam) • E.curvature).val
      (thetaPshSupremum (θ - (c - lam) • E.curvature).val)) :
    ∃ C : ℝ, ∀ lam ∈ Icc 0 c, ∀ x,
      thetaPshSupremum (θ - (c - lam) • E.curvature).val x ≤ excBranch F E û c lam x ∧
        excBranch F E û c lam x ≤
          thetaPshSupremum (θ - (c - lam) • E.curvature).val x + (C : EReal) := by
  obtain ⟨C, hC⟩ := excBranch_spec_of_family F hE hû hcb
  refine ⟨C, fun lam hl x => ⟨thetaPshSupremum_le_excBranch F hE hû hcb hl (hV lam hl).1 x, ?_⟩⟩
  have hlow := thetaPshSupremum_le_excBranch F hE hû hcb hl (hV lam hl).1
  -- `w_λ - C` is a competitor
  have hpot : IsThetaPshPotential (θ - (c - lam) • E.curvature).val
      (excBranch F E û c lam) := by
    refine ⟨(hC lam hl).1, fun y U hU hyU => ?_⟩
    obtain ⟨z, hzU, hz⟩ := (hV lam hl).2 y U hU hyU
    exact ⟨z, hzU, fun hbot => hz (le_bot_iff.mp (hbot ▸ hlow z))⟩
  have hcomp := le_thetaPshSupremum (hpot.sub_const C) (fun y => by
    have h := (hC lam hl).2.2 y
    show excBranch F E û c lam y - (C : EReal) ≤ 0
    have h2 := add_le_add h (le_refl (((-C : ℝ) : EReal)))
    rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h2
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact h2) x
  have h := add_le_add hcomp (le_refl (C : EReal))
  refine le_trans (le_of_eq ?_) h
  rw [sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add, neg_add_cancel,
    EReal.coe_zero, add_zero]

end Branch

/-! ### Reindexing a supremum over `[0, c]` by `t = c - λ` -/

theorem iSup_Icc_reindex (c : ℝ) (f : ℝ → EReal) :
    (⨆ lam ∈ Icc 0 c, f lam) = ⨆ t ∈ Icc 0 c, f (c - t) := by
  apply le_antisymm
  · refine iSup₂_le fun lam hl => ?_
    have ht : c - lam ∈ Icc 0 c := ⟨by linarith [hl.2], by linarith [hl.1]⟩
    have := le_iSup₂ (f := fun t (_ : t ∈ Icc 0 c) => f (c - t)) (c - lam) ht
    simpa only [sub_sub_cancel] using this
  · refine iSup₂_le fun t ht => ?_
    have hl : c - t ∈ Icc 0 c := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact le_iSup₂ (f := fun lam (_ : lam ∈ Icc 0 c) => f lam) (c - t) hl

/-! ### Step 1: the restricted volume is the mass of `ũ|_ℰ` -/

section Mass

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **`vol_{𝒳|ℰ}(β)` is the mass of `ũ|_ℰ`** (`tok-wn-vf3:exceptional-mass`, WN21 §4,
`vol_{𝒳|ℰ}(β) = ∫_ℰ MA_{θ̃|_ℰ}(ũ|_ℰ)`): `ℰ` is a connected compact submanifold, the restriction
of a Kähler form to it is Kähler, and `ℰ` meets `K(β)` (`betaBig`), so VOLCONC's
identification applies. -/
theorem exceptionalRestrictedVolume_eq_exceptionalMass
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 < c) (hcb : c < b)
    (hξ : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ))
    (hξc : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
      c • RealBottChern.ofRepresentative E.curvature)) :
    letI := exceptionalChartedSpace F hμ
    haveI := isComplexManifold_exceptional F hμ
    ∃ hV : IsThetaPshPotential (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ)
        (deformationForm F hμ.contMDiff θ b c Eℰ)).val
        (fun y : exceptionalSet F μ =>
          thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val y),
      exceptionalRestrictedVolume F hμ
          (RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ)) =
        exceptionalMass F hμ (deformationForm F hμ.contMDiff θ b c Eℰ)
          (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) hV := by
  have := compactSpace_normalCone F hμ
  let := exceptionalChartedSpace F hμ
  have := isComplexManifold_exceptional F hμ
  let : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  have : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  have := compactSpace_exceptional F hμ
  have := connectedSpace_exceptional F hμ
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ with hΘ
  obtain ⟨hbig, -, -, hEx⟩ := betaBig F E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc hcb hξ hξc.1
  have : Nonempty 𝒳 := by
    obtain ⟨z, -, -⟩ := hEx
    exact ⟨z⟩
  obtain ⟨η'⟩ := nonempty_kahler_normalCone F hμ
  have hιE := contMDiff_exceptionalInclusion F hμ
  have hpull : (ClosedRealOneOneForm.pullback hιE η'.form).val.IsKahler :=
    SubmanifoldKahlerRestriction.isKahler_pullback (Nat.le_succ (m + 1))
      (fun _ hz => regularAtDim_exceptionalSet F hμ hz) η'.form η'.isKahler
  have hZE : ∃ y : exceptionalSet F μ,
      (y : 𝒳) ∉ nonKahlerLocus (RealBottChern.ofRepresentative Θ) := by
    obtain ⟨z, hz, hzK⟩ := hEx
    exact ⟨⟨z, hz⟩, hzK⟩
  obtain ⟨hV, hR⟩ := TranscendentalVolumeConcavity.restrictedVolume_eq_restrictedMinimalMass
    hιE η' hpull Θ ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig) hZE
  refine ⟨hV, ?_⟩
  unfold exceptionalRestrictedVolume exceptionalMass
  rw [← TranscendentalVolumeConcavity.restrictedVolume_eq_classRestrictedVolume, hR]

end Mass

/-! ### The restricted volume along `Z` through a potential with minimal singularities -/

/-- **`R(ξ')` is the restricted mass of any potential with minimal singularities**
(`tok-wn-vf3:z-mass`, used by `ExcBundleLegendreMAStatement`: `∫_Z MA(W_t|_Z) = R(ξ_t)`): if
`ξ' = {θ'}` is big with Kähler locus meeting `Z` and `V_{θ'} ≤ W ≤ V_{θ'} + C` with `W`
`θ'`-psh, then `W|_Z` is a `θ'|_Z`-psh potential and `vol_{X|Z}(ξ') = ∫_Z ⟨(θ'|_Z + dd^c W|_Z)^d⟩`
(VOLCONC's identification for `V_{θ'}` and the monotonicity of masses). -/
theorem firstFlagRestrictedVolume_eq_mass {θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    (hξ' : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ'))
    {W : F.carrier → EReal} (hW : ThetaPlurisubharmonic θ'.val W) {C : ℝ}
    (hbd : ∀ x, thetaPshSupremum θ'.val x ≤ W x ∧ W x ≤ thetaPshSupremum θ'.val x + (C : EReal)) :
    letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
    haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
    ∃ hWZ : IsThetaPshPotential
        (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) θ').val
        (fun y => W (firstFlagInclusion F y)),
      firstFlagRestrictedVolume F (RealBottChern.ofRepresentative θ') =
        diagonalPotentialMass (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) θ')
          (fun y => W (firstFlagInclusion F y)) hWZ := by
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  have : BorelSpace F.tail.carrier := ⟨rfl⟩
  obtain ⟨hbig, hmeet⟩ := (isBigMeetingFirstDivisor_iff F _).mp hξ'
  have : Nonempty F.carrier := by
    obtain ⟨y, -⟩ := hmeet
    exact ⟨firstFlagInclusion F y⟩
  have hι := contMDiff_firstFlagInclusion F
  obtain ⟨hV, hR⟩ := TranscendentalVolumeConcavity.restrictedVolume_eq_restrictedMinimalMass hι
    F.omega F.tail.omega.isKahler θ' hbig hmeet
  have hWZ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ').val
      (fun y => W (firstFlagInclusion F y)) := by
    refine ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hW, fun y U hU hyU => ?_⟩
    obtain ⟨z, hzU, hz⟩ := hV.2 y U hU hyU
    exact ⟨z, hzU, fun hbot => hz (le_bot_iff.mp (hbot ▸ (hbd _).1))⟩
  refine ⟨hWZ, ?_⟩
  have hmass : diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ')
      (fun y => thetaPshSupremum θ'.val (firstFlagInclusion F y)) hV =
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ')
        (fun y => W (firstFlagInclusion F y)) hWZ := by
    apply le_antisymm
    · exact diagonalPotentialMass_mono_of_kahler F.tail.omega hV hWZ
        ⟨0, fun y _ => by rw [EReal.coe_zero, add_zero]; exact (hbd _).1⟩
    · exact diagonalPotentialMass_mono_of_kahler F.tail.omega hWZ hV
        ⟨C, fun y _ => (hbd _).2⟩
  unfold firstFlagRestrictedVolume
  rw [← TranscendentalVolumeConcavity.restrictedVolume_eq_classRestrictedVolume, hR, hmass]

/-! ### The non-Kähler loci along the segment -/

open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination in
/-- **The non-Kähler loci along a segment** (`tok-wn-vf3:nK-segment`): if `ξ` and `ξ - c e` are
big, then `E_nK(ξ - t e) ⊆ E_nK(ξ) ∪ E_nK(ξ - c e)` for `t ∈ [0, c]` (a convex combination of
Kähler currents with polar sets `E_nK(ξ)`, `E_nK(ξ - c e)` (Boucksom) has finite potential off
their union). -/
theorem nonKahlerLocus_sub_smul_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] (hn : 0 < n)
    {ξ e : RealBottChern n M} {c : ℝ} (hξ : IsBigClass ξ) (hξc : IsBigClass (ξ - c • e))
    {t : ℝ} (ht : t ∈ Icc 0 c) :
    nonKahlerLocus (ξ - t • e) ⊆ nonKahlerLocus ξ ∪ nonKahlerLocus (ξ - c • e) := by
  rcases ht.1.eq_or_lt with rfl | ht0
  · simp only [zero_smul, sub_zero]; exact subset_union_left
  rcases ht.2.eq_or_lt with rfl | htc
  · exact subset_union_right
  have hc : 0 < c := ht0.trans htc
  set s : ℝ := 1 - t / c with hs
  have hs0 : 0 < s := by rw [hs, sub_pos, div_lt_one hc]; exact htc
  have hs1 : s < 1 := by rw [hs]; linarith [div_pos ht0 hc]
  have hclass : s • ξ + (1 - s) • (ξ - c • e) = ξ - t • e := by
    have h1 : 1 - s = t / c := by rw [hs]; ring
    rw [h1, hs]
    have hct : t = t / c * c := by field_simp
    conv_rhs => rw [hct]
    module
  obtain ⟨K₁, -, hK₁⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      hn ξ hξ
  obtain ⟨K₂, -, hK₂⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      hn (ξ - c • e) hξc
  intro x hx
  by_contra hxu
  simp only [mem_union, not_or] at hxu
  have h₁ : K₁.potential x ≠ ⊥ := fun h => hxu.1 (by rw [← hK₁]; exact h)
  have h₂ : K₂.potential x ≠ ⊥ := fun h => hxu.2 (by rw [← hK₂]; exact h)
  have hfin : (kahlerCurrentConvexComb K₁ K₂ hs0 hs1).potential x ≠ ⊥ := by
    intro hbot
    rcases poles_convexComb_subset hs0 hs1 K₁.potential K₂.potential hbot with h | h
    · exact h₁ h
    · exact h₂ h
  have := not_mem_nonKahlerLocus_of_potential_ne_bot hn (kahlerCurrentConvexComb K₁ K₂ hs0 hs1) hfin
  rw [hclass] at this
  exact this hx

/-! ### Step 3: the bundle Legendre identity (statement) -/

/-- **`tok-wn-vf3:bundle-legendre-ma`** (WN21 Theorem 3.5 on the `ℂ*`-bundle
`ℰ \ (X' ∪ Z̃) ≅ N_{Z|X} \ 0`, as used at the end of WN21 §4).  Let `W_t`, `t ∈ [0, c]`, be a
family of `(θ - tη)`-psh functions on `X`, concave in `t`, with minimal singularities in
`ξ_t = ξ - t{Z}` (uniformly), and let `φ` be a `θ̃|_ℰ`-psh potential on `ℰ` which, at every
point `p ∈ ℰ` off the strict transforms `X'` (`S₁ = 0`) and `Z̃` (`S₂ = 0`) with
`π_X(p) ∉ E_nK(ξ) ∪ E_nK(ξ_c)` (a proper analytic subset of `Z`), is given by

  `φ(p) = sup_{t ∈ [0, c]} (W_t(π_X p) + t log S₂(p) + (c - t) log S₁(p))`.

Then `∫_ℰ ⟨(θ̃|_ℰ + dd^c φ)^n⟩ = n ∫₀^c vol_{X|Z}(ξ_t) dt`.  (In the fibre coordinate
`log S₂ - log S₁ = log |z̃₁|² - g_Z` the function `φ - c log S₁` is the inverse Legendre
transform of `t ↦ W_t|_Z`, and `θ̃|_ℰ = π_Z^*(θ|_Z) - c dd^c log S₁`.)  **Not proved here.** -/
def ExcBundleLegendreMAStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    (∀ x, E.weight x ≤ 0) →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
      (hμ : IsNormalConeDeformation F μ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳),
      IsDeformationExceptionalMetric F E hμ Eℰ →
      ∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ), 0 < c → c < b →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ) →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
          c • RealBottChern.ofRepresentative E.curvature) →
        ∀ W : ℝ → F.carrier → EReal,
          (∀ t ∈ Icc 0 c, ThetaPlurisubharmonic (θ - t • E.curvature).val (W t)) →
          (∀ x, IsConcaveFamilyAt W (Icc 0 c) x) →
          (∃ C : ℝ, ∀ t ∈ Icc 0 c, ∀ x,
            thetaPshSupremum (θ - t • E.curvature).val x ≤ W t x ∧
              W t x ≤ thetaPshSupremum (θ - t • E.curvature).val x + (C : EReal)) →
          ∀ (φ : 𝒳 → EReal)
            (hφ : letI := exceptionalChartedSpace F hμ
              haveI := isComplexManifold_exceptional F hμ
              IsThetaPshPotential (ClosedRealOneOneForm.pullback
                (contMDiff_exceptionalInclusion F hμ)
                  (deformationForm F hμ.contMDiff θ b c Eℰ)).val
                (fun y : exceptionalSet F μ => φ y)),
            (∀ p ∈ exceptionalSet F μ, 0 < strictWeight F E μ p → 0 < zStrictWeight F E μ p →
              (μ p).1 ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ) →
              (μ p).1 ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ -
                c • RealBottChern.ofRepresentative E.curvature) →
              φ p = ⨆ t ∈ Icc 0 c, W t (μ p).1 +
                ((t * Real.log (zStrictWeight F E μ p) +
                  (c - t) * Real.log (strictWeight F E μ p) : ℝ) : EReal)) →
            (exceptionalMass F hμ (deformationForm F hμ.contMDiff θ b c Eℰ) φ hφ).toReal =
              ((m + 1 : ℕ) : ℝ) * ∫ t in (0 : ℝ)..c,
                (firstFlagRestrictedVolume F (RealBottChern.ofRepresentative θ -
                  t • RealBottChern.ofRepresentative E.curvature)).toReal

/-! ### The reduction -/

/-- **`tok-wn:formula-E` from the Legendre input and the bundle Legendre identity**
(`tok-wn-vf3:reduction`): `vol_{𝒳|ℰ}(β) = n ∫₀^c vol_{X|Z}(ξ_t) dt`, conditional on
`ExcLegendreInputStatement` (WN21 Propositions 4.2, 4.5, Legendre duality) and
`ExcBundleLegendreMAStatement` (WN21 Theorem 3.5 on `ℰ`). -/
theorem exceptionalRestrictedVolume_of_bundleLegendre (hIn : ExcLegendreInputStatement F)
    (hMA : ExcBundleLegendreMAStatement F) : ExceptionalRestrictedVolumeStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc
  obtain ⟨û, hû⟩ := hIn E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc
  have := compactSpace_normalCone F hμ
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ with hΘ
  -- the reindexed branches `W_t = w_{c - t}`
  set W : ℝ → F.carrier → EReal := fun t => excBranch F E û c (c - t) with hWdef
  have hmem : ∀ t ∈ Icc (0 : ℝ) c, c - t ∈ Icc 0 c :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hbigt : ∀ t ∈ Icc (0 : ℝ) c,
      IsBigClass (RealBottChern.ofRepresentative (θ - t • E.curvature)) := by
    intro t ht
    rw [ofRepresentative_sub_smul]
    exact (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp
      (isBigMeetingFirstDivisor_sub_smul_of_mem_Icc F hξ hξc ht).1
  have hVt : ∀ t ∈ Icc (0 : ℝ) c, IsThetaPshPotential (θ - t • E.curvature).val
      (thetaPshSupremum (θ - t • E.curvature).val) := by
    intro t ht
    have : Nonempty F.carrier := by
      obtain ⟨y, -, -⟩ := hξ.2
      exact ⟨y⟩
    exact MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _ (hbigt t ht)
  obtain ⟨C, hC⟩ := excBranch_spec_of_family F hE hû hcb.le
  have hW1 : ∀ t ∈ Icc 0 c, ThetaPlurisubharmonic (θ - t • E.curvature).val (W t) := by
    intro t ht
    have h := (hC (c - t) (hmem t ht)).1
    rwa [sub_sub_cancel] at h
  have hW2 : ∀ x, IsConcaveFamilyAt W (Icc 0 c) x := by
    intro x t₁ ht₁ t₂ ht₂ s hs0 hs1
    have h := excBranch_concave F hE hû hcb.le x (c - t₁) (hmem t₁ ht₁) (c - t₂) (hmem t₂ ht₂)
      s hs0 hs1
    simp only at h
    simp only [hWdef]
    have e : s * (c - t₁) + (1 - s) * (c - t₂) = c - (s * t₁ + (1 - s) * t₂) := by ring
    rwa [e] at h
  have hW3 : ∃ C : ℝ, ∀ t ∈ Icc 0 c, ∀ x,
      thetaPshSupremum (θ - t • E.curvature).val x ≤ W t x ∧
        W t x ≤ thetaPshSupremum (θ - t • E.curvature).val x + (C : EReal) := by
    obtain ⟨C', hC'⟩ := excBranch_minimal F hE hû hcb.le (fun lam hl => by
      have h := hVt (c - lam) (hmem lam hl)
      exact h)
    refine ⟨C', fun t ht x => ?_⟩
    have h := hC' (c - t) (hmem t ht) x
    simp only [sub_sub_cancel] at h
    exact h
  obtain ⟨hV, hvol⟩ := exceptionalRestrictedVolume_eq_exceptionalMass F hE hμ hEℰ hc hcb hξ hξc
  have hformula : ∀ p ∈ exceptionalSet F μ, 0 < strictWeight F E μ p →
      0 < zStrictWeight F E μ p →
      (μ p).1 ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ) →
      (μ p).1 ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ -
        c • RealBottChern.ofRepresentative E.curvature) →
      thetaPshSupremum Θ.val p = ⨆ t ∈ Icc 0 c, W t (μ p).1 +
        ((t * Real.log (zStrictWeight F E μ p) +
          (c - t) * Real.log (strictWeight F E μ p) : ℝ) : EReal) := by
    intro p hp hS₁ hS₂ hK₀ hKc
    have hK : ∀ t ∈ Icc 0 c, (μ p).1 ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ -
        t • RealBottChern.ofRepresentative E.curvature) := by
      intro t ht hmem
      rcases nonKahlerLocus_sub_smul_subset (Nat.succ_pos m)
          ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξ.1)
          ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξc.1) ht hmem with h | h
      · exact hK₀ h
      · exact hKc h
    rw [thetaPshSupremum_exceptional_eq_iSup F hE hμ hEℰ hc hcb hξ hξc hû hp hS₁ hS₂ hK,
      iSup_Icc_reindex c]
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    simp only [hWdef, sub_sub_cancel]
  rw [hvol]
  exact hMA E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc W hW1 hW2 hW3
    (thetaPshSupremum Θ.val) hV hformula

end SGPT.Okounkov.TranscendentalWN

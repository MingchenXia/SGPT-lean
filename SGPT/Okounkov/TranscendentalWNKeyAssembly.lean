import SGPT.Okounkov.TranscendentalWNKeyGeometry
import SGPT.Okounkov.TranscendentalWNRestrictedContinuity
import SGPT.Okounkov.TranscendentalWNCone2
import SGPT.Foundations.Analysis.Pending.MeteredDivisorScaling

/-!
# Assembly of Witt Nyström's Theorem C (packages WN-KEY and WN-ASM)

Blueprint chapter `claude-tok-wn`, nodes `tok-wn:key-equality`, `tok-wn:integrated` and
`tok-wn:derivative`, and the supplement `claude-tok-wn-key` (nodes `tok-wn-key:unit-metric`,
`tok-wn-key:key-equality-limit`); source D. Witt Nyström, arXiv:2103.03660 (WN21), Theorem 1.7
and Theorem C, and DRWNXZ, proof of Theorem 2.10.

## Main results

* `keyEquality_of_keyEasy_of_keyConvergence` (**`tok-wn:key-equality`**, WN21 Theorem 1.7): the
  key equality `vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) = vol(ξ)` from the easy inequality
  (`KeyEasyStatement`), the perturbed hard inequality (`KeyConvergenceStatement`) and
  `tok-wn:beta-big` (`BetaBigStatement`), by the continuity of restricted volumes on `𝒳`
  along `X'` and `ℰ` (`continuousAt_classRestrictedVolume_add_smul`, with
  `isKahler_pullback_centralSection` and `connectedSpace_exceptional`);
* `exists_unitMetric_weight_nonpos`: every unit metric of `𝒪(Z)` can be renormalized by a
  constant to have `|s_Z|_h ≤ 1`, without changing its curvature;
* `wnIntegrated_of_keyEquality` (**`tok-wn:integrated`**, WN21 Theorem 1.6 (3)--(4) with
  Theorem 1.7): the integrated derivative formula
  `vol(ξ) - vol(ξ_c) = n ∫₀^c vol_{X|Z}(ξ_t) dt` from the key equality and the restricted-volume
  formulas along `X'` and `ℰ` (`StrictTransformRestrictedVolumeStatement`,
  `ExceptionalRestrictedVolumeStatement`, package WN-VF);
* `wnDerivative_of_wnIntegrated` (**`tok-wn:derivative`**, WN21 Theorem C, DRWNXZ Theorem 2.10):
  the derivative `d/dt|_{t=0} vol(ξ - t{Z}) = -n vol_{X|Z}(ξ)` from the integrated formula, by
  the fundamental theorem of calculus and the continuity `wnContinuity`;
* `wnStatement_of_key`, `wnDerivative_of_key`: the package statements, conditional on the named
  statements of WN-KEY (`KeyEasyStatement`, `KeyConvergenceStatement`), WN-DEF
  (`BetaBigStatement`) and WN-VF (`StrictTransformRestrictedVolumeStatement`,
  `ExceptionalRestrictedVolumeStatement`).
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
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

/-! ### Renormalizing a metric by a constant -/

section Shift

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `dd^c (h - K) = dd^c h` for a constant `K`. -/
theorem smoothDDC_sub_const (h : ComplexModel n → ℝ) (K : ℝ) (z : ComplexModel n) :
    smoothDDC (fun y => h y - K) z = smoothDDC h z := by
  have hdc : smoothDc (fun y => h y - K) = smoothDc h := by
    funext y
    ext v
    simp only [smoothDc_apply, fderiv_sub_const]
  unfold smoothDDC
  rw [hdc]

/-- The metered divisor with weight `ψ_E - K` (the metric multiplied by `e^{-K}`) and the same
curvature. -/
def meteredWeightShift (E : MeteredEffectiveQDivisor n M) (K : ℝ) :
    MeteredEffectiveQDivisor n M where
  weight y := E.weight y + ((-K : ℝ) : EReal)
  curvature := E.curvature
  local_presentation x := by
    obtain ⟨U, hU, hxU, N, a, g, h, ha, hg, hgne, hh, hw, hc⟩ := E.local_presentation x
    refine ⟨U, hU, hxU, N, a, g, fun y => h y - K, ha, hg, hgne,
      fun e => (hh e).sub contDiffOn_const, fun y hy => ?_, fun e z hz hzU => ?_⟩
    · rw [hw y hy, add_assoc, ← EReal.coe_add]
      show _ = _ + ((h y - K : ℝ) : EReal)
      rw [sub_eq_add_neg]
    · rw [hc e z hz hzU]
      exact congrArg Neg.neg (smoothDDC_sub_const _ K z).symm

@[simp] theorem meteredWeightShift_weight (E : MeteredEffectiveQDivisor n M) (K : ℝ) (y : M) :
    (meteredWeightShift E K).weight y = E.weight y + ((-K : ℝ) : EReal) := rfl

@[simp] theorem meteredWeightShift_curvature (E : MeteredEffectiveQDivisor n M) (K : ℝ) :
    (meteredWeightShift E K).curvature = E.curvature := rfl

/-- The shifted metered divisor has the same support. -/
theorem meteredWeightShift_support (E : MeteredEffectiveQDivisor n M) (K : ℝ) :
    (meteredWeightShift E K).support = E.support := by
  ext y
  simp only [MeteredEffectiveQDivisor.support, mem_poleSet, meteredWeightShift_weight,
    EReal.add_eq_bot_iff, EReal.coe_ne_bot, or_false]

/-- A shifted metric of a divisor is a metric of the same divisor. -/
theorem isDivisorMetric_meteredWeightShift {D : EffectiveDivisor n M}
    {E : MeteredEffectiveQDivisor n M} (hE : DivisorMetric.IsDivisorMetric D E) (K : ℝ) :
    DivisorMetric.IsDivisorMetric D (meteredWeightShift E K) := by
  intro x
  obtain ⟨V, hV, hxV, g, hg, hgen, h, hh, hw⟩ := hE x
  refine ⟨V, hV, hxV, g, hg, hgen, fun y => h y - K, fun e => (hh e).sub contDiffOn_const,
    fun y hy => ?_⟩
  rw [meteredWeightShift_weight, hw y hy, add_assoc, ← EReal.coe_add]
  show _ = _ + ((h y - K : ℝ) : EReal)
  rw [sub_eq_add_neg]

end Shift

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **Renormalized unit metric** (`tok-wn-key:unit-metric`): every unit metric `E` of `𝒪(Z)`
can be multiplied by a constant so that `|s_Z|_h ≤ 1` (`ψ_E ≤ 0`), keeping its curvature
(the weight is bounded above on the compact `X`, `exists_forall_weight_le`). -/
theorem exists_unitMetric_weight_nonpos {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) :
    ∃ E' : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E' ∧
      (∀ x, E'.weight x ≤ 0) ∧ E'.curvature = E.curvature := by
  obtain ⟨K, hK⟩ := MeteredDivisorScaling.exists_forall_weight_le E
  obtain ⟨D, hD, hsupp, hmet⟩ := hE
  refine ⟨meteredWeightShift E K, ⟨D, hD, by rw [meteredWeightShift_support, hsupp],
    isDivisorMetric_meteredWeightShift hmet K⟩, fun x => ?_, rfl⟩
  rw [meteredWeightShift_weight]
  calc E.weight x + ((-K : ℝ) : EReal) ≤ (K : EReal) + ((-K : ℝ) : EReal) := by
        gcongr
        exact hK x
    _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]

/-! ### The lift of `x ↦ (x, 0)` is unique -/

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- Every holomorphic lift `ι` of `x ↦ (x, 0)` has image the strict transform `X'` and
`ι⁻¹(ℰ) = Z` (it is the lift of `exists_centralSection`, by the uniqueness in the universal
property of the blow-up). -/
theorem range_centralLift (hμ : IsNormalConeDeformation F μ) {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) :
    range ι = strictCentralFibre F μ ∧ ι ⁻¹' exceptionalSet F μ = F.flag (1 : Fin (m + 2)) := by
  obtain ⟨ι₀, hι₀, hμι₀, hrange, hpre⟩ := exists_centralSection F hμ
  have hinv : (GermIdeal.pullback (m := m + 1) (fun x : F.carrier => (x, projectiveZero))
      (vanishingIdeal (n := m + 1 + 1) (deformationCentre F))).IsInvertible := by
    rw [pullback_vanishingIdeal_centre_zeroSection F]
    exact isInvertible_vanishingIdeal_firstFlag F
  obtain ⟨_, _, huniq⟩ := hμ.2.2.2.2 (m + 1) F.carrier (fun x => (x, projectiveZero))
    (contMDiff_slice F projectiveZero) hinv
  have h1 : ι = ι₀ := by
    rw [huniq ι ⟨hι, funext hμι⟩, huniq ι₀ ⟨hι₀, funext hμι₀⟩]
  subst h1
  exact ⟨hrange, hpre⟩

end Deformation

/-! ### The key equality -/

/-- **`tok-wn:key-equality`** (WN21 Theorem 1.7): `vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) = vol(ξ)`.

Proof (`tok-wn-key:key-equality-limit`): `≤` is `KeyEasyStatement`.  By `BetaBigStatement`,
`β` is big and its Kähler locus meets `X'` and `ℰ`; for a Kähler form `η'` of `𝒳`, the
restrictions `ι'^*η'` (`isKahler_pullback_centralSection`) and `η'|_ℰ` are Kähler and `X ≅ X'`,
`ℰ` are connected (`connectedSpace_exceptional`), so `s ↦ vol_{𝒳|X'}(β + s{η'})` and
`s ↦ vol_{𝒳|ℰ}(β + s{η'})` are continuous at `0` (`continuousAt_classRestrictedVolume_add_smul`).
Letting `ε → 0⁺` in `KeyConvergenceStatement` gives `≥`. -/
theorem keyEquality_of_keyEasy_of_keyConvergence (hEasy : KeyEasyStatement F)
    (hConv : KeyConvergenceStatement F) (hBeta : BetaBigStatement F) :
    KeyEqualityStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι
  set β := RealBottChern.ofRepresentative (deformationForm F hμ.contMDiff θ b c Eℰ) with hβ
  refine le_antisymm (hEasy E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc (by linarith) hξ hξc ι hι hμι) ?_
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  obtain ⟨η'⟩ := nonempty_kahler_normalCone F hμ
  obtain ⟨hbig, -, hX', hEx⟩ := hBeta E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc
    (by linarith) hξ hξc.1
  have hbigC : IsBigClass β := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  have hZX' : ∃ y : F.carrier, ι y ∉ nonKahlerLocus β := by
    obtain ⟨z, hz, hzK⟩ := hX'
    rw [← (range_centralLift F hμ hι hμι).1] at hz
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, hzK⟩
  have hZE : ∃ y : exceptionalSet F μ, (y : 𝒳) ∉ nonKahlerLocus β := by
    obtain ⟨z, hz, hzK⟩ := hEx
    exact ⟨⟨z, hz⟩, hzK⟩
  set γ := RealBottChern.ofRepresentative η'.form with hγ
  -- continuity along `X'`
  have hcontX' : ContinuousAt
      (fun s : ℝ => (sectionRestrictedVolume F ι hι (β + s • γ)).toReal) 0 := by
    let : MeasurableSpace F.carrier := borel F.carrier
    have : BorelSpace F.carrier := ⟨rfl⟩
    exact continuousAt_classRestrictedVolume_add_smul hι η'
      (isKahler_pullback_centralSection F hμ hι hμι η') β η'.form hbigC hZX'
  -- continuity along `ℰ`
  have hcontE : ContinuousAt
      (fun s : ℝ => (exceptionalRestrictedVolume F hμ (β + s • γ)).toReal) 0 := by
    let := exceptionalChartedSpace F hμ
    have := isComplexManifold_exceptional F hμ
    let : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
    have : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
    have := compactSpace_exceptional F hμ
    have := connectedSpace_exceptional F hμ
    exact continuousAt_classRestrictedVolume_add_smul (contMDiff_exceptionalInclusion F hμ) η'
      (SubmanifoldKahlerRestriction.isKahler_pullback (Nat.le_succ (m + 1))
        (fun _ hz => regularAtDim_exceptionalSet F hμ hz) η'.form η'.isKahler) β η'.form hbigC
      hZE
  have hlim := (hcontX'.add hcontE).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), classVolumeReal F (RealBottChern.ofRepresentative θ) ≤
      (sectionRestrictedVolume F ι hι (β + s • γ)).toReal +
        (exceptionalRestrictedVolume F hμ (β + s • γ)).toReal :=
    eventually_nhdsWithin_of_forall fun s hs =>
      hConv E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' s hs
  have h := ge_of_tendsto hlim hev
  simpa only [Pi.add_apply, zero_smul, add_zero] using h

/-! ### The integrated formula -/

/-- **`tok-wn:integrated`** (WN21 Theorem 1.6 (3)--(4) and Theorem 1.7; DRWNXZ proof of
Theorem 2.10): if `ξ` and `ξ_c = ξ - c{Z}` (`c ≥ 0`) are big with Kähler loci meeting `Z`, then
`vol(ξ) - vol(ξ_c) = n ∫₀^c vol_{X|Z}(ξ_t) dt`.

Proof: for `c = 0` both sides vanish.  For `c > 0`, renormalize the metric of `𝒪(Z)` so that
`|s_Z|_h ≤ 1` (`exists_unitMetric_weight_nonpos`, same curvature), write `ξ = {θ}`, take the
deformation `μ : 𝒳 → X × ℙ¹` (`deformationExists`), the metric of `𝒪(ℰ)`
(`exists_isDeformationExceptionalMetric`), the lift `ι'` of `x ↦ (x, 0)` and `b = c + 2`.  The
key equality gives `vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) = vol(ξ)`, and the restricted-volume formulas
give `vol_{𝒳|X'}(β) = vol(ξ_c)` and `vol_{𝒳|ℰ}(β) = n ∫₀^c vol_{X|Z}(ξ_t) dt`. -/
theorem wnIntegrated_of_keyEquality (hKey : KeyEqualityStatement F)
    (hX' : StrictTransformRestrictedVolumeStatement F)
    (hEx : ExceptionalRestrictedVolumeStatement F) : WNIntegratedStatement F := by
  intro ξ E hE c hc hξ hξc
  rcases hc.eq_or_lt with rfl | hc0
  · simp
  obtain ⟨E', hE', hE'0, hcurv⟩ := exists_unitMetric_weight_nonpos F hE
  rw [← hcurv] at hξc ⊢
  obtain ⟨θ, rfl⟩ : ∃ θ : ClosedRealOneOneForm (m + 1) F.carrier,
      RealBottChern.ofRepresentative θ = ξ := ⟨Quotient.out ξ, Quotient.out_eq ξ⟩
  obtain ⟨𝒳, _, _, _, μ, hμ⟩ := deformationExists F
  obtain ⟨Eℰ, hEℰ⟩ := exists_isDeformationExceptionalMetric F hE' hμ
  obtain ⟨ι, hι, hμι, -, -⟩ := exists_centralSection F hμ
  have h1 := hKey E' hE' hE'0 𝒳 μ hμ Eℰ hEℰ θ (c + 2) c hc0 (by linarith) hξ hξc ι hι hμι
  have h2 := hX' E' hE' hE'0 𝒳 μ hμ Eℰ hEℰ θ (c + 2) c hc0 (by linarith) hξ hξc ι hι hμι
  have h3 := hEx E' hE' hE'0 𝒳 μ hμ Eℰ hEℰ θ (c + 2) c hc0 (by linarith) hξ hξc
  rw [h2, h3] at h1
  linarith

/-! ### The derivative -/

/-- **`tok-wn:derivative`** (WN21 Theorem C; DRWNXZ Theorem 2.10, first point; `tok:ext-wn21`):
for `ξ` big with Kähler locus meeting `Z`, `t ↦ vol(ξ - t{Z})` has derivative `-n vol_{X|Z}(ξ)`
at `t = 0`.

Proof: by `tok-wn:cone` there is `s₀ > 0` with `ξ_t ∈ 𝒜_Z` for `|t| < s₀`; put `s₁ = s₀/2` and
`ξ' = ξ_{-s₁}`.  For `|t| < s₁` the integrated formula for `ξ'` and `c = t + s₁` gives
`vol(ξ_t) = vol(ξ') - n ∫₀^{t+s₁} R(ξ'_u) du`, the integrand is continuous on `[0, 2s₁]`
(`wnContinuity`), and the fundamental theorem of calculus gives the derivative
`-n R(ξ'_{s₁}) = -n R(ξ)` at `t = 0`. -/
theorem wnDerivative_of_wnIntegrated (hInt : WNIntegratedStatement F) :
    WNDerivativeStatement F := by
  intro ξ E hE hξ
  set e := RealBottChern.ofRepresentative E.curvature with he
  obtain ⟨s₀, hs₀, hA⟩ := exists_isBigMeetingFirstDivisor_sub_smul_Ioo F E.curvature (c := 0) hξ
    (by simpa using hξ)
  set s₁ : ℝ := s₀ / 2 with hs₁
  have hs₁pos : 0 < s₁ := by positivity
  set ξ' := ξ - (-s₁) • e with hξ'def
  have hshift : ∀ t : ℝ, ξ' - (t + s₁) • e = ξ - t • e := by
    intro t
    rw [hξ'def]
    module
  have hξ' : IsBigMeetingFirstDivisor F ξ' := hA (-s₁) ⟨by linarith, by linarith⟩
  have hξ'2 : IsBigMeetingFirstDivisor F (ξ' - (2 * s₁) • e) := by
    rw [show 2 * s₁ = s₁ + s₁ by ring, hshift]
    exact hA s₁ ⟨by linarith, by linarith⟩
  set g : ℝ → ℝ := fun u => (firstFlagRestrictedVolume F (ξ' - u • e)).toReal with hg
  have hgc : ContinuousOn g (Icc 0 (2 * s₁)) :=
    wnContinuity F ξ' E hE (2 * s₁) (by positivity) hξ' hξ'2
  set n : ℝ := ((m + 1 : ℕ) : ℝ) with hn
  have hV : ∀ t ∈ Ioo (-s₁) s₁, classVolumeReal F (ξ - t • e) =
      classVolumeReal F ξ' - n * ∫ u in (0 : ℝ)..(t + s₁), g u := by
    intro t ht
    have hc : 0 ≤ t + s₁ := by linarith [ht.1]
    have hmem : IsBigMeetingFirstDivisor F (ξ' - (t + s₁) • e) := by
      rw [hshift]
      exact hA t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h := hInt ξ' E hE (t + s₁) hc hξ' hmem
    rw [hshift] at h
    linarith
  have hgcont : ContinuousAt g s₁ :=
    hgc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hint : IntervalIntegrable g volume 0 s₁ :=
    (hgc.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hs₁pos.le
  have hmeas : StronglyMeasurableAtFilter g (𝓝 s₁) volume :=
    (hgc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s₁
      ⟨hs₁pos, by linarith⟩
  have hF : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, g x) (g s₁) s₁ :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hgcont
  have hF' : HasDerivAt (fun t => ∫ x in (0 : ℝ)..(t + s₁), g x) (g s₁) 0 :=
    HasDerivAt.comp_add_const 0 s₁ (by simpa using hF)
  have hgs₁ : g s₁ = (firstFlagRestrictedVolume F ξ).toReal := by
    simp only [hg]
    rw [show ξ' - s₁ • e = ξ' - (0 + s₁) • e by rw [zero_add], hshift, zero_smul, sub_zero]
  have hderiv : HasDerivAt
      (fun t => classVolumeReal F ξ' - n * ∫ x in (0 : ℝ)..(t + s₁), g x)
      (-n * (firstFlagRestrictedVolume F ξ).toReal) 0 := by
    have := (hF'.const_mul n).const_sub (classVolumeReal F ξ')
    rw [hgs₁, ← neg_mul] at this
    exact this
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (show -s₁ < 0 by linarith) hs₁pos] with t ht
  exact hV t ht

/-! ### The package statements -/

/-- **WN21 Theorem C, integrated form, with continuity** (`WNStatement`, consumed by package
VOL), conditional on the key easy inequality and the perturbed hard inequality (WN-KEY),
`tok-wn:beta-big` (WN-DEF) and the restricted-volume formulas along `X'` and `ℰ` (WN-VF). -/
theorem wnStatement_of_key (hEasy : KeyEasyStatement F) (hConv : KeyConvergenceStatement F)
    (hBeta : BetaBigStatement F) (hX' : StrictTransformRestrictedVolumeStatement F)
    (hEx : ExceptionalRestrictedVolumeStatement F) : WNStatement F :=
  ⟨wnIntegrated_of_keyEquality F (keyEquality_of_keyEasy_of_keyConvergence F hEasy hConv hBeta)
    hX' hEx, wnContinuity F⟩

/-- **WN21 Theorem C** (`tok:ext-wn21`, DRWNXZ Theorem 2.10, first point), conditional on the
same named statements as `wnStatement_of_key`. -/
theorem wnDerivative_of_key (hEasy : KeyEasyStatement F) (hConv : KeyConvergenceStatement F)
    (hBeta : BetaBigStatement F) (hX' : StrictTransformRestrictedVolumeStatement F)
    (hEx : ExceptionalRestrictedVolumeStatement F) : WNDerivativeStatement F :=
  wnDerivative_of_wnIntegrated F (wnStatement_of_key F hEasy hConv hBeta hX' hEx).1

end SGPT.Okounkov.TranscendentalWN

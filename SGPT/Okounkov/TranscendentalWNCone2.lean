import SGPT.Okounkov.TranscendentalWNCone
import SGPT.Foundations.Analysis.Pending.AmbientConvexCurrent
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.FirstPass.LelongNumberPole
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSetBounded
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

/-!
# Convexity of the cone of classes whose Kähler locus meets `Y₁`

Blueprint node `tok-wn:cone`, parts (b) and (c) (chapter `claude-tok-wn`; Matsumura 2013,
Proposition 4.10; DRWNXZ, proof of Theorem 2.10, first paragraph): the set `𝒜_Z` of big classes
`ξ` with `Z ∩ K(ξ) ≠ ∅`, `K(ξ) = X \ E_nK(ξ)`, is convex, and if `ξ, ξ - c{Y₁} ∈ 𝒜_{Y₁}`
(`c ≥ 0`) then `ξ - t{Y₁} ∈ 𝒜_{Y₁}` for all `t` in an open interval containing `[0, c]`.

Proof of convexity: by Boucksom's theorem
(`NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus`)
`ξ^i` contains a Kähler current `T^i` whose polar set is exactly `E_nK(ξ^i)`. Its potential is
finite at a point of `Z`, so its restriction to the connected manifold `Z` is a genuine
quasi-psh potential (identity principle), and the polar set of a convex combination of two
genuine potentials is locally pluripolar: there is `y ∈ Z` where both potentials are finite.
The Kähler current `tT^0 + (1 - t)T^1 ∈ tξ^0 + (1 - t)ξ^1` (`kahlerCurrentConvexComb`) has finite
potential at `y`, hence Lelong number `0` at `y`
(`NonKahlerLocus.eq_bot_of_lelongNumber_pos`), so `y ∉ E_nK(tξ^0 + (1 - t)ξ^1)`.

## Main results

* `kahlerCurrentConvexComb`, `kahlerCurrentSmul`: convex combinations and positive multiples of
  Kähler currents;
* `exists_kahlerCurrent_finite_common`: Kähler currents in `ξ^0`, `ξ^1` finite at a common
  point of `Z`;
* `isBigClass_meeting_convexComb` (**`tok-wn:cone` (b)** for `Z = ι(V)`, `V` connected) and
  `isBigMeetingFirstDivisor_convex` (`Convex ℝ 𝒜_{Y₁}`); `isBigClass_meeting_smul`,
  `isBigMeetingFirstDivisor_smul` (`𝒜_Z` is a cone);
* `isBigMeetingFirstDivisor_sub_smul_of_mem_Icc`, `exists_isBigMeetingFirstDivisor_sub_smul_Ioo`
  (**`tok-wn:cone` (c)**).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

section ConvexCurrent

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The convex combination of two Kähler currents.** If `T = θ_T + dd^c φ ≥ κ_T` is a Kähler
current in `α` and `S = θ_S + dd^c ψ ≥ κ_S` one in `β`, then for `0 < t < 1`,
`tT + (1 - t)S = (tθ_T + (1 - t)θ_S) + dd^c(tφ + (1 - t)ψ) ≥ tκ_T` is a Kähler current in
`tα + (1 - t)β`. -/
def kahlerCurrentConvexComb {α β : RealBottChern n M} (T : KahlerCurrent α)
    (S : KahlerCurrent β) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    KahlerCurrent (t • α + (1 - t) • β) where
  representative := t • T.representative + (1 - t) • S.representative
  represents := by
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul,
      RealBottChern.ofRepresentative_smul, T.represents, S.represents]
  potential := convexComb t T.potential S.potential
  lowerBound := KahlerBackground.smul ht0 T.lowerBound
  strictlyPsh := by
    have h := AmbientConvexCurrent.isThetaPshPotential_convexComb_forms T.strictlyPsh
      S.strictlyPsh ht0 ht1
    have h2 := LocalPotentials.isThetaPshPotential_add_of_semipositive h
      (KahlerDomination.isSemipositive_smul S.lowerBound.isSemipositive
        (by linarith : (0 : ℝ) ≤ 1 - t))
    have he : t • (T.representative - T.lowerBound.form) +
        (1 - t) • (S.representative - S.lowerBound.form) + (1 - t) • S.lowerBound.form =
        t • T.representative + (1 - t) • S.representative -
          (KahlerBackground.smul ht0 T.lowerBound).form := by
      rw [KahlerBackground.smul_form]
      module
    rwa [he] at h2

@[simp] theorem kahlerCurrentConvexComb_potential {α β : RealBottChern n M}
    (T : KahlerCurrent α) (S : KahlerCurrent β) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (kahlerCurrentConvexComb T S ht0 ht1).potential = convexComb t T.potential S.potential :=
  rfl

/-- **A positive multiple of a Kähler current.** If `T = θ_T + dd^c φ ≥ κ` is a Kähler current
in `α` and `c > 0`, then `cT = cθ_T + dd^c(cφ) ≥ cκ` is a Kähler current in `cα`. -/
def kahlerCurrentSmul {α : RealBottChern n M} (T : KahlerCurrent α) {c : ℝ} (hc : 0 < c) :
    KahlerCurrent (c • α) where
  representative := c • T.representative
  represents := by rw [RealBottChern.ofRepresentative_smul, T.represents]
  potential := fun x => (c : EReal) * T.potential x
  lowerBound := KahlerBackground.smul hc T.lowerBound
  strictlyPsh := by
    rw [KahlerBackground.smul_form, ← smul_sub]
    exact RestrictedApproximantComparison.isThetaPshPotential_smul T.strictlyPsh hc

@[simp] theorem kahlerCurrentSmul_potential {α : RealBottChern n M} (T : KahlerCurrent α)
    {c : ℝ} (hc : 0 < c) :
    (kahlerCurrentSmul T hc).potential = fun x => (c : EReal) * T.potential x :=
  rfl

/-- A Kähler current whose potential is finite at `x` has Lelong number `0` at `x`, so `x` is
not in the non-Kähler locus. -/
theorem not_mem_nonKahlerLocus_of_potential_ne_bot (hn : 0 < n) {α : RealBottChern n M}
    (T : KahlerCurrent α) {x : M} (hx : T.potential x ≠ ⊥) : x ∉ nonKahlerLocus α :=
  fun h => hx (eq_bot_of_lelongNumber_pos hn T.strictlyPsh.1 (h T))

end ConvexCurrent

section Cone

variable {n k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [ConnectedSpace V]
  {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

include hι in
/-- **Kähler currents finite at a common point of `Z`.** If `α`, `β` are big and `ι(V)` (`V`
connected) meets both Kähler loci, there are Kähler currents in `α` and `β` whose potentials
are finite at a common point of `ι(V)`. -/
theorem exists_kahlerCurrent_finite_common (hn : 0 < n) {α β : RealBottChern n M}
    (hα : IsBigClass α) (hβ : IsBigClass β) (hαZ : ∃ y : V, ι y ∉ nonKahlerLocus α)
    (hβZ : ∃ y : V, ι y ∉ nonKahlerLocus β) :
    ∃ (Tα : KahlerCurrent α) (Tβ : KahlerCurrent β) (y : V),
      Tα.potential (ι y) ≠ ⊥ ∧ Tβ.potential (ι y) ≠ ⊥ := by
  obtain ⟨yα, hyα⟩ := hαZ
  obtain ⟨yβ, hyβ⟩ := hβZ
  obtain ⟨Kα, -, hKα⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      hn α hα
  obtain ⟨Kβ, -, hKβ⟩ :=
    NonKahlerLocusPoleSetBounded.exists_kahlerCurrent_analyticSingularityType_poleSet_eq_nonKahlerLocus
      hn β hβ
  have hfin : ∀ {γ : RealBottChern n M} (K : KahlerCurrent γ),
      poleSet K.potential = nonKahlerLocus γ → ∀ y : V, ι y ∉ nonKahlerLocus γ →
        IsThetaPshPotential
          (ClosedRealOneOneForm.pullback hι (K.representative - K.lowerBound.form)).val
          (fun z => K.potential (ι z)) := by
    intro γ K hK y hy
    have hpsh := GlobalPotentialPullback.thetaPlurisubharmonic_comp hι K.strictlyPsh.1
    refine ⟨hpsh, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh
      ⟨y, fun hbot => hy ?_⟩⟩
    rw [← hK]
    exact hbot
  have hα' := hfin Kα hKα yα hyα
  have hβ' := hfin Kβ hKβ yβ hyβ
  have hc := AmbientConvexCurrent.isThetaPshPotential_convexComb_forms hα' hβ'
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨y, -, hy⟩ := hc.2 yα univ isOpen_univ (mem_univ _)
  refine ⟨Kα, Kβ, y, fun h => hy ?_, fun h => hy ?_⟩
  · have := poles_convexComb_subset (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) (fun z => Kα.potential (ι z)) (fun z => Kβ.potential (ι z))
    simp only [convexComb_apply, h, EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      EReal.bot_add]
  · simp only [convexComb_apply, h,
      EReal.coe_mul_bot_of_pos (by norm_num : (0 : ℝ) < 1 - 1 / 2), EReal.add_bot]

include hι in
/-- **`tok-wn:cone` (b)** (Matsumura 2013, Proposition 4.10): if `α`, `β` are big with Kähler
loci meeting `Z = ι(V)` (`V` connected), then for `0 ≤ t ≤ 1` the class `tα + (1 - t)β` is big
and its Kähler locus meets `Z`. -/
theorem isBigClass_meeting_convexComb (hn : 0 < n) {α β : RealBottChern n M}
    (hα : IsBigClass α) (hβ : IsBigClass β) (hαZ : ∃ y : V, ι y ∉ nonKahlerLocus α)
    (hβZ : ∃ y : V, ι y ∉ nonKahlerLocus β) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsBigClass (t • α + (1 - t) • β) ∧
      ∃ y : V, ι y ∉ nonKahlerLocus (t • α + (1 - t) • β) := by
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp only [zero_smul, sub_zero, one_smul, zero_add]
    exact ⟨hβ, hβZ⟩
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp only [zero_smul, sub_self, one_smul, add_zero]
    exact ⟨hα, hαZ⟩
  obtain ⟨Tα, Tβ, y, hyα, hyβ⟩ := exists_kahlerCurrent_finite_common hι hn hα hβ hαZ hβZ
  let T := kahlerCurrentConvexComb Tα Tβ ht0' ht1'
  refine ⟨⟨T⟩, y, not_mem_nonKahlerLocus_of_potential_ne_bot hn T ?_⟩
  intro hbot
  rcases poles_convexComb_subset ht0' ht1' _ _ hbot with h | h
  · exact hyα h
  · exact hyβ h

include hι in
/-- The cone `𝒜_Z` is invariant under positive scaling: if `α` is big with Kähler locus
meeting `Z = ι(V)` and `c > 0`, so is `cα`. -/
theorem isBigClass_meeting_smul (hn : 0 < n) {α : RealBottChern n M} (hα : IsBigClass α)
    (hαZ : ∃ y : V, ι y ∉ nonKahlerLocus α) {c : ℝ} (hc : 0 < c) :
    IsBigClass (c • α) ∧ ∃ y : V, ι y ∉ nonKahlerLocus (c • α) := by
  obtain ⟨Tα, -, y, hy, -⟩ := exists_kahlerCurrent_finite_common hι hn hα hα hαZ hαZ
  refine ⟨⟨kahlerCurrentSmul Tα hc⟩, y,
    not_mem_nonKahlerLocus_of_potential_ne_bot hn (kahlerCurrentSmul Tα hc) ?_⟩
  exact fun hbot => hy (eq_bot_of_coe_mul_eq_bot hc hbot)

end Cone

/-! ### The flag case -/

section Flag

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- `IsBigMeetingFirstDivisor` in terms of the inclusion `Y₁ ↪ X`. -/
theorem isBigMeetingFirstDivisor_iff (ξ : RealBottChern (m + 1) F.carrier) :
    IsBigMeetingFirstDivisor F ξ ↔
      IsBigClass ξ ∧ ∃ y : F.tail.carrier, firstFlagInclusion F y ∉ nonKahlerLocus ξ := by
  unfold IsBigMeetingFirstDivisor
  rw [SGPT.PSH.BookCurrent.isBig_iff_isBigClass]
  constructor
  · rintro ⟨h1, y, hy, hyK⟩
    exact ⟨h1, ⟨y, hy⟩, hyK⟩
  · rintro ⟨h1, y, hyK⟩
    exact ⟨h1, y.1, y.2, hyK⟩

/-- **`tok-wn:cone` (b)** (Matsumura 2013, Proposition 4.10): the cone `𝒜_{Y₁}` of big classes
whose Kähler locus meets `Y₁` is convex. -/
theorem isBigMeetingFirstDivisor_convex :
    Convex ℝ {ξ : RealBottChern (m + 1) F.carrier | IsBigMeetingFirstDivisor F ξ} := by
  intro α hα β hβ a b ha hb hab
  obtain ⟨hα1, hα2⟩ := (isBigMeetingFirstDivisor_iff F α).mp hα
  obtain ⟨hβ1, hβ2⟩ := (isBigMeetingFirstDivisor_iff F β).mp hβ
  have hb' : b = 1 - a := by linarith
  subst hb'
  exact (isBigMeetingFirstDivisor_iff F _).mpr
    (isBigClass_meeting_convexComb (contMDiff_firstFlagInclusion F) (Nat.succ_pos m) hα1 hβ1
      hα2 hβ2 ha (by linarith))

/-- The cone `𝒜_{Y₁}` is invariant under positive scaling. -/
theorem isBigMeetingFirstDivisor_smul {ξ : RealBottChern (m + 1) F.carrier}
    (hξ : IsBigMeetingFirstDivisor F ξ) {c : ℝ} (hc : 0 < c) :
    IsBigMeetingFirstDivisor F (c • ξ) := by
  obtain ⟨h1, h2⟩ := (isBigMeetingFirstDivisor_iff F ξ).mp hξ
  exact (isBigMeetingFirstDivisor_iff F _).mpr
    (isBigClass_meeting_smul (contMDiff_firstFlagInclusion F) (Nat.succ_pos m) h1 h2 hc)

/-- **`tok-wn:cone` (c)**, closed segment: if `ξ` and `ξ - c e` (`c ≥ 0`) lie in `𝒜_{Y₁}`, then
so does `ξ - t e` for every `t ∈ [0, c]`. -/
theorem isBigMeetingFirstDivisor_sub_smul_of_mem_Icc {ξ e : RealBottChern (m + 1) F.carrier}
    {c : ℝ} (hξ : IsBigMeetingFirstDivisor F ξ) (hξc : IsBigMeetingFirstDivisor F (ξ - c • e))
    {t : ℝ} (ht : t ∈ Icc 0 c) : IsBigMeetingFirstDivisor F (ξ - t • e) := by
  rcases (ht.1.trans ht.2).eq_or_lt with hc0 | hc0
  · have ht0 : t = 0 := le_antisymm (hc0 ▸ ht.2) ht.1
    simpa [ht0] using hξ
  have hmem := isBigMeetingFirstDivisor_convex F hξ hξc
    (a := 1 - t / c) (b := t / c) (by rw [sub_nonneg, div_le_one hc0]; exact ht.2)
    (div_nonneg ht.1 hc0.le) (by ring)
  have he : (1 - t / c) • ξ + (t / c) • (ξ - c • e) = ξ - t • e := by
    have hct : t = t / c * c := by field_simp
    conv_rhs => rw [hct]
    module
  rwa [he] at hmem

/-- **`tok-wn:cone` (c)** (DRWNXZ, proof of Theorem 2.10): if `ξ` and `ξ - c{γ}` lie in `𝒜_{Y₁}`,
there is `s₀ > 0` with `ξ - t{γ} ∈ 𝒜_{Y₁}` for all `t ∈ (-s₀, c + s₀)`. -/
theorem exists_isBigMeetingFirstDivisor_sub_smul_Ioo {ξ : RealBottChern (m + 1) F.carrier}
    (γ : ClosedRealOneOneForm (m + 1) F.carrier) {c : ℝ}
    (hξ : IsBigMeetingFirstDivisor F ξ)
    (hξc : IsBigMeetingFirstDivisor F (ξ - c • RealBottChern.ofRepresentative γ)) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ t ∈ Ioo (-s₀) (c + s₀),
      IsBigMeetingFirstDivisor F (ξ - t • RealBottChern.ofRepresentative γ) := by
  set e := RealBottChern.ofRepresentative γ with he
  obtain ⟨s₁, hs₁, h₁⟩ := isBigMeetingFirstDivisor_add_smul F hξ γ
  obtain ⟨s₂, hs₂, h₂⟩ := isBigMeetingFirstDivisor_add_smul F hξc γ
  set s₀ := min s₁ s₂ with hs₀
  have hs₀pos : 0 < s₀ := lt_min hs₁ hs₂
  have hlo : IsBigMeetingFirstDivisor F (ξ - (-s₀) • e) := by
    have h := h₁ s₀ (by rw [abs_of_pos hs₀pos]; exact min_le_left _ _)
    rwa [show ξ + s₀ • e = ξ - (-s₀) • e by module] at h
  have hhi : IsBigMeetingFirstDivisor F (ξ - (-s₀) • e - (c + 2 * s₀) • e) := by
    have h := h₂ (-s₀) (by rw [abs_neg, abs_of_pos hs₀pos]; exact min_le_right _ _)
    rwa [show ξ - c • e + (-s₀) • e = ξ - (-s₀) • e - (c + 2 * s₀) • e by module] at h
  refine ⟨s₀, hs₀pos, fun t ht => ?_⟩
  have h := isBigMeetingFirstDivisor_sub_smul_of_mem_Icc F hlo hhi
    (t := t + s₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rwa [show ξ - (-s₀) • e - (t + s₀) • e = ξ - t • e by module] at h

end Flag

end SGPT.Okounkov.TranscendentalWN

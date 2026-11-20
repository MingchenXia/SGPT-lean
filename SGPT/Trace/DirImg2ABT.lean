import SGPT.Trace.Trace2Bertini
import SGPT.Trace.OTExtAlongOpenness
import SGPT.NAPotential.GAGAMultSiuGerms
import SGPT.NAPotential.BJPrepLelongConvex
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.RegularPointDimension
import Mathlib.Data.Rat.Denumerable

/-!
# `cor:ABTfortrace` from `thm:Bert`

Source: `chapter_trace.tex`, Section "Analytic Bertini theorems", `cor:ABTfortrace` (992--998)
and `thm:Bert` (814--820). Blueprint `claude-dirimg2.tex`, nodes `claude-dirimg2:levels`,
`claude-dirimg2:stalk-to-germ`, `claude-dirimg2:abt-of-bert`.

The partial formalization of `cor:ABTfortrace` (`SGPT.Trace.Trace2Bertini`) reduced its open
half `Tr_H(φ) ⪯_𝓘 φ|_H` to the reverse Bertini inclusion in the *germ-ideal* form
`Rest_H 𝓘(c φ) ⊆ 𝓘(c φ|_H)` (`ReverseRestrictionInclusion`, `restrictIdeal`) at *every real*
level `c > 0`. The book obtains this from `thm:Bert` applied to the countably many potentials
`k φ`. This file proves the two bridges that make this step formal, so that `cor:ABTfortrace`
follows from `thm:Bert` alone:

* `multiplierIdeal_one_mul_eq`: `𝓘(1 · (c φ)) = 𝓘(c φ)` (the multiplier clause of `thm:Bert` for
  the potential `c φ` is the level-`c` clause for `φ`);
* `restrict_mem_of_reverseMultiplierInclusion`: the stalk form of the reverse inclusion used in
  `thm:Bert` (`ReverseMultiplierInclusion`, inside `𝒪_{H',y} = 𝒪_{X,y}/𝓘_{H',y}` through
  `structureStalkEquiv`) gives the germ form: restrictions of germs of `𝓘(c φ)` lie in `𝓘(c φ|_H)`;
* `reverseRestrictionInclusion_of_rat`: rational levels suffice (strong openness, Guan–Zhou,
  `PositiveCurrentTraceMultiplier.exists_gt_mem_multiplierIdeal`, and monotonicity in the level);
* `coPluripolar_abtTrace_of_rat_reverse`: `cor:ABTfortrace` holds as soon as the reverse inclusion
  of `thm:Bert` holds for quasi-every `H` at every rational level;
* `coPluripolar_reverse_of_bertiniGoodSet_mul`: `thm:Bert` for the potential `q φ` gives that
  reverse inclusion at level `q`;
* `coPluripolar_abtTrace_of_analyticBertini`: **`thm:Bert` (`AnalyticBertiniStatement`) implies
  `cor:ABTfortrace`** on every connected projective manifold, with the hypotheses of the proved
  clauses (`coPluripolar_abtTracePartial`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.DirImg2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Okounkov SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi

/-! ### Levels of multiplier ideals -/

section Levels

variable {m : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]

/-- **`𝓘(1 · (c u)) = 𝓘(c u)`** for `c > 0`: the multiplier ideal of the potential `c u` at level
`1` is the level-`c` multiplier ideal of `u` (the weight is `e^{-2 c u}` in both cases). -/
theorem multiplierIdeal_one_mul_eq (u : Z → EReal) {c : ℝ} (hc : 0 < c) :
    multiplierIdeal (n := m) 1 (fun z => (c : EReal) * u z) = multiplierIdeal (n := m) c u := by
  have hden : ∀ (e : ComplexChart m Z) (f : ComplexModel m → ℂ),
      multiplierDensity (chartFunction (fun z => (c : EReal) * u z) e) 1 f =
        multiplierDensity (chartFunction u e) c f := by
    intro e f
    funext z
    simp only [multiplierDensity, multiplierWeight, chartFunction, EReal.coe_one, one_mul]
  ext x g
  simp only [multiplierIdeal, MultiplierIntegrableAt, WeightedL2On, hden]
  constructor
  · rintro ⟨hg, -, h⟩
    exact ⟨hg, hc, h⟩
  · rintro ⟨hg, -, h⟩
    exact ⟨hg, one_pos, h⟩

/-- `IsInSpanAt` is monotone in the set of generators. -/
theorem isInSpanAt_mono {S T : (Z → ℂ) → Prop} {x : Z} {g : Z → ℂ}
    (h : IsInSpanAt (n := m) S x g) (hST : ∀ s, S s → T s) : IsInSpanAt (n := m) T x g := by
  obtain ⟨hg, N, s, a, hs, ha, heq⟩ := h
  exact ⟨hg, N, s, a, fun i => hST _ (hs i), ha, heq⟩

end Levels

/-! ### From the stalk form to the germ form of the reverse inclusion -/

section Bridge

open SGPT.Trace.Bertini SGPT.Trace.BertiniGeneral SGPT.Trace.Trace2Bertini SGPT.Projective
  SubmanifoldIdealRestriction

variable {N n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)
  (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)

/-- **Stalk form ⇒ germ form.** On a smooth member `H'` of dimension `k`, if the reverse
inclusion `Rest_{H'} 𝓘(c φ) ⊆ 𝓘(c φ|_{H'})` holds in the stalk form of `thm:Bert`
(`ReverseMultiplierInclusion`, `c > 0`) and `φ|_{H'}` is quasi-psh, then the restriction to `H'` of
every germ of `𝓘(c φ)` at a point of `H'` is a germ of `𝓘(c φ|_{H'})`. -/
theorem restrict_mem_of_reverseMultiplierInclusion {l : HyperplaneSpace N} {k : ℕ} (hk : k ≤ n)
    (hsm : IsSmoothMemberOfDim p hp l k) {φ : X → EReal} {c : ℝ} (hc : 0 < c)
    (hrev : ReverseMultiplierInclusion p hp hk hsm φ c)
    (hφW : letI := chartedSpace hk hsm.1
      haveI : IsComplexManifold k (member p l) := isComplexManifold_chartedSpace hk hsm.1
      ManifoldQuasiPlurisubharmonic (n := k) (fun y : member p l => φ y.1))
    (y : member p l) {a : X → ℂ} (ha : (multiplierIdeal (n := n) c φ).mem y.1 a) :
    letI := chartedSpace hk hsm.1
    (multiplierIdeal (n := k) c (fun y : member p l => φ y.1)).mem y (a ∘ Subtype.val) := by
  let := chartedSpace hk hsm.1
  have : IsComplexManifold k (member p l) := isComplexManifold_chartedSpace hk hsm.1
  have hhol : HolomorphicAt n a y.1 := ha.1
  have hx : NativeHolGerm.mk a hhol ∈ stalkIdeal (multiplierIdeal (n := n) c φ) y.1 :=
    SGPT.NAPotential.GAGAMult.mk_mem_stalkIdeal hhol ha
  have hrest : Ideal.Quotient.mk _ (NativeHolGerm.mk a hhol) ∈
      restStalk (multiplierIdeal (n := n) c φ)
        (submanifoldSubspace (isClosedSubmanifold_of_isSmoothMemberOfDim p hp hsm)) y.1 :=
    Ideal.mem_map_of_mem _ hx
  have hmem := hrev y hrest
  rw [Ideal.mem_comap, structureStalkEquiv_mk, restrictGerm_mk] at hmem
  have hspan := SGPT.NAPotential.GAGAMult.isInSpanAt_of_mk_mem_spanGerms
    (holomorphicAt_comp_val hk hsm.1 hhol) hmem
  exact MultiplierIdealProductComparison.mem_multiplierIdeal_of_isInSpanAt hφW hc hspan

/-- **Rational levels suffice (strong openness).** Let `H'` be a connected smooth member, `φ`
`θ`-psh with `φ|_{H'} ≢ -∞`. If the reverse inclusion of `thm:Bert` holds on `H'` at every
rational level `q > 0` (stalk form), then `Rest_{H'} 𝓘(c φ) ⊆ 𝓘(c φ|_{H'})` at every real level
`c > 0`, in the germ-ideal form `ReverseRestrictionInclusion` used by `cor:ABTfortrace`. -/
theorem reverseRestrictionInclusion_of_rat {l : HyperplaneSpace N}
    (h : IsConnectedSmoothMember n p l) {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hne : ∃ x ∈ member p l, φ x ≠ ⊥)
    (hrat : ∀ q : ℚ, 0 < q →
      ReverseMultiplierInclusion p hp (Nat.sub_le n 1)
        (isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p hp h.1) φ q) :
    ReverseRestrictionInclusion (isClosedConnectedSubmanifold_member p hp h) φ := by
  set hW := isClosedConnectedSubmanifold_member p hp h
  set hsm := isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p hp h.1
  have hk : n - 1 ≤ n := Nat.sub_le n 1
  let : ChartedSpace (ComplexModel (n - 1)) (member p l) := chartedSpace hk hW.2.2
  have : IsComplexManifold (n - 1) (member p l) := isComplexManifold_chartedSpace hk hW.2.2
  have : ConnectedSpace (member p l) := isConnected_iff_connectedSpace.mp hW.2.1
  have hι := contMDiff_val hk hW.2.2
  obtain ⟨x, hx, hφx⟩ := hne
  have hne' : ∃ y : member p l, φ (y : X) ≠ ⊥ := ⟨⟨x, hx⟩, hφx⟩
  have hφW : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y : member p l => φ y) := isThetaPshPotential_comp hι hφ hne'
  have hqW : ManifoldQuasiPlurisubharmonic (n := n - 1) (fun y : member p l => φ y) :=
    hφW.1.quasiPlurisubharmonic
  have hqX : ManifoldQuasiPlurisubharmonic (n := n) φ := hφ.1.quasiPlurisubharmonic
  intro c hc y g hg
  rw [mem_restrictIdeal_iff] at hg
  refine MultiplierIdealProductComparison.mem_multiplierIdeal_of_isInSpanAt hqW hc
    (isInSpanAt_mono hg ?_)
  rintro s ⟨a, ha, rfl⟩
  -- strong openness on `X`, then a rational level in between
  obtain ⟨c', hcc', hc'⟩ :=
    PositiveCurrentTraceMultiplier.exists_gt_mem_multiplierIdeal hqX ha
  obtain ⟨q, hcq, hqc'⟩ := exists_rat_btwn hcc'
  have hq0 : (0 : ℝ) < q := hc.trans hcq
  have haq : (multiplierIdeal (n := n) (q : ℝ) φ).mem y.1 a :=
    SGPT.Trace.OTExt.mem_multiplierIdeal_of_exponent_le hqX hq0 hqc'.le hc'
  have hres := restrict_mem_of_reverseMultiplierInclusion p hp hk hsm hq0
    (hrat q (by exact_mod_cast hq0)) hqW y haq
  exact SGPT.Trace.OTExt.mem_multiplierIdeal_of_exponent_le hqW hc hcq.le hres

/-- **`thm:Bert` for `c φ` is the level-`c` reverse inclusion for `φ`.** If `φ` is quasi-psh,
`c > 0` and the good set `𝒢` of `thm:Bert` for the potential `c φ` is co-pluripolar, then for
quasi-every `H` the reverse inclusion `Rest_{H'} 𝓘(c φ) ⊆ 𝓘(c φ|_{H'})` holds (stalk form) on every
smooth structure of the member `H'` (the dimension of a nonempty smooth member is unique). -/
theorem coPluripolar_reverse_of_bertiniGoodSet_mul {φ : X → EReal} {c : ℝ} (hc : 0 < c)
    (hG : (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      (bertiniGoodSet p hp (fun x => (c : EReal) * φ x))) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∀ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothMemberOfDim p hp l k),
        ReverseMultiplierInclusion p hp hk hsm φ c} := by
  refine coPluripolar_mono hG fun l hl => ?_
  obtain ⟨k, hk, hsm, heq⟩ := hl
  intro k' hk' hsm' y
  have hkk : k = k' := RegularPointDimension.eq_of_regularAtDim (hsm.1 y y.2) (hsm'.1 y y.2)
  subst hkk
  let := chartedSpace hk hsm.1
  have h1 := heq y
  have hX := multiplierIdeal_one_mul_eq (m := n) φ hc
  have hW := multiplierIdeal_one_mul_eq (m := k) (fun y : member p l => φ y.1) hc
  rw [hX] at h1
  erw [hW] at h1
  exact h1.symm.le

end Bridge

/-! ### `cor:ABTfortrace` from `thm:Bert` -/

section General

open SGPT.Trace.Bertini SGPT.Trace.BertiniGeneral SGPT.Trace.Trace2Bertini SGPT.Projective
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {N n : ℕ}

/-- **`cor:ABTfortrace` from the rational-level reverse inclusion of `thm:Bert`.** Let `X` be a
compact connected complex manifold of dimension `n ≠ 0` with a Kähler form, `p : X → ℙᴺ`
nondegenerate (`N ≥ 1`) with connected members for quasi-every `H` (the book's standing
assumption), and `φ ∈ PSH(X, θ)`. If for every rational `q > 0` the reverse inclusion
`Rest_{H'} 𝓘(q φ) ⊆ 𝓘(q φ|_{H'})` of `thm:Bert` holds for quasi-every `H` (stalk form, on every
smooth member), then quasi-every `H ∈ Λ` is connected and smooth, satisfies `ν(φ, H) = 0`, and
`Tr_H(φ) ∼_𝓘 φ|_H` for every trace operator. -/
theorem coPluripolar_abtTrace_of_rat_reverse {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]
    (p : X → ComplexProjectiveSpace N)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hn : n ≠ 0) (omega : KahlerBackground n X) (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | IsConnected (member p l)})
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hrev : ∀ q : ℚ, 0 < q →
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
        {l | ∀ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothMemberOfDim p hp l k),
          ReverseMultiplierInclusion p hp hk hsm φ q}) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        IsABTTrace omega (isClosedConnectedSubmanifold_member p hp h) φ} := by
  let S : ℕ → Set (HyperplaneSpace N) := fun j =>
    {l | 0 < Denumerable.ofNat ℚ j → ∀ (k : ℕ) (hk : k ≤ n) (hsm : IsSmoothMemberOfDim p hp l k),
      ReverseMultiplierInclusion p hp hk hsm φ (Denumerable.ofNat ℚ j)}
  have hS : ∀ j, (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      (S j) := by
    intro j
    by_cases hj : 0 < Denumerable.ofNat ℚ j
    · exact coPluripolar_mono (hrev _ hj) fun l hl _ => hl
    · exact coPluripolar_mono (hrev 1 one_pos) fun l _ h => absurd h hj
  refine coPluripolar_mono (coPluripolar_inter (coPluripolar_generalPositionSet p
    (qpshGeneralRestriction p hp hnd hN) hconn hφ) (coPluripolar_iInter hS)) fun l hl => ?_
  obtain ⟨⟨h, hx⟩, hr⟩ := hl
  refine ⟨h, isABTTrace_of_reverse hn omega _ hφ hx ?_⟩
  refine reverseRestrictionInclusion_of_rat p hp h hφ hx fun q hq => ?_
  obtain ⟨j, hjq⟩ : ∃ j, Denumerable.ofNat ℚ j = q :=
    ⟨@Encodable.encode ℚ Denumerable.toEncodable q, Denumerable.ofNat_encode q⟩
  have hj : l ∈ S j := Set.mem_iInter.mp hr j
  have hj' := hj (hjq ▸ hq) _ (Nat.sub_le n 1)
    (isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p hp h.1)
  rwa [hjq] at hj'

/-- **`thm:Bert` implies `cor:ABTfortrace`.** Assume the analytic Bertini theorem
(`AnalyticBertiniStatement`, the statement of `thm:Bert`). Let `X` be a connected projective
manifold of dimension `n ≠ 0` with a Kähler form, `p : X → ℙᴺ` nondegenerate (`Λ` base-point
free, `N ≥ 1`) whose connected members form a co-pluripolar set (the book's standing assumption
of the section), and `φ ∈ PSH(X, θ)`. Then quasi-every `H ∈ Λ` is connected and smooth,
satisfies `ν(φ, H) = 0`, and `Tr_H(φ) ∼_𝓘 φ|_H`: the full statement of `cor:ABTfortrace`.
(`thm:Bert` is applied to the countably many quasi-psh potentials `q φ`, `q ∈ ℚ_{>0}`.) -/
theorem coPluripolar_abtTrace_of_analyticBertini (hABT : AnalyticBertiniStatement)
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [CompactSpace X] [ConnectedSpace X] (hproj : IsProjectiveManifold n X)
    (p : X → ComplexProjectiveSpace N)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hn : n ≠ 0) (omega : KahlerBackground n X) (hnd : IsNondegenerate p) (hN : 1 ≤ N)
    (hconn : (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | IsConnected (member p l)})
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ h : IsConnectedSmoothMember n p l,
        IsABTTrace omega (isClosedConnectedSubmanifold_member p hp h) φ} := by
  refine coPluripolar_abtTrace_of_rat_reverse p hp hn omega hnd hN hconn hφ fun q hq => ?_
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqφ := SGPT.NAPotential.BJPrep.manifoldQuasiPlurisubharmonic_const_mul
    hφ.1.quasiPlurisubharmonic hq'
  exact coPluripolar_reverse_of_bertiniGoodSet_mul p hp hq' (hABT n N X hproj hN p hp _ hqφ)

end General

end SGPT.Trace.DirImg2

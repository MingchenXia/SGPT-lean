import SGPT.TestCurve.GlobalSkodaGauge
import SGPT.Okounkov.ValGenBook
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison

/-!
# Multiplier conditions through one atlas, and products of sections across line bundles

Lane POB-VALGEN2, blueprint `claude-val-gen2.tex`. Source: chapter *The theory of Okounkov
bodies*, Section *Algebraic partial Okounkov bodies* (`sec:PoB`), for an arbitrary valuation
`ν : ℂ(X)^× → ℤⁿ`.

The condition `s ∈ H⁰(X, L^k ⊗ 𝔞)` (`SGPT.Okounkov.IsIdealSection`) quantifies over *all* local
frames of `L`. The proofs of `prop:suba` and `prop:res` multiply sections of different line
bundles (`L ⊗ L'`, `L^a`), whose frames are not all products, resp. powers, of frames of the
factors. This file shows that for an ideal sheaf `𝔞` whose membership is a germ property and
which absorbs holomorphic multiples (`IsGermLocalIdeal`; multiplier ideals `𝓘(cφ)` and the ideals
`𝓘_∞(φ)` are such), the condition may be checked in the frames of **one** atlas
(`isIdealSection_iff_atlas`): two frames differ by a holomorphic unit on their overlap
(`SGPT.TestCurve.GlobalSkoda.sectionFrameCoefficient_transition`).

## Main results

* `isIdealSection_iff_atlas`, `isGermLocalIdeal_multiplierIdeal`, `isGermLocalIdeal_inftyIdeal`.
* `isInftySection_tensorPowerSectionProduct`: `s ∈ H⁰(L^k ⊗ 𝓘_∞(kφ))`,
  `t ∈ H⁰(N^k ⊗ 𝓘_∞(kψ))` give `s t ∈ H⁰((L ⊗ N)^k ⊗ 𝓘_∞(k(φ + ψ)))`; hence
  `inftySectionSet_add_mem_tensor`: `Γ^∞(θ, φ)_k + Γ^∞(θ', ψ)_k ⊆ Γ^∞(θ + θ', φ + ψ)_k`.
* `isIdealSection_tensorPowerMulIso_iff`: under `L^{rm} ≅ (L^r)^m`, `s ∈ H⁰(L^{rm} ⊗ 𝔞)` iff its
  image lies in `H⁰((L^r)^m ⊗ 𝔞)`; with `𝓘(m · rφ) = 𝓘(rm φ)`
  (`multiplierIdeal_natCast_mul`), `mem_multiplierSectionSet_tensorPower_iff`:
  `(x, m) ∈ Γ(L^r, rφ) ↔ (x, rm) ∈ Γ(L, φ)` (the Veronese description used in `prop:res`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.AlgebraicValuation
open scoped Topology

/-! ### Ideal sheaves of germs -/

section Germs

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- An ideal sheaf of holomorphic germs whose membership is a germ property and which absorbs
holomorphic multiples (a genuine ideal sheaf of `𝒪_M`). -/
def IsGermLocalIdeal (𝔞 : GermIdeal n M) : Prop :=
  (∀ (x : M) (g h : M → ℂ), 𝔞.mem x g → g =ᶠ[𝓝 x] h → 𝔞.mem x h) ∧
    ∀ (x : M) (g h : M → ℂ), 𝔞.mem x g → HolomorphicAt n h x → 𝔞.mem x (fun y => h y * g y)

variable [IsComplexManifold n M]

/-- Multiplier ideals `𝓘(cφ)` are ideal sheaves. -/
theorem isGermLocalIdeal_multiplierIdeal (c : ℝ) (φ : M → EReal) :
    IsGermLocalIdeal (multiplierIdeal (n := n) c φ) :=
  ⟨fun _ _ _ hg h => MultiplierIdealProductComparison.mem_multiplierIdeal_congr hg h,
    fun _ _ _ hg hh => MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul hh hg⟩

/-- The ideals `𝓘_∞(φ)` (source `def:Iinfty`) are ideal sheaves. -/
theorem isGermLocalIdeal_inftyIdeal (φ : M → EReal) :
    IsGermLocalIdeal (SGPT.PSH.inftyIdeal (n := n) φ) := by
  refine ⟨fun x g h hg hgh => (SGPT.PSH.inftyIdeal_mem_congr hgh).mp hg, ?_⟩
  intro x g h hg hh
  have h0 := SGPT.Okounkov.ValGen.mem_inftyIdeal_zero hh
  have h1 := SGPT.Okounkov.OkoNS.inftyIdeal_mul_mem_add h0 hg
  have hfun : (fun y => (0 : EReal) + φ y) = φ := funext fun y => zero_add _
  rwa [hfun] at h1

end Germs

/-! ### One atlas suffices -/

section Atlas

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance valGen2AtlasTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGen2AtlasCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- Near a point of the overlap of two frames `α, β` of `L`, the coefficient of a section of
`L^k` in `β^k` is the `k`-th power of the (holomorphic, nonvanishing) transition times the
coefficient in `α^k`. -/
theorem sectionFrameCoefficient_eventuallyEq_transition {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (k : ℕ)
    (s : bundlePowerGlobalSections L k) {p : SchemeComplexPoint f}
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    sectionFrameCoefficient f n E β k s =ᶠ[𝓝 p]
      fun q => schemeFrameTransition f n E α β q ^ k * sectionFrameCoefficient f n E α k s q := by
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' ((U ⊓ V : X.Opens) : Set X)) :=
    (U ⊓ V).isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hO.mem_nhds ⟨hpU, hpV⟩] with q hq
  exact SGPT.TestCurve.GlobalSkoda.sectionFrameCoefficient_transition α β k s hq.1 hq.2

/-- Powers of a frame transition are holomorphic on the overlap. -/
theorem schemeFrameTransition_pow_holomorphicAt {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (k : ℕ) {p : SchemeComplexPoint f}
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    HolomorphicAt n (fun q => schemeFrameTransition f n E α β q ^ k) p := by
  induction k with
  | zero => simpa only [pow_zero] using holomorphicAt_const (n := n) (1 : ℂ)
  | succ k ih =>
    simpa only [pow_succ] using
      ih.mul (schemeFrameTransition_holomorphicAt f n E α β p hpU hpV)

/-- **The multiplier condition through one atlas.** For an ideal sheaf `𝔞` of germs,
`s ∈ H⁰(X, L^k ⊗ 𝔞)` (a condition on the coefficients of `s` in *all* local frames of `L`)
holds as soon as it holds in the frames of one atlas of `L`. -/
theorem isIdealSection_of_atlas {𝔞 : GermIdeal n (SchemeComplexPoint f)}
    (h𝔞 : IsGermLocalIdeal 𝔞) {L : X.Modules} (a : LineBundleAtlas L) {k : ℕ}
    {s : bundlePowerGlobalSections L k}
    (hs : ∀ (i : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens i →
      𝔞.mem p (sectionFrameCoefficient f n E (a.frame i) k s)) :
    IsIdealSection f n E 𝔞 k s := by
  intro U α p hp
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f p)
  have h1 := h𝔞.2 p _ _ (hs i p hi)
    (schemeFrameTransition_pow_holomorphicAt f n E (a.frame i) α k hi hp)
  exact h𝔞.1 p _ _ h1
    (sectionFrameCoefficient_eventuallyEq_transition f n E (a.frame i) α k s hi hp).symm

/-- `isIdealSection_of_atlas` as an equivalence. -/
theorem isIdealSection_iff_atlas {𝔞 : GermIdeal n (SchemeComplexPoint f)}
    (h𝔞 : IsGermLocalIdeal 𝔞) {L : X.Modules} (a : LineBundleAtlas L) {k : ℕ}
    (s : bundlePowerGlobalSections L k) :
    IsIdealSection f n E 𝔞 k s ↔
      ∀ (i : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens i →
        𝔞.mem p (sectionFrameCoefficient f n E (a.frame i) k s) :=
  ⟨fun hs i p hp => hs _ (a.frame i) p hp, isIdealSection_of_atlas f n E h𝔞 a⟩

end Atlas

/-! ### Products of sections of two line bundles -/

section Tensor

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance valGen2TensorTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGen2TensorCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance valGen2TensorManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {L N : X.Modules}

/-- In the frame `(e ⊗ f)^k` of `(L ⊗ N)^k`, the regular coefficient of a product of global
sections is the product of the regular coefficients. -/
theorem algCoef_tensorPowerSectionProduct (a : LineBundleAtlas L) (b : LineBundleAtlas N)
    (k : ℕ) (ij : a.I × b.I) (s : bundlePowerGlobalSections L k)
    (t : bundlePowerGlobalSections N k) :
    (((pairwiseTensorAtlas a b).frame ij).tensorPower k).coefficients (𝟙 _)
        ((bundleTensorPower (bundleTensor L N) k).val.map (homOfLE le_top).op
          (tensorPowerSectionProduct a b k s t)) =
      ((leftRestrictedFrame a b ij).tensorPower k).coefficients (𝟙 _)
          ((bundleTensorPower L k).val.map (homOfLE le_top).op s) *
        ((rightRestrictedFrame a b ij).tensorPower k).coefficients (𝟙 _)
          ((bundleTensorPower N k).val.map (homOfLE le_top).op t) := by
  let U : X.Opens := a.opens ij.1 ⊓ b.opens ij.2
  let Ψ := tensorPowerTensorIso a b k
  have hn := PresheafOfModules.naturality_apply Ψ.inv.val (homOfLE (le_top : U ≤ ⊤)).op
    (tensorSection (bundleTensorPower L k) (bundleTensorPower N k) ⊤ s t)
  change Ψ.inv.val.app (op U)
      ((bundleTensor (bundleTensorPower L k) (bundleTensorPower N k)).val.map (homOfLE le_top).op
        (tensorSection (bundleTensorPower L k) (bundleTensorPower N k) ⊤ s t)) =
    (bundleTensorPower (bundleTensor L N) k).val.map (homOfLE le_top).op
      (Ψ.inv.val.app (op ⊤) (tensorSection (bundleTensorPower L k) (bundleTensorPower N k) ⊤ s t))
    at hn
  change (((leftRestrictedFrame a b ij).tensor (rightRestrictedFrame a b ij)).tensorPower k).coefficients
      (𝟙 U) ((bundleTensorPower (bundleTensor L N) k).val.map (homOfLE le_top).op
        (Ψ.inv.val.app (op ⊤)
          (tensorSection (bundleTensorPower L k) (bundleTensorPower N k) ⊤ s t))) = _
  rw [← hn, tensorSection_restrict]
  exact tensorPowerTensorIso_inv_coefficients a b k ij (𝟙 U) _ _

/-- The analytic coefficient of a product of sections in a frame of the pairwise atlas. -/
theorem sectionFrameCoefficient_tensorPowerSectionProduct (a : LineBundleAtlas L)
    (b : LineBundleAtlas N) (k : ℕ) (ij : a.I × b.I) (s : bundlePowerGlobalSections L k)
    (t : bundlePowerGlobalSections N k) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ (pairwiseTensorAtlas a b).opens ij) :
    sectionFrameCoefficient f n E ((pairwiseTensorAtlas a b).frame ij) k
        (tensorPowerSectionProduct a b k s t) p =
      sectionFrameCoefficient f n E (leftRestrictedFrame a b ij) k s p *
        sectionFrameCoefficient f n E (rightRestrictedFrame a b ij) k t p := by
  unfold sectionFrameCoefficient
  rw [algCoef_tensorPowerSectionProduct a b k ij s t]
  exact schemeOpenRegularFunction_mul f n E _ _ _ hp

/-- `k (φ + ψ) = k φ + k ψ` in `EReal` for natural `k`. -/
theorem ereal_natCast_mul_add (k : ℕ) (x y : EReal) :
    (k : EReal) * (x + y) = (k : EReal) * x + (k : EReal) * y := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcoe : (k : EReal) = ((k : ℝ) : EReal) := rfl
  rw [hcoe]
  induction x using EReal.rec with
  | bot =>
    rw [EReal.bot_add, EReal.coe_mul_bot_of_pos hkR, EReal.bot_add]
  | top =>
    induction y using EReal.rec with
    | bot => rw [EReal.add_bot, EReal.coe_mul_bot_of_pos hkR, EReal.add_bot]
    | top => rw [EReal.top_add_top, EReal.coe_mul_top_of_pos hkR, EReal.top_add_top]
    | coe y =>
      rw [EReal.top_add_coe, EReal.coe_mul_top_of_pos hkR, ← EReal.coe_mul, EReal.top_add_coe]
  | coe x =>
    induction y using EReal.rec with
    | bot => rw [EReal.add_bot, EReal.coe_mul_bot_of_pos hkR, EReal.add_bot]
    | top =>
      rw [EReal.coe_add_top, EReal.coe_mul_top_of_pos hkR, ← EReal.coe_mul, EReal.coe_add_top]
    | coe y =>
      rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        mul_add]

/-- **Products of `𝓘_∞` sections of two line bundles**: `s ∈ H⁰(L^k ⊗ 𝓘_∞(kφ))` and
`t ∈ H⁰(N^k ⊗ 𝓘_∞(kψ))` give `s t ∈ H⁰((L ⊗ N)^k ⊗ 𝓘_∞(k(φ + ψ)))`. -/
theorem isInftySection_tensorPowerSectionProduct (a : LineBundleAtlas L) (b : LineBundleAtlas N)
    {φ ψ : SchemeComplexPoint f → EReal} {k : ℕ} {s : bundlePowerGlobalSections L k}
    {t : bundlePowerGlobalSections N k} (hs : IsInftySection f n E φ k s)
    (ht : IsInftySection f n E ψ k t) :
    IsInftySection f n E (fun x => φ x + ψ x) k (tensorPowerSectionProduct a b k s t) := by
  let := E.isSeparated
  let := E.quasiCompact
  unfold IsInftySection at hs ht ⊢
  refine isIdealSection_of_atlas f n E (isGermLocalIdeal_inftyIdeal _) (pairwiseTensorAtlas a b)
    fun ij p hp => ?_
  have h1 := hs _ (leftRestrictedFrame a b ij) p hp
  have h2 := ht _ (rightRestrictedFrame a b ij) p hp
  have h3 := SGPT.Okounkov.OkoNS.inftyIdeal_mul_mem_add h1 h2
  have hfun : (fun y => (k : EReal) * φ y + (k : EReal) * ψ y) =
      fun y => (k : EReal) * (φ y + ψ y) :=
    funext fun y => (ereal_natCast_mul_add k (φ y) (ψ y)).symm
  rw [hfun] at h3
  refine (SGPT.PSH.inftyIdeal_mem_congr ?_).mp h3
  have hO : IsOpen (schemeComplexPointImage f ⁻¹'
      (((pairwiseTensorAtlas a b).opens ij : X.Opens) : Set X)) :=
    ((pairwiseTensorAtlas a b).opens ij).isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hO.mem_nhds hp] with q hq
  exact (sectionFrameCoefficient_tensorPowerSectionProduct f n E a b k ij s t hq).symm

variable (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X}

/-- **Source `prop:suba`, the product step**: for the valuation `v` (values at a point `c` with
`v ≥ 0` there, e.g. the centre), `Γ^∞(θ, φ)_k + Γ^∞(θ', ψ)_k ⊆ Γ^∞(θ + θ', φ + ψ)_k`, the last
for any atlas `d` of `L ⊗ N`. -/
theorem inftySectionSet_add_mem_tensor (hc : IsNonnegAt v c)
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (d : LineBundleAtlas (bundleTensor L N))
    {φ ψ : SchemeComplexPoint f → EReal} (x y : Fin n → ℤ) (k : ℤ)
    (hx : (x, k) ∈ AlgebraicValuation.inftySectionSet f n E v c a φ)
    (hy : (y, k) ∈ AlgebraicValuation.inftySectionSet f n E v c b ψ) :
    (x + y, k) ∈ AlgebraicValuation.inftySectionSet f n E v c d (fun z => φ z + ψ z) := by
  obtain ⟨m, s, hs, hsI, hz⟩ := hx
  obtain ⟨m', t, ht, htI, hz'⟩ := hy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
  obtain ⟨rfl, hmm⟩ := Prod.mk.inj hz'
  have hm : m' = m := by exact_mod_cast hmm.symm
  subst hm
  have hv := sectionValue_tensorPowerSectionProduct hc a b d m' s t
  have hst : tensorPowerSectionProduct a b m' s t ≠ 0 := by
    intro h0
    rw [h0, (sectionValue_eq_top_iff c d m' 0).mpr rfl] at hv
    exact WithTop.add_ne_top.mpr ⟨(sectionValue_eq_top_iff c a m' s).not.mpr hs,
      (sectionValue_eq_top_iff c b m' t).not.mpr ht⟩ hv.symm
  refine ⟨m', tensorPowerSectionProduct a b m' s t, hst,
    isInftySection_tensorPowerSectionProduct f n E a b hsI htI, ?_⟩
  rw [sectionValue_eq_vector c d m' _ hst, sectionValue_eq_vector c a m' s hs,
    sectionValue_eq_vector c b m' t ht, ← WithTop.coe_add, ← toLex_add] at hv
  rw [toLex.injective (WithTop.coe_injective hv)]

end Tensor

/-! ### Tensor powers: `Γ(L^r, rφ)` is the Veronese subset of `Γ(L, φ)` -/

section Power

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance valGen2PowerTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGen2PowerCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable {L : X.Modules}

/-- Under `L^{rm} ≅ (L^r)^m`, the coefficient of the image in `(α^r)^m` is the coefficient in
`α^{rm}`, for every frame `α` of `L`. -/
theorem sectionFrameCoefficient_tensorPowerMulIso (a : LineBundleAtlas L) (r m : ℕ) {U : X.Opens}
    (α : LocalBundleFrame L U) (s : bundlePowerGlobalSections L (r * m)) :
    sectionFrameCoefficient f n E (α.tensorPower r) m
        ((nativeLineTensorPowerMulIso a r m).hom.val.app (op ⊤) s) =
      sectionFrameCoefficient f n E α (r * m) s := by
  unfold sectionFrameCoefficient
  congr 1
  have hn := PresheafOfModules.naturality_apply (nativeLineTensorPowerMulIso a r m).hom.val
    (homOfLE (le_top : U ≤ ⊤)).op s
  change (nativeLineTensorPowerMulIso a r m).hom.val.app (op U)
      ((bundleTensorPower L (r * m)).val.map (homOfLE le_top).op s) =
    (bundleTensorPower (bundleTensorPower L r) m).val.map (homOfLE le_top).op
      ((nativeLineTensorPowerMulIso a r m).hom.val.app (op ⊤) s) at hn
  rw [← hn]
  exact nativeLineTensorPowerMulIso_anyFrame a r m α (𝟙 U) _

/-- **Frame compatibility between `L^r` and `L`**: for an ideal sheaf `𝔞` of germs,
`s ∈ H⁰(X, L^{rm} ⊗ 𝔞)` iff its image under `L^{rm} ≅ (L^r)^m` lies in `H⁰(X, (L^r)^m ⊗ 𝔞)`
(the latter condition ranges over all frames of `L^r`). -/
theorem isIdealSection_tensorPowerMulIso_iff {𝔞 : GermIdeal n (SchemeComplexPoint f)}
    (h𝔞 : IsGermLocalIdeal 𝔞) (a : LineBundleAtlas L) (r m : ℕ)
    (s : bundlePowerGlobalSections L (r * m)) :
    IsIdealSection f n E 𝔞 m ((nativeLineTensorPowerMulIso a r m).hom.val.app (op ⊤) s) ↔
      IsIdealSection f n E 𝔞 (r * m) s := by
  constructor
  · intro h U α p hp
    rw [← sectionFrameCoefficient_tensorPowerMulIso f n E a r m α s]
    exact h U (α.tensorPower r) p hp
  · intro h
    refine isIdealSection_of_atlas f n E h𝔞 (a.tensorPower r) fun i p hp => ?_
    change 𝔞.mem p (sectionFrameCoefficient f n E ((a.frame i).tensorPower r) m _)
    rw [sectionFrameCoefficient_tensorPowerMulIso f n E a r m (a.frame i) s]
    exact h _ (a.frame i) p hp

variable [IsSeparated f] [QuasiCompact f]

local instance valGen2PowerManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- `𝓘(m · rφ) = 𝓘((rm) φ)`: multiplier ideals only see the product of the exponent and the
weight. -/
theorem multiplierIdeal_natCast_mul (φ : SchemeComplexPoint f → EReal) {r m : ℕ} (hr : 0 < r)
    (hm : 0 < m) :
    multiplierIdeal (n := n) (m : ℝ) (fun x => (r : EReal) * φ x) =
      multiplierIdeal (n := n) ((r * m : ℕ) : ℝ) φ := by
  ext p g
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff
    (w := chartFunction φ (complexChartAt (n := n) p)) (μ := MeasureTheory.volume) hmR hrR
    (f := fun z => g ((complexChartAt (n := n) p).val.symm z))
    (z := (complexChartAt (n := n) p).val p)
  have hc : ((r * m : ℕ) : ℝ) = (m : ℝ) * r := by push_cast; ring
  change (HolomorphicAt n g p ∧ MultiplierIntegrableAt _ _ _ _ _) ↔
    (HolomorphicAt n g p ∧ MultiplierIntegrableAt _ _ _ _ _)
  rw [hc]
  exact and_congr_right fun _ => h

variable (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X}

/-- **`Γ(L^r, rφ)` is the Veronese subset of `Γ(L, φ)`** (the step of source `prop:res` reducing
it to the line bundle `L`): for every atlas `b` of `L^r`, `(x, m) ∈ Γ(L^r, rφ)` iff
`(x, rm) ∈ Γ(L, φ)`, for the valuation `v` at a point `c` where `v ≥ 0`. -/
theorem mem_multiplierSectionSet_tensorPower_iff (hc : IsNonnegAt v c) (a : LineBundleAtlas L)
    {r : ℕ} (hr : 0 < r) (b : LineBundleAtlas (bundleTensorPower L r))
    (φ : SchemeComplexPoint f → EReal) (x : Fin n → ℤ) (k : ℤ) :
    (x, k) ∈ AlgebraicValuation.multiplierSectionSet f n E v c b (fun z => (r : EReal) * φ z) ↔
      (x, (r : ℤ) * k) ∈ AlgebraicValuation.multiplierSectionSet f n E v c a φ := by
  -- the condition on a section of `(L^r)^m` and on its preimage in `L^{rm}`
  have key : ∀ (m : ℕ) (s : bundlePowerGlobalSections L (r * m)),
      IsMultiplierSection f n E (fun z => (r : EReal) * φ z) m
          ((nativeLineTensorPowerMulIso a r m).hom.val.app (op ⊤) s) ↔
        IsMultiplierSection f n E φ (r * m) s := by
    intro m s
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨fun _ => Or.inl (by simp), fun _ => Or.inl rfl⟩
    have hrm : r * m ≠ 0 := Nat.mul_ne_zero hr.ne' hm.ne'
    unfold IsMultiplierSection
    rw [or_iff_right hm.ne', or_iff_right hrm, multiplierIdeal_natCast_mul f n φ hr hm]
    exact isIdealSection_tensorPowerMulIso_iff f n E (isGermLocalIdeal_multiplierIdeal _ _) a r m s
  have hvals : ∀ (m : ℕ) (s : bundlePowerGlobalSections L (r * m)) (hs : s ≠ 0)
      (hs' : (nativeLineTensorPowerMulIso a r m).hom.val.app (op ⊤) s ≠ 0),
      sectionVector v c b m _ hs' = sectionVector v c a (r * m) s hs := by
    intro m s hs hs'
    refine sectionVector_eq_of_value_eq c c _ _ _ _ _ _ hs' hs ?_
    rw [sectionValue_atlas_independent hc b (a.tensorPower r)]
    exact sectionValue_tensorPowerMulIso hc a r m s
  constructor
  · rintro ⟨m, s', hs', hP, hz⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
    let Φ := nativeLineTensorPowerMulIso a r m
    let s := Φ.inv.val.app (op ⊤) s'
    have hss : Φ.hom.val.app (op ⊤) s = s' :=
      congrArg (fun α => α.val.app (op ⊤) s') Φ.inv_hom_id
    have hs : s ≠ 0 := by
      intro h0
      apply hs'
      rw [← hss, h0, map_zero]
    have hP' : IsMultiplierSection f n E (fun z => (r : EReal) * φ z) m
        (Φ.hom.val.app (op ⊤) s) := by rw [hss]; exact hP
    refine ⟨r * m, s, hs, (key m s).mp hP', ?_⟩
    have hv := hvals m s hs (by rw [hss]; exact hs')
    have hcongr : sectionVector v c b m s' hs' =
        sectionVector v c b m (Φ.hom.val.app (op ⊤) s) (by rw [hss]; exact hs') :=
      sectionVector_congr c b m hs' _ hss.symm
    rw [hcongr, hv]
    push_cast
    rfl
  · rintro ⟨m', s, hs, hP, hz⟩
    obtain ⟨hx, hk⟩ := Prod.mk.inj hz
    have hk0 : 0 ≤ k := by
      have : (0 : ℤ) ≤ (r : ℤ) * k := by rw [hk]; exact Int.natCast_nonneg _
      have hr' : (0 : ℤ) < r := by exact_mod_cast hr
      nlinarith
    lift k to ℕ using hk0
    have hm' : m' = r * k := by exact_mod_cast hk.symm
    subst hm' hx
    let Φ := nativeLineTensorPowerMulIso a r k
    have hΦs : Φ.hom.val.app (op ⊤) s ≠ 0 := by
      intro h0
      apply hs
      have hh := congrArg (fun α => α.val.app (op ⊤) s) Φ.hom_inv_id
      change Φ.inv.val.app (op ⊤) (Φ.hom.val.app (op ⊤) s) = s at hh
      rw [← hh, h0, map_zero]
    refine ⟨k, Φ.hom.val.app (op ⊤) s, hΦs, (key k s).mpr hP, ?_⟩
    rw [hvals k s hs hΦs]

end Power

end SGPT.Okounkov.ValGen2

import SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
import SGPT.Foundations.Analysis.Pending.SubmanifoldRestrictLe
import SGPT.Foundations.Analysis.Pending.RestrictedIdealExtension
import SGPT.Foundations.Analysis.Pending.GermIdealTotalTransform
import SGPT.Foundations.Analysis.Pending.IdealComparisonResidual
import SGPT.Foundations.Analysis.Pending.CoherentIdealWeight

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Analytic singularity types and ideal sheaves on a closed submanifold: restriction and lift

Source: Copy-4, `sec:positive-current`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1398-1712`): the
restricted approximants `φ_q = Φ_q|_V` have analytic singularities of type
`(q⁻¹, 𝔅̄_q)` with `𝔅̄_q = Res_V 𝓘(qV_θ)`, and the end of the section passes from the
coherent ideal `𝔅_ℓ = 𝓘_V(ℓφ_K)` **of `𝒪_V`** to a coherent ambient ideal `𝔅` with
`Res_V 𝔅 = 𝔅_ℓ` and a weight `ψ_𝔅` on `X` of type `(1, 𝔅)` (the input
`Copy4TraceInputReduction.PositiveCurrentInput` asks for exactly these). Here `V` is any
closed complex submanifold `W` of dimension `k`, made a complex manifold by
`Pending.SubmanifoldChartedSpace` (flattening charts).

* `hasAnalyticSingularitiesOfType_comp` — along a holomorphic map `f`, a function of type
  `(c, 𝔞)` pulls back to one of type `(c, 𝔞 𝒪_Z)`; for `f` the inclusion of `W` this is the
  restriction `φ|_W` of type `(c, Res_W 𝔞)` (`Res_W = SubmanifoldIdealRestriction.restrictIdeal`).
* `flatExtend`, `exists_holomorphicAt_extension` — every holomorphic germ on `W` is the
  restriction of an ambient holomorphic germ: in a flattening chart `Φ` it is
  `y ↦ g(Φ⁻¹(pr_k Φ(y)))`. No weight and no `L²` estimate are involved (the weighted version
  is Ohsawa–Takegoshi, `Pending.RestrictionOhsawaTakegoshi`, TN-CLASSICAL).
* `restrictLe_of_restrictIdeal_le` — the converse of
  `SubmanifoldRestrictLe.restrictIdeal_le_of_restrictLe`: an inclusion of restricted ideals
  **on the manifold `W`** gives the ambient restricted inclusion `RestrictLe W` in which every
  Copy-4 inclusion "on `V`" is stated. The coefficients are lifted by the germ extension.
* `liftIdeal` — the ambient lift `𝔟̂ = {g : g|_W ∈ 𝔟}` of an ideal `𝔟` of `𝒪_W` (all holomorphic
  germs off `W`). For coherent `𝔟`: `isCoherent_liftIdeal` (generators: the flattening extensions
  of generators of `𝔟`, together with generators of `𝓘_W`), `restrictIdeal_liftIdeal`
  (`Res_W 𝔟̂ = 𝔟`), `mem_zeroLocus_liftIdeal_iff` (`Z(𝔟̂) ∩ W = Z(𝔟)`).
* `exists_liftIdeal_weight`, `sameSingularityTypeOn_inv_mul_liftWeight` — on a compact `X`, a
  weight `ψ` of type `(1, 𝔟̂)` restricts to a weight of type `(1, 𝔟)` on `W`, and any `φ` of type
  `(ℓ⁻¹, 𝔟)` on `W` has the singularities of `ℓ⁻¹ ψ|_W` — the last clause of
  `PositiveCurrentInput`.
* `restrictLe_liftIdeal_mul_idealPow` — the ideal clause of `PositiveCurrentInput` for
  `𝔅 = 𝔟̂` reduces to an inclusion of ideals on `W`: `𝔟 · (Res_W 𝔄)^p ⊆ Res_W 𝔠` implies
  `RestrictLe W (𝔟̂ · 𝔄^p) 𝔠`.

Programme `TN.2.3.PCI`, piece C2 of `scratch/tn23-envelopes-qea-plan-0117.md` §5.3. Sorry-free;
no compactness, connectedness or Kähler hypothesis except where stated.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction

noncomputable section

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.GlobalAnalyticSingularities
  FirstPass.BlowupSequences FirstPass.RegularLocusDense SubmanifoldChartedSpace SubmanifoldIdealRestriction
  RestrictedIdealWeight RestrictedIdealExtension RelativePrincipalizationSpan
  GermIdealPullbackCalculus GermIdealTotalTransform IdealWeightPowers

/-! ### Analytic singularity types pull back along holomorphic maps -/

section Pullback

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
  [IsComplexManifold m Z]

/-- **A function of type `(c, 𝔞)` pulls back to one of type `(c, 𝔞 𝒪_Z)`** along a holomorphic
map: the pulled-back generators present the pulled-back ideal
(`GermIdealPullbackCalculus.isCoherent_pullback`) and `log ∑|gᵢ ∘ f|² = (log ∑|gᵢ|²) ∘ f`. No
nondegeneracy is needed: if the generators vanish identically on the image, both sides are
`-∞` there. -/
theorem hasAnalyticSingularitiesOfType_comp {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {φ : M → EReal} {c : ℚ} {𝔞 : GermIdeal n M}
    (hφ : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) :
    HasAnalyticSingularitiesOfType (n := m) (φ ∘ f) c (GermIdeal.pullback (m := m) f 𝔞) := by
  obtain ⟨hc, hcoh, hpres⟩ := hφ
  refine ⟨hc, isCoherent_pullback hf hcoh, fun y => ?_⟩
  obtain ⟨U, hU, hxU, N, g, hgdiff, hgiff, R, C, hRb, hφeq⟩ := hpres (f y)
  have hfat : ∀ {z : Z}, ∀ᶠ z' in 𝓝 z,
      ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z' :=
    fun {_} => Eventually.of_forall fun z => hf.contMDiffAt
  have hghol : ∀ (i : Fin N), ∀ x ∈ U, HolomorphicAt n (g i) x := fun i x hx =>
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hgdiff i) hx
  refine ⟨f ⁻¹' U, hU.preimage hf.continuous, hxU, N, fun i => g i ∘ f, ?_, ?_,
    R ∘ f, C, fun z hz => hRb (f z) hz, fun z hz => hφeq (f z) hz⟩
  · intro i z hz
    exact ((hghol i (f z) hz).comp_contMDiff hfat).mdifferentiableAt.mdifferentiableWithinAt
  · intro z hz h
    constructor
    · intro hh
      refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hh)
      rintro t ⟨a, ham, rfl⟩
      refine IsInSpanAt.mono ?_ (isInSpanAt_comp hf ((hgiff (f z) hz a).mp ham))
      rintro s' ⟨σ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · intro hh
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hh)
      rintro s' ⟨i, rfl⟩
      exact ⟨g i, (hgiff (f z) hz (g i)).mpr (InvertibleIdealQuotient.isInSpanAt_self
        ⟨i, rfl⟩ (hghol i (f z) hz)), rfl⟩

end Pullback

/-! ### Germs of coherent ideals -/

section Coherent

variable {m : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
  [IsComplexManifold m Z]

/-- Membership in a coherent ideal depends only on the germ. -/
theorem mem_of_eventuallyEq_of_isCoherent {𝔟 : GermIdeal m Z} (h𝔟 : 𝔟.IsCoherent) {z : Z}
    {g g' : Z → ℂ} (hg : 𝔟.mem z g) (hgg' : g =ᶠ[𝓝 z] g') : 𝔟.mem z g' := by
  have hhol := GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg
  refine mem_of_isInSpanAt_mem h𝔟 (isInSpanAt_of_eq_mul hg (hhol.congr hgg')
    (holomorphicAt_const 1) ?_)
  filter_upwards [hgg'] with y hy
  rw [← hy, one_mul]

end Coherent

/-! ### Extending holomorphic germs off a closed submanifold -/

section Extension

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

/-- The flattened coordinate `pr_k (Φ (e y))` of an **ambient** point `y`. -/
def flatCoordAmb (F : FlatData n k X W) (y : X) : ComplexModel k :=
  coordinateProjection n k (F.flat (F.amb.val y))

/-- **The flattening extension** of a function on `W`: `y ↦ g(Φ⁻¹(pr_k Φ(y)))`, i.e. `g` made
constant along the normal coordinates of the flattening chart `F`. -/
def flatExtend (F : FlatData n k X W) (g : W → ℂ) : X → ℂ :=
  fun y => g (F.invPoint (flatCoordAmb F y))

theorem flatCoordAmb_val (F : FlatData n k X W) (p : W) :
    flatCoordAmb F p.1 = F.toCoord p := rfl

theorem invPoint_flatCoordAmb (F : FlatData n k X W) (hk : k ≤ n) {p : W}
    (hp : p.1 ∈ F.ambSource) : F.invPoint (flatCoordAmb F p.1) = p :=
  (F.chart hk).left_inv (x := p) hp

/-- On the chart domain the flattening extension restricts to the function itself. -/
theorem flatExtend_val (F : FlatData n k X W) (hk : k ≤ n) (g : W → ℂ) {p : W}
    (hp : p.1 ∈ F.ambSource) : flatExtend F g p.1 = g p := by
  simp only [flatExtend]
  rw [invPoint_flatCoordAmb F hk hp]

theorem continuousOn_flatCoordAmb (F : FlatData n k X W) :
    ContinuousOn (flatCoordAmb F) F.ambSource :=
  (coordinateProjection n k).continuous.comp_continuousOn
    (F.flat.continuousOn.comp (F.amb.val.continuousOn.mono fun _ hy => hy.1) fun _ hy => hy.2)

theorem mdifferentiableAt_flatCoordAmb (F : FlatData n k X W) {y : X} (hy : y ∈ F.ambSource) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) (flatCoordAmb F) y := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) F.amb.val y :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) F.amb.property hy.1
  have h2 : DifferentiableAt ℂ F.flat (F.amb.val y) :=
    F.differentiableOn_flat.differentiableAt (F.flat.open_source.mem_nhds hy.2)
  have h3 : DifferentiableAt ℂ (fun z => coordinateProjection n k (F.flat z)) (F.amb.val y) :=
    (coordinateProjection n k).differentiableAt.comp _ h2
  exact h3.mdifferentiableAt.comp y h1

/-- `{y | y` lies in the chart domain and `Φ⁻¹(pr_k Φ(y)) ∈ U}` is open for `U` open in `W`. -/
theorem isOpen_flatPreimage (F : FlatData n k X W) {U : Set W} (hU : IsOpen U) :
    IsOpen (F.ambSource ∩ flatCoordAmb F ⁻¹' (F.coordTarget ∩ F.invPoint ⁻¹' U)) :=
  (continuousOn_flatCoordAmb F).isOpen_inter_preimage F.isOpen_ambSource
    (F.continuousOn_invPoint.isOpen_inter_preimage F.isOpen_coordTarget hU)

variable (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

include hk hW in
/-- **The flattening extension is holomorphic** wherever the function is holomorphic at the
corresponding point of `W`. -/
theorem holomorphicAt_flatExtend :
    letI := chartedSpace hk hW
    ∀ (F : FlatData n k X W) (g : W → ℂ) {y : X}, y ∈ F.ambSource →
      flatCoordAmb F y ∈ F.coordTarget →
      HolomorphicAt k g (F.invPoint (flatCoordAmb F y)) → HolomorphicAt n (flatExtend F g) y := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro F g y hy hyt hg
  have hinv : ContinuousAt F.invPoint (flatCoordAmb F y) :=
    F.continuousOn_invPoint.continuousAt (F.isOpen_coordTarget.mem_nhds hyt)
  have hdiff : ∀ᶠ ζ in 𝓝 (flatCoordAmb F y),
      DifferentiableAt ℂ (fun ζ => g (F.invPoint ζ)) ζ := by
    filter_upwards [F.isOpen_coordTarget.mem_nhds hyt, hinv.eventually hg] with ζ hζ hgζ
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k)
        (F.chart hk).symm ζ :=
      mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel k))
        (SubmanifoldChartedSpace.chart_mem_atlas hk hW F) hζ
    exact mdifferentiableAt_iff_differentiableAt.mp (hgζ.comp ζ h1)
  have hcont : ContinuousAt (flatCoordAmb F) y :=
    (continuousOn_flatCoordAmb F).continuousAt (F.isOpen_ambSource.mem_nhds hy)
  filter_upwards [F.isOpen_ambSource.mem_nhds hy, hcont.eventually hdiff] with y' hy' hd
  exact hd.mdifferentiableAt.comp y' (mdifferentiableAt_flatCoordAmb F hy')

include hk hW in
/-- **Every holomorphic germ on a closed submanifold is the restriction of an ambient
holomorphic germ** (the flattening extension in the preferred chart at the point). -/
theorem exists_holomorphicAt_extension :
    letI := chartedSpace hk hW
    ∀ (p : W) (g : W → ℂ), HolomorphicAt k g p →
      ∃ G : X → ℂ, HolomorphicAt n G p.1 ∧ ∀ᶠ q in 𝓝 p, G q.1 = g q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro p g hg
  set F := FlatData.ofRegularAtDim (hW p.1 p.2)
  have hp : p.1 ∈ F.ambSource := FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)
  have hpt : flatCoordAmb F p.1 ∈ F.coordTarget := F.toCoord_mem_coordTarget p hp
  have hinv : F.invPoint (flatCoordAmb F p.1) = p := invPoint_flatCoordAmb F hk hp
  refine ⟨flatExtend F g,
    holomorphicAt_flatExtend hk hW F g hp hpt (by rw [hinv]; exact hg), ?_⟩
  filter_upwards [(F.chart hk).open_source.mem_nhds (show p ∈ (F.chart hk).source from hp)]
    with q hq
  exact flatExtend_val F hk g hq

end Extension

/-! ### Eventual statements along `W` -/

section Eventually

variable {X : Type*} [TopologicalSpace X] {W : Set X}

/-- An eventual statement at `p` in the subtype is an eventual statement along `W` at `p.1`. -/
theorem eventually_nhds_val_of_eventually {p : W} {P : X → Prop}
    (h : ∀ᶠ q in 𝓝 p, P q.1) : ∀ᶠ y in 𝓝 p.1, y ∈ W → P y :=
  eventually_nhdsWithin_iff.mp ((eventually_nhds_subtype_iff W p P).mp h)

/-- The converse of `eventually_nhds_val_of_eventually`. -/
theorem eventually_of_eventually_nhds_val {p : W} {P : X → Prop}
    (h : ∀ᶠ y in 𝓝 p.1, y ∈ W → P y) : ∀ᶠ q in 𝓝 p, P q.1 :=
  (eventually_nhds_subtype_iff W p P).mpr (eventually_nhdsWithin_iff.mpr h)

end Eventually

/-! ### Ambient restricted inclusions from inclusions on `W` -/

section RestrictLe

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

include hk hW in
/-- **`Res_W 𝔞 ⊆ Res_W 𝔟` on the manifold `W` gives the ambient `RestrictLe W 𝔞 𝔟`.**  The
converse of `SubmanifoldRestrictLe.restrictIdeal_le_of_restrictLe`: a germ of `𝔞` restricts to a
combination `∑ aᵢ (bᵢ|_W)` with `aᵢ` holomorphic **on `W`**; the coefficients are extended to
ambient germs (`exists_holomorphicAt_extension`). -/
theorem restrictLe_of_restrictIdeal_le {𝔞 𝔟 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (restrictIdeal (k := k) (W := W) 𝔞).Le (restrictIdeal (k := k) (W := W) 𝔟) →
      RestrictLe W 𝔞 𝔟 := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro hle x hx g hg
  set p : W := ⟨x, hx⟩
  have hval := contMDiff_val hk hW
  have hgW : (restrictIdeal (k := k) (W := W) 𝔞).mem p (fun q : W => g q.1) :=
    (mem_restrictIdeal_iff 𝔞 p _).mpr <| isInSpanAt_of_eq_mul ⟨g, hg, rfl⟩
      (holomorphicAt_comp_val hval (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg))
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm)
  obtain ⟨-, N, s, a, hs, ha, hsum⟩ := hle p _ hgW
  choose b hb hsb using hs
  choose A hA hAa using fun i => exists_holomorphicAt_extension hk hW p (a i) (ha i)
  refine ⟨N, b, A, hb, hA, eventually_nhds_val_of_eventually (p := p)
    (P := fun y => g y = ∑ i, A i y * b i y) ?_⟩
  filter_upwards [hsum, eventually_all.mpr hAa] with q hq hq'
  show g q.1 = ∑ i, A i q.1 * b i q.1
  rw [show g q.1 = ∑ i, a i q * s i q from hq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsb i, hq' i]
  rfl

include hk hW in
/-- `RestrictLe W 𝔞 𝔟 ↔ Res_W 𝔞 ⊆ Res_W 𝔟` for coherent `𝔞`. -/
theorem restrictLe_iff_restrictIdeal_le {𝔞 𝔟 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    RestrictLe W 𝔞 𝔟 ↔
      (restrictIdeal (k := k) (W := W) 𝔞).Le (restrictIdeal (k := k) (W := W) 𝔟) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  exact ⟨SubmanifoldRestrictLe.restrictIdeal_le_of_restrictLe (contMDiff_val hk hW) h𝔞,
    restrictLe_of_restrictIdeal_le hk hW h𝔞⟩

end RestrictLe

/-! ### The ambient lift of an ideal of `𝒪_W` -/

section Lift

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable (n) in
/-- **The ambient lift `𝔟̂` of an ideal `𝔟 ⊆ 𝒪_W`**: the holomorphic germs whose restriction to
`W` lies in `𝔟` (at points off `W`, every holomorphic germ).  This is the preimage of `𝔟` under
`𝒪_X → 𝒪_W`; it contains `𝓘_W`. -/
def liftIdeal (W : Set X) [ChartedSpace (ComplexModel k) W] (𝔟 : GermIdeal k W) :
    GermIdeal n X where
  mem x g := HolomorphicAt n g x ∧ ∀ hx : x ∈ W, 𝔟.mem ⟨x, hx⟩ (fun q : W => g q.1)

variable {W : Set X} (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

include hk hW in
/-- A germ of `𝔟` is the restriction of a germ of the lift `𝔟̂`. -/
theorem exists_mem_liftIdeal :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ (𝔟 : GermIdeal k W), 𝔟.IsCoherent → ∀ (p : W) (G : W → ℂ), 𝔟.mem p G →
      ∃ Ĝ : X → ℂ, (liftIdeal n W 𝔟).mem p.1 Ĝ ∧ ∀ᶠ q in 𝓝 p, Ĝ q.1 = G q := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro 𝔟 h𝔟 p G hG
  obtain ⟨Ĝ, hĜ, hĜG⟩ := exists_holomorphicAt_extension hk hW p G
    (GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hG)
  exact ⟨Ĝ, ⟨hĜ, fun _ => mem_of_eventuallyEq_of_isCoherent h𝔟 hG
    (hĜG.mono fun _ hq => hq.symm)⟩, hĜG⟩

include hk hW in
/-- **`Res_W 𝔟̂ = 𝔟`** for a coherent ideal `𝔟` of `𝒪_W`. -/
theorem restrictIdeal_liftIdeal :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ 𝔟 : GermIdeal k W, 𝔟.IsCoherent →
      restrictIdeal (k := k) (W := W) (liftIdeal n W 𝔟) = 𝔟 := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro 𝔟 h𝔟
  ext p G
  constructor
  · intro hG
    refine mem_of_isInSpanAt_mem h𝔟 (IsInSpanAt.mono ?_ ((mem_restrictIdeal_iff _ p G).mp hG))
    rintro s ⟨a, ⟨-, ha⟩, rfl⟩
    exact ha p.2
  · intro hG
    obtain ⟨Ĝ, hĜmem, hĜG⟩ := exists_mem_liftIdeal hk hW 𝔟 h𝔟 p G hG
    refine (mem_restrictIdeal_iff _ p G).mpr <| isInSpanAt_of_eq_mul ⟨Ĝ, hĜmem, rfl⟩
      (GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hG) (holomorphicAt_const 1) ?_
    filter_upwards [hĜG] with q hq
    simp [hq]

include hk hW in
/-- **`Z(𝔟̂) ∩ W = Z(𝔟)`.** -/
theorem mem_zeroLocus_liftIdeal_iff :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ 𝔟 : GermIdeal k W, 𝔟.IsCoherent → ∀ p : W,
      p.1 ∈ (liftIdeal n W 𝔟).zeroLocus ↔ p ∈ 𝔟.zeroLocus := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro 𝔟 h𝔟 p
  constructor
  · intro hp G hG
    obtain ⟨Ĝ, hĜmem, hĜG⟩ := exists_mem_liftIdeal hk hW 𝔟 h𝔟 p G hG
    rw [← hĜG.self_of_nhds]
    exact hp Ĝ hĜmem
  · intro hp g hg
    exact hp _ (hg.2 p.2)

include hk hW in
/-- **The lift of a coherent ideal of `𝒪_W` is coherent** (`W` closed).  Off `W` it is the unit
ideal, which agrees there with `𝓘_W`.  Near a point of `W`, in the flattening chart `F` at that
point, it is generated by the flattening extensions `Sᵢ` of generators `sᵢ` of `𝔟` together with
generators `hⱼ` of `𝓘_W` (`VanishingIdealCoherent`): a germ `g` with `g|_W = ∑ aᵢ sᵢ` differs
from `∑ âᵢ Sᵢ` by a germ vanishing on `W`. -/
theorem isCoherent_liftIdeal (hWc : IsClosed W) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ 𝔟 : GermIdeal k W, 𝔟.IsCoherent → (liftIdeal n W 𝔟).IsCoherent := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro 𝔟 h𝔟 x
  have hval := contMDiff_val hk hW
  have hWsub : IsClosedSubmanifold n W := ⟨hWc, fun x hx => ⟨k, hW x hx⟩⟩
  obtain ⟨U', hU', hxU', P, h, hhdiff, hhiff⟩ :=
    VanishingIdealCoherent.isCoherent_vanishingIdeal hWsub x
  have hhhol : ∀ j, ∀ y ∈ U', HolomorphicAt n (h j) y := fun j y hy =>
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU' (hhdiff j) hy
  by_cases hx : x ∈ W
  swap
  · -- off `W` the lift is the unit ideal, i.e. `𝓘_W`
    refine ⟨U' ∩ Wᶜ, hU'.inter hWc.isOpen_compl, ⟨hxU', hx⟩, P, h,
      fun j => (hhdiff j).mono inter_subset_left, ?_⟩
    intro y hy g
    constructor
    · rintro ⟨hg, -⟩
      refine (hhiff y hy.1 g).mp ⟨hg, ?_⟩
      filter_upwards [hWc.isOpen_compl.mem_nhds hy.2] with z hz hzW
      exact absurd hzW hz
    · intro hg
      exact ⟨hg.holomorphicAt, fun hyW => absurd hyW hy.2⟩
  set p : W := ⟨x, hx⟩
  obtain ⟨UW, hUW, hpUW, N, s, hsdiff, hsiff⟩ := h𝔟 p
  have hshol : ∀ i, ∀ q ∈ UW, HolomorphicAt k (s i) q := fun i q hq =>
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hUW (hsdiff i) hq
  set F := FlatData.ofRegularAtDim (hW x hx)
  set U : Set X := F.ambSource ∩ flatCoordAmb F ⁻¹' (F.coordTarget ∩ F.invPoint ⁻¹' UW)
    with hUdef
  have hUopen : IsOpen U := isOpen_flatPreimage F hUW
  have hxamb : x ∈ F.ambSource := FlatData.mem_ambSource_ofRegularAtDim (hW x hx)
  have hxU : x ∈ U := by
    refine ⟨hxamb, F.toCoord_mem_coordTarget p hxamb, ?_⟩
    show F.invPoint (flatCoordAmb F p.1) ∈ UW
    rw [invPoint_flatCoordAmb F hk hxamb]
    exact hpUW
  set S : Fin N → X → ℂ := fun i => flatExtend F (s i) with hSdef
  have hShol : ∀ i, ∀ y ∈ U, HolomorphicAt n (S i) y := fun i y hy =>
    holomorphicAt_flatExtend hk hW F (s i) hy.1 hy.2.1 (hshol i _ hy.2.2)
  -- points of `U ∩ W` and the local identity `Sᵢ|_W = sᵢ`
  have hUW_mem : ∀ y (hyU : y ∈ U) (hyW : y ∈ W), (⟨y, hyW⟩ : W) ∈ UW := by
    intro y hyU hyW
    have h1 : F.invPoint (flatCoordAmb F (⟨y, hyW⟩ : W).1) ∈ UW := hyU.2.2
    rwa [invPoint_flatCoordAmb F hk (p := ⟨y, hyW⟩) hyU.1] at h1
  have hSval : ∀ (q : W), q.1 ∈ F.ambSource → ∀ᶠ q' in 𝓝 q, ∀ i, S i q'.1 = s i q' := by
    intro q hq
    filter_upwards [(F.chart hk).open_source.mem_nhds (show q ∈ (F.chart hk).source from hq)]
      with q' hq' i
    exact flatExtend_val F hk (s i) hq'
  refine ⟨U ∩ U', hUopen.inter hU', ⟨hxU, hxU'⟩, N + P, sumFamily S h, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j z hz => ?_) (fun j z hz => ?_) i
    · simpa [sumFamily] using
        ((hShol j z hz.1).mdifferentiableAt).mdifferentiableWithinAt
    · simpa [sumFamily] using ((hhdiff j z hz.2).mono inter_subset_right)
  intro y hy g
  constructor
  · rintro ⟨hghol, hgW⟩
    by_cases hyW : y ∈ W
    · set q : W := ⟨y, hyW⟩
      have hqUW : q ∈ UW := hUW_mem y hy.1 hyW
      obtain ⟨-, K, t, a, ht, ha, hsum⟩ := (hsiff q hqUW _).mp (hgW hyW)
      choose σ hσ using ht
      have hqinv : F.invPoint (flatCoordAmb F y) = q := invPoint_flatCoordAmb F hk (p := q) hy.1.1
      -- lift the coefficients
      set A : Fin K → X → ℂ := fun j => flatExtend F (a j) with hAdef
      have hAhol : ∀ j, HolomorphicAt n (A j) y := fun j =>
        holomorphicAt_flatExtend hk hW F (a j) hy.1.1 hy.1.2.1 (by rw [hqinv]; exact ha j)
      set v : X → ℂ := fun z => ∑ j, A j z * S (σ j) z with hvdef
      have hvhol : HolomorphicAt n v y :=
        HolomorphicAt.sum _ fun j _ => (hAhol j).mul (hShol (σ j) y hy.1)
      have hvspan : IsInSpanAt (n := n) (· ∈ range (sumFamily S h)) y v :=
        ⟨hvhol, K, fun j => S (σ j), A,
          fun j => range_left_subset_sumFamily ⟨σ j, rfl⟩, hAhol,
          Eventually.of_forall fun _ => rfl⟩
      have hrhol : HolomorphicAt n (fun z => g z - v z) y := by
        refine HolomorphicAt.congr (hghol.add ((holomorphicAt_const (-1 : ℂ)).mul hvhol)) ?_
        filter_upwards with z
        ring
      have hrvan : (vanishingIdeal (n := n) W).mem y (fun z => g z - v z) := by
        refine ⟨hrhol, eventually_nhds_val_of_eventually (p := q)
          (P := fun z => g z - v z = 0) ?_⟩
        have hAval : ∀ᶠ q' in 𝓝 q, ∀ j, A j q'.1 = a j q' := by
          filter_upwards [(F.chart hk).open_source.mem_nhds
            (show q ∈ (F.chart hk).source from hy.1.1)] with q' hq' j
          exact flatExtend_val F hk (a j) hq'
        filter_upwards [hsum, hAval, hSval q hy.1.1] with q' h1 h2 h3
        show g q'.1 - ∑ j, A j q'.1 * S (σ j) q'.1 = 0
        rw [show g q'.1 = ∑ j, a j q' * t j q' from h1, sub_eq_zero]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h2 j, h3 (σ j), hσ j]
      have hrspan : IsInSpanAt (n := n) (· ∈ range (sumFamily S h)) y (fun z => g z - v z) :=
        IsInSpanAt.mono (fun _ hs => range_right_subset_sumFamily hs)
          ((hhiff y hy.2 _).mp hrvan)
      refine isInSpanAt_congr (IsInSpanAt.add hrspan hvspan) ?_
      filter_upwards with z
      ring
    · have hgvan : (vanishingIdeal (n := n) W).mem y g := by
        refine ⟨hghol, ?_⟩
        filter_upwards [hWc.isOpen_compl.mem_nhds hyW] with z hz hzW
        exact absurd hzW hz
      exact IsInSpanAt.mono (fun _ hs => range_right_subset_sumFamily hs)
        ((hhiff y hy.2 g).mp hgvan)
  · intro hg
    refine ⟨hg.holomorphicAt, fun hyW => ?_⟩
    set q : W := ⟨y, hyW⟩
    have hqUW : q ∈ UW := hUW_mem y hy.1 hyW
    refine (hsiff q hqUW _).mpr ?_
    refine IsInSpanAt.trans ?_ (isInSpanAt_comp (y := q) hval hg)
    rintro t ⟨a, ha, rfl⟩
    rcases mem_range_sumFamily ha with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine isInSpanAt_of_eq_mul ⟨i, rfl⟩
        (holomorphicAt_comp_val hval (hShol i y hy.1)) (holomorphicAt_const 1) ?_
      filter_upwards [hSval q hy.1.1] with q' hq'
      simp [hq' i]
    · have hjvan : (vanishingIdeal (n := n) W).mem y (h j) :=
        IdealWeightComparison.mem_of_isPresentation hU' hy.2 hhdiff hhiff j
      refine ⟨holomorphicAt_comp_val hval (hhhol j y hy.2), 0, Fin.elim0, Fin.elim0,
        fun i => i.elim0, fun i => i.elim0, ?_⟩
      filter_upwards [eventually_of_eventually_nhds_val (p := q) (P := fun z => h j z = 0)
        hjvan.2] with q' hq'
      simpa using hq'

end Lift

/-! ### Weights of the lift on a compact manifold -/

section Weight

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

include hk hW in
/-- **A weight of type `(1, 𝔟̂)` on `X` restricts to a weight of type `(1, 𝔟)` on `W`.** -/
theorem hasAnalyticSingularitiesOfType_comp_val_liftIdeal :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ (𝔟 : GermIdeal k W), 𝔟.IsCoherent → ∀ (ψ : X → EReal) (c : ℚ),
      HasAnalyticSingularitiesOfType (n := n) ψ c (liftIdeal n W 𝔟) →
      HasAnalyticSingularitiesOfType (n := k) (fun q : W => ψ q.1) c 𝔟 := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro 𝔟 h𝔟 ψ c hψ
  have h := hasAnalyticSingularitiesOfType_comp (contMDiff_val hk hW) hψ
  have heq : GermIdeal.pullback (m := k) (Subtype.val : W → X) (liftIdeal n W 𝔟) = 𝔟 :=
    restrictIdeal_liftIdeal hk hW 𝔟 h𝔟
  rw [heq] at h
  exact h

include hk hW in
/-- **The ambient weight of a coherent ideal of `𝒪_W`** (`X` compact, `W` closed): a weight `ψ`
of type `(1, 𝔟̂)` on `X` whose restriction has type `(1, 𝔟)` on `W`. -/
theorem exists_liftIdeal_weight [CompactSpace X] (hWc : IsClosed W) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ 𝔟 : GermIdeal k W, 𝔟.IsCoherent →
      ∃ ψ : X → EReal, HasAnalyticSingularitiesOfType (n := n) ψ 1 (liftIdeal n W 𝔟) ∧
        HasAnalyticSingularitiesOfType (n := k) (fun q : W => ψ q.1) 1 𝔟 := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro 𝔟 h𝔟
  obtain ⟨ψ, hψ⟩ := CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent
    (isCoherent_liftIdeal hk hW hWc 𝔟 h𝔟)
  exact ⟨ψ, hψ, hasAnalyticSingularitiesOfType_comp_val_liftIdeal hk hW 𝔟 h𝔟 ψ 1 hψ⟩

include hk hW in
/-- **`φ ~ ℓ⁻¹ ψ|_W`**: on a compact `X` with `W` closed, a function `φ` on `W` of type
`(ℓ⁻¹, 𝔟)` has the singularities of `ℓ⁻¹ ψ|_W` for any weight `ψ` of type `(1, 𝔟̂)` on `X`,
with one constant on all of `W`.  This is the last clause of
`Copy4TraceInputReduction.PositiveCurrentInput` (`φ_K ~ (mr)⁻¹ ψ_𝔅` on `V`, `ℓ = mr`). -/
theorem sameSingularityTypeOn_inv_mul_liftWeight [CompactSpace X] (hWc : IsClosed W) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ (𝔟 : GermIdeal k W), 𝔟.IsCoherent → ∀ (ψ : X → EReal) (φ : W → EReal) (ℓ : ℕ),
      0 < ℓ → HasAnalyticSingularitiesOfType (n := n) ψ 1 (liftIdeal n W 𝔟) →
      HasAnalyticSingularitiesOfType (n := k) φ ((ℓ : ℚ)⁻¹) 𝔟 →
      SameSingularityTypeOn φ (fun q : W => ((1 / (ℓ : ℝ) : ℝ) : EReal) * ψ q.1) univ := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro 𝔟 h𝔟 ψ φ ℓ hℓ hψ hφ
  have : CompactSpace W := isCompact_iff_compactSpace.mp hWc.isCompact
  have hd : (0 : ℚ) < (ℓ : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast hℓ)
  have h1 := IdealComparisonResidual.hasAnalyticSingularitiesOfType_smul hd
    (hasAnalyticSingularitiesOfType_comp_val_liftIdeal hk hW 𝔟 h𝔟 ψ 1 hψ)
  rw [mul_one] at h1
  have hcast : (((ℓ : ℚ)⁻¹ : ℚ) : ℝ) = 1 / (ℓ : ℝ) := by push_cast; ring
  rw [hcast] at h1
  exact IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hφ h1

end Weight

/-! ### The ideal clause of `PositiveCurrentInput` for a lifted ideal -/

section IdealClause

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  (hk : k ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k)

include hk hW in
/-- **`𝔟 · (Res_W 𝔄)^p ⊆ Res_W 𝔠` on `W` gives `RestrictLe W (𝔟̂ · 𝔄^p) 𝔠`.**  Restriction
is submultiplicative (`GermIdealPullbackCalculus.pullback_mul_le`, `pullback_idealPow_le`) and
`Res_W 𝔟̂ = 𝔟`; the ambient form then comes from `restrictLe_of_restrictIdeal_le`. -/
theorem restrictLe_liftIdeal_mul_idealPow (hWc : IsClosed W) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∀ (𝔟 : GermIdeal k W), 𝔟.IsCoherent → ∀ {𝔄 : GermIdeal n X}, 𝔄.IsCoherent →
      ∀ (𝔠 : GermIdeal n X) (p : ℕ),
        (𝔟.mul (idealPow (restrictIdeal (k := k) (W := W) 𝔄) p)).Le
          (restrictIdeal (k := k) (W := W) 𝔠) →
        RestrictLe W ((liftIdeal n W 𝔟).mul (idealPow 𝔄 p)) 𝔠 := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  intro 𝔟 h𝔟 𝔄 h𝔄 𝔠 p hle
  have hval := contMDiff_val hk hW
  have hlift := isCoherent_liftIdeal hk hW hWc 𝔟 h𝔟
  have hpow := isCoherent_idealPow h𝔄 p
  refine restrictLe_of_restrictIdeal_le hk hW (isCoherent_mul hlift hpow) ?_
  intro q G hG
  have h1 := pullback_mul_le hval
    (fun {_ _} hm => GermIdeal.IsCoherent.holomorphicAt_mem hlift hm)
    (fun {_ _} hm => GermIdeal.IsCoherent.holomorphicAt_mem hpow hm) q G hG
  refine hle q G (InvertibleIdealQuotient.mem_mul_iff.mpr
    (IsInSpanAt.mono ?_ (InvertibleIdealQuotient.mem_mul_iff.mp h1)))
  rintro s ⟨a, b, ha, hb, rfl⟩
  refine ⟨a, b, ?_, pullback_idealPow_le hval h𝔄 p q b hb, rfl⟩
  have heq : GermIdeal.pullback (m := k) (Subtype.val : W → X) (liftIdeal n W 𝔟) = 𝔟 :=
    restrictIdeal_liftIdeal hk hW 𝔟 h𝔟
  rw [← heq]
  exact ha

end IdealClause

end

end SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction

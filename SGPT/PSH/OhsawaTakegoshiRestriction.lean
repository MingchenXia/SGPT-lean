import SGPT.Foundations.Analysis.Pending.RestrictionOhsawaTakegoshi
import SGPT.Foundations.Analysis.Pending.VanishingIdealCoherent
import SGPT.PSH.BookRestrictionIdeal
import SGPT.PSH.BookMultiplierSections

/-!
# The Ohsawa–Takegoshi restriction theorem `𝓘(φ|_Y) ⊆ Rest_Y 𝓘(φ)` (`thm:OT`)

Source: `thm:OT` of the chapter *Plurisubharmonic functions* (Xia, *Singularities in global
pluripotential theory*): let `Y` be a connected submanifold of `X` and `φ ∈ PSH(X)` with
`φ|_Y ≢ -∞`. Then `𝓘(φ|_Y) ⊆ Rest_Y 𝓘(φ)`.

Both sides are ideal sheaves of `𝒪_Y`. `Rest_Y 𝓘(φ)` is the book's restriction ideal
(`def:restidealsheaf`, `SGPT.PSH.IdealRestriction.restStalk`): the image of `𝓘(φ)` in
`𝒪_Y = 𝒪_X/𝓘_Y`, where `Y` is the closed complex subspace defined by the ideal sheaf `𝓘_Y` of
germs vanishing on `Y` (`submanifoldSubspace`, coherent by `isCoherent_vanishingIdeal`).
`𝓘(φ|_Y)` is the multiplier ideal of the restriction on the complex manifold `↥Y` (with the
flattening complex structure of `SubmanifoldChartedSpace`), an ideal of the germ ring
`𝒪_{↥Y,y}`. The two germ rings are identified by restriction of germs: `restrictGerm` is a
surjective ring map `𝒪_{X,y} → 𝒪_{↥Y,y}` (every holomorphic germ on `Y` extends) with kernel
`𝓘_{Y,y}` (`ker_restrictGerm`), so it induces the ring isomorphism
`structureStalkEquiv : 𝒪_{X,y}/𝓘_{Y,y} ≃+* 𝒪_{↥Y,y}`.

* `multiplierIdeal_restrict_le_restStalk` — **`thm:OT`**: for every `y ∈ Y` and every `c`, the
  stalk `𝓘(c φ|_Y)_y`, transported to `𝒪_{Y,y} = 𝒪_{X,y}/𝓘_{Y,y}`, is contained in
  `(Rest_Y 𝓘(c φ))_y`. The book's statement is `c = 1` (`thm_OT`).
* `exists_extension_mem_multiplierIdeal` — the germ form: every germ of `𝓘(φ|_Y)` extends to a
  germ of `𝓘(φ)`.

The analytic input is TN's Ohsawa–Takegoshi theorem from a coordinate subspace, proved from
Hörmander's `L²` estimate (`RestrictionOhsawaTakegoshi.exists_extension_mem_multiplierIdeal`).
The hypothesis `φ|_Y ≢ -∞` of the book is not needed: it only makes `φ|_Y` a psh function on
`Y`; where `φ|_Y ≡ -∞` near `y` the stalk `𝓘(φ|_Y)_y` is zero and the inclusion is trivial.
`φ` may even be quasi-psh (`multiplierIdeal_restrict_le_restStalk_of_quasi`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.PSH.OhsawaTakegoshi

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Okounkov SGPT.PSH.IdealRestriction

universe u

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Psh functions are quasi-psh -/

/-- A psh function on a complex manifold is quasi-psh in every chart. -/
theorem manifoldQuasiPlurisubharmonic_of_manifoldPSH {φ : X → EReal}
    (hφ : ManifoldPSH (n := n) φ) : ManifoldQuasiPlurisubharmonic (n := n) φ :=
  fun e z hz => (hφ.chartPlurisubharmonic e z hz).quasiPlurisubharmonicAt

/-! ### The closed complex subspace defined by a closed submanifold -/

/-- The closed complex subspace `Y` of `X` defined by a closed complex submanifold `W`: its
defining ideal sheaf is the ideal `𝓘_W` of holomorphic germs vanishing on `W`, which is coherent
(`VanishingIdealCoherent.isCoherent_vanishingIdeal`). -/
def submanifoldSubspace {W : Set X} (hW : IsClosedSubmanifold n W) : ClosedComplexSubspace n X :=
  ⟨vanishingIdeal (n := n) W, VanishingIdealCoherent.isCoherent_vanishingIdeal hW⟩

@[simp] theorem submanifoldSubspace_ideal {W : Set X} (hW : IsClosedSubmanifold n W) :
    (submanifoldSubspace hW).ideal = vanishingIdeal (n := n) W := rfl

/-- The support of the subspace defined by a closed submanifold `W` is `W`. -/
theorem support_submanifoldSubspace {W : Set X} (hW : IsClosedSubmanifold n W) :
    (submanifoldSubspace hW).support = W := by
  ext x
  constructor
  · intro hx
    by_contra hxW
    have hmem : (vanishingIdeal (n := n) W).mem x (fun _ => (1 : ℂ)) := by
      refine ⟨holomorphicAt_const 1, ?_⟩
      filter_upwards [hW.1.isOpen_compl.mem_nhds hxW] with y hy hyW
      exact absurd hyW hy
    exact one_ne_zero (hx _ hmem)
  · intro hx g hg
    exact hg.2.self_of_nhds hx

omit [IsComplexManifold n X] in
/-- A closed connected complex submanifold of dimension `k` is a closed complex submanifold. -/
theorem isClosedSubmanifold_of_isClosedConnectedSubmanifold {W : Set X}
    (hW : IsClosedConnectedSubmanifold n W k) : IsClosedSubmanifold n W :=
  ⟨hW.1, fun x hx => ⟨k, hW.2.2 x hx⟩⟩

/-! ### Restriction of germs to the submanifold -/

section Restriction

variable {W : Set X} (hk : k ≤ n) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x k)

/-- Every holomorphic germ on the submanifold `W` (flattening complex structure) is the
restriction of an ambient holomorphic germ. -/
theorem exists_ambient_holomorphic_germ :
    letI := chartedSpace hk hreg
    ∀ (p : W) (b : W → ℂ), HolomorphicAt k b p →
      ∃ B : X → ℂ, HolomorphicAt n B p.val ∧ B ∘ (Subtype.val : W → X) =ᶠ[𝓝 p] b := by
  let := chartedSpace hk hreg
  have := isComplexManifold_chartedSpace hk hreg
  intro p b hb
  let F := FlatData.ofRegularAtDim (hreg p.val p.property)
  let e := F.chart hk
  let G : X → ComplexModel k := fun y => coordinateProjection n k (F.flat (F.amb.val y))
  let R : X → W := fun y => e.symm (G y)
  have hpAmb : p.val ∈ F.ambSource :=
    FlatData.mem_ambSource_ofRegularAtDim (hreg p.val p.property)
  have hpSource : p ∈ e.source := hpAmb
  have hpCoord : G p.val ∈ e.target := e.map_source hpSource
  have hG (y : X) (hy : y ∈ F.ambSource) :
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ G y := by
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ F.amb.val y :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas F.amb.property) hy.1
    have h2 : ContDiffAt ℂ ∞ (fun z => coordinateProjection n k (F.flat z)) (F.amb.val y) :=
      (coordinateProjection n k).contDiff.contDiffAt.comp _
        ((contDiffOn_of_differentiableOn_complex F.differentiableOn_flat
          F.flat.open_source).contDiffAt (F.flat.open_source.mem_nhds hy.2))
    exact h2.contMDiffAt.comp y h1
  have hemax : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel k) ∞ W :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas hk hreg F)
  have hR : ∀ᶠ y in 𝓝 p.val,
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ R y := by
    filter_upwards [F.isOpen_ambSource.mem_nhds hpAmb,
      (hG p.val hpAmb).continuousAt.eventually (e.open_target.mem_nhds hpCoord)] with
      y hy hyCoord
    exact (contMDiffAt_symm_of_mem_maximalAtlas hemax hyCoord).comp y (hG y hy)
  have hRp : R p.val = p := e.left_inv hpSource
  have hbR : HolomorphicAt k b (R p.val) := by rwa [hRp]
  refine ⟨b ∘ R, hbR.comp_contMDiff hR, ?_⟩
  filter_upwards [e.open_source.mem_nhds hpSource] with q hq
  change b (e.symm (e q)) = b q
  rw [e.left_inv hq]

/-- Restriction of germs `𝒪_{X,y} → 𝒪_{↥W,y}`, `g ↦ g|_W`, for `y ∈ W`. -/
def restrictGerm (p : W) :
    letI := chartedSpace hk hreg
    haveI := isComplexManifold_chartedSpace hk hreg
    NativeHolGerm n X p.1 →+* NativeHolGerm k W p :=
  letI := chartedSpace hk hreg
  haveI := isComplexManifold_chartedSpace hk hreg
  NativeHolGerm.comap Subtype.val (contMDiff_val hk hreg) p

theorem holomorphicAt_comp_val {p : W} {f : X → ℂ} (hf : HolomorphicAt n f p.1) :
    letI := chartedSpace hk hreg
    HolomorphicAt k (f ∘ (Subtype.val : W → X)) p := by
  let := chartedSpace hk hreg
  have := isComplexManifold_chartedSpace hk hreg
  exact hf.comp_contMDiff (Eventually.of_forall fun _ => (contMDiff_val hk hreg).contMDiffAt)

theorem restrictGerm_mk (p : W) (f : X → ℂ) (hf : HolomorphicAt n f p.1) :
    letI := chartedSpace hk hreg
    restrictGerm hk hreg p (NativeHolGerm.mk f hf) =
      NativeHolGerm.mk (f ∘ Subtype.val) (holomorphicAt_comp_val hk hreg hf) :=
  rfl

/-- Restriction of germs to a submanifold is surjective. -/
theorem restrictGerm_surjective (p : W) : Function.Surjective (restrictGerm hk hreg p) := by
  let := chartedSpace hk hreg
  intro b
  obtain ⟨g, hg, rfl⟩ := NativeHolGerm.exists_eq_mk b
  obtain ⟨B, hB, hBg⟩ := exists_ambient_holomorphic_germ hk hreg p g hg
  exact ⟨NativeHolGerm.mk B hB, by
    rw [restrictGerm_mk]
    exact NativeHolGerm.mk_eq_mk_iff.mpr hBg⟩

/-- The kernel of restriction of germs to `W` is the stalk of the ideal sheaf `𝓘_W`. -/
theorem ker_restrictGerm (p : W) :
    RingHom.ker (restrictGerm hk hreg p) = stalkIdeal (vanishingIdeal (n := n) W) p.1 := by
  let := chartedSpace hk hreg
  apply le_antisymm
  · intro G hG
    obtain ⟨g, hg, rfl⟩ := NativeHolGerm.exists_eq_mk G
    rw [RingHom.mem_ker, restrictGerm_mk] at hG
    have h0 : NativeHolGerm.mk (n := k) (x := p) (fun _ : W => (0 : ℂ)) (holomorphicAt_const 0) =
        0 := rfl
    rw [← h0, NativeHolGerm.mk_eq_mk_iff] at hG
    have hvan : (vanishingIdeal (n := n) W).mem p.1 g := by
      refine ⟨hg, ?_⟩
      have h1 := (eventually_nhds_subtype_iff W p (fun y => g y = 0)).mp hG
      filter_upwards [eventually_nhdsWithin_iff.mp h1] with y hy hyW
      exact hy hyW
    exact Ideal.subset_span ⟨g, hg, hvan, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨g, hg, hvan, rfl⟩
    change restrictGerm hk hreg p (NativeHolGerm.mk g hg) = 0
    rw [restrictGerm_mk]
    have h0 : NativeHolGerm.mk (n := k) (x := p) (fun _ : W => (0 : ℂ)) (holomorphicAt_const 0) =
        0 := rfl
    rw [← h0, NativeHolGerm.mk_eq_mk_iff]
    have h1 : ∀ᶠ q : W in 𝓝 p, q.1 ∈ W → g q.1 = 0 :=
      continuous_subtype_val.continuousAt.eventually hvan.2
    filter_upwards [h1] with q hq
    exact hq q.2

/-- **`𝒪_Y = 𝒪_X/𝓘_Y`**: for the closed complex subspace `Y` defined by a closed submanifold `W`,
restriction of germs identifies the structure stalk `𝒪_{X,y}/𝓘_{W,y}` with the germ ring of the
complex manifold `↥W` at `y`. -/
def structureStalkEquiv (hW : IsClosedSubmanifold n W) (p : W) :
    letI := chartedSpace hk hreg
    (submanifoldSubspace hW).structureStalk p.1 ≃+* NativeHolGerm k W p :=
  letI := chartedSpace hk hreg
  (Ideal.quotEquivOfEq (ker_restrictGerm hk hreg p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (restrictGerm_surjective hk hreg p))

theorem structureStalkEquiv_mk (hW : IsClosedSubmanifold n W) (p : W)
    (G : NativeHolGerm n X p.1) :
    structureStalkEquiv hk hreg hW p (Ideal.Quotient.mk _ G) = restrictGerm hk hreg p G :=
  rfl

end Restriction

/-! ### The Ohsawa–Takegoshi restriction theorem -/

section OT

variable {W : Set X}

/-- Germ form of `thm:OT`: every germ of `𝓘(c φ|_W)` at `p ∈ W` is the restriction of a germ of
`𝓘(c φ)` (`φ` quasi-psh on `X`, `W` a closed complex submanifold of dimension `k` with the
flattening complex structure). -/
theorem exists_extension_mem_multiplierIdeal (hk : k ≤ n)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} :
    letI := chartedSpace hk hreg
    ∀ (p : W) (f : W → ℂ), (multiplierIdeal (n := k) c (fun q : W => φ q.1)).mem p f →
      ∃ F : X → ℂ, (multiplierIdeal (n := n) c φ).mem p.1 F ∧
        (fun q : W => F q.1) =ᶠ[𝓝 p] f :=
  RestrictionOhsawaTakegoshi.exists_extension_mem_multiplierIdeal hk hreg hφ

/-- **Ohsawa–Takegoshi restriction (`thm:OT`), quasi-psh weights.** Let `W ⊆ X` be a closed
connected complex submanifold of dimension `k`, `Y` the closed complex subspace it defines and
`φ` quasi-psh on `X`. For every `y ∈ W` and every real `c`, the stalk `𝓘(c φ|_W)_y ⊆ 𝒪_{↥W,y}`,
transported to `𝒪_{Y,y} = 𝒪_{X,y}/𝓘_{W,y}` by `structureStalkEquiv`, is contained in
`(Rest_Y 𝓘(c φ))_y`. -/
theorem multiplierIdeal_restrict_le_restStalk_of_quasi
    (hW : IsClosedConnectedSubmanifold n W k) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (c : ℝ) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ∀ p : W,
      Ideal.comap (structureStalkEquiv (le_of_isClosedConnectedSubmanifold hW) hW.2.2
          (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW) p)
          (stalkIdeal (multiplierIdeal (n := k) c (fun q : W => φ q.1)) p) ≤
        restStalk (multiplierIdeal (n := n) c φ)
          (submanifoldSubspace (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW)) p.1 := by
  set hk := le_of_isClosedConnectedSubmanifold hW
  set hreg := hW.2.2
  set hC := isClosedSubmanifold_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hreg
  intro p
  set e := structureStalkEquiv hk hreg hC p
  rw [← Ideal.map_symm, Ideal.map_le_iff_le_comap]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨f, hf, hmem, rfl⟩
  obtain ⟨F, hF, hFf⟩ := exists_extension_mem_multiplierIdeal hk hreg hφ p f hmem
  have hFhol : HolomorphicAt n F p.1 := hF.1
  have he : e (Ideal.Quotient.mk _ (NativeHolGerm.mk F hFhol)) = NativeHolGerm.mk f hf := by
    rw [structureStalkEquiv_mk, restrictGerm_mk]
    exact NativeHolGerm.mk_eq_mk_iff.mpr hFf
  have hsymm : e.symm (NativeHolGerm.mk f hf) =
      Ideal.Quotient.mk _ (NativeHolGerm.mk F hFhol) := by
    rw [← he]
    exact e.symm_apply_apply _
  rw [SetLike.mem_coe, Ideal.mem_comap]
  change e.symm (NativeHolGerm.mk f hf) ∈ _
  rw [hsymm]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨F, hFhol, hF, rfl⟩)

/-- **Ohsawa–Takegoshi restriction (`thm:OT`).** Let `W ⊆ X` be a closed connected complex
submanifold of dimension `k`, `Y` the closed complex subspace it defines and `φ ∈ PSH(X)`. For
every `y ∈ W` and every real `c`, `𝓘(c φ|_W)_y ⊆ (Rest_Y 𝓘(c φ))_y` inside
`𝒪_{Y,y} = 𝒪_{X,y}/𝓘_{W,y}` (identified with `𝒪_{↥W,y}` by restriction of germs,
`structureStalkEquiv`). The hypothesis `φ|_Y ≢ -∞` of the book is not needed. -/
theorem multiplierIdeal_restrict_le_restStalk
    (hW : IsClosedConnectedSubmanifold n W k) {φ : X → EReal}
    (hφ : ManifoldPSH (n := n) φ) (c : ℝ) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ∀ p : W,
      Ideal.comap (structureStalkEquiv (le_of_isClosedConnectedSubmanifold hW) hW.2.2
          (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW) p)
          (stalkIdeal (multiplierIdeal (n := k) c (fun q : W => φ q.1)) p) ≤
        restStalk (multiplierIdeal (n := n) c φ)
          (submanifoldSubspace (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW)) p.1 :=
  multiplierIdeal_restrict_le_restStalk_of_quasi hW
    (manifoldQuasiPlurisubharmonic_of_manifoldPSH hφ) c

/-- **`thm:OT`**, the book's normalization `𝓘(φ) = 𝓘(1·φ)` (`def:pshfunctions:L1122`):
`𝓘(φ|_Y) ⊆ Rest_Y 𝓘(φ)` stalkwise inside `𝒪_Y = 𝒪_X/𝓘_Y`. -/
theorem thm_OT (hW : IsClosedConnectedSubmanifold n W k) {φ : X → EReal}
    (hφ : ManifoldPSH (n := n) φ) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ∀ p : W,
      Ideal.comap (structureStalkEquiv (le_of_isClosedConnectedSubmanifold hW) hW.2.2
          (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW) p)
          (stalkIdeal (multiplierIdeal (n := k) 1 (fun q : W => φ q.1)) p) ≤
        restStalk (multiplierIdeal (n := n) 1 φ)
          (submanifoldSubspace (isClosedSubmanifold_of_isClosedConnectedSubmanifold hW)) p.1 :=
  multiplierIdeal_restrict_le_restStalk hW hφ 1

end OT

end SGPT.PSH.OhsawaTakegoshi

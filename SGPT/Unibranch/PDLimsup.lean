import SGPT.Unibranch.PDCurveSelection
import SGPT.Unibranch.ComplexSpaceFornaessNarasimhan
import SGPT.PSH.GrauertRemmertBounded
import SGPT.Foundations.Analysis.FirstPass.PshClosedDiscMaximum

/-!
# The limsup formula for psh functions on singular complex spaces

Let `X` be a complex space (reduced, possibly singular, not necessarily unibranch) and `Z ⊆ X` an
analytic subset with empty interior (codimension `≥ 1` everywhere). Every plurisubharmonic
function `η` on `X` (`def:unibranch:L105`) satisfies
`η(x) = limsup_{X \ Z ∋ y → x} η(y)` for every `x ∈ X` (`IsPSH.eq_limsup_compl`).

This is the uniqueness part of the proof of the Grauert--Remmert extension theorem
(`thm:GRexten2`, Appendix B): for `z ∈ Z` take a holomorphic disc `f : Δ → X` with `f(0) = z` and
`f(Δ \ {0}) ∩ Z = ∅` (curve selection, `PDCurveSelection.exists_avoiding_disc`, which uses the local
resolution of singularities); `f^*η` satisfies the disc criterion (`thm:FN` (1) ⇒ (2)), so by the
maximum principle on small circles `η(z) = f^*η(0) ≤ limsup_{w → 0, w ≠ 0} f^*η(w) ≤
limsup_{X \ Z ∋ y → z} η(y)`; the reverse inequality is upper semicontinuity.

Consequences:

* `IsPSH.eq_of_eqOn_compl`: two psh functions which agree off `Z` agree everywhere;
* `grauertRemmert_extension_eq_limsup`, `grauertRemmert_extension_unique`: **source
  `thm:GRexten2`, uniqueness and formula `eq:GRextvarphi`**: on every complex space (in particular
  every unibranch one), for `Z` analytic of codimension `≥ 1` (a fortiori `≥ 2`), a psh extension
  of `φ` from `X \ Z` is unique and equals `limsup_{X \ Z ∋ y → x} φ(y)` at every `x ∈ X`, i.e. the
  regularized extension `analyticExtension Z φ` of the manifold case.

Lane PD, blueprint `pd.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceMaps

namespace SGPT.Unibranch.PD

open SourceReducedComplexSpace

noncomputable section

/-- The value of a function satisfying the disc criterion on the unit disc at the centre is
bounded by its upper limit on the punctured disc (maximum principle on small circles). -/
theorem le_limsup_punctured {u : ℂ → EReal}
    (hu : SGPT.Foundations.Analysis.DiscPshOn u (ball 0 1)) :
    u 0 ≤ limsup u (𝓝[≠] (0 : ℂ)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨C, hC1, hC2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), u t < C := eventually_lt_of_limsup_lt hC1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  set R : ℝ := min δ 1 / 2 with hR
  have hRpos : 0 < R := by
    rw [hR]
    exact div_pos (lt_min hδ one_pos) two_pos
  have hRδ : R < δ := by
    have := min_le_left δ 1
    rw [hR]
    linarith
  have hR1 : R < 1 := by
    have := min_le_right δ 1
    rw [hR]
    linarith
  have hpsh : SGPT.Foundations.Analysis.PlurisubharmonicOn u (ball 0 1) :=
    fun x hx => ⟨ball 0 1, isOpen_ball, hx, hu⟩
  have hs : ∀ z ∈ sphere (0 : ℂ) R, u z ≤ (C : EReal) := by
    intro z hz
    have hzR : dist z 0 = R := mem_sphere.mp hz
    have hz0 : z ≠ 0 := ne_of_mem_sphere hz hRpos.ne'
    exact (hball (by rw [hzR]; exact hRδ) (mem_compl_singleton_iff.mpr hz0)).le
  have h0 := hpsh.le_const_on_closedBall_of_le_on_sphere hRpos (closedBall_subset_ball hR1) hs 0
    (mem_closedBall_self hRpos.le)
  exact absurd h0 (not_le.mpr hC2)

/-- The open immersion `(Ω, C) → X` of a local embedding, as a morphism of complex spaces. -/
def embeddingMorphism {X : SourceReducedComplexSpace} (e : LocalEmbedding X) :
    sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic ⟶ X :=
  ObjectProperty.homMk (Over.homMk e.map e.overPoint)

/-- **Curve selection on complex spaces.** If `Z ⊆ X` is analytic with empty interior, then
through every point `z` of `X` there is a holomorphic disc `f : Δ → X` with `f(0) = z` which meets
`Z` at most at its centre: for every `φ`, `f^*φ(0) = φ(z)`, and near `0` the pull-back `f^*φ` is
`φ ∘ γ` for a curve `γ` tending to `z` inside `X \ Z` along the punctured disc. -/
theorem exists_disc_avoiding {X : SourceReducedComplexSpace} {Z : Set X.obj.left}
    (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅) (z : X.obj.left) :
    ∃ (f : unitDisc ⟶ X) (γ : ℂ → X.obj.left),
      (∀ φ : X.obj.left → EReal, ∀ t ∈ ball (0 : ℂ) 1, discPullback f φ t = φ (γ t)) ∧
      γ 0 = z ∧ Tendsto γ (𝓝[≠] (0 : ℂ)) (𝓝[Zᶜ] z) := by
  classical
  obtain ⟨e, ⟨c, rfl⟩, A', hA', hpre⟩ := hZ z
  have hmemZ : ∀ c' : e.carrier, e.toPoint c' ∈ Z ↔ (c' : e.ambient) ∈ A' := by
    intro c'
    change c' ∈ e.toPoint ⁻¹' Z ↔ _
    rw [hpre]
    rfl
  have hthin : ∀ O : Set e.ambient, IsOpen O → O ∩ e.carrier ⊆ A' → O ∩ e.carrier = ∅ := by
    intro O hO hOA
    by_contra hne
    obtain ⟨y, hyO, hyC⟩ := nonempty_iff_ne_empty.mpr hne
    let P : Set e.carrier := Subtype.val ⁻¹' O
    have hP : IsOpen P := hO.preimage continuous_subtype_val
    have himg : e.toPoint '' P ⊆ Z := by
      rintro _ ⟨c', hc', rfl⟩
      exact (hmemZ c').mpr (hOA ⟨hc', c'.property⟩)
    have hopen : IsOpen (e.toPoint '' P) := e.isOpenEmbedding_toPoint.isOpenMap _ hP
    have hsub := interior_maximal himg hopen
    rw [hZi] at hsub
    exact hsub ⟨⟨y, hyC⟩, hyO, rfl⟩
  obtain ⟨G, hG, hG0, hGC, hGA⟩ :=
    PDCurveSelection.exists_avoiding_disc e.analytic hA' hthin c.property
  have hmaps : MapsTo G unitDiscOpens e.ambient := by
    intro q hq
    obtain ⟨y, -, hy⟩ := hGC q hq
    rw [← hy]
    exact y.property
  have hcar : ∀ q : (univ : Set unitDiscOpens),
      (⟨G q.val.val, hmaps q.val.property⟩ : e.ambient) ∈ e.carrier := by
    intro q
    obtain ⟨y, hyC, hy⟩ := hGC q.val.val q.val.property
    have hyq : (⟨G q.val.val, hmaps q.val.property⟩ : e.ambient) = y := Subtype.ext hy.symm
    rw [hyq]
    exact hyC
  let g : unitDiscOpens → e.ambient := fun z => ⟨G z, hmaps z.2⟩
  have hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel e.dim) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff e.ambient g).mp
    exact hG.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)
  let F : unitDisc ⟶ sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic :=
    ObjectProperty.homMk (Over.homMk
      (actualSubspaceMap hg (C := (univ : Set unitDiscOpens)) (D := e.carrier)
        (fun c _ => hcar ⟨c, trivial⟩))
      (actualSubspaceMap_point hg _))
  let f : unitDisc ⟶ X := F ≫ embeddingMorphism e
  let κ : ℂ → e.carrier := fun t =>
    if h : discCoordinate t ∈ unitDiscOpens then
      ⟨⟨G (discCoordinate t), hmaps h⟩, hcar ⟨⟨discCoordinate t, h⟩, trivial⟩⟩
    else c
  refine ⟨f, fun t => e.toPoint (κ t), ?_, ?_, ?_⟩
  · intro φ t ht
    have h := discCoordinate_mem_unitDiscOpens ht
    simp only [discPullback, modelPullback, κ, dif_pos h]
    rfl
  · have h0 : discCoordinate 0 ∈ unitDiscOpens :=
      discCoordinate_mem_unitDiscOpens (mem_ball_self one_pos)
    have hκ0 : κ 0 = c := by
      simp only [κ, dif_pos h0]
      apply Subtype.ext
      apply Subtype.ext
      simp [hG0]
    show e.toPoint (κ 0) = e.toPoint c
    rw [hκ0]
  · have hκ : Tendsto κ (𝓝 (0 : ℂ)) (𝓝 c) := by
      have hind :
          Topology.IsInducing (fun q : e.carrier => ((q : e.ambient) : ComplexModel e.dim)) :=
        (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).isInducing
      rw [hind.tendsto_nhds_iff]
      have hGc : ContinuousAt G 0 :=
        hG.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
      have hdc : Tendsto (fun t : ℂ => G (discCoordinate t)) (𝓝 0) (𝓝 (G 0)) := by
        have h0 : Tendsto (discCoordinate : ℂ → ComplexModel 1) (𝓝 0) (𝓝 0) := by
          simpa using discCoordinate.continuous.tendsto 0
        exact hGc.tendsto.comp h0
      rw [hG0] at hdc
      refine hdc.congr' ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with t ht
      have h := discCoordinate_mem_unitDiscOpens ht
      simp only [Function.comp_apply, κ, dif_pos h]
    have hcont : Tendsto (fun t => e.toPoint (κ t)) (𝓝 (0 : ℂ)) (𝓝 (e.toPoint c)) :=
      (e.isOpenEmbedding_toPoint.continuous.tendsto c).comp hκ
    refine tendsto_nhdsWithin_iff.mpr ⟨hcont.mono_left nhdsWithin_le_nhds, ?_⟩
    have hball : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball (0 : ℂ) 1 ∧ t ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self one_pos)),
        self_mem_nhdsWithin] with t ht ht0
      exact ⟨ht, ht0⟩
    filter_upwards [hball] with t ht
    have h := discCoordinate_mem_unitDiscOpens ht.1
    change e.toPoint (κ t) ∉ Z
    rw [hmemZ]
    simp only [κ, dif_pos h]
    have hne : discCoordinate t ≠ 0 := by
      intro h0
      apply ht.2
      have := norm_discCoordinate t
      rw [h0, norm_zero] at this
      exact norm_eq_zero.mp this.symm
    exact hGA _ h hne _ rfl

/-- Functions satisfying condition 2 of `def:unibranch:L105` (local ambient psh restrictions)
are bounded at every point by their upper limit off a nowhere dense analytic subset. -/
theorem le_limsup_compl {X : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (hφ : ∀ x, X.IsLocallyAmbientPSHAt φ x) {Z : Set X.obj.left}
    (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅) (z : X.obj.left) :
    φ z ≤ limsup φ (𝓝[Zᶜ] z) := by
  obtain ⟨f, γ, hfγ, hγ0, hγ⟩ := exists_disc_avoiding hZ hZi z
  have hD := discPshOn_modelPullback hφ f.hom.left (Over.w f.hom)
  have hL := hD.comp_affine discCoordinate 0
  rw [discCoordinate_preimage] at hL
  have heq : (fun t : ℂ => modelPullback f.hom.left φ (0 + discCoordinate t)) =
      discPullback f φ := by
    funext t
    simp [discPullback]
  rw [heq] at hL
  have h1 := le_limsup_punctured hL
  have h0 : discPullback f φ 0 = φ z := by
    rw [hfγ φ 0 (mem_ball_self one_pos), hγ0]
  have hev : discPullback f φ =ᶠ[𝓝[≠] (0 : ℂ)] φ ∘ γ := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self one_pos))] with t ht
    exact hfγ φ t ht
  rw [h0, limsup_congr hev, limsup_comp] at h1
  exact h1.trans (limsup_le_limsup_of_le hγ)

/-- The upper limit off any set is at most the value, for an upper semicontinuous function. -/
theorem limsup_compl_le {X : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (hφ : UpperSemicontinuous φ) (Z : Set X.obj.left) (x : X.obj.left) :
    limsup φ (𝓝[Zᶜ] x) ≤ φ x :=
  (limsup_le_limsup_of_le nhdsWithin_le_nhds).trans (upperSemicontinuousAt_iff_limsup_le.mp (hφ x))

/-- **Limsup formula for psh functions on complex spaces.** If `Z ⊆ X` is analytic with empty
interior, every `η ∈ PSH(X)` satisfies `η(x) = limsup_{X \ Z ∋ y → x} η(y)` for all `x ∈ X`. -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsPSH.eq_limsup_compl
    {X : SourceReducedComplexSpace} {η : X.obj.left → EReal}
    (hη : X.IsPSH η) {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅)
    (x : X.obj.left) : η x = limsup η (𝓝[Zᶜ] x) :=
  le_antisymm (le_limsup_compl hη.2 hZ hZi x) (limsup_compl_le hη.upperSemicontinuous Z x)

/-- Psh functions agreeing off a nowhere dense analytic subset agree everywhere. -/
theorem _root_.SGPT.Unibranch.SourceReducedComplexSpace.IsPSH.eq_of_eqOn_compl
    {X : SourceReducedComplexSpace} {η₁ η₂ : X.obj.left → EReal}
    (h₁ : X.IsPSH η₁) (h₂ : X.IsPSH η₂) {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z)
    (hZi : interior Z = ∅) (heq : EqOn η₁ η₂ Zᶜ) : η₁ = η₂ := by
  funext x
  rw [h₁.eq_limsup_compl hZ hZi x, h₂.eq_limsup_compl hZ hZi x]
  apply limsup_congr
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact heq hy

/-- **Source `thm:GRexten2`, formula `eq:GRextvarphi`.** Let `X` be a complex space (unibranch or
not), `Z ⊆ X` an analytic subset of codimension `≥ 1` everywhere (empty interior; this covers both
items of the theorem) and `φ` a function on `X \ Z`. Every psh extension `η` of `φ` to `X` is given
by `η(x) = limsup_{X \ Z ∋ y → x} φ(y)`, i.e. it is the regularized extension
`analyticExtension Z φ`. -/
theorem grauertRemmert_extension_eq_limsup {X : SourceReducedComplexSpace}
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅)
    {φ η : X.obj.left → EReal} (hη : X.IsPSH η) (hext : EqOn η φ Zᶜ) (x : X.obj.left) :
    η x = limsup φ (𝓝[Zᶜ] x) := by
  rw [hη.eq_limsup_compl hZ hZi x]
  apply limsup_congr
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hext hy

/-- `eq:GRextvarphi` in terms of the regularized extension `analyticExtension` of the manifold
case (`thm:GRexten`). -/
theorem grauertRemmert_extension_eq_analyticExtension {X : SourceReducedComplexSpace}
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅)
    {φ η : X.obj.left → EReal} (hη : X.IsPSH η) (hext : EqOn η φ Zᶜ) :
    η = SGPT.PSH.VariableComplexAtlas.analyticExtension Z φ := by
  funext x
  rw [SGPT.PSH.VariableComplexAtlas.analyticExtension_eq_limsup]
  exact grauertRemmert_extension_eq_limsup hZ hZi hη hext x

/-- **Source `thm:GRexten2`, uniqueness.** On every complex space, a psh extension of a function
from the complement of an analytic subset of codimension `≥ 1` is unique. -/
theorem grauertRemmert_extension_unique {X : SourceReducedComplexSpace}
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅)
    {φ η₁ η₂ : X.obj.left → EReal} (h₁ : X.IsPSH η₁) (h₂ : X.IsPSH η₂)
    (hext₁ : EqOn η₁ φ Zᶜ) (hext₂ : EqOn η₂ φ Zᶜ) : η₁ = η₂ :=
  h₁.eq_of_eqOn_compl h₂ hZ hZi fun _ hy => (hext₁ hy).trans (hext₂ hy).symm

end

end SGPT.Unibranch.PD

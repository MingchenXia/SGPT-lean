import SGPT.Unibranch.PD3GRLocal
import SGPT.Unibranch.PD3Forward
import SGPT.Unibranch.PDFNReduction
import SGPT.Unibranch.PDLimsup
import SGPT.Unibranch.ResolutionLocal
import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Unibranch.ComplexSpaceSmoothPSHMaximum

/-!
# The Grauert--Remmert extension theorem on unibranch complex spaces, item (2)

Source `thm:GRexten2` (Appendix B, `appendix_unibranch.tex`). Let `X` be a unibranch complex space,
`Z ⊆ X` an analytic subset and `φ ∈ PSH(X \ Z)`. If `Z` has codimension `≥ 1` everywhere (empty
interior) and `φ` is locally bounded from above near `Z`, then `φ` has a unique psh extension to
`X`, given by `eq:GRextvarphi`: `φ(x) = limsup_{X \ Z ∋ y → x} φ(y)`.

The open subspace `X \ Z` is given, as usual, by an open immersion `j : W → X` with image `X \ Z`
(any such `W`; e.g. the open subspace on `Zᶜ`), and `φ ∈ PSH(X \ Z)` means `φ ∘ j ∈ PSH(W)`
(`def:unibranch:L105` on `W`). The values of `φ` on `Z` play no role.

Proof (the book's): uniqueness and the formula are the (`PD.grauertRemmert_extension_unique`,
via the limsup formula for psh functions on complex spaces). For existence, the candidate is
`η = analyticExtension Z φ` (the upper-regularized extension, equal to the right-hand side of
`eq:GRextvarphi`). Condition 1 (`η ≢ -∞` on irreducible components) holds because the components of
the unibranch `X` are its (open) connected components and `φ` is finite on a dense subset of
`X \ Z`. Condition 2 is local: near `x ∈ X` take a local resolution `π : Y → V` of an open
neighbourhood `V` (`exists_local_resolution`); on the manifold `Y` the regularized extension
`η_Y` of `π^*φ` is psh (the smooth version, `isLocallyAmbientPSHAt_analyticExtension_comp`; the
components of `Y` are open, `IsProperBimeromorphic.isOpen_of_isIrreducibleComponent`); by Zariski's
main theorem, the maximum principle on the compact connected fibres, the ramified lifting of discs
and `thm:FN`, `η_Y` descends to `ψ ∈ PSH(V)` (`PD.existsUnique_psh_descent`); and `ψ = η` on `V`
by the limsup formula on `V`.

Main results:

* `isPSH_analyticExtension_of_bounded`: the existence statement with local hypotheses on `X`;
* `grauertRemmert_extension_bounded`, `existsUnique_grauertRemmert_extension_bounded`:
  **`thm:GRexten2` (2)**, with uniqueness and `eq:GRextvarphi`.

Lane PD3, blueprint `pd3.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.PD3

open SourceReducedComplexSpace
open SGPT.PSH.VariableComplexAtlas (analyticExtension analyticExtension_eq_limsup)

noncomputable section

/-- The regularized extension agrees with the function at points off `Z` where the function is
upper semicontinuous. -/
theorem analyticExtension_eq_of_upperSemicontinuousAt {Y : Type*} [TopologicalSpace Y]
    {Z : Set Y} {φ : Y → EReal} {x : Y} (hx : x ∉ Z) (hφ : UpperSemicontinuousAt φ x) :
    analyticExtension Z φ x = φ x := by
  classical
  have h := uscRegularization_eq_of_le (f := fun y => if y ∈ Z then ⊥ else φ y) (g := φ) (x := x)
    (fun y => by
      by_cases hy : y ∈ Z
      · simp only [hy, if_true, bot_le]
      · simp only [hy, if_false, le_refl])
    hφ (by simp only [hx, if_false])
  unfold analyticExtension
  convert h using 1
  simp only [hx, if_false]

/-- A function satisfying condition 2 of `def:unibranch:L105` off `Z` and locally bounded above
near `Z` is locally bounded above off `Z` near every point. -/
theorem locallyBoundedAboveOff_of_bound {X : SourceReducedComplexSpace} {Z : Set X.obj.left}
    {φ : X.obj.left → EReal} (hφ : ∀ x, x ∉ Z → X.IsLocallyAmbientPSHAt φ x)
    (hb : ∀ x ∈ Z, ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, y ∉ Z → φ y ≤ C) :
    ∀ x, ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, y ∉ Z → φ y ≤ C := by
  intro x
  by_cases hx : x ∈ Z
  · exact hb x hx
  · obtain ⟨C, hC, -⟩ := EReal.lt_iff_exists_real_btwn.mp
      (lt_top_iff_ne_top.mpr (hφ x hx).ne_top)
    exact ⟨{y | φ y < C}, (hφ x hx).upperSemicontinuousAt C hC, C, fun y hy _ => hy.le⟩

/-- **Existence in `thm:GRexten2` (2), with local hypotheses.** Let `X` be unibranch, `Z ⊆ X`
analytic with empty interior, and `φ` satisfy condition 2 of `def:unibranch:L105` at every point
off `Z`, be finite on a dense set of points off `Z`, and be locally bounded above near `Z`. Then the
upper-regularized extension `analyticExtension Z φ` is psh on `X`. -/
theorem isPSH_analyticExtension_of_bounded {X : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅)
    {φ : X.obj.left → EReal} (hφ : ∀ x, x ∉ Z → X.IsLocallyAmbientPSHAt φ x)
    (hd : Dense {x | x ∉ Z ∧ φ x ≠ ⊥})
    (hb : ∀ x ∈ Z, ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, y ∉ Z → φ y ≤ C) :
    X.IsPSH (analyticExtension Z φ) := by
  have hb' := locallyBoundedAboveOff_of_bound hφ hb
  refine ⟨?_, fun x => ?_⟩
  · -- condition 1: components of the unibranch `X` are open
    intro K hK
    obtain ⟨x₀, hx₀⟩ := hK.1.2.1
    let _ := hX.locallyConnectedSpace
    have hKeq := hX.eq_connectedComponent_of_isIrreducibleComponent hK x₀ hx₀
    have hKo : IsOpen K := by
      have h : IsOpen (connectedComponent x₀ : Set X.obj.left) := isOpen_connectedComponent
      rwa [← hKeq] at h
    obtain ⟨y, hyK, hyZ, hyfin⟩ := hd.inter_open_nonempty K hKo ⟨x₀, hx₀⟩
    exact ⟨y, hyK, ne_bot_of_le_ne_bot hyfin (le_analyticExtension hyZ)⟩
  · -- condition 2: local resolution, extension upstairs, descent
    obtain ⟨V, jV, hjV, ⟨v, rfl⟩, Y, π, hY, hπ⟩ := exists_local_resolution X x
    have hV : V.IsUnibranch := hX.of_openImmersion jV hjV
    let ρ : Y ⟶ X := π ≫ jV
    have hρ : ∀ y, ρ.hom.left.base y = jV.hom.left.base (π.hom.left.base y) := fun _ => rfl
    have hjo : Topology.IsOpenEmbedding jV.hom.left.base := hjV.base_open
    have hdV : Dense (jV.hom.left.base ⁻¹' {x | x ∉ Z ∧ φ x ≠ ⊥}) := hd.preimage hjo.isOpenMap
    have hdY : Dense {y | ρ.hom.left.base y ∉ Z ∧ φ (ρ.hom.left.base y) ≠ ⊥} :=
      hπ.dense_preimage hdV
    set ηY := analyticExtension (ρ.hom.left.base ⁻¹' Z) (fun y => φ (ρ.hom.left.base y))
      with hηYdef
    have hηY : Y.IsPSH ηY := by
      refine ⟨?_, isLocallyAmbientPSHAt_analyticExtension_comp hY.hasDomainCharts ρ hZ hφ hb' hdY⟩
      intro K hK
      have hKo := hπ.isOpen_of_isIrreducibleComponent hV hK
      obtain ⟨y, hyK, hyZ, hyfin⟩ := hdY.inter_open_nonempty K hKo hK.1.2.1
      exact ⟨y, hyK, ne_bot_of_le_ne_bot hyfin
        (le_analyticExtension (Z := ρ.hom.left.base ⁻¹' Z) (φ := fun y => φ (ρ.hom.left.base y))
          hyZ)⟩
    obtain ⟨w, ⟨hw, hwη⟩, -⟩ := PD.existsUnique_psh_descent π hπ hV hηY
    -- the descended function is `η` on `V`
    set ZV : Set V.obj.left := jV.hom.left.base ⁻¹' Z with hZVdef
    have hZV : V.IsAnalyticSubset ZV := hZ.preimage jV
    have hZVi : interior ZV = ∅ := by
      rw [hZVdef, ← hjo.isOpenMap.preimage_interior_eq_interior_preimage
        jV.hom.left.base.hom.continuous, hZi, preimage_empty]
    have hoff : ∀ v', v' ∉ ZV → w v' = φ (jV.hom.left.base v') := by
      intro v' hv'
      obtain ⟨y, rfl⟩ := hπ.surjective v'
      rw [hwη y, hηYdef]
      exact analyticExtension_eq_of_upperSemicontinuousAt (Z := ρ.hom.left.base ⁻¹' Z)
        (φ := fun y => φ (ρ.hom.left.base y)) hv'
        (UpperSemicontinuousAt.comp (f := φ) (g := ρ.hom.left.base)
          (hφ _ hv').upperSemicontinuousAt ρ.hom.left.base.hom.continuous.continuousAt)
    have hweq : ∀ v', w v' = analyticExtension Z φ (jV.hom.left.base v') := by
      intro v'
      rw [hw.eq_limsup_compl hZV hZVi v', analyticExtension_eq_limsup]
      have h1 : limsup w (𝓝[ZVᶜ] v') = limsup (φ ∘ jV.hom.left.base) (𝓝[ZVᶜ] v') := by
        apply limsup_congr
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact hoff y hy
      rw [h1, limsup_comp]
      congr 1
      rw [hjo.isEmbedding.map_nhdsWithin_eq, hZVdef, ← preimage_compl,
        image_preimage_eq_inter_range]
      exact nhdsWithin_inter_of_mem'
        (mem_nhdsWithin_of_mem_nhds (hjo.isOpen_range.mem_nhds (mem_range_self v')))
    have hwV : V.IsPSH (fun v' => analyticExtension Z φ (jV.hom.left.base v')) := by
      have h : w = fun v' => analyticExtension Z φ (jV.hom.left.base v') := funext hweq
      rwa [h] at hw
    exact isLocallyAmbientPSHAt_of_openImmersion jV hjV (hwV.2 v)

/-- Condition 2 of `def:unibranch:L105` on the open subspace `j : W → X` gives condition 2 on `X`
at the points of the image. -/
theorem isLocallyAmbientPSHAt_of_isPSH_openImmersion {X W : SourceReducedComplexSpace}
    (j : W ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) {φ : X.obj.left → EReal}
    (hφ : W.IsPSH (fun w => φ (j.hom.left.base w))) {x : X.obj.left}
    (hx : x ∈ range j.hom.left.base) : X.IsLocallyAmbientPSHAt φ x := by
  obtain ⟨w, rfl⟩ := hx
  exact isLocallyAmbientPSHAt_of_openImmersion j hj (hφ.2 w)

/-- A psh function on an open subspace `j : W → X` of a unibranch space with dense image
`X \ Z` is finite on a dense set of points of `X \ Z`. -/
theorem dense_finite_of_isPSH_openImmersion {X W : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    {Z : Set X.obj.left} (hZi : interior Z = ∅) (j : W ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (hjr : range j.hom.left.base = Zᶜ)
    {φ : X.obj.left → EReal} (hφ : W.IsPSH (fun w => φ (j.hom.left.base w))) :
    Dense {x | x ∉ Z ∧ φ x ≠ ⊥} := by
  have hW : W.IsUnibranch := hX.of_openImmersion j hj
  have hdW := hφ.dense_finite_of_isUnibranch hW
  have hjo : Topology.IsOpenEmbedding j.hom.left.base := hj.base_open
  rw [dense_iff_inter_open]
  intro O hO hOne
  have hOZ : (O ∩ range j.hom.left.base).Nonempty := by
    rw [hjr]
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← sdiff_eq] at h
    obtain ⟨x, hx⟩ := hOne
    have hsub : O ⊆ Z := fun y hy => by
      by_contra hyZ
      exact (Set.eq_empty_iff_forall_notMem.mp h) y ⟨hy, hyZ⟩
    have : x ∈ interior Z := mem_interior.mpr ⟨O, hsub, hO, hx⟩
    rw [hZi] at this
    exact this
  obtain ⟨_, hxO, w, rfl⟩ := hOZ
  obtain ⟨w', hw'O, hw'fin⟩ := hdW.inter_open_nonempty _
    (hO.preimage j.hom.left.base.hom.continuous) ⟨w, hxO⟩
  have hw'Z : j.hom.left.base w' ∉ Z := by
    have h : j.hom.left.base w' ∈ range j.hom.left.base := mem_range_self w'
    rw [hjr] at h
    exact h
  exact ⟨j.hom.left.base w', hw'O, hw'Z, hw'fin⟩

/-- **Source `thm:GRexten2`, item (2), with uniqueness and `eq:GRextvarphi`.** Let `X` be a
unibranch complex space, `Z ⊆ X` an analytic subset of codimension `≥ 1` everywhere
(`interior Z = ∅`), `j : W → X` the open subspace `X \ Z` (an open immersion with image `Zᶜ`), and
`φ` a function with `φ ∘ j ∈ PSH(W)` (i.e. `φ ∈ PSH(X \ Z)`) which is locally bounded from above
near `Z`. Then `analyticExtension Z φ` is psh on `X` and extends `φ`; every psh extension of `φ`
equals it; and its value at every `x ∈ X` is `limsup_{X \ Z ∋ y → x} φ(y)`. -/
theorem grauertRemmert_extension_bounded {X W : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hZi : interior Z = ∅) (j : W ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (hjr : range j.hom.left.base = Zᶜ)
    {φ : X.obj.left → EReal} (hφ : W.IsPSH (fun w => φ (j.hom.left.base w)))
    (hb : ∀ x ∈ Z, ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, y ∉ Z → φ y ≤ C) :
    X.IsPSH (analyticExtension Z φ) ∧ EqOn (analyticExtension Z φ) φ Zᶜ ∧
      (∀ η : X.obj.left → EReal, X.IsPSH η → EqOn η φ Zᶜ → η = analyticExtension Z φ) ∧
      ∀ x, analyticExtension Z φ x = limsup φ (𝓝[Zᶜ] x) := by
  have hloc : ∀ x, x ∉ Z → X.IsLocallyAmbientPSHAt φ x := fun x hx =>
    isLocallyAmbientPSHAt_of_isPSH_openImmersion j hj hφ (by rw [hjr]; exact hx)
  have hd := dense_finite_of_isPSH_openImmersion hX hZi j hj hjr hφ
  have hpsh := isPSH_analyticExtension_of_bounded hX hZ hZi hloc hd hb
  have heq : EqOn (analyticExtension Z φ) φ Zᶜ := fun x hx =>
    analyticExtension_eq_of_upperSemicontinuousAt hx (hloc x hx).upperSemicontinuousAt
  exact ⟨hpsh, heq, fun η hη hηφ => PD.grauertRemmert_extension_unique hZ hZi hη hpsh hηφ heq,
    fun x => analyticExtension_eq_limsup Z φ x⟩

/-- **Source `thm:GRexten2`, item (2)**, as unique existence: under the hypotheses of
`grauertRemmert_extension_bounded`, `φ` has exactly one psh extension to `X`. -/
theorem existsUnique_grauertRemmert_extension_bounded {X W : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z)
    (hZi : interior Z = ∅) (j : W ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (hjr : range j.hom.left.base = Zᶜ) {φ : X.obj.left → EReal}
    (hφ : W.IsPSH (fun w => φ (j.hom.left.base w)))
    (hb : ∀ x ∈ Z, ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, y ∉ Z → φ y ≤ C) :
    ∃! η : X.obj.left → EReal, X.IsPSH η ∧ EqOn η φ Zᶜ := by
  obtain ⟨hpsh, heq, huniq, -⟩ := grauertRemmert_extension_bounded hX hZ hZi j hj hjr hφ hb
  exact ⟨_, ⟨hpsh, heq⟩, fun η hη => huniq η hη.1 hη.2⟩

end

end SGPT.Unibranch.PD3

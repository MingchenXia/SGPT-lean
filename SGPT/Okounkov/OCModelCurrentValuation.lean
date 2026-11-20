import SGPT.Okounkov.OCSpaceFormNative
import SGPT.Okounkov.OCKahlerCommonModel
import SGPT.Okounkov.SmoothModelCurrentValuation
import SGPT.Okounkov.ThetaCurrentPullbackFunctorial
import SGPT.Okounkov.FlagLiftingExistence
import SGPT.Unibranch.ComplexSpaceAnalyticPreimage
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent

/-!
# the valuation of a current on a normal (reduced) model, `def:modelvalcurr`

Source (`chapter_Okounkov.tex`):

* `def:modelvalcurr`: let `π : Z → X` be a proper bimeromorphic morphism from a normal compact
  Kähler space and `S` a closed positive `(1,1)`-current on `Z`. Choose a proper bimeromorphic
  `h : Ẑ → Z` from a compact Kähler manifold such that `Y•` admits a lifting `(W•, g)` to `Ẑ` with
  respect to `π ∘ h`, `g = cor(Y•, π ∘ h)`, and set `ν_{Y•}(S) := ν_{W•}(h^*S) g⁻¹ ∈ ℝⁿ`.
* `lma:modelvalcurrbir`: the definition does not depend on `h`; and for a proper bimeromorphic
  `p : Z' → Z` from a normal compact Kähler space, `ν_{Y•}(p^*S) = ν_{Y•}(S)` with respect to the
  model `π ∘ p`.

Objects. `Z` is a reduced complex space (`SourceReducedComplexSpace`; compact because `π` is
proper); normality enters only through unibranchness (`SourceReducedComplexSpace.IsUnibranch`,
implied by normality, `isUnibranch_of_normal_stalks`), which makes `θ`-psh functions pull back.
A closed positive `(1,1)`-current on `Z` is `S = θ + ddᶜφ` with `θ` a smooth closed real
`(1,1)`-form on `Z` and `φ` a `θ`-psh function (`def:unibranch:L105`); `h^*S` is the native
current `h^*θ + ddᶜ(φ ∘ h)` (`OCSpaceFormNative`). A choice of `h` is a compact connected Kähler
flagged manifold `W` with a proper bimeromorphic morphism `h : (W, 𝒪) ⟶ Z` and a flag lifting
of `Y•` along `π ∘ h`.

Results.

* `modelCurrentFlagValuation`: `ν_{W•}(h^*S) g⁻¹` for a choice `h`
  (`correctedModelCurrentFlagValuation` of the smooth case);
* `modelCurrentFlagValuation_eq_of_choices`: **independence of the choice** (first sentence of
  `lma:modelvalcurrbir`), via a compact Kähler common model (`OCKahlerCommonModel`), a lifting on
  a finite modification of it and the smooth-case pull-back identity; no Chow lemma;
* `isProperBimeromorphic_of_isAnalyticModification_comp`: `h` is proper bimeromorphic as soon as
  `π ∘ h` is a modification of manifolds;
* `modelCurrentFlagValuation_pullback`: **birational invariance** (second sentence of
  `lma:modelvalcurrbir`) for every choice on `Z'` and every choice on `Z`.

The existence of a choice for an arbitrary normal `Z` (needed to make the definition total) is
the Chow-domination input of `thm:liftableflag`; see `OCLiftableFlag` and
`exists_choice_of_chow`.

Blueprint: `blueprint/src/oc.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OCModelCurrentValuation

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent AnalyticModificationLocalDiscrepancy
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.OriginalProperBimeromorphicNative
open SGPT.Okounkov.OCSpaceFormNative

/-! ### Isomorphisms over open sets and compositions -/

section Compositions

/-- If `g` is an isomorphism over `U` and so is `f ≫ g`, then `f` is an isomorphism over
`g⁻¹ U`. -/
theorem IsIsoOver.of_comp {X Y Z : SourceReducedComplexSpace} {f : Z ⟶ Y} {g : Y ⟶ X}
    {U : Set X.obj.left} (hg : IsIsoOver g U) (hfg : IsIsoOver (f ≫ g) U) :
    IsIsoOver f (g.hom.left.base ⁻¹' U) := by
  obtain ⟨V, j, hj, hjr, hjg, hjgr⟩ := hg
  obtain ⟨V', j', hj', hj'r, hj'fg, hj'fgr⟩ := hfg
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let : LocallyRingedSpace.IsOpenImmersion (j ≫ g.hom.left) := hjg
  let : LocallyRingedSpace.IsOpenImmersion (j' ≫ (f ≫ g).hom.left) := hj'fg
  have hr : range (j' ≫ f.hom.left).base ⊆ range j.base := by
    rintro _ ⟨w, rfl⟩
    rw [hjr]
    have hw : j'.base w ∈ range j'.base := ⟨w, rfl⟩
    rw [hj'r] at hw
    exact hw
  let k := LocallyRingedSpace.IsOpenImmersion.lift j (j' ≫ f.hom.left) hr
  have hkj : k ≫ j = j' ≫ f.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac j (j' ≫ f.hom.left) hr
  have hrange : range (j' ≫ (f ≫ g).hom.left).base = range (j ≫ g.hom.left).base :=
    hj'fgr.trans hjgr.symm
  let E := HironakaEmbeddedNativeMorphism.openImmersionIsoOfRangeEq
    (j' ≫ (f ≫ g).hom.left) (j ≫ g.hom.left) hrange
  have hE : E.hom ≫ (j ≫ g.hom.left) = j' ≫ (f ≫ g).hom.left :=
    HironakaEmbeddedNativeMorphism.openImmersionIsoOfRangeEq_hom_fac _ _ _
  have hkE : k = E.hom := by
    apply (cancel_mono (j ≫ g.hom.left)).mp
    calc k ≫ (j ≫ g.hom.left) = (k ≫ j) ≫ g.hom.left := (Category.assoc _ _ _).symm
      _ = (j' ≫ f.hom.left) ≫ g.hom.left := by rw [hkj]
      _ = j' ≫ (f.hom.left ≫ g.hom.left) := Category.assoc _ _ _
      _ = j' ≫ (f ≫ g).hom.left := rfl
      _ = E.hom ≫ (j ≫ g.hom.left) := hE.symm
  have hj'f : j' ≫ f.hom.left = E.hom ≫ j := by rw [← hkE, hkj]
  refine ⟨V', j', hj', hj'r, ?_, ?_⟩
  · rw [hj'f]
    infer_instance
  · rw [hj'f, HironakaResolutionSpaceComplex.range_iso_hom_comp_base, hjr]

variable {n : ℕ} {M W : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace W] [ChartedSpace (ComplexModel n) W]
  [IsComplexManifold n W]

/-- **A morphism whose composite with a proper bimeromorphic map onto a manifold is a modification
is proper bimeromorphic.** If `π : Z ⟶ (M, 𝒪)` is proper bimeromorphic and `π ∘ h` is a native
analytic modification for `h : (W, 𝒪) ⟶ Z`, then `h` is proper bimeromorphic. -/
theorem isProperBimeromorphic_of_isAnalyticModification_comp {Z : SourceReducedComplexSpace}
    {π : Z ⟶ wholeModel (n := n) M} (hπ : IsProperBimeromorphic π)
    (h : wholeModel (n := n) W ⟶ Z)
    (hmod : IsAnalyticModification (n := n) (nativePointMap (h ≫ π))) :
    IsProperBimeromorphic h := by
  have : T2Space ↑↑Z.obj.left.toPresheafedSpace := Z.property.1
  have hG : IsProperBimeromorphic (h ≫ π) := by
    have := nativeMorphism_isProperBimeromorphic hmod
    rwa [nativeMorphism_nativePointMap] at this
  obtain ⟨hGp, E0, hE0a, hE0t, hGE0, hGiso⟩ := hG
  obtain ⟨hπp, T, hTa, hTt, hπT, hπiso⟩ := hπ
  have hAc : IsClosed (E0 ∪ T) := hE0a.isClosed.union hTa.isClosed
  have hAt : interior (E0 ∪ T) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty hE0a.isClosed hTt, hE0t]
  have hAa : (wholeModel (n := n) M).IsAnalyticSubset (E0 ∪ T) := by
    intro x
    let e := LocalEmbedding.ofPoint (wholeModel (n := n) M) x
    refine ⟨e, LocalEmbedding.mem_range_ofPoint _ x,
      (Subtype.val '' (e.toPoint ⁻¹' E0)) ∪ (Subtype.val '' (e.toPoint ⁻¹' T)),
      ConstantRankImage.IsComplexAnalyticSubset.union
        (hE0a.analytic_image_localEmbedding e) (hTa.analytic_image_localEmbedding e), ?_⟩
    rw [preimage_union, preimage_union, preimage_image_eq _ Subtype.val_injective,
      preimage_image_eq _ Subtype.val_injective]
  refine ⟨isProperMap_of_comp_of_t2 h.hom.left.base.hom.continuous
    π.hom.left.base.hom.continuous hGp, π.hom.left.base ⁻¹' (E0 ∪ T), hAa.preimage π, ?_, ?_, ?_⟩
  · exact IsIsoOver.interior_preimage_eq_empty hπiso hπT hAt
  · change interior ((h ≫ π).hom.left.base ⁻¹' (E0 ∪ T)) = ∅
    exact IsIsoOver.interior_preimage_eq_empty hGiso hGE0 hAt
  · have hπA : IsIsoOver π (E0 ∪ T)ᶜ :=
      hπiso.of_isOpen_subset hAc.isOpen_compl (fun x hx hxT => hx (Or.inr hxT))
    have hGA : IsIsoOver (h ≫ π) (E0 ∪ T)ᶜ :=
      hGiso.of_isOpen_subset hAc.isOpen_compl (fun x hx hxE => hx (Or.inl hxE))
    have := IsIsoOver.of_comp hπA hGA
    rwa [preimage_compl] at this

end Compositions

/-! ### The pulled-back current -/

variable {m : ℕ}

section Current

variable {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel (m + 1)) W]
  [IsComplexManifold (m + 1) W] {Z : SourceReducedComplexSpace}

/-- The pull-back `h^*θ` as a closed real `(1,1)`-form. -/
def nativePullbackClosed (h : wholeModel (n := m + 1) W ⟶ Z) (θ : SpaceForm Z 2)
    (hθc : θ.IsClosed) (hθ11 : θ.IsOneOne) : ClosedRealOneOneForm (m + 1) W :=
  ⟨nativePullback h θ, nativePullback_isClosed h θ hθc, nativePullback_isTypeOneOne h θ hθ11⟩

/-- **The pull-back current** `h^*S = h^*θ + ddᶜ(φ ∘ h)` of `S = θ + ddᶜφ`. -/
def modelPullbackCurrent (h : wholeModel (n := m + 1) W ⟶ Z) (hh : IsProperBimeromorphic h)
    (hZ : Z.IsUnibranch) (θ : SpaceForm Z 2) (φ : Z.obj.left → EReal)
    (hφ : Z.IsThetaPSH θ φ) : GlobalCurrent (m + 1) W (degreeTwo (Nat.succ_pos m)) :=
  thetaPotentialCurrent (nativePullback h θ) (nativePotential h φ)
    (isThetaPshPotential_nativePullback h θ hφ hZ hh)

theorem modelPullbackCurrent_closed_type_positive (h : wholeModel (n := m + 1) W ⟶ Z)
    (hh : IsProperBimeromorphic h) (hZ : Z.IsUnibranch) (θ : SpaceForm Z 2)
    (φ : Z.obj.left → EReal) (hφ : Z.IsThetaPSH θ φ) :
    (modelPullbackCurrent h hh hZ θ φ hφ).IsClosed (canonicalBasis (m + 1)) ∧
    (modelPullbackCurrent h hh hZ θ φ hφ).IsTypeOneOne (canonicalBasis (m + 1))
      (Nat.succ_pos m) ∧
    IsFullPositive (modelPullbackCurrent h hh hZ θ φ hφ) :=
  thetaPotentialCurrent_closed_type_positive _ _ _

end Current

/-! ### The valuation for a choice of `h` -/

variable (F : OriginalFlagGeometry.{0} (m + 1)) {Z : SourceReducedComplexSpace}

/-- **Source `def:modelvalcurr`.** For a choice `h : (W, 𝒪) ⟶ Z` (proper bimeromorphic, with
`Y•` lifting to `W` along `π ∘ h`), `ν_{Y•}(S) := ν_{W•}(h^*S) g⁻¹`, `g = cor(Y•, π ∘ h)`. -/
def modelCurrentFlagValuation (π : Z ⟶ wholeModel (n := m + 1) F.carrier)
    {W : OriginalFlagGeometry.{0} (m + 1)} (h : wholeModel (n := m + 1) W.carrier ⟶ Z)
    (hh : IsProperBimeromorphic h) (hLift : IsFlagLifting F W (nativePointMap (h ≫ π)))
    (hZ : Z.IsUnibranch) (θ : SpaceForm Z 2) (φ : Z.obj.left → EReal)
    (hφ : Z.IsThetaPSH θ φ) : Fin (m + 1) → ℝ :=
  correctedModelCurrentFlagValuation hLift (modelPullbackCurrent h hh hZ θ φ hφ)
    (modelPullbackCurrent_closed_type_positive h hh hZ θ φ hφ).1
    (modelPullbackCurrent_closed_type_positive h hh hZ θ φ hφ).2.1
    (modelPullbackCurrent_closed_type_positive h hh hZ θ φ hφ).2.2

private theorem thetaPotentialCurrent_congr {V : Type} [TopologicalSpace V]
    [ChartedSpace (ComplexModel (m + 1)) V] [IsComplexManifold (m + 1) V]
    {θ σ : SmoothRealForm (m + 1) V 2} {v w : V → EReal} (hθσ : θ.GeometricallyEq σ)
    (hvw : v = w) (hv : IsThetaPshPotential θ v) (hw : IsThetaPshPotential σ w) :
    thetaPotentialCurrent θ v hv = thetaPotentialCurrent σ w hw := by
  subst hvw
  exact thetaPotentialCurrent_eq_of_geometricallyEq hθσ hv hw

private theorem corrected_congr {V : OriginalFlagGeometry.{0} (m + 1)}
    {f f' : V.carrier → F.carrier} (hf : IsFlagLifting F V f) (hf' : IsFlagLifting F V f')
    (hff' : f = f') {S S' : GlobalCurrent (m + 1) V.carrier (degreeTwo (Nat.succ_pos m))}
    (hSS' : S = S') (hc : S.IsClosed (canonicalBasis (m + 1)))
    (hc' : S'.IsClosed (canonicalBasis (m + 1)))
    (h11 : S.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (h11' : S'.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : IsFullPositive S) (hp' : IsFullPositive S') :
    correctedModelCurrentFlagValuation hf S hc h11 hp =
      correctedModelCurrentFlagValuation hf' S' hc' h11' hp' := by
  subst hff'
  subst hSS'
  rfl

/-- **Source `lma:modelvalcurrbir`, first sentence: independence of the choice of `h`.** Any two
choices give the same value. The proof follows the book: a compact Kähler common model
`U → Ẑ_i` over `Z` (`OCKahlerCommonModel.exists_kahler_commonModel`), a lifting of `Y•` to a
finite modification `V` of `U` (`exists_flagLifting_dominating_nativeModel`), and the smooth
pull-back identity `ν_V(q_i^*h_i^*S) cor(π h_i q_i)⁻¹ = ν_{W_i}(h_i^*S) cor(π h_i)⁻¹`
(`prop:cormatrix`, `prop:cormult`, `exists_unique_correctedModelCurrentFlagValuation_pullback`). -/
theorem modelCurrentFlagValuation_eq_of_choices (π : Z ⟶ wholeModel (n := m + 1) F.carrier)
    {W₁ W₂ : OriginalFlagGeometry.{0} (m + 1)}
    (h₁ : wholeModel (n := m + 1) W₁.carrier ⟶ Z) (h₂ : wholeModel (n := m + 1) W₂.carrier ⟶ Z)
    (hh₁ : IsProperBimeromorphic h₁) (hh₂ : IsProperBimeromorphic h₂)
    (L₁ : IsFlagLifting F W₁ (nativePointMap (h₁ ≫ π)))
    (L₂ : IsFlagLifting F W₂ (nativePointMap (h₂ ≫ π)))
    (hZ : Z.IsUnibranch) (θ : SpaceForm Z 2) (hθc : θ.IsClosed) (hθ11 : θ.IsOneOne)
    (φ : Z.obj.left → EReal) (hφ : Z.IsThetaPSH θ φ) :
    modelCurrentFlagValuation F π h₁ hh₁ L₁ hZ θ φ hφ =
      modelCurrentFlagValuation F π h₂ hh₂ L₂ hZ θ φ hφ := by
  -- A compact Kähler common model.
  obtain ⟨U, topU, chartsU, complexU, compactU, connU, ωU, g₁, g₂, hg₁, hg₂, hsq⟩ :=
    OCKahlerCommonModel.exists_kahler_commonModel W₁.omega W₂.omega h₁ h₂ hh₁ hh₂
  let := topU
  let := chartsU
  have := complexU
  have := compactU
  have := connU
  -- A lifting of `Y•` on a finite modification of `U`.
  have hρ : IsAnalyticModification (n := m + 1) (nativePointMap (h₁ ≫ π) ∘ g₁) :=
    AnalyticModificationComposition.isAnalyticModification_comp L₁.1 hg₁
  obtain ⟨V, r, hr, hLV⟩ :=
    exists_flagLifting_dominating_nativeModel (m + 1) F U ωU _ hρ
  have hrmod : IsAnalyticModification (n := m + 1) r :=
    isAnalyticModification_of_finiteBlowupSequence hr
  have hp₁ : IsAnalyticModification (n := m + 1) (g₁ ∘ r) :=
    AnalyticModificationComposition.isAnalyticModification_comp hg₁ hrmod
  have hp₂ : IsAnalyticModification (n := m + 1) (g₂ ∘ r) :=
    AnalyticModificationComposition.isAnalyticModification_comp hg₂ hrmod
  -- Pointwise equality of the two composites `U → Z`.
  have hpt (u : U) : h₁.hom.left.base ⟨g₁ u, mem_univ _⟩ = h₂.hom.left.base ⟨g₂ u, mem_univ _⟩ :=
    congrArg (fun H : wholeModel (n := m + 1) U ⟶ Z => H.hom.left.base ⟨u, mem_univ u⟩) hsq
  have hfun : nativePointMap (h₁ ≫ π) ∘ g₁ = nativePointMap (h₂ ≫ π) ∘ g₂ := by
    funext u
    exact congrArg (fun z => (π.hom.left.base z).val) (hpt u)
  have hq₁ : IsFlagLifting F V (nativePointMap (h₁ ≫ π) ∘ (g₁ ∘ r)) := hLV
  have hq₂ : IsFlagLifting F V (nativePointMap (h₂ ≫ π) ∘ (g₂ ∘ r)) := by
    have h' : IsFlagLifting F V ((nativePointMap (h₂ ≫ π) ∘ g₂) ∘ r) := hfun ▸ hLV
    exact h'
  have hmaps : nativePointMap (h₁ ≫ π) ∘ (g₁ ∘ r) = nativePointMap (h₂ ≫ π) ∘ (g₂ ∘ r) := by
    funext x
    exact congrFun hfun (r x)
  -- The two pulled-back currents.
  obtain ⟨hc₁, h11₁, hT₁⟩ := modelPullbackCurrent_closed_type_positive h₁ hh₁ hZ θ φ hφ
  obtain ⟨hc₂, h11₂, hT₂⟩ := modelPullbackCurrent_closed_type_positive h₂ hh₂ hZ θ φ hφ
  obtain ⟨S₁, ⟨hcS₁, h11S₁, hS₁, hread₁, hval₁⟩, -⟩ :=
    exists_unique_correctedModelCurrentFlagValuation_pullback L₁ hq₁ hp₁
      (modelPullbackCurrent h₁ hh₁ hZ θ φ hφ) hc₁ h11₁ hT₁
  obtain ⟨S₂, ⟨hcS₂, h11S₂, hS₂, hread₂, hval₂⟩, -⟩ :=
    exists_unique_correctedModelCurrentFlagValuation_pullback L₂ hq₂ hp₂
      (modelPullbackCurrent h₂ hh₂ hZ θ φ hφ) hc₂ h11₂ hT₂
  have hS₁eq := hread₁ (nativePullbackClosed h₁ θ hθc hθ11) (nativePotential h₁ φ)
    (isThetaPshPotential_nativePullback h₁ θ hφ hZ hh₁) rfl
  have hS₂eq := hread₂ (nativePullbackClosed h₂ θ hθc hθ11) (nativePotential h₂ φ)
    (isThetaPshPotential_nativePullback h₂ θ hφ hZ hh₂) rfl
  -- The two composite morphisms `V → Z` agree.
  have hmor : nativeMorphism hp₁.1 ≫ h₁ = nativeMorphism hp₂.1 ≫ h₂ :=
    morphism_eq_of_pointwise_eq _ _ (fun x => hpt (r x.val))
  have hS : S₁ = S₂ := by
    rw [hS₁eq, hS₂eq]
    unfold thetaPotentialModificationCurrent
    apply thetaPotentialCurrent_congr
    · have h1 := nativePullback_comp_geometricallyEq h₁ θ hp₁.1
      have h2 := nativePullback_comp_geometricallyEq h₂ θ hp₂.1
      rw [hmor] at h1
      exact h1.symm.trans h2
    · funext x
      exact congrArg φ (hpt (r x))
  calc modelCurrentFlagValuation F π h₁ hh₁ L₁ hZ θ φ hφ
      = correctedModelCurrentFlagValuation hq₁ S₁ hcS₁ h11S₁ hS₁ := hval₁.symm
    _ = correctedModelCurrentFlagValuation hq₂ S₂ hcS₂ h11S₂ hS₂ :=
        corrected_congr F hq₁ hq₂ hmaps hS hcS₁ hcS₂ h11S₁ h11S₂ hS₁ hS₂
    _ = modelCurrentFlagValuation F π h₂ hh₂ L₂ hZ θ φ hφ := hval₂

/-- **Source `lma:modelvalcurrbir`, second sentence: birational invariance.** Let
`p : Z' ⟶ Z` be proper bimeromorphic, `Z'` unibranch. For every choice `h'` on `Z'` with respect
to the model `π ∘ p` and every choice `h` on `Z` with respect to `π`,
`ν_{Y•}(p^*S) = ν_{Y•}(S)`, where `p^*S = p^*θ + ddᶜ(φ ∘ p)`. -/
theorem modelCurrentFlagValuation_pullback (π : Z ⟶ wholeModel (n := m + 1) F.carrier)
    (hπ : IsProperBimeromorphic π) {Z' : SourceReducedComplexSpace} (p : Z' ⟶ Z)
    (hp : IsProperBimeromorphic p) {W W' : OriginalFlagGeometry.{0} (m + 1)}
    (h : wholeModel (n := m + 1) W.carrier ⟶ Z) (hh : IsProperBimeromorphic h)
    (L : IsFlagLifting F W (nativePointMap (h ≫ π)))
    (h' : wholeModel (n := m + 1) W'.carrier ⟶ Z') (hh' : IsProperBimeromorphic h')
    (L' : IsFlagLifting F W' (nativePointMap (h' ≫ (p ≫ π))))
    (hZ : Z.IsUnibranch) (hZ' : Z'.IsUnibranch) (θ : SpaceForm Z 2) (hθc : θ.IsClosed)
    (hθ11 : θ.IsOneOne) (φ : Z.obj.left → EReal) (hφ : Z.IsThetaPSH θ φ) :
    modelCurrentFlagValuation F (p ≫ π) h' hh' L' hZ' (SpaceForm.pullback θ p)
        (fun z => φ (p.hom.left.base z)) (hφ.pullback_of_isProperBimeromorphic hZ p hp) =
      modelCurrentFlagValuation F π h hh L hZ θ φ hφ := by
  have hassoc : nativePointMap (h' ≫ (p ≫ π)) = nativePointMap ((h' ≫ p) ≫ π) := by
    rw [Category.assoc]
  have L'' : IsFlagLifting F W' (nativePointMap ((h' ≫ p) ≫ π)) := hassoc ▸ L'
  have hh'' : IsProperBimeromorphic (h' ≫ p) :=
    isProperBimeromorphic_of_isAnalyticModification_comp hπ (h' ≫ p) L''.1
  have hstep : modelCurrentFlagValuation F (p ≫ π) h' hh' L' hZ' (SpaceForm.pullback θ p)
        (fun z => φ (p.hom.left.base z)) (hφ.pullback_of_isProperBimeromorphic hZ p hp) =
      modelCurrentFlagValuation F π (h' ≫ p) hh'' L'' hZ θ φ hφ := by
    unfold modelCurrentFlagValuation
    apply corrected_congr F L' L'' hassoc
    unfold modelPullbackCurrent
    apply thetaPotentialCurrent_congr
    · exact nativePullback_spacePullback_geometricallyEq θ p h'
    · rfl
  exact hstep.trans (modelCurrentFlagValuation_eq_of_choices F π (h' ≫ p) h hh'' hh L'' L hZ θ
    hθc hθ11 φ hφ)

/-! ### Existence of a choice from the Chow lemma -/

/-- **Existence of a choice, from Hironaka's Chow lemma.** For every reduced `Z` and proper
bimeromorphic `π`, the Chow lemma for compact complex manifolds gives a choice of `h` in
`def:modelvalcurr` (via `thm:liftableflag`, `OCLiftableFlag`). This is the only use of the Chow
lemma in `def:modelvalcurr` and `lma:modelvalcurrbir`. -/
theorem exists_choice_of_chow (hChow : HironakaChowLemma.HironakaChowLemmaManifold.{0})
    (π : Z ⟶ wholeModel (n := m + 1) F.carrier) (hπ : IsProperBimeromorphic π) :
    ∃ (W : OriginalFlagGeometry.{0} (m + 1)) (h : wholeModel (n := m + 1) W.carrier ⟶ Z),
      IsProperBimeromorphic h ∧ IsFlagLifting F W (nativePointMap (h ≫ π)) := by
  obtain ⟨W, σ, hσ, g, hg, hLift⟩ :=
    OCLiftableFlag.exists_flagLifting_dominating_reducedModel_of_chow hChow F Z π hπ
  have hmap : nativePointMap (g ≫ π) = σ := (congrArg nativePointMap hg).trans rfl
  have hLift' : IsFlagLifting F W (nativePointMap (g ≫ π)) := hmap ▸ hLift
  exact ⟨W, g, isProperBimeromorphic_of_isAnalyticModification_comp hπ g hLift'.1, hLift'⟩

end SGPT.Okounkov.OCModelCurrentValuation

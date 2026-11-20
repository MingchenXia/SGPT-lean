import SGPT.Checks.Comparison.BJModel2Dimension
import SGPT.Checks.Comparison.BJProjFormula
import SGPT.NAPotential.BJModel3Algebra
import SGPT.Foundations.Envelope.AlgGeom.FiniteSchemeNormalization
import SGPT.Foundations.Envelope.AlgGeom.NormalSchemeNormalization
import SGPT.Foundations.Envelope.AlgGeom.NormalizationAffineIsomorphism
import SGPT.Foundations.Envelope.AlgGeom.DominantCartierPullback
import SGPT.Foundations.Envelope.AlgGeom.CurveFiniteMapDegrees
import SGPT.Support.Alterations.Algebra.IntegralClosureFiniteType

/-!
# Normalized test configurations of flag ideals (lane BJ-MODEL3, step (a) of `claude-bj-model2:plan`)

Source: [BJ22] (`references/bj22-trivval`), §1.2 and §2.1 (proof of `thm:VCarPL`: "the
normalization `𝒳` of the blow-up of `X × 𝔸¹` along `𝔞` is a test configuration on which
`𝔞 · 𝒪_𝒳` is a vertical Cartier divisor"). Used for `thm:BJappseq` of `chapter_NApotential.tex`.
Blueprint: `claude-bj-model3.tex`.

For a flag ideal `𝔞` with weight bound `b` on an integral projective `k`-scheme `X`, let
`normModel p 𝔞 b` be the normalization (Mathlib's relative normalization of the generic point,
packaged by SGPT.Foundations.Envelope as `IntegralSchemeNormalization.normalization`) of the blow-up model
`flagModel p 𝔞 b = Bl_{t^b 𝔞}(X × ℙ¹)` of lane BJ-MODEL2, with `ν : normModel ⟶ flagModel`.

## Main results

* `exists_isIso_projection_restrict`: for every integral scheme locally of finite type over a
  field, the normalization is an isomorphism over a nonempty open set (generic normality,
  `SGPT.NAPotential.BJModel3.exists_isIntegrallyClosed_away`);
* `genericPoint_eq_and_bijective_of_isIso_restrict`: a morphism of integral schemes that is an
  isomorphism over a nonempty open maps generic point to generic point with bijective stalk map;
* `normModel_isIntegral`, `normModelν_isFinite`, `normModelStructure_isProjective`: the
  normalized model is integral, finite over the blow-up model and projective over `k`;
* `normModel_stalk_isIntegrallyClosed`: it is normal;
* `topologicalKrullDim_normModel`: it has the dimension of `X × ℙ¹` (so `≤ dim X + 1`);
* `isInvertible_comap_normModelπ`: `(t^b 𝔞) · 𝒪` is invertible on it;
* `interFormQ_normModel`: intersection numbers of `ℚ`-line bundles pulled back from the blow-up
  model are unchanged (BJ-PROJ's birational invariance).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.IntegralSchemeNormalization
open SGPT.NAPotential.BJModel SGPT.NAPotential.BJIntersect FlagIdealBound

/-! ### Generic isomorphism of the normalization -/

section generic

variable {k : Type u} [Field k]

/-- **The normalization is an isomorphism over a nonempty open set.** For an integral scheme `Z`
locally of finite type over a field, there is a nonempty (affine) open `V ⊆ Z` over which the
normalization `Z̃ ⟶ Z` is an isomorphism. -/
theorem exists_isIso_projection_restrict {Z : Scheme.{u}} [IsIntegral Z]
    (f : Z ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ V : Z.Opens, Nonempty V ∧ IsIso (projection Z ∣_ V) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint Z ∈ (⊤ : Z.Opens) from trivial) (⊤ : Z.Opens).isOpen
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  let := f.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(Z, U) := f.finiteType_sectionsAlgebra hU
  have : Module.Finite Γ(Z, U) (integralClosure Γ(Z, U) (FractionRing Γ(Z, U))) :=
    SGPT.Support.Alterations.Algebra.IntegralClosureFiniteType.finite_integralClosure
      k Γ(Z, U) (FractionRing Γ(Z, U))
  obtain ⟨d, hd, hS⟩ := SGPT.NAPotential.BJModel3.exists_isIntegrallyClosed_away (R := Γ(Z, U))
  have hV : IsAffineOpen (Z.basicOpen d) := hU.basicOpen d
  have hne : Nonempty (Z.basicOpen d) := by
    by_contra h
    apply hd
    rw [← AlgebraicGeometry.basicOpen_eq_bot_iff d]
    ext z
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hz => h ⟨⟨z, hz⟩⟩
  have : IsLocalization.Away d Γ(Z, Z.basicOpen d) := hU.isLocalization_basicOpen d
  have : IsIntegrallyClosed Γ(Z, Z.basicOpen d) := hS _
  exact ⟨Z.basicOpen d, hne, projection_isIso_on_affine Z (Z.basicOpen d) hV⟩

/-- A morphism of integral schemes which is an isomorphism over a nonempty open subset of the
target maps the generic point to the generic point, with bijective map of function fields. -/
theorem genericPoint_eq_and_bijective_of_isIso_restrict {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (h : Y ⟶ Z) (W : Z.Opens) [Nonempty W] [IsIso (h ∣_ W)] :
    h (genericPoint Y) = genericPoint Z ∧
      Function.Bijective (h.stalkMap (genericPoint Y)).hom := by
  have hV : Nonempty (h ⁻¹ᵁ W) := ⟨inv (h ∣_ W) (Classical.arbitrary W)⟩
  let x : h ⁻¹ᵁ W := genericPoint (h ⁻¹ᵁ W)
  have hx : (h ⁻¹ᵁ W).ι x = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgx : (h ∣_ W) x = genericPoint W := genericPoint_eq_of_isOpenImmersion _
  have hcomm : h ((h ⁻¹ᵁ W).ι x) = W.ι ((h ∣_ W) x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  refine ⟨?_, ?_⟩
  · rw [← hx, hcomm, hgx]
    exact genericPoint_eq_of_isOpenImmersion _
  · have h1 : IsIso ((h ∣_ W).stalkMap x) := inferInstance
    have h2 : IsIso (h.stalkMap x.1) :=
      ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
        (morphismRestrictStalkMap h W x)).mp h1
    have h3 : Function.Bijective (h.stalkMap ((h ⁻¹ᵁ W).ι x)).hom :=
      ConcreteCategory.bijective_of_isIso (h.stalkMap x.1)
    exact hx ▸ h3

end generic

/-! ### The normalized model -/

section model

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsProjective p] (𝔞 : FlagIdeal X) (b : ℤ)

/-- **The normalized model of a flag ideal** ([BJ22, §2.1]): the normalization of the blow-up
`Bl_{t^b 𝔞}(X × ℙ¹)`; it is the (compactified) test configuration of `𝔞`. -/
abbrev normModel : Scheme.{0} := normalization (flagModel p 𝔞 b)

/-- The normalization map `ν : normModel ⟶ flagModel`. -/
abbrev normModelν : normModel p 𝔞 b ⟶ flagModel p 𝔞 b := projection (flagModel p 𝔞 b)

/-- The map `normModel ⟶ X × ℙ¹`. -/
abbrev normModelπ : normModel p 𝔞 b ⟶ productLine p := normModelν p 𝔞 b ≫ flagModelπ p 𝔞 b

/-- The structure morphism of the normalized model over `k`. -/
abbrev normModelStructure : normModel p 𝔞 b ⟶ Spec (.of k) :=
  normModelν p 𝔞 b ≫ flagModelStructure p 𝔞 b

instance flagModelStructure_locallyOfFiniteType :
    LocallyOfFiniteType (flagModelStructure p 𝔞 b) := inferInstance

/-- **The normalized model is integral.** -/
instance normModel_isIntegral : IsIntegral (normModel p 𝔞 b) := inferInstance

/-- **The normalization of the model is finite** (SGPT.Foundations.Envelope, from the finiteness of
integral closures of finitely generated domains). -/
instance normModelν_isFinite : IsFinite (normModelν p 𝔞 b) :=
  projection_isFinite k (flagModel p 𝔞 b) (flagModelStructure p 𝔞 b)

/-- **The normalized model is projective over `k`** (polynomial projective factorization). -/
theorem normModelStructure_isProjectiveFactorization :
    IsProjectiveFactorization (normModelStructure p 𝔞 b) :=
  CurveFiniteMapDegrees.finite_comp_projectiveFactorization _
    (flagModelStructure_isProjectiveFactorization p 𝔞 b) (normModelν p 𝔞 b)

instance normModelStructure_isProjective : IsProjective (normModelStructure p 𝔞 b) :=
  NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization _
    (normModelStructure_isProjectiveFactorization p 𝔞 b)

instance normModelStructure_isProper : IsProper (normModelStructure p 𝔞 b) :=
  (normModelStructure_isProjectiveFactorization p 𝔞 b).isProper

instance normModel_compactSpace : CompactSpace (normModel p 𝔞 b) :=
  QuasiCompact.compactSpace_of_compactSpace (normModelStructure p 𝔞 b)

instance normModel_isSeparated : (normModel p 𝔞 b).IsSeparated :=
  ⟨by
    have h : IsSeparated (normModelStructure p 𝔞 b ≫ terminal.from (Spec (.of k))) :=
      inferInstance
    simpa only [terminal.comp_from] using h⟩

instance normModelπ_isProper : IsProper (normModelπ p 𝔞 b) := inferInstance

/-- **The normalized model is normal**: all its local rings are integrally closed. -/
theorem normModel_stalk_isIntegrallyClosed (z : normModel p 𝔞 b) :
    IsIntegrallyClosed ((normModel p 𝔞 b).presheaf.stalk z) :=
  stalk_isIntegrallyClosed (flagModel p 𝔞 b) z

/-- The normalization of the model is surjective. -/
theorem normModelν_surjective : Function.Surjective (normModelν p 𝔞 b) :=
  projection_surjective (flagModel p 𝔞 b)

/-- **The normalization is an isomorphism over a nonempty open subset of the model.** -/
theorem exists_isIso_normModelν_restrict :
    ∃ V : (flagModel p 𝔞 b).Opens, Nonempty V ∧ IsIso (normModelν p 𝔞 b ∣_ V) :=
  exists_isIso_projection_restrict (flagModelStructure p 𝔞 b)

/-- **The normalized model has the dimension of the model**, i.e. of `X × ℙ¹`. -/
theorem topologicalKrullDim_normModel :
    topologicalKrullDim (normModel p 𝔞 b) = topologicalKrullDim (flagModel p 𝔞 b) := by
  obtain ⟨V, hV, hiso⟩ := exists_isIso_normModelν_restrict p 𝔞 b
  obtain ⟨h1, h2⟩ := genericPoint_eq_and_bijective_of_isIso_restrict (normModelν p 𝔞 b) V
  exact topologicalKrullDim_eq_of_stalkMap_genericPoint (normModelStructure p 𝔞 b)
    (flagModelStructure p 𝔞 b) (normModelν p 𝔞 b) rfl h1 h2

/-- **The normalized model of a flag ideal on `X` of dimension `≤ n` has dimension `≤ n + 1`.** -/
theorem topologicalKrullDim_normModel_le (n : ℕ) (hX : topologicalKrullDim X ≤ n) :
    topologicalKrullDim (normModel p 𝔞 b) ≤ (n + 1 : ℕ) := by
  rw [topologicalKrullDim_normModel]
  exact topologicalKrullDim_flagModel_le p 𝔞 b n hX

/-- **`(t^b 𝔞) · 𝒪` is invertible on the normalized model** (pull-back of a Cartier divisor along
the dominant normalization). -/
theorem isInvertible_comap_normModelπ :
    ((flagSheaf p 𝔞 b).comap (normModelπ p 𝔞 b)).IsInvertible := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact cartier_comap (flagModel p 𝔞 b) (isInvertible_comap_flagSheaf p 𝔞 b)

/-- More generally every invertible ideal sheaf of the model stays invertible on the normalized
model. -/
theorem isInvertible_comap_normModelν {J : (flagModel p 𝔞 b).IdealSheafData}
    (hJ : J.IsInvertible) : (J.comap (normModelν p 𝔞 b)).IsInvertible :=
  cartier_comap (flagModel p 𝔞 b) hJ

/-- **Intersection numbers do not change under normalization** (BJ-PROJ's birational invariance,
`interFormQ_pullback_eq_of_isIso_restrict`): for `ℚ`-line bundles `θᵢ` on the model,
`(ν^*θ₁ ⋯ ν^*θ_d)_{normModel} = (θ₁ ⋯ θ_d)_{flagModel}` whenever both dimensions are `≤ d`. -/
theorem interFormQ_normModel (d : ℕ) (hd : topologicalKrullDim (flagModel p 𝔞 b) ≤ d)
    (s : Multiset (PicQ (flagModel p 𝔞 b))) :
    interFormQ (normModelStructure p 𝔞 b) d ((topologicalKrullDim_normModel p 𝔞 b).trans_le hd)
        (Scheme.Modules.unitObj _) (s.map (picPullbackQ (normModelν p 𝔞 b))) =
      interFormQ (flagModelStructure p 𝔞 b) d hd (Scheme.Modules.unitObj _) s := by
  obtain ⟨V, hV, hiso⟩ := exists_isIso_normModelν_restrict p 𝔞 b
  exact BJProj.interFormQ_pullback_eq_of_isIso_restrict (flagModelStructure p 𝔞 b)
    (normModelν p 𝔞 b) d hd _ V s

end model

end SGPT.NAPotential.BJ

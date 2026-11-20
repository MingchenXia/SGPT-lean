import SGPT.Checks.Comparison.BJModel3Normal
import SGPT.Support.Alterations.Geometry.RationalCoordinateMapGenericFiberOpenDimension
import SGPT.Support.Alterations.Algebra.AffinePrimeDimension

/-!
# Dimensions of the models and of closures of codimension-one points

Source: [BJ22] (`references/bj22-trivval`), §1.2 (a test configuration of an `n`-dimensional `X`
has dimension `n + 1`) and the dimension formula `ht 𝔭 + dim A/𝔭 = dim A` for finitely generated
domains over a field. Towards the hypothesis `RelAmplePositive` of `bjAppSeq_of_cycleLowerBound`
(`thm:BJappseq` of `chapter_NApotential.tex`). Blueprint: `claude-bj-relample.tex`.

* `topologicalKrullDim_pullback_mvPolynomial_eq`: `dim (Spec A ×_k 𝔸^σ) = dim A + |σ|`;
* `topologicalKrullDim_productLine_eq`: `dim (X × ℙ¹) = dim X + 1` for an integral projective `X`;
* `topologicalKrullDim_normModel_eq`: the normalized blow-up models have dimension `dim X + 1`;
* `le_topologicalKrullDim_of_coheight_eq_one`: on an integral scheme of finite type over a field of
  dimension `n + 1`, every closed subscheme with underlying set `closure {z}` for a point `z` of
  codimension one has dimension `≥ n` (the dimension formula on an affine chart).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order Topology
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry

/-! ### `dim (X × ℙ¹) = dim X + 1` -/

section product

universe u

variable {k : Type u} [Field k]

/-- `dim (Spec A ×_k Spec k[σ]) = dim A + |σ|` for a Noetherian `k`-algebra `A` and a finite set of
variables `σ`. -/
theorem topologicalKrullDim_pullback_mvPolynomial_eq (R : CommRingCat.{u}) [IsNoetherianRing R]
    (φ : Spec R ⟶ Spec (.of k)) (σ : Type) [Finite σ] (d : ℕ) (hR : ringKrullDim R = d) :
    topologicalKrullDim (pullback φ (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial σ k)))) : Scheme.{u}) = (d + Nat.card σ : ℕ) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ, φ = Spec.map ψ := ⟨Spec.preimage φ, (Spec.map_preimage φ).symm⟩
  let : Algebra k R := ψ.hom.toAlgebra
  have hψ : ψ = CommRingCat.ofHom (algebraMap k R) := rfl
  let e₁ := pullback.congrHom (congrArg Spec.map hψ) rfl ≪≫
    pullbackSpecIso k R (MvPolynomial σ k)
  have h1 := topologicalKrullDim_le_of_isOpenImmersion e₁.hom
  have h2 := topologicalKrullDim_le_of_isOpenImmersion e₁.inv
  have h3 : topologicalKrullDim (Spec (.of (TensorProduct k R (MvPolynomial σ k)))) =
      (d + Nat.card σ : ℕ) := by
    change topologicalKrullDim (PrimeSpectrum (TensorProduct k R (MvPolynomial σ k))) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv k R).toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, hR]
    push_cast
    rfl
  exact le_antisymm (h1.trans h3.le) (h3.ge.trans h2)

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- **`dim (X × ℙ¹) ≥ dim X + 1`** for an integral `X` locally of finite type over `k`: the chart
`Spec Γ(X, U) ×_k 𝔸¹` of an affine open `U ≠ ∅` is open in `X × ℙ¹` and has dimension
`dim Γ(X, U) + 1 = dim X + 1`. -/
theorem le_topologicalKrullDim_productLine [IsIntegral X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType p] (n : ℕ) (hX : topologicalKrullDim X = n) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (productLine p) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).isOpen
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.primeIdealOf ⟨_, hηU⟩⟩
  have hR : ringKrullDim Γ(X, U) = n := by
    have h := FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion p hU.fromSpec
    change topologicalKrullDim (PrimeSpectrum Γ(X, U)) = _ at h
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hX] at h
  have hj := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (f := hU.fromSpec ≫ p)
    (g := Segre.coordinateChartInclusion (R := k) (0 : Fin (1 + 1)) ≫ projectiveSpaceStructure k 1)
    (f' := p) (g' := projectiveSpaceStructure k 1) (i₁ := hU.fromSpec)
    (i₂ := Segre.coordinateChartInclusion (R := k) (0 : Fin (1 + 1))) inferInstance inferInstance
    rfl rfl
  have hle := @topologicalKrullDim_le_of_isOpenImmersion _ _ _ hj
  have hc : Nat.card {l : Fin 2 // l ≠ 0} = 1 :=
    (Nat.card_congr (finSuccAboveEquiv (0 : Fin 2))).symm.trans (by simp)
  have h := topologicalKrullDim_pullback_mvPolynomial_eq Γ(X, U) (hU.fromSpec ≫ p)
    {l : Fin 2 // l ≠ 0} n hR
  rw [hc] at h
  have h' : topologicalKrullDim (pullback (hU.fromSpec ≫ p)
      (Segre.coordinateChartInclusion (R := k) (0 : Fin (1 + 1)) ≫
        projectiveSpaceStructure k 1) : Scheme.{u}) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [Segre.coordinateChartInclusion_structure]
    exact h
  rw [← h']
  exact hle

/-- **`dim (X × ℙ¹) = dim X + 1`** for an integral `X` locally of finite type over `k`. -/
theorem topologicalKrullDim_productLine_eq [IsIntegral X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType p] (n : ℕ) (hX : topologicalKrullDim X = n) :
    topologicalKrullDim (productLine p) = (n + 1 : ℕ) :=
  le_antisymm (topologicalKrullDim_productLine_le p n hX.le)
    (le_topologicalKrullDim_productLine p n hX)

end product

/-! ### The normalized models -/

section model

open SGPT.NAPotential.BJModel

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsProjective p]

local instance relAmpleDim_isProper : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **The normalized model of a flag ideal on an `n`-dimensional `X` has dimension `n + 1`**
([BJ22, §1.2]). -/
theorem topologicalKrullDim_normModel_eq (𝔞 : FlagIdeal X) (b : ℤ) (n : ℕ)
    (hX : topologicalKrullDim X = n) : topologicalKrullDim (normModel p 𝔞 b) = (n + 1 : ℕ) := by
  let := isLocallyNoetherian_of_isProjective p
  rw [topologicalKrullDim_normModel, topologicalKrullDim_flagModel]
  exact topologicalKrullDim_productLine_eq p n hX

end model

/-! ### Closures of codimension-one points -/

section closure

variable {k : Type} [Field k]

/-- A point of codimension one is not the generic point. -/
theorem ne_genericPoint_of_coheight_eq_one {Y : Scheme.{0}} [IsIntegral Y] {z : Y}
    (hz : coheight z = 1) : z ≠ genericPoint Y := by
  rintro rfl
  have h : coheight (genericPoint Y) = 0 := by
    rw [Order.coheight_eq_zero]
    intro y _
    rw [Scheme.le_iff_specializes]
    exact genericPoint_specializes y
  rw [h] at hz
  exact zero_ne_one hz

/-- **The closure of a codimension-one point of an `(n + 1)`-dimensional variety has dimension
`≥ n`**: on an affine chart `Spec A ∋ z`, `z` is a prime `𝔭` of height one, so
`dim A/𝔭 = dim A - 1 = n` (de Jong's dimension formula), and `Spec A/𝔭` embeds into every closed
subscheme with underlying set `closure {z}`. -/
theorem le_topologicalKrullDim_of_coheight_eq_one {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q] {n : ℕ}
    (hY : topologicalKrullDim Y = (n + 1 : ℕ)) {z : Y} (hz : coheight z = 1) {Z : Scheme.{0}}
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (hι : Set.range ι = closure {z}) :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show z ∈ (⊤ : Y.Opens) from trivial) (⊤ : Y.Opens).isOpen
  let := q.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(Y, U) := q.finiteType_sectionsAlgebra hU
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  let x := hU.primeIdealOf ⟨z, hzU⟩
  set P := x.asIdeal with hPdef
  have : Nonempty (Spec Γ(Y, U)) := ⟨x⟩
  have hdimA : ringKrullDim Γ(Y, U) = (n + 1 : ℕ) := by
    have h := FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion q hU.fromSpec
    change topologicalKrullDim (PrimeSpectrum Γ(Y, U)) = _ at h
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hY] at h
  have hP : P.height = 1 := by
    let := Y.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
    have : IsLocalization.AtPrime (Y.presheaf.stalk z) P := hU.isLocalization_stalk ⟨z, hzU⟩
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Y.presheaf.stalk z), hz] at h1
    exact_mod_cast h1
  have hform :=
    SGPT.Support.Alterations.Algebra.AffinePrimeDimension.height_add_quotient_dimension k Γ(Y, U) P
  -- the quotient `A/𝔭` has finite dimension, computed by its transcendence degree
  let : Algebra.FiniteType k (Γ(Y, U) ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  have hfin : Algebra.trdeg k (Γ(Y, U) ⧸ P) < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  let : FaithfulSMul (Γ(Y, U) ⧸ P) P.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr P.injective_algebraMap_quotient_residueField
  let : FaithfulSMul k (Γ(Y, U) ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k (Γ(Y, U) ⧸ P)).injective
  let : Algebra.IsAlgebraic (Γ(Y, U) ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic P.ResidueField (nonZeroDivisors (Γ(Y, U) ⧸ P))
  have heq : Algebra.trdeg k (Γ(Y, U) ⧸ P) = Algebra.trdeg k P.ResidueField := by
    have h := trdeg_add_eq k (Γ(Y, U) ⧸ P) (A := P.ResidueField)
    rwa [trdeg_eq_zero (R := Γ(Y, U) ⧸ P), add_zero] at h
  obtain ⟨d', hd'⟩ := Cardinal.lt_aleph0.mp (heq ▸ hfin)
  have hdimQ := SGPT.Foundations.Envelope.SchemeFunctionFieldDimension.affine_dimension_eq k (Γ(Y, U) ⧸ P)
    P.ResidueField d' hd'
  have hd'n : d' = n := by
    rw [hP, hdimQ, hdimA] at hform
    have : (1 : WithBot ℕ∞) + (d' : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast hform
    have h2 : 1 + d' = n + 1 := by exact_mod_cast this
    omega
  -- `Spec A/𝔭 ⟶ Spec A ⟶ Y` is an embedding onto a subset of `closure {z}`
  let F : PrimeSpectrum (Γ(Y, U) ⧸ P) → Y := fun y =>
    hU.fromSpec (PrimeSpectrum.comap (Ideal.Quotient.mk P) y)
  have hF : IsEmbedding F :=
    hU.fromSpec.isOpenEmbedding.isEmbedding.comp
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).isEmbedding
  have hFι : ∀ y, F y ∈ Set.range ι := by
    intro y
    rw [hι]
    apply specializes_iff_mem_closure.mp
    have h1 : x ⤳ PrimeSpectrum.comap (Ideal.Quotient.mk P) y := by
      rw [← PrimeSpectrum.le_iff_specializes]
      intro a ha
      change Ideal.Quotient.mk P a ∈ y.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact zero_mem _
    have h2 := h1.map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at h2
  choose g hg using hFι
  have hgι : (ι : Z → Y) ∘ g = F := funext hg
  have hge : IsEmbedding g := by
    rw [← IsEmbedding.of_comp_iff ι.isClosedEmbedding.isEmbedding, hgι]
    exact hF
  have hle := hge.isInducing.topologicalKrullDim_le
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdimQ, hd'n] at hle
  exact hle

end closure

end SGPT.NAPotential.BJ

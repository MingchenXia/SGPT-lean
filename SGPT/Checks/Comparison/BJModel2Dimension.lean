import SGPT.Checks.Comparison.BJModel2TestConfig
import SGPT.Foundations.Envelope.AlgGeom.IntegralSchemeDimension
import SGPT.Foundations.Envelope.AlgGeom.SchemeFunctionFieldDimension
import SGPT.Support.Alterations.Geometry.SegreGluing
import SGPT.Support.Principalization.Algebra.RegularSmooth.Stalk
import SGPT.Support.Principalization.Scheme.IdealSheaf.Derivative.Pullback

/-!
# Dimension of `X × ℙ¹` and of the blow-up models (lane BJ-MODEL2, step R1(a), R1(c))

Source: [BJ22] (`references/bj22-trivval`), §1.2: a test configuration of an `n`-dimensional
variety `X` is a variety of dimension `n + 1`; its intersection numbers ([BJ22, §3.2]) are the
top intersection numbers in dimension `n + 1`. Blueprint: `claude-bj-model2.tex`.

* `topologicalKrullDim_productLine_le`: `dim (X × ℙ¹) ≤ dim X + 1` for `X` locally Noetherian
  (cover by `Spec (A ⊗_k k[t])`, `A` Noetherian with `dim A ≤ dim X`, and
  `dim A[t] = dim A + 1`);
* `topologicalKrullDim_eq_of_stalkMap_genericPoint`: two integral schemes locally of finite type
  over `k` that are birational (a `k`-morphism mapping the generic point to the generic point with
  bijective map of function fields) have the same dimension (both are the transcendence degree of
  the function field; SGPT.Foundations.Envelope's `SchemeFunctionFieldDimension`);
* `topologicalKrullDim_flagModel_le`: the blow-up model of a flag ideal on an integral projective
  `X` of dimension `≤ n` has dimension `≤ n + 1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### `dim (X × ℙ¹) ≤ dim X + 1` -/

section product

variable {k : Type u} [Field k]

/-- The dimension of an open subscheme is at most the dimension of the scheme. -/
theorem topologicalKrullDim_le_of_isOpenImmersion {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] : topologicalKrullDim Y ≤ topologicalKrullDim Z :=
  f.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le

/-- `dim (Spec A ×_k Spec k[σ]) ≤ dim A + |σ|` for a Noetherian `k`-algebra `A` and a finite set
of variables `σ`. -/
theorem topologicalKrullDim_pullback_mvPolynomial_le (R : CommRingCat.{u}) [IsNoetherianRing R]
    (φ : Spec R ⟶ Spec (.of k)) (σ : Type) [Finite σ] (d : ℕ)
    (hR : ringKrullDim R ≤ d) :
    topologicalKrullDim (pullback φ (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial σ k)))) : Scheme.{u}) ≤ (d + Nat.card σ : ℕ) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ, φ = Spec.map ψ := ⟨Spec.preimage φ, (Spec.map_preimage φ).symm⟩
  let : Algebra k R := ψ.hom.toAlgebra
  have hψ : ψ = CommRingCat.ofHom (algebraMap k R) := rfl
  let e₁ := pullback.congrHom (congrArg Spec.map hψ) rfl ≪≫
    pullbackSpecIso k R (MvPolynomial σ k)
  refine (topologicalKrullDim_le_of_isOpenImmersion e₁.hom).trans ?_
  change topologicalKrullDim (PrimeSpectrum (TensorProduct k R (MvPolynomial σ k))) ≤ _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv k R).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing]
  push_cast
  exact add_le_add_left hR _

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- **`dim (X × ℙ¹) ≤ dim X + 1`** for `X` locally Noetherian over `k`. -/
theorem topologicalKrullDim_productLine_le [IsLocallyNoetherian X] (n : ℕ)
    (hX : topologicalKrullDim X ≤ n) : topologicalKrullDim (productLine p) ≤ (n + 1 : ℕ) := by
  apply SGPT.Foundations.Envelope.IntegralSchemeDimension.topologicalKrullDim_le_of_openCover _ (n + 1)
    (Scheme.Pullback.openCoverOfLeftRight X.affineOpenCover.openCover
      (Segre.coordinateCover k 1) p (projectiveSpaceStructure k 1))
  rintro ⟨i, j⟩
  change Fin 2 at j
  let R := X.affineOpenCover.X i
  let f : Spec R ⟶ X := X.affineOpenCover.f i
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  have hR : ringKrullDim R ≤ n := by
    have h := (topologicalKrullDim_le_of_isOpenImmersion f).trans hX
    change topologicalKrullDim (PrimeSpectrum R) ≤ n at h
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  have hc : Nat.card {l : Fin 2 // l ≠ j} = 1 :=
    (Nat.card_congr (finSuccAboveEquiv j)).symm.trans (by simp)
  have h := topologicalKrullDim_pullback_mvPolynomial_le R (f ≫ p) {l : Fin 2 // l ≠ j} n hR
  rw [hc] at h
  change topologicalKrullDim (pullback (f ≫ p)
    (Segre.coordinateChartInclusion (R := k) j ≫ projectiveSpaceStructure k 1) : Scheme.{u}) ≤ _
  rw [Segre.coordinateChartInclusion_structure]
  exact h

end product

/-! ### Birational invariance of the dimension -/

section birational

variable {k : Type u} [Field k]

/-- An integral scheme locally of finite type over `k` has finite transcendence degree, equal to
its dimension. -/
theorem exists_trdeg_eq_and_dim_eq {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    ∃ d : ℕ, (letI := f.stalkAlgebra (genericPoint Y);
      Algebra.trdeg k (Y.presheaf.stalk (genericPoint Y)) = d) ∧ topologicalKrullDim Y = d := by
  let := f.stalkAlgebra (genericPoint Y)
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial) (⊤ : Y.Opens).isOpen
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  let := f.sectionsAlgebra U
  have : IsScalarTower k Γ(Y, U) Y.functionField := f.isScalarTower_sectionsAlgebra_stalk U hx
  have : Algebra.FiniteType k Γ(Y, U) := f.finiteType_sectionsAlgebra hU
  have : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic Y.functionField (nonZeroDivisors Γ(Y, U))
  have : FaithfulSMul Γ(Y, U) Y.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  have heq : Algebra.trdeg k Γ(Y, U) = Algebra.trdeg k Y.functionField := by
    have h := trdeg_add_eq k Γ(Y, U) (A := Y.functionField)
    rwa [trdeg_eq_zero (R := Γ(Y, U)) (A := Y.functionField), add_zero] at h
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := Γ(Y, U)))
  have htr : Algebra.trdeg k Y.functionField = d := heq ▸ hd
  exact ⟨d, htr, SGPT.Foundations.Envelope.SchemeFunctionFieldDimension.topologicalKrullDim_eq f d htr⟩

/-- **Birational invariance of the dimension.** Let `h : Y ⟶ Z` be a morphism over `k` of integral
schemes locally of finite type over `k`, mapping the generic point of `Y` to the generic point of
`Z`, whose map of function fields is bijective. Then `dim Y = dim Z`. -/
theorem topologicalKrullDim_eq_of_stalkMap_genericPoint {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (fY : Y ⟶ Spec (.of k)) (fZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType fY]
    [LocallyOfFiniteType fZ] (h : Y ⟶ Z) (hf : h ≫ fZ = fY)
    (hη : h (genericPoint Y) = genericPoint Z)
    (hbij : Function.Bijective (h.stalkMap (genericPoint Y)).hom) :
    topologicalKrullDim Y = topologicalKrullDim Z := by
  subst hf
  obtain ⟨d, hdtr, hd⟩ := exists_trdeg_eq_and_dim_eq fZ
  rw [hd]
  apply SGPT.Foundations.Envelope.SchemeFunctionFieldDimension.topologicalKrullDim_eq (h ≫ fZ) d
  rw [← hη] at hdtr
  let := fZ.stalkAlgebra (h (genericPoint Y))
  let := (h ≫ fZ).stalkAlgebra (genericPoint Y)
  let e : Z.presheaf.stalk (h (genericPoint Y)) ≃ₐ[k] Y.functionField :=
    { RingEquiv.ofBijective (h.stalkMap (genericPoint Y)).hom hbij with
      commutes' := fun c =>
        RingHom.congr_fun (Scheme.Hom.stalkMap_comp_algebraMap_stalkAlgebra fZ h _) c }
  rw [← e.trdeg_eq]
  exact hdtr

end birational

/-! ### Dimension of the blow-up models -/

section model

open SGPT.NAPotential.BJModel

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (.of k)) (𝔞 : FlagIdeal X) (b : ℤ)

/-- **The blow-down is birational**: it maps the generic point of the model to the generic point
of `X × ℙ¹`, and its map of function fields is bijective (it is an isomorphism over the dense open
complement of the cosupport of `t^b 𝔞`). -/
theorem flagModelπ_genericPoint [IsIntegral X] [IsProjective p] :
    flagModelπ p 𝔞 b (genericPoint (flagModel p 𝔞 b)) = genericPoint (productLine p) ∧
      Function.Bijective ((flagModelπ p 𝔞 b).stalkMap (genericPoint (flagModel p 𝔞 b))).hom := by
  let := productLine_isIntegral_of_isProjective p
  let W : (productLine p).Opens := (flagSheaf p 𝔞 b).support.compl
  let π := flagModelπ p 𝔞 b
  let : IsIso (π ∣_ W) := flagModelπ_isIso_restrict p 𝔞 b
  have hW : Nonempty W := by
    by_contra hne
    apply support_flagSheaf_ne_top p 𝔞 b
    ext z
    simp only [TopologicalSpace.Closeds.coe_top, Set.mem_univ, iff_true]
    by_contra hz
    exact hne ⟨⟨z, hz⟩⟩
  have hV : Nonempty (π ⁻¹ᵁ W) := ⟨inv (π ∣_ W) hW.some⟩
  let x : π ⁻¹ᵁ W := genericPoint (π ⁻¹ᵁ W)
  have hx : (π ⁻¹ᵁ W).ι x = genericPoint (flagModel p 𝔞 b) :=
    genericPoint_eq_of_isOpenImmersion _
  have hgx : (π ∣_ W) x = genericPoint W := genericPoint_eq_of_isOpenImmersion _
  have hcomm : π ((π ⁻¹ᵁ W).ι x) = W.ι ((π ∣_ W) x) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  refine ⟨?_, ?_⟩
  · rw [← hx, hcomm, hgx]
    exact genericPoint_eq_of_isOpenImmersion _
  · have h1 : IsIso ((π ∣_ W).stalkMap x) := inferInstance
    have h2 : IsIso (π.stalkMap x.1) :=
      ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
        (morphismRestrictStalkMap π W x)).mp h1
    have h3 : Function.Bijective (π.stalkMap ((π ⁻¹ᵁ W).ι x)).hom :=
      ConcreteCategory.bijective_of_isIso (π.stalkMap x.1)
    exact hx ▸ h3

/-- **The model has the dimension of `X × ℙ¹`.** -/
theorem topologicalKrullDim_flagModel [IsIntegral X] [IsProjective p] :
    topologicalKrullDim (flagModel p 𝔞 b) = topologicalKrullDim (productLine p) := by
  let := productLine_isIntegral_of_isProjective p
  obtain ⟨h1, h2⟩ := flagModelπ_genericPoint p 𝔞 b
  exact topologicalKrullDim_eq_of_stalkMap_genericPoint (flagModelStructure p 𝔞 b)
    (productStructure p) (flagModelπ p 𝔞 b) rfl h1 h2

/-- **The model of a flag ideal on an integral projective `X` of dimension `≤ n` has dimension
`≤ n + 1`** ([BJ22, §1.2]). -/
theorem topologicalKrullDim_flagModel_le [IsIntegral X] [IsProjective p] (n : ℕ)
    (hX : topologicalKrullDim X ≤ n) : topologicalKrullDim (flagModel p 𝔞 b) ≤ (n + 1 : ℕ) := by
  let := isLocallyNoetherian_of_isProjective p
  rw [topologicalKrullDim_flagModel]
  exact topologicalKrullDim_productLine_le p n hX

end model

end SGPT.NAPotential.BJ

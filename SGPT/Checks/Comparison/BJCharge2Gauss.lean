import SGPT.Checks.Comparison.BJCharge2Rees
import SGPT.Checks.Comparison.BJModel2GaussCentral
import SGPT.Checks.Comparison.BJModel3Normal


/-!
# The Gauss point on the normalized flag model (lane BJ-CHARGE, step R8(c)(i))

Source: [BJ22] (`references/bj22-trivval`), §1.3, §2.1 and the proof of Lemma `lem:tcdiv`: the
Gauss extension `σ(v)` of a valuation `v` of `ℂ(X)` is a valuation of `ℂ(X)(t) = ℂ(X × ℙ¹)`, hence
a point of the normalized test configurations. Towards `thm:BJappseq` of
`chapter_NApotential.tex`. Blueprint: `claude-bj-charge2.tex`.

* `range_fieldEmb_comp_subset`, `range_fieldEmb_fromSpecResidueField`: images of residue
  embeddings of field-valued points;
* `algebraicIndependent_gaussFamily_one`: `t` is transcendental over `K` in `K(t)`;
* `coheight_add_card_le`, `eq_genericPoint_of_coheight_eq_zero`: codimension versus residue
  transcendence degree;
* `fieldPt_gaussMap_eq_genericPoint`, `fieldPt_gaussModelMap_eq_genericPoint`: **the Gauss point
  of a valuation of `ℂ(X)` is the generic point** of `X × ℙ¹` and of every flag model;
* `exists_gaussNormMap`: it lifts to the normalized model, generically;
* `center_fieldBerkovichPoint_comp`, `center_fieldBerkovichPoint_fromSpecResidueField`,
  `fieldEmb_specializationMap_of_eq`, `fieldEmb_specializationMap_stalkMap`: centres and images of
  germs for field-valued points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BerkovichPoint
open SGPT.NAPotential.BJCharge SGPT.NAPotential.BJModel
open scoped Polynomial

/-! ### Ranges of residue embeddings of field-valued points -/

section range

variable {Y : Scheme.{0}} {L : Type} [Field L]

theorem range_fieldEmb_comp_subset {Z : Scheme.{0}} (g : Spec (.of L) ⟶ Y) (h : Y ⟶ Z) :
    Set.range (fieldEmb (g ≫ h)).hom ⊆ Set.range (fieldEmb g).hom := by
  rw [fieldEmb_comp]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, rfl⟩

theorem range_fieldEmb_fromSpecResidueField (y : Y) (φ : Y.residueField y ⟶ .of L) :
    Set.range (fieldEmb (Spec.map φ ≫ Y.fromSpecResidueField y)).hom = Set.range φ.hom := by
  have hσ : (Scheme.SpecToEquivOfField L Y) (Spec.map φ ≫ Y.fromSpecResidueField y) = ⟨y, φ⟩ :=
    (Scheme.SpecToEquivOfField L Y).apply_symm_apply ⟨y, φ⟩
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hσ
  have key : ∀ (x : Y) (e : x = y) (η : Y.residueField x ⟶ .of L),
      η = (Y.residueFieldCongr e).hom ≫ φ → Set.range η.hom = Set.range φ.hom := by
    intro x e η hη
    subst e hη
    rw [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp]
  exact key _ e _ he

end range

/-! ### The Gauss point is generic -/

section generic

variable {K : Type} [Field K] [Algebra ℂ K]

/-- `t` and the elements of `K` are independent: `(u, t)` is algebraically independent in `K(t)`
when `u` is. -/
theorem algebraicIndependent_gaussFamily_one {ι : Type*} {u : ι → K}
    (hu : AlgebraicIndependent ℂ u) : AlgebraicIndependent ℂ (gaussFamily u 1 1) := by
  rw [algebraicIndependent_iff]
  intro P hP
  rw [aeval_gaussFamily] at hP
  have h0 := (map_eq_zero_iff _ (IsFractionRing.injective K[X] (FractionRing K[X]))).mp hP
  set Q := MvPolynomial.optionEquivLeft ℂ ι P
  have hQ : Q = 0 := by
    refine Polynomial.ext fun k => ?_
    by_cases hk : k < Q.natDegree + 1
    · have hc := congrArg (fun F : K[X] => F.coeff k) h0
      simp only [Polynomial.coeff_zero] at hc
      rw [coeff_gaussPoly _ _ one_pos, if_pos ⟨one_dvd _, by simpa using hk⟩] at hc
      simp only [Nat.div_one, one_pow, div_one] at hc
      rw [Polynomial.coeff_zero]
      exact (algebraicIndependent_iff.mp hu) _ hc
    · rw [Polynomial.coeff_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by push Not at hk; omega)
  have := congrArg (MvPolynomial.optionEquivLeft ℂ ι).symm hQ
  rwa [AlgEquiv.symm_apply_apply, map_zero] at this

end generic

section coheight

variable {𝒳 : Scheme.{0}} [IsIntegral 𝒳] (q : 𝒳 ⟶ Spec (.of ℂ)) [LocallyOfFiniteType q]

/-- **Codimension and residue transcendence**: `coheight c + n ≤ dim 𝒳` when the residue field at
`c` contains `n` elements algebraically independent over `ℂ`. -/
theorem coheight_add_card_le (c : 𝒳) {n : ℕ}
    (x : Fin n → IsLocalRing.ResidueField (𝒳.presheaf.stalk c))
    (hx : letI := q.stalkAlgebra c; AlgebraicIndependent ℂ x) :
    (coheight c : WithBot ℕ∞) + (n : WithBot ℕ∞) ≤ topologicalKrullDim 𝒳 := by
  let := q.stalkAlgebra c
  obtain ⟨_, ⟨U, hU, rfl⟩, hc, -⟩ := 𝒳.isBasis_affineOpens.exists_subset_of_mem_open
    (show c ∈ (⊤ : 𝒳.Opens) from trivial) (⊤ : 𝒳.Opens).isOpen
  let := q.sectionsAlgebra U
  let := 𝒳.presheaf.algebra_section_stalk (⟨c, hc⟩ : U)
  have : Algebra.FiniteType ℂ Γ(𝒳, U) := q.finiteType_sectionsAlgebra hU
  have : Nonempty U := ⟨⟨c, hc⟩⟩
  set P := (hU.primeIdealOf ⟨c, hc⟩).asIdeal
  have : IsLocalization.AtPrime (𝒳.presheaf.stalk c) P := hU.isLocalization_stalk ⟨c, hc⟩
  let r := residueFieldAlgEquiv q hU hc
  have hP := height_add_card_le_ringKrullDim (k := ℂ) P (hx.map' (f := r.toAlgHom) r.injective)
  have hstalk : coheight c = P.height := by
    have h1 := ringKrullDim_stalk_eq_coheight c
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (𝒳.presheaf.stalk c)] at h1
    exact (WithBot.coe_injective h1).symm
  have hA : ringKrullDim Γ(𝒳, U) ≤ topologicalKrullDim 𝒳 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    have := hU.isOpenImmersion_fromSpec
    exact hU.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
  rw [hstalk]
  simpa [Nat.card_eq_fintype_card, Fintype.card_fin] using hP.trans hA

/-- A point of coheight `0` of an integral scheme is the generic point. -/
theorem eq_genericPoint_of_coheight_eq_zero {c : 𝒳} (h : coheight c = 0) : c = genericPoint 𝒳 := by
  rw [Order.coheight_eq_zero] at h
  have h1 : c ≤ genericPoint 𝒳 := by
    rw [Scheme.le_iff_specializes]
    exact genericPoint_specializes c
  exact (inseparable_iff_specializes_and.mpr
    ⟨Scheme.le_iff_specializes.mp (h h1), genericPoint_specializes c⟩).eq

end coheight

section gaussGeneric

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Spec (.of ℂ)} [IsProjective p]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

omit [IsProjective p] in
/-- A transcendence family of `ℂ(X)`, in the residue field of a point equal to the generic
point. -/
theorem exists_algebraicIndependent_residueField_of_eq_genericPoint (y : X)
    (hy : y = genericPoint X) {d : ℕ}
    (htr : letI := p.stalkAlgebra (genericPoint X)
      Algebra.trdeg ℂ (X.presheaf.stalk (genericPoint X)) = d) :
    ∃ k : Fin d → X.residueField y,
      letI := residueComplexAlgebra p y; AlgebraicIndependent ℂ k := by
  subst hy
  let := p.stalkAlgebra (genericPoint X)
  let := residueComplexAlgebra p (genericPoint X)
  let e : X.functionField ≃ₐ[ℂ] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective (X.residue (genericPoint X)).hom
        (residue_bijective_of_eq_genericPoint _ rfl) with
      commutes' := fun a => by
        have h := congrArg (fun φ => φ.hom a) (residueComplexHom_eq_stalkAlgebra p (genericPoint X))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h.symm }
  let : FaithfulSMul ℂ X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap ℂ X.functionField).injective
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis'.{0} ℂ X.functionField
  have hcard : Cardinal.mk ι = d := by rw [hx.cardinalMk_eq_trdeg, htr]
  obtain ⟨φ⟩ := Cardinal.mk_eq_nat_iff.mp hcard
  exact ⟨fun i => e (x (φ.symm i)), (hx.1.comp _ φ.symm.injective).map' (f := e.toAlgHom) e.injective⟩

/-- **The Gauss point is generic**: for a valuation `v` of `ℂ(X)` (support the generic point), the
field-valued point `Spec ℂ(X)(t) → X × ℙ¹` of the Gauss extension hits the generic point of
`X × ℙ¹` (its residue field contains a transcendence basis of `ℂ(X)` and `t`). -/
theorem fieldPt_gaussMap_eq_genericPoint (v : BerkovichPoint p) (hv : v.support = genericPoint X) :
    letI := residueComplexAlgebra p v.support
    fieldPt (gaussMap (K := X.residueField v.support) p (X.fromSpecResidueField v.support)
      (fromSpecResidueField_structure v)) = genericPoint (productLine p) := by
  let := residueComplexAlgebra p v.support
  let := productLine_isIntegral_of_isProjective p
  let := isLocallyNoetherian_of_isProjective p
  let g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ productLine p :=
    gaussMap (K := X.residueField v.support) p (X.fromSpecResidueField v.support)
      (fromSpecResidueField_structure v)
  obtain ⟨d, htr, hd⟩ := exists_trdeg_eq_and_dim_eq p
  obtain ⟨k, hk⟩ := exists_algebraicIndependent_residueField_of_eq_genericPoint v.support hv htr
  -- the elements `k_j` and `t` lie in the image of `κ(z) → K(t)`
  have hC : ∀ j, gaussFamily k 1 1 (some j) ∈ Set.range (fieldEmb g).hom := by
    intro j
    apply range_fieldEmb_comp_subset g (productFst p)
    rw [gaussMap_fst]
    change _ ∈ Set.range (fieldEmb (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField v.support)
      (FractionRing (X.residueField v.support)[X]))) ≫ X.fromSpecResidueField v.support)).hom
    rw [range_fieldEmb_fromSpecResidueField]
    refine ⟨k j, ?_⟩
    change algebraMap (X.residueField v.support) (FractionRing (X.residueField v.support)[X]) (k j) =
      algebraMap (X.residueField v.support)[X] _ (Polynomial.C (k j))
    rw [IsScalarTower.algebraMap_apply (X.residueField v.support) (X.residueField v.support)[X]
      (FractionRing (X.residueField v.support)[X]), Polynomial.algebraMap_apply]
    rfl
  have hX : gaussFamily k 1 1 none ∈ Set.range (fieldEmb g).hom := by
    apply range_fieldEmb_comp_subset g (productSnd p)
    rw [gaussMap_snd]
    obtain ⟨s, -, hs⟩ := exists_mem_stalkIdeal_zeroIdeal_stalkMap
    refine ⟨(specializationMap ((fieldPt_chartGauss_specializes (K := X.residueField v.support)).map
      (lineChart ℂ).continuous)).hom s, ?_⟩
    change (fieldEmb (chartGauss (X.residueField v.support) ≫ lineChart ℂ)).hom _ = _
    rw [fieldEmb_comp_specializationMap (chartGauss (X.residueField v.support)) (lineChart ℂ)
      fieldPt_chartGauss_specializes, hs, fieldEmb_chartGauss_germ, ΓSpecIso_hom_inv_apply]
    simp [gaussFamily, gaussRatio, gaussChartHom]
  choose x hx using fun o => (Option.rec hX hC o : gaussFamily k 1 1 o ∈ Set.range (fieldEmb g).hom)
  -- algebraic independence in the residue field at `z`
  let := residueComplexAlgebra (productStructure p) (fieldPt g)
  let φ : (productLine p).residueField (fieldPt g) →ₐ[ℂ] FractionRing (X.residueField v.support)[X] :=
    { (fieldEmb g).hom with
      commutes' := fun a => by
        have h := congrArg (fun ψ => ψ.hom a) (residueComplexHom_fieldEmb (productStructure p) g
          (gaussMap_structure (K := X.residueField v.support) p _ (fromSpecResidueField_structure v)))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h }
  have hxind : AlgebraicIndependent ℂ x := by
    apply AlgebraicIndependent.of_comp φ
    have : (φ ∘ x) = gaussFamily k 1 1 := funext hx
    rw [this]
    exact algebraicIndependent_gaussFamily_one hk
  -- the `ℂ`-structure of the residue field through the stalk
  let := (productStructure p).stalkAlgebra (fieldPt g)
  let ι : (productLine p).residueField (fieldPt g) →ₐ[ℂ]
      IsLocalRing.ResidueField ((productLine p).presheaf.stalk (fieldPt g)) :=
    { RingHom.id _ with
      commutes' := fun a => by
        have h := congrArg (fun ψ => ψ.hom a)
          (residueComplexHom_eq_stalkAlgebra (productStructure p) (fieldPt g))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h }
  have hx' : AlgebraicIndependent ℂ (ι ∘ x ∘ finSuccEquiv d) :=
    (hxind.comp _ (finSuccEquiv d).injective).map' (f := ι) (fun _ _ h => h)
  have hco := coheight_add_card_le (productStructure p) (fieldPt g) _ hx'
  have hdim := topologicalKrullDim_productLine_le p d hd.le
  have h0 : coheight (fieldPt g) = 0 := by
    have h1 := hco.trans hdim
    have h2 : (coheight (fieldPt g) : WithBot ℕ∞) + ((d + 1 : ℕ) : WithBot ℕ∞) ≤
        (0 : WithBot ℕ∞) + ((d + 1 : ℕ) : WithBot ℕ∞) := by simpa using h1
    have h3 : coheight (fieldPt g) + ((d + 1 : ℕ) : ℕ∞) ≤ 0 + ((d + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast h2
    exact le_antisymm ((WithTop.add_le_add_iff_right (ENat.natCast_ne_top _)).mp h3) bot_le
  exact eq_genericPoint_of_coheight_eq_zero h0

end gaussGeneric

section normGauss

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Spec (.of ℂ)} [IsProjective p]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **The Gauss point of the flag model is generic.** -/
theorem fieldPt_gaussModelMap_eq_genericPoint (v : BerkovichPoint p)
    (hv : v.support = genericPoint X) (𝔞 : FlagIdeal X) (b : ℤ) :
    letI := residueComplexAlgebra p v.support
    fieldPt (gaussModelMap (K := X.residueField v.support) p (X.fromSpecResidueField v.support)
      (fromSpecResidueField_structure v) 𝔞 b) = genericPoint (flagModel p 𝔞 b) := by
  let := residueComplexAlgebra p v.support
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
  obtain ⟨h1, -⟩ := flagModelπ_genericPoint p 𝔞 b
  have hηW : genericPoint (productLine p) ∈ W :=
    ((genericPoint_spec (productLine p)).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  set z := fieldPt (gaussModelMap (K := X.residueField v.support) p (X.fromSpecResidueField v.support)
      (fromSpecResidueField_structure v) 𝔞 b)
  have hz : π z = genericPoint (productLine p) := by
    rw [← fieldPt_gaussMap_eq_genericPoint v hv]
    rw [← gaussModelMap_π (K := X.residueField v.support) p _ (fromSpecResidueField_structure v) 𝔞 b]
    rfl
  have hm1 : z ∈ π ⁻¹ᵁ W := by change π z ∈ W; rw [hz]; exact hηW
  have hm2 : genericPoint (flagModel p 𝔞 b) ∈ π ⁻¹ᵁ W := by change π _ ∈ W; rw [h1]; exact hηW
  have hinj : Function.Injective (π ∣_ W) :=
    (ConcreteCategory.bijective_of_isIso ((π ∣_ W).base)).1
  have := @hinj ⟨_, hm1⟩ ⟨_, hm2⟩ (by
    apply Subtype.ext
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    rw [hz, h1])
  exact congrArg Subtype.val this

/-- **The Gauss point lifts to the normalized model** and its lift is generic. -/
theorem exists_gaussNormMap (v : BerkovichPoint p) (hv : v.support = genericPoint X)
    (𝔞 : FlagIdeal X) (b : ℤ) :
    letI := residueComplexAlgebra p v.support
    ∃ g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ normModel p 𝔞 b,
      g ≫ normModelν p 𝔞 b = gaussModelMap (K := X.residueField v.support) p
        (X.fromSpecResidueField v.support) (fromSpecResidueField_structure v) 𝔞 b ∧
      fieldPt g = genericPoint (normModel p 𝔞 b) := by
  let := residueComplexAlgebra p v.support
  let ν := normModelν p 𝔞 b
  let gm := gaussModelMap (K := X.residueField v.support) p (X.fromSpecResidueField v.support)
    (fromSpecResidueField_structure v) 𝔞 b
  obtain ⟨V, hVne, hiso⟩ := exists_isIso_normModelν_restrict p 𝔞 b
  obtain ⟨hνη, -⟩ := genericPoint_eq_and_bijective_of_isIso_restrict ν V
  have hηV : genericPoint (flagModel p 𝔞 b) ∈ V :=
    ((genericPoint_spec (flagModel p 𝔞 b)).mem_open_set_iff V.isOpen).mpr (by simpa using hVne)
  have hgen := fieldPt_gaussModelMap_eq_genericPoint v hv 𝔞 b
  have hrange : Set.range gm ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : x = closedPoint (FractionRing (X.residueField v.support)[X]) := Subsingleton.elim _ _
    subst this
    change fieldPt gm ∈ V
    rw [hgen]
    exact hηV
  let g₁ := IsOpenImmersion.lift V.ι gm hrange
  have hg₁ : g₁ ≫ V.ι = gm := IsOpenImmersion.lift_fac _ _ _
  refine ⟨g₁ ≫ inv (ν ∣_ V) ≫ (ν ⁻¹ᵁ V).ι, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hg₁]
  · have hm1 : fieldPt (g₁ ≫ inv (ν ∣_ V) ≫ (ν ⁻¹ᵁ V).ι) ∈ ν ⁻¹ᵁ V := by
      change ((ν ⁻¹ᵁ V).ι) _ ∈ ν ⁻¹ᵁ V
      exact ((ν ⁻¹ᵁ V).range_ι ▸ Set.mem_range_self _ : _)
    have hm2 : genericPoint (normModel p 𝔞 b) ∈ ν ⁻¹ᵁ V := by
      change ν _ ∈ V
      rw [hνη]
      exact hηV
    have hinj : Function.Injective (ν ∣_ V) :=
      (ConcreteCategory.bijective_of_isIso ((ν ∣_ V).base)).1
    have hν1 : ν (fieldPt (g₁ ≫ inv (ν ∣_ V) ≫ (ν ⁻¹ᵁ V).ι)) = genericPoint (flagModel p 𝔞 b) := by
      rw [← hgen]
      change fieldPt ((g₁ ≫ inv (ν ∣_ V) ≫ (ν ⁻¹ᵁ V).ι) ≫ ν) = _
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hg₁]
    have := @hinj ⟨_, hm1⟩ ⟨_, hm2⟩ (by
      apply Subtype.ext
      rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
      rw [hν1, hνη])
    exact congrArg Subtype.val this

end normGauss

/-! ### Centres and images of germs for field-valued points -/

section fieldCenters

variable {Y Z : Scheme.{0}} {fY : Y ⟶ Spec (.of ℂ)} {fZ : Z ⟶ Spec (.of ℂ)}
  {L : Type} [Field L] [Algebra ℂ L]

/-- The centre of the image of a field-valued semi-valuation is the image of its centre. -/
theorem center_fieldBerkovichPoint_comp [IsProper fY] [IsProper fZ] (g : Spec (.of L) ⟶ Y)
    (hg : g ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) (h : Y ⟶ Z)
    (hh : h ≫ fZ = fY) (W : SourceRealValuation L) :
    (fieldBerkovichPoint fZ (g ≫ h) (comp_structure_eq hg h hh) W).center =
      h (fieldBerkovichPoint fY g hg W).center := by
  let w := fieldBerkovichPoint fY g hg W
  have hs : fieldPt g ⤳ w.center := w.support_specializes_center
  exact center_eq_of_compat h w _ (hs.map h.continuous)
    (fun s => congrArg W.toFun (fieldEmb_comp_specializationMap g h hs s))

omit [Algebra ℂ L] in
/-- The residue embedding of `Spec ψ ≫ (Spec κ(y) → Y)` on germs is `ψ` composed with the
specialization map. -/
theorem fieldEmb_specializationMap_of_eq {y z : Y} (G : Spec (.of L) ⟶ Y)
    (ψ : Y.residueField y ⟶ .of L) (hG : G = Spec.map ψ ≫ Y.fromSpecResidueField y)
    (h : fieldPt G ⤳ z) (hy : y ⤳ z) (s : Y.presheaf.stalk z) :
    (fieldEmb G).hom ((specializationMap h).hom s) = ψ.hom ((specializationMap hy).hom s) := by
  subst hG
  have hσ : (Scheme.SpecToEquivOfField L Y) (Spec.map ψ ≫ Y.fromSpecResidueField y) = ⟨y, ψ⟩ :=
    (Scheme.SpecToEquivOfField L Y).apply_symm_apply ⟨y, ψ⟩
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hσ
  have key : ∀ (x : Y) (e : x = y) (η : Y.residueField x ⟶ .of L)
      (_ : η = (Y.residueFieldCongr e).hom ≫ ψ) (hx : x ⤳ z),
      η.hom ((specializationMap hx).hom s) = ψ.hom ((specializationMap hy).hom s) := by
    intro x e η hη hx
    subst e hη
    rw [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp]
  exact key _ e _ he h

/-- **Centre of the point of `Spec ψ ≫ (Spec κ(y) → Y)`**: if `W ∘ ψ` is the valuation of `v`, the
field-valued semi-valuation has the centre of `v`. -/
theorem center_fieldBerkovichPoint_fromSpecResidueField [IsProper fY] (v : BerkovichPoint fY)
    (ψ : Y.residueField v.support ⟶ .of L) (W : SourceRealValuation L)
    (hg : (Spec.map ψ ≫ Y.fromSpecResidueField v.support) ≫ fY =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (hW : ∀ a, W (ψ.hom a) = v.valAt a) :
    (fieldBerkovichPoint fY (Spec.map ψ ≫ Y.fromSpecResidueField v.support) hg W).center =
      v.center := by
  let w := fieldBerkovichPoint fY (Spec.map ψ ≫ Y.fromSpecResidueField v.support) hg W
  have hσ : (Scheme.SpecToEquivOfField L Y) (Spec.map ψ ≫ Y.fromSpecResidueField v.support) =
      ⟨v.support, ψ⟩ := (Scheme.SpecToEquivOfField L Y).apply_symm_apply ⟨v.support, ψ⟩
  obtain ⟨e, -⟩ := Scheme.SpecToEquivOfField_eq_iff.mp hσ
  have e' : fieldPt (Spec.map ψ ≫ Y.fromSpecResidueField v.support) = v.support := e
  have hv : v.support ⤳ w.center := e' ▸ w.support_specializes_center
  have hval : ∀ s : Y.presheaf.stalk w.center, v.valAt ((specializationMap hv).hom s) =
      w.valAt ((specializationMap w.support_specializes_center).hom s) := fun s =>
    ((congrArg W.toFun (fieldEmb_specializationMap_of_eq _ ψ rfl
      w.support_specializes_center hv s)).trans (hW _)).symm
  have hc : v.IsCenter w.center := by
    refine ⟨hv, fun s => ?_, fun s hs => ?_⟩
    · rw [hval]; exact w.centerVal_nonneg s
    · rw [hval]; exact w.centerVal_pos hs
  exact (v.isCenter_iff_eq_center _).mp hc

omit [Algebra ℂ L] in
/-- Images of germs under field-valued points, through a morphism and a specialization. -/
theorem fieldEmb_specializationMap_stalkMap (g : Spec (.of L) ⟶ Y) (h : Y ⟶ Z) {c : Y}
    (hs : fieldPt g ⤳ c) {z₀ : Z} (hz : h c ⤳ z₀) (s : Z.presheaf.stalk z₀) :
    (fieldEmb g).hom ((specializationMap hs).hom
      ((h.stalkMap c).hom ((Z.presheaf.stalkSpecializes hz).hom s))) =
      (fieldEmb (g ≫ h)).hom ((specializationMap ((hs.map h.continuous).trans hz)).hom s) := by
  rw [← fieldEmb_comp_specializationMap g h hs]
  congr 1
  unfold specializationMap
  rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

end fieldCenters

end SGPT.NAPotential.BJ

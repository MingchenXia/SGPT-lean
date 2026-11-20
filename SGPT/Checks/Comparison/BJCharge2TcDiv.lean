import SGPT.Checks.Comparison.BJCharge2Gauss
import SGPT.NAPotential.BJCharge2Valuation

/-!
# Divisorial points are Rees valuations of normal test configurations (R8(c))

Source: [BJ22, Lemma `lem:tcdiv`]
(`references/sgpt-d3f272c3/source/author/chapter_NApotential.tex`),
following [BHJ17, Theorem 4.6]; blueprint `claude-bj-charge2.tex`.

Let `v ∈ X^An` be a valuation of `ℂ(X)` with residually independent ratios `a_i / b_i`
(`i < m`, `dim X ≤ m + 1`) of germs at its centre of integral values `μ_i`, and a germ `f` of
positive integral value `l` (the data of step R8(a), `exists_reesData_of_primeDivisor`). Take the
flag ideal `𝔞 = valFlag v N` of valuation ideals of `v`, `N = l + Σ μ_i` (step R8(b),
`phi_valFlag`). Then the Gauss extension `σ(v)` lifts to a point of the normalized flag model
`normModel p 𝔞 N` supported at its generic point; its centre `c` lies in the central fibre, has
codimension one, `𝒪_c` is a discrete valuation ring and `σ(v) = β · ord_c` with `β > 0`.

## Main results

* `exists_gaussGerms`: the germs `pr₁^*(α) t^j` at the centre of `σ(v)` on the normalized model,
  their images `C(α) X^j` in `K(t)` and their membership in `(t^N 𝔞) · 𝒪`.
* `reesCenter'`: the Rees-centre criterion `reesCenter` for an arbitrary family of ratios
  (residual independence transported along an equivalence).
* `exists_reesComponent`: the centre of `σ(v)` on the normalized flag model is a codimension-one
  point of the central fibre, and `σ(v) = β · ord_c`.
* `exists_reesComponent_of_divisorial`: **[BJ22, `lem:tcdiv`]**: for every divisorial point
  `t · ord_F ∈ X^Div`, the Gauss extension is `β · ord_c` for a codimension-one point `c` of the
  normal test configuration `normModel p 𝔞 N` lying in its central fibre.

The identification of such `c` with the generic point of an irreducible component of the central
fibre (a Cartier divisor, so of pure codimension one) is not stated here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BerkovichPoint
open SGPT.NAPotential.BJCharge SGPT.NAPotential.BJModel FlagIdealBound
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open scoped Polynomial

/-! ### Auxiliary lemmas -/

section aux

variable {Y : Scheme.{0}}

/-- Transport of stalk-ideal membership along an equality of points. -/
theorem stalkSpecializes_mem_stalkIdeal {y₁ y₂ : Y} (e : y₁ = y₂) (J : Y.IdealSheafData)
    {a : Y.presheaf.stalk y₂} (ha : a ∈ stalkIdeal J y₂) :
    (Y.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes).hom a ∈ stalkIdeal J y₁ := by
  subst e
  rwa [TopCat.Presheaf.stalkSpecializes_refl]

theorem stalkIdeal_pow (J : Y.IdealSheafData) (c : Y) (j : ℕ) :
    stalkIdeal (J ^ j) c = stalkIdeal J c ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, stalkIdeal_mul, ih, pow_succ]

/-- The Gauss value of a monomial: `σ(v)(a t^j) = v(a) + j`. -/
theorem gaussExtension_C_mul_X_pow {K : Type*} [Field K] [Algebra ℂ K] (v : SourceRealValuation K)
    (a : K) (j : ℕ) :
    gaussExtension v (polyEmb (Polynomial.C a) * polyEmb Polynomial.X ^ j) =
      v a + ((j : ℝ) : WithTop ℝ) := by
  rw [(gaussExtension v).map_mul', gaussExtension_C]
  congr 1
  induction j with
  | zero => rw [pow_zero, SourceRealValuation.map_one]; simp
  | succ j ih =>
    rw [pow_succ, (gaussExtension v).map_mul', ih, gaussExtension_X]
    push_cast
    rfl

end aux

/-- The germ of `t` at `0 ∈ ℙ¹` maps to `t` under the Gauss point of `ℙ¹`. -/
theorem fieldEmb_specializationMap_chartGerm {K : Type} [Field K] [Algebra ℂ K]
    (G : Spec (.of (FractionRing K[X])) ⟶ projectiveSpace ℂ 1)
    (hG : G = chartGauss K ≫ lineChart ℂ) (h : fieldPt G ⤳ lineChart ℂ chartZero)
    {s : (projectiveSpace ℂ 1).presheaf.stalk (lineChart ℂ chartZero)}
    (hs : ((lineChart ℂ).stalkMap chartZero).hom s =
      (Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))).presheaf.germ ⊤ chartZero
        trivial ((Scheme.ΓSpecIso _).inv (MvPolynomial.X ⟨1, by decide⟩))) :
    (fieldEmb G).hom ((specializationMap h).hom s) = polyEmb Polynomial.X := by
  subst hG
  refine (fieldEmb_comp_specializationMap (chartGauss K) (lineChart ℂ)
    fieldPt_chartGauss_specializes s).trans ?_
  rw [hs, fieldEmb_chartGauss_germ, ΓSpecIso_hom_inv_apply]
  simp [gaussChartHom]

section tcdiv

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Spec (.of ℂ)} [IsProjective p]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- The germs `pr₁^*(α) t^j` at the centre of the normalized Gauss point, their images in
`ℂ(X)(t)`, values and membership in `(t^N 𝔞) · 𝒪` (the computational core of R8(c)). -/
theorem exists_gaussGerms (v : BerkovichPoint p) (hv : v.support = genericPoint X)
    (𝔞 : FlagIdeal X) (N : ℕ) :
    letI := residueComplexAlgebra p v.support
    ∃ (g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ normModel p 𝔞 N)
      (hg : g ≫ normModelStructure p 𝔞 N =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X])))),
      fieldPt g = genericPoint (normModel p 𝔞 N) ∧
      (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg (berkovichGaussExtension v)).idealVal
        ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔞 N)) = (gaussPoint v).idealVal (flagSheaf p 𝔞 N) ∧
      normModelπ p 𝔞 N (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg
        (berkovichGaussExtension v)).center ∈ ((centralIdeal p).support : Set (productLine p)) ∧
      ∃ H : X.presheaf.stalk v.center → ℕ → (normModel p 𝔞 N).presheaf.stalk
          (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg (berkovichGaussExtension v)).center,
        (∀ α j, (fieldEmb g).hom ((specializationMap (fieldBerkovichPoint (normModelStructure p 𝔞 N)
          g hg (berkovichGaussExtension v)).support_specializes_center).hom (H α j)) =
            polyEmb (Polynomial.C ((specializationMap v.support_specializes_center).hom α)) *
              polyEmb Polynomial.X ^ j) ∧
        (∀ α j, α ∈ stalkIdeal (𝔞.ideal ((N : ℤ) - (j : ℕ))) v.center →
          H α j ∈ stalkIdeal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔞 N))
            (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg
              (berkovichGaussExtension v)).center) := by
  let := residueComplexAlgebra p v.support
  obtain ⟨g, hgν, hgη⟩ := exists_gaussNormMap v hv 𝔞 N
  let ι := X.fromSpecResidueField v.support
  have hι := fromSpecResidueField_structure v
  have h_gπ : g ≫ normModelπ p 𝔞 N = gaussMap (K := X.residueField v.support) p ι hι := by
    rw [normModelπ, ← Category.assoc, hgν, gaussModelMap_π]
  have hg : g ≫ normModelStructure p 𝔞 N =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X]))) := by
    rw [normModelStructure, ← Category.assoc, hgν, gaussModelMap_structure]
  let W := berkovichGaussExtension v
  let w := fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg W
  have hππ : normModelπ p 𝔞 N ≫ productStructure p = normModelStructure p 𝔞 N := rfl
  -- centres
  have hx₀ : (gaussPoint v).center = normModelπ p 𝔞 N w.center := by
    have h := center_fieldBerkovichPoint_comp g hg (normModelπ p 𝔞 N) hππ W
    rw [fieldBerkovichPoint_congr h_gπ _ (gaussMap_structure (K := X.residueField v.support) p ι
      hι)] at h
    exact h
  set x₀ := normModelπ p 𝔞 N w.center
  have e₁ : productFst p x₀ = v.center := by
    have h := center_fieldBerkovichPoint_comp (gaussMap (K := X.residueField v.support) p ι hι)
      (gaussMap_structure (K := X.residueField v.support) p ι hι) (productFst p) rfl W
    rw [fieldBerkovichPoint_congr (gaussMap_fst (K := X.residueField v.support) p ι hι) _
      (gaussBaseMap_structure (K := X.residueField v.support) p ι hι)] at h
    rw [← hx₀]
    refine h.symm.trans ?_
    refine center_fieldBerkovichPoint_fromSpecResidueField v
      (CommRingCat.ofHom (algebraMap (X.residueField v.support)
        (FractionRing (X.residueField v.support)[X]))) W _ (fun a => ?_)
    change gaussExtension v.val (algebraMap (X.residueField v.support)
      (FractionRing (X.residueField v.support)[X]) a) = v.val a
    rw [IsScalarTower.algebraMap_apply (X.residueField v.support) (X.residueField v.support)[X]
      (FractionRing (X.residueField v.support)[X]), Polynomial.algebraMap_apply]
    exact gaussExtension_C v.val a
  have e₂ : productSnd p x₀ = lineChart ℂ chartZero := by
    have h := center_fieldBerkovichPoint_comp (gaussMap (K := X.residueField v.support) p ι hι)
      (gaussMap_structure (K := X.residueField v.support) p ι hι) (productSnd p)
      (productSnd_structure p) W
    rw [fieldBerkovichPoint_congr (gaussMap_snd (K := X.residueField v.support) p ι hι) _
      (gaussLineMap_structure _)] at h
    rw [← hx₀]
    refine h.symm.trans ?_
    exact (((lineGaussPoint v.val).isCenter_iff_eq_center _).mp
      (lineGaussPoint_isCenter v.val)).symm
  obtain ⟨sₜ, hsₜI, hsₜ⟩ := exists_mem_stalkIdeal_zeroIdeal_stalkMap
  have hs := w.support_specializes_center
  let A : X.presheaf.stalk v.center → (productLine p).presheaf.stalk x₀ := fun α =>
    ((productFst p).stalkMap x₀).hom
      ((X.presheaf.stalkSpecializes (Inseparable.of_eq e₁).specializes).hom α)
  let B : (productLine p).presheaf.stalk x₀ :=
    ((productSnd p).stalkMap x₀).hom (((projectiveSpace ℂ 1).presheaf.stalkSpecializes
      (Inseparable.of_eq e₂).specializes).hom sₜ)
  let H : X.presheaf.stalk v.center → ℕ → (normModel p 𝔞 N).presheaf.stalk w.center :=
    fun α j => ((normModelπ p 𝔞 N).stalkMap w.center).hom (A α * B ^ j)
  have himgA : ∀ α, (fieldEmb (g ≫ normModelπ p 𝔞 N)).hom
      ((specializationMap (hs.map (normModelπ p 𝔞 N).continuous)).hom (A α)) =
        polyEmb (Polynomial.C ((specializationMap v.support_specializes_center).hom α)) := by
    intro α
    refine (fieldEmb_specializationMap_stalkMap (g ≫ normModelπ p 𝔞 N) (productFst p)
      (hs.map (normModelπ p 𝔞 N).continuous) (Inseparable.of_eq e₁).specializes α).trans ?_
    refine (fieldEmb_specializationMap_of_eq _ (CommRingCat.ofHom (algebraMap
      (X.residueField v.support) (FractionRing (X.residueField v.support)[X]))) ?_ _
      v.support_specializes_center α).trans ?_
    · rw [h_gπ, gaussMap_fst]
      rfl
    · change algebraMap (X.residueField v.support)
        (FractionRing (X.residueField v.support)[X]) _ = _
      rw [IsScalarTower.algebraMap_apply (X.residueField v.support) (X.residueField v.support)[X]
        (FractionRing (X.residueField v.support)[X]), Polynomial.algebraMap_apply]
      rfl
  have himgB : (fieldEmb (g ≫ normModelπ p 𝔞 N)).hom
      ((specializationMap (hs.map (normModelπ p 𝔞 N).continuous)).hom B) =
        polyEmb Polynomial.X := by
    refine (fieldEmb_specializationMap_stalkMap (g ≫ normModelπ p 𝔞 N) (productSnd p)
      (hs.map (normModelπ p 𝔞 N).continuous) (Inseparable.of_eq e₂).specializes sₜ).trans ?_
    exact fieldEmb_specializationMap_chartGerm _ (by rw [h_gπ, gaussMap_snd]; rfl) _ hsₜ
  refine ⟨g, hg, hgη, ?_, ?_, H, ?_, ?_⟩
  · refine (idealVal_comap_fieldBerkovichPoint (normModelπ p 𝔞 N) hππ g hg W _).trans ?_
    rw [fieldBerkovichPoint_congr h_gπ _ (gaussMap_structure (K := X.residueField v.support) p ι
      hι)]
    rfl
  · rw [support_centralIdeal]
    refine ⟨closedPoint ℂ, ?_⟩
    rw [e₂]
    rfl
  · intro α j
    refine (fieldEmb_comp_specializationMap g (normModelπ p 𝔞 N) hs (A α * B ^ j)).symm.trans ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (himgA α) (congrArg (· ^ j) himgB)
  · intro α j hα
    rw [stalkIdeal_comap]
    apply Ideal.mem_map_of_mem
    apply stalkIdeal_mono (le_flagSheaf p 𝔞 N j)
    rw [stalkIdeal_mul, stalkIdeal_pow]
    refine Ideal.mul_mem_mul ?_ (Ideal.pow_mem_pow ?_ j)
    · rw [stalkIdeal_comap]
      exact Ideal.mem_map_of_mem _ (stalkSpecializes_mem_stalkIdeal e₁ _ hα)
    · change B ∈ stalkIdeal ((zeroIdeal ℂ).comap (productSnd p)) x₀
      rw [stalkIdeal_comap]
      exact Ideal.mem_map_of_mem _ (stalkSpecializes_mem_stalkIdeal e₂ _ hsₜI)

end tcdiv

section reesPrime

variable {𝒳 : Scheme.{0}} [IsIntegral 𝒳] (q : 𝒳 ⟶ Spec (.of ℂ)) [IsLocallyNoetherian 𝒳] [IsProper q]

/-- `reesCenter` for a semi-valuation supported at the generic point. -/
theorem reesCenter' (hnorm : ∀ x : 𝒳, IsIntegrallyClosed (𝒳.presheaf.stalk x)) {n : ℕ}
    (hdim : topologicalKrullDim 𝒳 ≤ n + 1) (w : BerkovichPoint q)
    (hw : w.support = genericPoint 𝒳) (hc : w.center ≠ genericPoint 𝒳)
    (J : 𝒳.IdealSheafData) (hJ : J.IsInvertible) (h h' : Fin n → 𝒳.presheaf.stalk w.center)
    (hh : ∀ i, h i ∈ stalkIdeal J w.center) (hh' : ∀ i, h' i ∈ stalkIdeal J w.center)
    (hv : ∀ i, w.centerVal (h i) = w.centerVal (h' i))
    (hmin : ∀ i, ∀ g ∈ stalkIdeal J w.center, w.centerVal (h' i) ≤ w.centerVal g)
    (hfin : ∀ i, w.centerVal (h' i) ≠ ⊤)
    (hind : letI := residueComplexAlgebra q w.support
      ResiduallyIndependent w.val (fun i =>
        (specializationMap w.support_specializes_center).hom (h i) /
          (specializationMap w.support_specializes_center).hom (h' i))) :
    coheight w.center = 1 ∧ IsDiscreteValuationRing (𝒳.presheaf.stalk w.center) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ val : ResidueValuation q (genericPoint 𝒳),
        w = ⟨genericPoint 𝒳, val⟩ ∧ ∀ F : 𝒳.functionField, F ≠ 0 →
          val ((𝒳.residue (genericPoint 𝒳)).hom F) =
            ((β * (Scheme.ord F w.center : ℝ) : ℝ) : WithTop ℝ) := by
  obtain ⟨y, val⟩ := w
  change y = genericPoint 𝒳 at hw
  subst hw
  obtain ⟨h1, h2, β, hβ, hF⟩ := reesCenter q hnorm hdim val hc J hJ h h' hh hh' hv hmin hfin hind
  exact ⟨h1, h2, β, hβ, val, rfl, hF⟩

end reesPrime

/-- Residual independence is preserved by reindexing. -/
theorem ResiduallyIndependent.comp_equiv {L : Type*} [Field L] [Algebra ℂ L]
    {w : SourceRealValuation L} {ι ι' : Type*} {u : ι → L} (hu : ResiduallyIndependent w u)
    (e : ι' ≃ ι) : ResiduallyIndependent w (u ∘ e) := by
  intro P hP
  rw [show MvPolynomial.aeval (u ∘ e) P = MvPolynomial.aeval u (MvPolynomial.rename e P) by
    rw [MvPolynomial.aeval_rename]]
  exact hu _ (fun h0 =>
    hP (MvPolynomial.rename_injective _ e.injective (h0.trans (map_zero _).symm)))

/-- Nonzero germs at the generic point are units. -/
theorem isUnit_of_eq_genericPoint {Y : Scheme.{0}} [IsIntegral Y] {c : Y} (hc : c = genericPoint Y)
    {s : Y.presheaf.stalk c} (hs : s ≠ 0) : IsUnit s := by
  subst hc
  exact isUnit_iff_ne_zero.mpr (show (s : Y.functionField) ≠ 0 from hs)

section main

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Spec (.of ℂ)} [IsProjective p]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- The normalized models are locally Noetherian. -/
theorem normModel_isLocallyNoetherian_of_finiteType (𝔞 : FlagIdeal X) (b : ℤ) :
    IsLocallyNoetherian (normModel p 𝔞 b) :=
  LocallyOfFiniteType.isLocallyNoetherian (normModelStructure p 𝔞 b)

local instance (𝔞 : FlagIdeal X) (b : ℤ) : IsLocallyNoetherian (normModel p 𝔞 b) :=
  normModel_isLocallyNoetherian_of_finiteType 𝔞 b

/-- **Rees components** (step R8(c), [BJ22, `lem:tcdiv`]): let `v` be a valuation of `ℂ(X)` with
`m` ratios `a_i / b_i` (`dim X ≤ m + 1`) of germs at its centre, of equal integral values,
residually independent for `v`, and a germ `f` of positive integral value `l`. Then for the flag
ideal `𝔞 = valFlag v N` of valuation ideals (`N = l + Σ μ_i`), the Gauss point `σ(v)` of the
normalized blow-up of `t^N 𝔞` is centred at a point `c` of codimension one lying in the central
fibre, with a discrete valuation ring as local ring, and `σ(v) = β · ord_c` for some `β > 0`
(so `σ(v) = v_E` for the prime divisor `E = closure {c}` of the normal test configuration). -/
theorem exists_reesComponent (v : BerkovichPoint p) (hv : v.support = genericPoint X) {m : ℕ}
    (hdimX : topologicalKrullDim X ≤ (m + 1 : ℕ))
    (a b : Fin m → X.presheaf.stalk v.center) (μ : Fin m → ℕ)
    (f : X.presheaf.stalk v.center) (l : ℕ)
    (hab : ∀ i, v.centerVal (a i) = ((μ i : ℝ) : WithTop ℝ) ∧
      v.centerVal (b i) = ((μ i : ℝ) : WithTop ℝ))
    (hl : 0 < l) (hf : v.centerVal f = ((l : ℝ) : WithTop ℝ))
    (hind : letI := residueComplexAlgebra p v.support
      ResiduallyIndependent v.val (fun i =>
        (specializationMap v.support_specializes_center).hom (a i) /
          (specializationMap v.support_specializes_center).hom (b i))) :
    letI := residueComplexAlgebra p v.support
    ∃ (𝔞 : FlagIdeal X) (N : ℕ)
      (g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ normModel p 𝔞 N)
      (hg : g ≫ normModelStructure p 𝔞 N =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X])))),
      normModelπ p 𝔞 N (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg
        (berkovichGaussExtension v)).center ∈ ((centralIdeal p).support : Set (productLine p)) ∧
      coheight (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg
        (berkovichGaussExtension v)).center = 1 ∧
      IsDiscreteValuationRing ((normModel p 𝔞 N).presheaf.stalk
        (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg (berkovichGaussExtension v)).center) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ val : ResidueValuation (normModelStructure p 𝔞 N)
          (genericPoint (normModel p 𝔞 N)),
        fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg (berkovichGaussExtension v) =
          ⟨genericPoint (normModel p 𝔞 N), val⟩ ∧
        ∀ F : (normModel p 𝔞 N).functionField, F ≠ 0 →
          val (((normModel p 𝔞 N).residue (genericPoint (normModel p 𝔞 N))).hom F) =
            ((β * (Scheme.ord F (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg
              (berkovichGaussExtension v)).center : ℝ) : ℝ) : WithTop ℝ) := by
  let := residueComplexAlgebra p v.support
  set N : ℕ := l + ∑ i, μ i with hN
  have hμN : ∀ i, μ i ≤ N := fun i => by
    have := Finset.single_le_sum (f := μ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hlN : l ≤ N := by omega
  let 𝔞 := valFlag v N
  have hwb : IsWeightBound 𝔞 (N : ℤ) := fun l' hl' => by
    have h1 : ¬ l' ≤ 0 := by omega
    have h2 : ¬ l' ≤ (N : ℤ) := by omega
    simp [𝔞, valFlag, h1, h2]
  obtain ⟨g, hg, hgη, hJval, hcentral, H, himg, hmem⟩ := exists_gaussGerms v hv 𝔞 N
  let w := fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg (berkovichGaussExtension v)
  let spv := (specializationMap v.support_specializes_center).hom
  let spw := (specializationMap w.support_specializes_center).hom
  -- values
  have hvalH : ∀ α j, w.centerVal (H α j) = v.centerVal α + ((j : ℝ) : WithTop ℝ) := by
    intro α j
    change gaussExtension v.val ((fieldEmb g).hom (spw (H α j))) = _
    refine (congrArg (gaussExtension v.val) (himg α j)).trans ?_
    rw [gaussExtension_C_mul_X_pow]
    rfl
  have hJ := isInvertible_comap_normModelπ p 𝔞 N
  have hJN : w.idealVal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔞 N)) = ENNReal.ofReal N := by
    rw [hJval, idealVal_gaussPoint_flagSheaf_eq' v 𝔞 hwb, phi_valFlag]
    simp
  have hmin : ∀ x ∈ stalkIdeal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔞 N)) w.center,
      ((N : ℝ) : WithTop ℝ) ≤ w.centerVal x := by
    intro x hx
    have h1 := w.idealVal_le _ hx
    rw [hJN] at h1
    cases hcv : w.centerVal x with
    | top => exact le_top
    | coe r =>
      unfold BerkovichPoint.centerValENN at h1
      rw [hcv, toENNReal_coe] at h1
      have hr : 0 ≤ r := by have := w.centerVal_nonneg x; rw [hcv] at this; exact_mod_cast this
      exact WithTop.coe_le_coe.mpr ((ENNReal.ofReal_le_ofReal_iff hr).mp h1)
  -- the pairs of germs, indexed by `Option (Fin m)`
  let hh : Option (Fin m) → (normModel p 𝔞 N).presheaf.stalk w.center :=
    fun o => o.elim (H 1 N) (fun i => H (a i) (N - μ i))
  let hh' : Option (Fin m) → (normModel p 𝔞 N).presheaf.stalk w.center :=
    fun o => o.elim (H f (N - l)) (fun i => H (b i) (N - μ i))
  have hcast : ∀ k : ℕ, k ≤ N → ((k : ℝ) : WithTop ℝ) + (((N - k : ℕ) : ℝ) : WithTop ℝ) =
      ((N : ℝ) : WithTop ℝ) := by
    intro k hk
    rw [← WithTop.coe_add]
    congr 1
    push_cast [Nat.cast_sub hk]
    ring
  have hvalN : ∀ o, w.centerVal (hh o) = ((N : ℝ) : WithTop ℝ) ∧
      w.centerVal (hh' o) = ((N : ℝ) : WithTop ℝ) := by
    intro o
    cases o with
    | none =>
      refine ⟨?_, ?_⟩
      · change w.centerVal (H 1 N) = _
        rw [hvalH, centerVal_one, zero_add]
      · change w.centerVal (H f (N - l)) = _
        rw [hvalH, hf, hcast l hlN]
    | some i =>
      refine ⟨?_, ?_⟩
      · change w.centerVal (H (a i) (N - μ i)) = _
        rw [hvalH, (hab i).1, hcast _ (hμN i)]
      · change w.centerVal (H (b i) (N - μ i)) = _
        rw [hvalH, (hab i).2, hcast _ (hμN i)]
  have hideal : ∀ k : ℕ, k ≤ N → ∀ α : X.presheaf.stalk v.center,
      ((k : ℝ) : WithTop ℝ) ≤ v.centerVal α →
        α ∈ stalkIdeal (𝔞.ideal ((N : ℤ) - ((N - k : ℕ) : ℤ))) v.center := by
    intro k hk α hα
    have hk' : (N : ℤ) - ((N - k : ℕ) : ℤ) = k := by push_cast [Nat.cast_sub hk]; ring
    rw [hk']
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [show ((0 : ℕ) : ℤ) = 0 from rfl, valFlag_ideal_of_nonpos v N le_rfl, stalkIdeal_top]
      exact Submodule.mem_top
    · rw [valFlag_ideal_of_pos v (by exact_mod_cast h0) (by exact_mod_cast hk)]
      apply germ_mem_stalkIdeal_valIdeal
      rw [mem_stalkValIdeal]
      exact_mod_cast hα
  have hmemN : ∀ o, hh o ∈ stalkIdeal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔞 N)) w.center ∧
      hh' o ∈ stalkIdeal ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔞 N)) w.center := by
    intro o
    cases o with
    | none =>
      refine ⟨hmem _ _ ?_, hmem _ _ (hideal l hlN f (le_of_eq hf.symm))⟩
      have := hideal 0 (Nat.zero_le N) 1 (by rw [centerVal_one]; simp)
      simpa using this
    | some i =>
      exact ⟨hmem _ _ (hideal _ (hμN i) _ (le_of_eq (hab i).1.symm)),
        hmem _ _ (hideal _ (hμN i) _ (le_of_eq (hab i).2.symm))⟩
  -- the images of the ratios in `ℂ(X)(t)`
  have hf0 : spv f ≠ 0 := by
    intro h0
    have : v.centerVal f = ⊤ := by
      change v.valAt (spv f) = ⊤
      rw [h0, valAt_zero]
    rw [hf] at this
    exact WithTop.coe_ne_top this
  have hX0 : polyEmb (Polynomial.X : (X.residueField v.support)[X]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr Polynomial.X_ne_zero
  let u : Fin m → X.residueField v.support := fun i => spv (a i) / spv (b i)
  have hratio : ∀ o, (fieldEmb g).hom (spw (hh o) / spw (hh' o)) =
      gaussFamily u (spv f) l o := by
    intro o
    rw [map_div₀]
    cases o with
    | none =>
      change (fieldEmb g).hom (spw (H 1 N)) / (fieldEmb g).hom (spw (H f (N - l))) =
        gaussRatio (spv f) l
      rw [himg, himg, map_one, Polynomial.C_1, map_one, one_mul, gaussRatio, map_pow]
      have hsplit : polyEmb (Polynomial.X : (X.residueField v.support)[X]) ^ N =
          polyEmb Polynomial.X ^ l * polyEmb Polynomial.X ^ (N - l) := by
        rw [← pow_add, Nat.add_sub_cancel' hlN]
      rw [hsplit, mul_div_mul_right _ _ (pow_ne_zero _ hX0)]
    | some i =>
      change (fieldEmb g).hom (spw (H (a i) (N - μ i))) /
        (fieldEmb g).hom (spw (H (b i) (N - μ i))) = polyEmb (Polynomial.C (u i))
      rw [himg, himg, mul_div_mul_right _ _ (pow_ne_zero _ hX0)]
      exact (map_div₀ (polyEmb.comp Polynomial.C) (spv (a i)) (spv (b i))).symm
  -- residual independence of the ratios for the normalized Gauss point
  let := residueComplexAlgebra (normModelStructure p 𝔞 N) (fieldPt g)
  let φ : (normModel p 𝔞 N).residueField (fieldPt g) →ₐ[ℂ]
      FractionRing (X.residueField v.support)[X] :=
    { (fieldEmb g).hom with
      commutes' := fun c => by
        have h := congrArg (fun ψ => ψ.hom c) (residueComplexHom_fieldEmb
          (normModelStructure p 𝔞 N) g hg)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h }
  have hRI := ResiduallyIndependent.comp_equiv
    (residuallyIndependent_gaussExtension v.val hind hf0 hl hf) (finSuccEquiv m)
  let := residueComplexAlgebra (normModelStructure p 𝔞 N) w.support
  have hind' : ResiduallyIndependent w.val (fun i : Fin (m + 1) =>
      spw (hh (finSuccEquiv m i)) / spw (hh' (finSuccEquiv m i))) := by
    intro P hP
    change gaussExtension v.val (φ (MvPolynomial.aeval _ P)) = 0
    rw [MvPolynomial.comp_aeval_apply]
    have : (fun i : Fin (m + 1) => φ (spw (hh (finSuccEquiv m i)) / spw (hh' (finSuccEquiv m i)))) =
        gaussFamily u (spv f) l ∘ finSuccEquiv m := by
      funext i
      exact hratio _
    rw [this]
    exact hRI P hP
  -- the centre is not the generic point
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : w.center ≠ genericPoint (normModel p 𝔞 N) := by
    intro hη
    have hne : H 1 N ≠ 0 := by
      intro h0
      have := (hvalN none).1
      change w.centerVal (H 1 N) = _ at this
      rw [h0, centerVal_zero] at this
      exact WithTop.top_ne_coe this
    have h0 := (w.centerVal_eq_zero_iff _).mpr (isUnit_of_eq_genericPoint hη hne)
    have := (hvalN none).1
    change w.centerVal (H 1 N) = _ at this
    rw [h0] at this
    have : (0 : ℝ) = N := by exact_mod_cast this
    linarith
  have hdim : topologicalKrullDim (normModel p 𝔞 N) ≤ ((m + 1 : ℕ) : WithBot ℕ∞) + 1 := by
    have := topologicalKrullDim_normModel_le p 𝔞 N (m + 1) hdimX
    simpa using this
  obtain ⟨h1, h2, β, hβ, val, hwv, hF⟩ := reesCenter' (normModelStructure p 𝔞 N)
    (normModel_stalk_isIntegrallyClosed p 𝔞 N) hdim w hgη hc
    ((flagSheaf p 𝔞 N).comap (normModelπ p 𝔞 N)) hJ
    (fun i => hh (finSuccEquiv m i)) (fun i => hh' (finSuccEquiv m i))
    (fun i => (hmemN _).1) (fun i => (hmemN _).2)
    (fun i => (hvalN _).1.trans (hvalN _).2.symm)
    (fun i x hx => by rw [(hvalN _).2]; exact hmin x hx)
    (fun i => by rw [(hvalN _).2]; exact WithTop.coe_ne_top) hind'
  exact ⟨𝔞, N, g, hg, hcentral, h1, h2, β, hβ, val, hwv, hF⟩

/-- **Every divisorial point is `v_E` for a component of the central fibre of a normal test
configuration** ([BJ22, Lemma `lem:tcdiv`], via [BHJ17, Theorem 4.6]; step R8(c)): for
`v = t · ord_F ∈ X^Div` there are a flag ideal `𝔞` (the valuation ideals of `v`), `N` and a
point `c` of codimension one lying in the central fibre of the normalized blow-up
`normModel p 𝔞 N` of `t^N 𝔞`, with a discrete valuation ring as local ring, such that the Gauss extension `σ(v)` (the
point of `normModel^An` of the lift `g` of the Gauss point) is `β · ord_c` for some `β > 0`. -/
theorem exists_reesComponent_of_divisorial (v : BerkovichPoint p) (hv : v ∈ divisorialSet p) :
    letI := residueComplexAlgebra p v.support
    ∃ (𝔞 : FlagIdeal X) (N : ℕ)
      (g : Spec (.of (FractionRing (X.residueField v.support)[X])) ⟶ normModel p 𝔞 N)
      (hg : g ≫ normModelStructure p 𝔞 N =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (FractionRing (X.residueField v.support)[X])))),
      normModelπ p 𝔞 N (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg
        (berkovichGaussExtension v)).center ∈ ((centralIdeal p).support : Set (productLine p)) ∧
      coheight (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg
        (berkovichGaussExtension v)).center = 1 ∧
      IsDiscreteValuationRing ((normModel p 𝔞 N).presheaf.stalk
        (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg (berkovichGaussExtension v)).center) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ val : ResidueValuation (normModelStructure p 𝔞 N)
          (genericPoint (normModel p 𝔞 N)),
        fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg (berkovichGaussExtension v) =
          ⟨genericPoint (normModel p 𝔞 N), val⟩ ∧
        ∀ F : (normModel p 𝔞 N).functionField, F ≠ 0 →
          val (((normModel p 𝔞 N).residue (genericPoint (normModel p 𝔞 N))).hom F) =
            ((β * (Scheme.ord F (fieldBerkovichPoint (normModelStructure p 𝔞 N) g hg
              (berkovichGaussExtension v)).center : ℝ) : ℝ) : WithTop ℝ) := by
  obtain ⟨E, s, hs, rfl⟩ := hv
  obtain ⟨m, a, b, μ, f, l, hdim, hab, hl, hf, hind⟩ :=
    exists_reesData_of_primeDivisor (p := p) E s hs
  exact exists_reesComponent (E.ordVal p s hs) E.isGenericPoint_image hdim a b μ f l hab hl hf hind

end main

end SGPT.NAPotential.BJ

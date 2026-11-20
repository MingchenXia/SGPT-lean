import SGPT.Okounkov.SchemeCoordinateAnalyticDerivation
import SGPT.Okounkov.SchemeCoordinateGlobalGerm
import SGPT.Okounkov.SchemeOpenRegularFunctions
import SGPT.Foundations.Schemes.PolynomialProjectiveTwistingTransition
import SGPT.Foundations.Schemes.NativeProjectiveFano

/-!
# The projective embedding is an immersion in the workspace charts

Blueprint `claude-fs-pos:immersion`.

Let `X` be smooth of relative dimension `n` over `ℂ`, with a closed projective embedding
`E.map : X ⟶ ℙᴺ`, and let `Uᵢ = E.map⁻¹ D₊(xᵢ)`.  The regular functions
`ratio E i k = (x_k / x_i)|_X ∈ Γ(X, Uᵢ)` have analytic functions
`schemeOpenRegularFunction f n E Uᵢ (ratio E i k)` on `Uᵢ(ℂ)`.

* `eq_zero_of_fderiv_ratio_eq_zero`: **the map `Uᵢ(ℂ) → ℂᴺ`, `p ↦ ((x_k/x_i)(p))_{k ≠ i}`, is an
  immersion in the workspace (`SGPT.Foundations.Analysis`) charts**: in the preferred chart `e` at a
  point `p ∈ Uᵢ(ℂ)`, a vector `v ∈ ℂⁿ` killed by the derivatives at `e p` of all the functions
  `(x_k/x_i) ∘ e⁻¹`, `k ≠ i`, is zero.

The proof is the cotangent argument.  A tangent vector `v` at `p` gives the point derivation
`r ↦ D_v (r^an)` of the algebraic local ring `𝒪_{X,x}` (`germDeriv`, `stalkToModel`).  Its kernel
is a subring closed under division by units (`tangentKernel`), it contains the structural
constants (their analytic functions are constant) and, by hypothesis, the germs of the ratios.
Since `E.map` is a closed immersion, `Γ(ℙᴺ, D₊(xᵢ)) = ℂ[x_k/x_i] → Γ(X, Uᵢ)` is surjective, and
`𝒪_{X,x}` is a localization of `Γ(X, Uᵢ)` (`Uᵢ` is affine): the kernel is everything
(`stalk_generated`).  But the coordinates of the preferred chart are analytic functions of
elements of `𝒪_{X,x}` (the free generators of the standard smooth chart), and `D_v` of the
`j`-th coordinate is `v_j`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.FSPos

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open HironakaHolomorphicJetMonomialSpan HolomorphicGermCoordinateDerivation
open SGPT.Okounkov
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The structural constants of projective space on a coordinate chart -/

section ProjConstants

variable (N : ℕ)

/-- The structural constants of `ℙᴺ`, restricted to `D₊(xᵢ)`, are the scalars of the coordinate
ring `ℂ[x_k/x_i]`. -/
theorem polynomialProj_constants_restrict (i : Fin (N + 1)) (b : ℂ) :
    (polynomialProj ℂ N).presheaf.map
        (homOfLE (le_top : polynomialProjCoordinateOpen ℂ N i ≤ ⊤)).op
        (schemeGlobalConstants (polynomialProjStructureMap ℂ N) b) =
      polynomialProjCoordinateSectionMap ℂ N i
        (algebraMap ℂ (polynomialProjCoordinateRing ℂ N i) b) := by
  let A : CommRingCat := .of (polynomialProjCoordinateRing ℂ N i)
  let D := polynomialProjCoordinateOpen ℂ N i
  let e := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) (by decide)
  let c := schemeGlobalConstants (polynomialProjStructureMap ℂ N) b
  have happ : e.hom.appTop = (Scheme.ΓSpecIso A).hom ≫
      CommRingCat.ofHom (polynomialProjCoordinateSectionMap ℂ N i) ≫ D.topIso.inv :=
    Proj.basicOpenToSpec_app_top _ _
  have hstr : (e.inv ≫ D.ι) ≫ polynomialProjStructureMap ℂ N =
      Spec.map (affineBaseRingMap ℂ A) := polynomialProjCoordinateImmersion_structure ℂ N i
  -- the constants pulled back to the affine chart
  have hnat := Scheme.ΓSpecIso_naturality (Spec.preimage ((e.inv ≫ D.ι) ≫
    polynomialProjStructureMap ℂ N))
  rw [Spec.map_preimage] at hnat
  have hz := congrArg (fun q : Γ(Spec (.of ℂ), ⊤) ⟶ A =>
    q ((Scheme.ΓSpecIso (.of ℂ)).inv b)) hnat
  have h1 : (Scheme.ΓSpecIso A).hom (e.inv.appTop (D.ι.appTop c)) =
      algebraMap ℂ (polynomialProjCoordinateRing ℂ N i) b := by
    have hpre : Spec.preimage ((e.inv ≫ D.ι) ≫ polynomialProjStructureMap ℂ N) =
        affineBaseRingMap ℂ A := by
      rw [hstr, Spec.preimage_map]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      Iso.inv_hom_id_apply, hpre] at hz
    exact hz
  -- transport through the chart isomorphism
  have h2 : e.hom.appTop (e.inv.appTop (D.ι.appTop c)) = D.ι.appTop c := by
    have hid : e.inv.appTop ≫ e.hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; rfl
    exact congrArg (fun q : Γ(D.toScheme, ⊤) ⟶ Γ(D.toScheme, ⊤) => q (D.ι.appTop c)) hid
  have h3 : D.ι.appTop c = D.topIso.inv (polynomialProjCoordinateSectionMap ℂ N i
      (algebraMap ℂ (polynomialProjCoordinateRing ℂ N i) b)) := by
    rw [← h2, happ, ← h1]
    rfl
  have h4 := congrArg D.topIso.hom h3
  rw [Iso.inv_hom_id_apply] at h4
  rw [← h4]
  change _ = (polynomialProj ℂ N).presheaf.map _ ((polynomialProj ℂ N).presheaf.map _ c)
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end ProjConstants

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)

/-- `Uᵢ = E.map⁻¹ D₊(xᵢ) ⊆ X`. -/
abbrev coordOpen (i : Fin (E.ambientDimension + 1)) : X.Opens :=
  E.map ⁻¹ᵁ polynomialProjCoordinateOpen ℂ E.ambientDimension i

/-- The regular function `(x_k / x_i)|_X` on `Uᵢ`. -/
def ratio (i k : Fin (E.ambientDimension + 1)) : Γ(X, coordOpen E i) :=
  E.map.app (polynomialProjCoordinateOpen ℂ E.ambientDimension i)
    (polynomialProjCoordinateRegularRatio ℂ E.ambientDimension i k)

theorem ratio_self (i : Fin (E.ambientDimension + 1)) : ratio E i i = 1 := by
  rw [ratio, polynomialProjCoordinateRegularRatio_self, map_one]

/-- `Uᵢ` is affine. -/
theorem isAffineOpen_coordOpen (i : Fin (E.ambientDimension + 1)) :
    IsAffineOpen (coordOpen E i) :=
  (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X ℂ i) (by decide)).preimage E.map

/-- The structural constants of `X` on `Uᵢ` are the images of the scalars of `ℂ[x_k/x_i]`. -/
theorem constants_restrict (i : Fin (E.ambientDimension + 1)) (b : ℂ) :
    X.presheaf.map (homOfLE (le_top : coordOpen E i ≤ ⊤)).op (schemeGlobalConstants f b) =
      E.map.app (polynomialProjCoordinateOpen ℂ E.ambientDimension i)
        (polynomialProjCoordinateSectionMap ℂ E.ambientDimension i
          (algebraMap ℂ (polynomialProjCoordinateRing ℂ E.ambientDimension i) b)) := by
  rw [← polynomialProj_constants_restrict]
  have hf : f.appTop = (E.map ≫ polynomialProjStructureMap ℂ E.ambientDimension).appTop := by
    rw [E.over_base]
  have hc : schemeGlobalConstants f b =
      E.map.appTop (schemeGlobalConstants (polynomialProjStructureMap ℂ E.ambientDimension) b) := by
    change f.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv b) = _
    rw [hf, Scheme.Hom.comp_appTop]
    rfl
  rw [hc]
  have hn := Scheme.Hom.naturality E.map
    (homOfLE (le_top : polynomialProjCoordinateOpen ℂ E.ambientDimension i ≤ ⊤)).op
  exact (congrArg (fun q : Γ(polynomialProj ℂ E.ambientDimension, ⊤) ⟶ Γ(X, coordOpen E i) =>
    q (schemeGlobalConstants (polynomialProjStructureMap ℂ E.ambientDimension) b)) hn).symm

/-- **Generation of the local ring.**  A subring of `𝒪_{X,x}`, `x ∈ Uᵢ`, which contains the
structural constants and the germs of the ratios `x_k/x_i`, and is closed under division by
units, is everything. -/
theorem stalk_generated (i : Fin (E.ambientDimension + 1)) (x : X) (hx : x ∈ coordOpen E i)
    (K : Subring (X.presheaf.stalk x))
    (hconst : ∀ b : ℂ, X.presheaf.germ ⊤ x trivial (schemeGlobalConstants f b) ∈ K)
    (hratio : ∀ a : Fin E.ambientDimension,
      X.presheaf.germ (coordOpen E i) x hx (ratio E i (i.succAbove a)) ∈ K)
    (hdiv : ∀ r s : X.presheaf.stalk x, s ∈ K → IsUnit s → r * s ∈ K → r ∈ K)
    (r : X.presheaf.stalk x) : r ∈ K := by
  have hpoly : ∀ P : MvPolynomial (Fin E.ambientDimension) ℂ,
      X.presheaf.germ (coordOpen E i) x hx
        (E.map.app (polynomialProjCoordinateOpen ℂ E.ambientDimension i)
          (polynomialProjCoordinateSectionMap ℂ E.ambientDimension i
            (polynomialProjRatioMap ℂ E.ambientDimension i P))) ∈ K := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C b =>
      have h1 : polynomialProjRatioMap ℂ E.ambientDimension i (MvPolynomial.C b) =
          algebraMap ℂ (polynomialProjCoordinateRing ℂ E.ambientDimension i) b :=
        (polynomialProjRatioMap ℂ E.ambientDimension i).commutes b
      rw [h1, ← constants_restrict E i b,
        TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : coordOpen E i ≤ ⊤)) x hx]
      exact hconst b
    | add P Q hP hQ =>
      simp only [map_add]
      exact K.add_mem hP hQ
    | mul_X P a hP =>
      simp only [map_mul]
      refine K.mul_mem hP ?_
      have h1 : polynomialProjRatioMap ℂ E.ambientDimension i (MvPolynomial.X a) =
          polynomialProjCoordinateRatio ℂ E.ambientDimension i (i.succAbove a) :=
        MvPolynomial.aeval_X _ a
      rw [h1]
      exact hratio a
  have hsec : ∀ s : Γ(X, coordOpen E i), X.presheaf.germ (coordOpen E i) x hx s ∈ K := by
    intro s
    obtain ⟨t, rfl⟩ := Scheme.Hom.app_surjective E.map
      (polynomialProjCoordinateOpen ℂ E.ambientDimension i)
      (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X ℂ i) (by decide)) s
    obtain ⟨z, rfl⟩ := (homogeneousPolynomialBasicOpenAwayEquiv (K := ℂ) i).surjective t
    have h := hpoly (polynomialProjCoordinateDehomogenization ℂ E.ambientDimension i z)
    rwa [polynomialProjRatioMap_coordinateDehomogenization] at h
  have hU := isAffineOpen_coordOpen E i
  let : Algebra Γ(X, coordOpen E i) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : coordOpen E i)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl r
  refine hdiv r _ (hsec s) (IsLocalization.map_units (X.presheaf.stalk x) s) ?_
  have ha := hsec a
  exact has ▸ ha

/-! ### The tangent derivation -/

section Derivation

variable {n : ℕ}

/-- The point derivation `h ↦ dh(0)·v` of `𝒪_{ℂⁿ,0}`. -/
def germDeriv (v : ComplexModel n) (h : HolGerm (ComplexModel n)) : ℂ :=
  ∑ j, v j * HolGerm.eval (coordinatePartial j h)

theorem germDeriv_zero (v : ComplexModel n) : germDeriv v 0 = 0 := by
  simp [germDeriv]

theorem germDeriv_add (v : ComplexModel n) (h k : HolGerm (ComplexModel n)) :
    germDeriv v (h + k) = germDeriv v h + germDeriv v k := by
  simp only [germDeriv, map_add, mul_add, Finset.sum_add_distrib]

theorem germDeriv_neg (v : ComplexModel n) (h : HolGerm (ComplexModel n)) :
    germDeriv v (-h) = -germDeriv v h := by
  simp only [germDeriv, map_neg, mul_neg, Finset.sum_neg_distrib]

/-- The Leibniz rule. -/
theorem germDeriv_mul (v : ComplexModel n) (h k : HolGerm (ComplexModel n)) :
    germDeriv v (h * k) =
      HolGerm.eval h * germDeriv v k + HolGerm.eval k * germDeriv v h := by
  simp only [germDeriv, Derivation.leibniz, smul_eq_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem germDeriv_algebraMap (v : ComplexModel n) (c : ℂ) :
    germDeriv v (algebraMap ℂ (HolGerm (ComplexModel n)) c) = 0 := by
  simp [germDeriv, Derivation.map_algebraMap]

theorem germDeriv_one (v : ComplexModel n) : germDeriv v 1 = 0 := by
  have h := germDeriv_algebraMap v 1
  rwa [map_one] at h

theorem germDeriv_coordinateGerm (v : ComplexModel n) (i : Fin n) :
    germDeriv v (coordinateGerm i) = v i := by
  simp only [germDeriv, coordinatePartial_coordinate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg (Ne.symm hji), map_zero, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- On a representative, the derivation is the Fréchet derivative at `0` applied to `v`. -/
theorem germDeriv_mk (v : ComplexModel n) (g : ComplexModel n → ℂ)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    germDeriv v (HolGerm.mk g hg) = fderiv ℂ g 0 v := by
  have hv : v = ∑ j, v j • (EuclideanSpace.single j (1 : ℂ) : ComplexModel n) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [germDeriv, coordinatePartial_mk, HolGerm.eval_mk]
  conv_rhs => rw [hv, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]

end Derivation

/-! ### The analytification of the local ring in the preferred chart -/

section Analytic

variable (f) (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance fsPosImmersionTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance fsPosImmersionCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance fsPosImmersionManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance fsPosImmersionAffineAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- `𝒪_{X,x} → 𝒪_{ℂⁿ,0}`: the analytic germ of an algebraic germ, read in the preferred chart
at `p` (centred at `p`). -/
def stalkToModel (p : SchemeComplexPoint f) :
    X.presheaf.stalk (schemeComplexPointImage f p) →+* HolGerm (ComplexModel n) :=
  (NativeHolGerm.chartEquiv p).toRingHom.comp (schemeNativeStalkGerm f n p)

/-- On the affine ring of the standard chart at `p`, this is the regular-germ algebra map. -/
theorem stalkToModel_regular (p : SchemeComplexPoint f) (a : SchemeCoordinateAffineRing f n p) :
    stalkToModel f n p (schemeCoordinateStalkEquiv f n p
        (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p) a)) =
      schemeCoordinateModelRegularAlgHom f n p a := by
  change NativeHolGerm.chartEquiv p (schemeNativeStalkGerm f n p _) = _
  rw [schemeNativeStalkGerm_regular, schemeNativeRegularGerm_chart]
  rfl

/-- The structural constants have constant analytic germs. -/
theorem stalkToModel_constants (p : SchemeComplexPoint f) (b : ℂ) :
    stalkToModel f n p (X.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial
        (schemeGlobalConstants f b)) =
      algebraMap ℂ (HolGerm (ComplexModel n)) b := by
  rw [← schemeCoordinateStalkEquiv_global f n p, schemeCoordinateGlobalCoefficient_const,
    stalkToModel_regular]
  exact (schemeCoordinateModelRegularAlgHom f n p).commutes b

/-- The kernel of the point derivation `r ↦ D_v(r^an)` of `𝒪_{X,x}`. -/
def tangentKernel (p : SchemeComplexPoint f) (v : ComplexModel n) :
    Subring (X.presheaf.stalk (schemeComplexPointImage f p)) where
  carrier := {r | germDeriv v (stalkToModel f n p r) = 0}
  mul_mem' := by
    intro a b ha hb
    change germDeriv v (stalkToModel f n p a) = 0 at ha
    change germDeriv v (stalkToModel f n p b) = 0 at hb
    change germDeriv v (stalkToModel f n p (a * b)) = 0
    rw [map_mul, germDeriv_mul, ha, hb, mul_zero, mul_zero, add_zero]
  one_mem' := by
    change germDeriv v (stalkToModel f n p 1) = 0
    rw [map_one, germDeriv_one]
  add_mem' := by
    intro a b ha hb
    change germDeriv v (stalkToModel f n p a) = 0 at ha
    change germDeriv v (stalkToModel f n p b) = 0 at hb
    change germDeriv v (stalkToModel f n p (a + b)) = 0
    rw [map_add, germDeriv_add, ha, hb, add_zero]
  zero_mem' := by
    change germDeriv v (stalkToModel f n p 0) = 0
    rw [map_zero, germDeriv_zero]
  neg_mem' := by
    intro a ha
    change germDeriv v (stalkToModel f n p a) = 0 at ha
    change germDeriv v (stalkToModel f n p (-a)) = 0
    rw [map_neg, germDeriv_neg, ha, neg_zero]

theorem mem_tangentKernel (p : SchemeComplexPoint f) (v : ComplexModel n)
    (r : X.presheaf.stalk (schemeComplexPointImage f p)) :
    r ∈ tangentKernel f n p v ↔ germDeriv v (stalkToModel f n p r) = 0 := Iff.rfl

/-- The kernel is closed under division by units. -/
theorem tangentKernel_div (p : SchemeComplexPoint f) (v : ComplexModel n)
    (r s : X.presheaf.stalk (schemeComplexPointImage f p)) (hs : s ∈ tangentKernel f n p v)
    (hu : IsUnit s) (hrs : r * s ∈ tangentKernel f n p v) : r ∈ tangentKernel f n p v := by
  rw [mem_tangentKernel] at hs hrs ⊢
  rw [map_mul, germDeriv_mul, hs, mul_zero, zero_add] at hrs
  have hne : HolGerm.eval (stalkToModel f n p s) ≠ 0 :=
    ((hu.map (stalkToModel f n p)).map HolGerm.eval).ne_zero
  exact (mul_eq_zero.mp hrs).resolve_left hne

/-- **Immersion, germ form.**  If the point derivation of a tangent vector `v` at `p ∈ Uᵢ(ℂ)`
kills the germs of the ratios `x_k/x_i`, `k ≠ i`, then `v = 0`. -/
theorem eq_zero_of_germDeriv_ratio_eq_zero (p : SchemeComplexPoint f)
    (i : Fin (E.ambientDimension + 1)) (hp : schemeComplexPointImage f p ∈ coordOpen E i)
    (v : ComplexModel n)
    (h : ∀ a : Fin E.ambientDimension, germDeriv v (stalkToModel f n p
      (X.presheaf.germ (coordOpen E i) (schemeComplexPointImage f p) hp
        (ratio E i (i.succAbove a)))) = 0) : v = 0 := by
  have hall : ∀ r, r ∈ tangentKernel f n p v :=
    stalk_generated E i (schemeComplexPointImage f p) hp (tangentKernel f n p v)
      (fun b => by rw [mem_tangentKernel, stalkToModel_constants, germDeriv_algebraMap])
      h (tangentKernel_div f n p v)
  ext j
  have hj := hall (schemeCoordinateStalkEquiv f n p
    (algebraMap (SchemeCoordinateAffineRing f n p) (SchemeCoordinateLocalRing f n p)
      (standardSmoothComplexChartFreeGenerator f n p j)))
  rw [mem_tangentKernel, stalkToModel_regular, schemeCoordinateModelRegularAlgHom_freeGenerator,
    germDeriv_add, germDeriv_coordinateGerm] at hj
  have hc : germDeriv v (HolGerm.constHom (standardSmoothComplexAlgebraPoint f n p
      (standardSmoothComplexChartFreeGenerator f n p j)) : HolGerm (ComplexModel n)) = 0 :=
    germDeriv_algebraMap v _
  rw [hc, add_zero] at hj
  simpa using hj

/-- The point derivation of the germ of a regular function is the derivative of its analytic
function in the preferred chart. -/
theorem germDeriv_stalkToModel_germ (U : X.Opens) (r : Γ(X, U)) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) (v : ComplexModel n) :
    germDeriv v (stalkToModel f n p (X.presheaf.germ U (schemeComplexPointImage f p) hp r)) =
      fderiv ℂ (fun z : ComplexModel n => schemeOpenRegularFunction f n E U r
          ((complexChartAt (n := n) p).val.symm z))
        ((complexChartAt (n := n) p).val p) v := by
  have hgerm := schemeOpenRegularFunction_germ f n E U r p hp
  change germDeriv v (NativeHolGerm.chartEquiv p (schemeNativeStalkGerm f n p _)) = _
  rw [← hgerm]
  obtain ⟨g, hg, hgeq⟩ := HolGerm.exists_eq_mk (NativeHolGerm.chartEquiv p
    (NativeHolGerm.mk (schemeOpenRegularFunction f n E U r)
      (schemeOpenRegularFunction_holomorphicAt f n E U r p hp)))
  have hcoe := congrArg (fun q : HolGerm (ComplexModel n) =>
    (q : Germ (𝓝 (0 : ComplexModel n)) ℂ)) hgeq
  simp only [NativeHolGerm.chartEquiv_mk, HolGerm.coe_mk] at hcoe
  have hev : (fun z : ComplexModel n => schemeOpenRegularFunction f n E U r
      ((complexChartAt (n := n) p).val.symm (z + (complexChartAt (n := n) p).val p))) =ᶠ[𝓝 0] g :=
    Germ.coe_eq.mp hcoe
  rw [hgeq, germDeriv_mk, ← hev.fderiv_eq,
    fderiv_comp_add_right (f := fun z : ComplexModel n => schemeOpenRegularFunction f n E U r
      ((complexChartAt (n := n) p).val.symm z)), zero_add]

/-- **The projective embedding is an immersion in the workspace charts.**  In the preferred
chart `e` at `p ∈ Uᵢ(ℂ)`, a vector `v` killed by the derivatives at `e p` of all the functions
`(x_k/x_i) ∘ e⁻¹`, `k ≠ i`, is zero. -/
theorem eq_zero_of_fderiv_ratio_eq_zero (p : SchemeComplexPoint f)
    (i : Fin (E.ambientDimension + 1)) (hp : schemeComplexPointImage f p ∈ coordOpen E i)
    (v : ComplexModel n)
    (h : ∀ a : Fin E.ambientDimension,
      fderiv ℂ (fun z : ComplexModel n => schemeOpenRegularFunction f n E (coordOpen E i)
          (ratio E i (i.succAbove a)) ((complexChartAt (n := n) p).val.symm z))
        ((complexChartAt (n := n) p).val p) v = 0) : v = 0 :=
  eq_zero_of_germDeriv_ratio_eq_zero f E n p i hp v fun a => by
    rw [germDeriv_stalkToModel_germ f E n]
    exact h a

end Analytic

end SGPT.NAPotential.FSPos

import SGPT.Foundations.Schemes.AffineChartSectionExtension

/-! # Actual polynomial projective line-section bounds

The genuine affine generators and a single homogeneous product of their actual
generic denominators place genuine global sections in the proved finite degree
coordinate Cech module. This is the polynomial-projective-space producer;
closed projective subschemes require a separate quotient/saturation bound.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace
open scoped DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {K I : Type u} [Field K] [Nonempty I]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual function field embeds in the actual full zero-prime localization,
using the native generic-point stalk isomorphism. -/
def homogeneousPolynomialFunctionFieldToFraction :
    (Proj (MvPolynomial.homogeneousSubmodule I K)).functionField →+*
      projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
        (homogeneousPolynomialZeroPrime (K := K) (I := I)) :=
  (algebraMap
    (HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule I K)
      (homogeneousPolynomialZeroPrime (K := K) (I := I)).asHomogeneousIdeal.toIdeal)
    (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
      (homogeneousPolynomialZeroPrime (K := K) (I := I)))).comp
    (((Proj (MvPolynomial.homogeneousSubmodule I K)).presheaf.stalkCongr
      (Inseparable.of_eq homogeneousPolynomialProj_genericPoint_eq_zero)).hom ≫
      (Proj.stalkIso (MvPolynomial.homogeneousSubmodule I K)
        homogeneousPolynomialZeroPrime).hom).hom

/-- Native stalk transport and homogeneous localization inclusion make this actual map faithful. -/
theorem homogeneousPolynomialFunctionFieldToFraction_injective :
    Function.Injective (homogeneousPolynomialFunctionFieldToFraction (K := K) (I := I)) :=
  (HomogeneousLocalization.val_injective _).comp (ConcreteCategory.bijective_of_isIso _).injective

/-- The actual zero prime lies in every genuine nonempty projective open. -/
theorem homogeneousPolynomialZeroPrime_mem_nonempty_open
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) [Nonempty U] :
    homogeneousPolynomialZeroPrime (K := K) (I := I) ∈ U := by
  simpa only [homogeneousPolynomialProj_genericPoint_eq_zero] using
    genericPoint_mem_nonempty_open U

/-- The full fraction of a native function-field germ is exactly its actual value at zero prime. -/
theorem homogeneousPolynomialFunctionFieldToFraction_germ
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) [Nonempty U]
    (r : Γ(Proj (MvPolynomial.homogeneousSubmodule I K), U)) :
    homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField U r) =
      (r.val ⟨homogeneousPolynomialZeroPrime,
        homogeneousPolynomialZeroPrime_mem_nonempty_open U⟩).val := by
  let X := Proj (MvPolynomial.homogeneousSubmodule I K)
  let e := Inseparable.of_eq (homogeneousPolynomialProj_genericPoint_eq_zero (K := K) (I := I))
  let he : homogeneousPolynomialZeroPrime (K := K) (I := I) ⤳ genericPoint X := e.ge
  have hg : (X.presheaf.stalkCongr e).hom (X.germToFunctionField U r) =
      X.presheaf.germ U homogeneousPolynomialZeroPrime
        (he.mem_open U.isOpen (genericPoint_mem_nonempty_open U)) r :=
    congrArg (fun f => f r)
      (X.presheaf.germ_stalkSpecializes (genericPoint_mem_nonempty_open U) he)
  change ((Proj.stalkIso' (MvPolynomial.homogeneousSubmodule I K) homogeneousPolynomialZeroPrime)
    ((X.presheaf.stalkCongr e).hom (X.germToFunctionField U r))).val = _
  rw [hg]
  exact congrArg HomogeneousLocalization.val
    (Proj.stalkIso'_germ (MvPolynomial.homogeneousSubmodule I K) U homogeneousPolynomialZeroPrime
      (he.mem_open U.isOpen (genericPoint_mem_nonempty_open U)) r)

/-- Every actual coordinate chart is nonempty, with its actual zero-prime point. -/
instance homogeneousPolynomialBasicOpenNonempty (i : I) :
    Nonempty (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) :=
  ⟨⟨homogeneousPolynomialZeroPrime, homogeneousPolynomialZeroPrime_mem i⟩⟩

/-- Actual homogeneous Away coordinates give the actual full fraction of their native germs. -/
theorem homogeneousPolynomialFunctionFieldToFraction_away (i : I)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) :
    homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField _
        (homogeneousPolynomialBasicOpenAwayEquiv i z)) =
      homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
        (homogeneousPolynomialZeroPrime_mem i) z.val := by
  rw [homogeneousPolynomialFunctionFieldToFraction_germ]
  exact homogeneousPolynomialBasicOpenAwayEquiv_eval i z homogeneousPolynomialZeroPrime
    (homogeneousPolynomialZeroPrime_mem i)

/-- A true nonzero regular coordinate function has a true nonzero homogeneous numerator. -/
theorem homogeneousPolynomialChart_nonzeroNumerator (i : I)
    (b : Γ(Proj (MvPolynomial.homogeneousSubmodule I K),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)))
    (hb : b ≠ 0) :
    ∃ (n : ℕ) (p : MvPolynomial I K),
      p ∈ MvPolynomial.homogeneousSubmodule I K n ∧ p ≠ 0 ∧
      homogeneousPolynomialFunctionFieldToFraction
        ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField _ b) *
          algebraMap (MvPolynomial I K)
            (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
              homogeneousPolynomialZeroPrime) (MvPolynomial.X i ^ n) =
        algebraMap (MvPolynomial I K)
          (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
            homogeneousPolynomialZeroPrime) p := by
  let z := (homogeneousPolynomialBasicOpenAwayEquiv i).symm b
  obtain ⟨n, p, hp, hz⟩ := HomogeneousLocalization.Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.isHomogeneous_X K i) z
  have hfrac : z.val * algebraMap (MvPolynomial I K)
      (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) (MvPolynomial.X i ^ n) =
      algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) p := by
    rw [← hz, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  have hzero := congrArg (homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
    (homogeneousPolynomialZeroPrime_mem i)) hfrac
  rw [map_mul, homogeneousPolynomialCoordinateAtPoint_algebraMap,
    homogeneousPolynomialCoordinateAtPoint_algebraMap] at hzero
  have hbz : homogeneousPolynomialBasicOpenAwayEquiv i z = b :=
    (homogeneousPolynomialBasicOpenAwayEquiv i).apply_symm_apply b
  rw [← homogeneousPolynomialFunctionFieldToFraction_away, hbz] at hzero
  refine ⟨n, p, by simpa using hp, ?_, hzero⟩
  intro hpzero
  have hn : homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField _ b) ≠ 0 := by
    intro h
    apply hb
    apply (Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField_injective _
    apply homogeneousPolynomialFunctionFieldToFraction_injective
    simpa only [map_zero] using h
  have hx : algebraMap (MvPolynomial I K)
      (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
        homogeneousPolynomialZeroPrime) (MvPolynomial.X i ^ n) ≠ 0 := by
    intro h
    exact pow_ne_zero n (MvPolynomial.X_ne_zero i)
      (homogeneousPolynomialZeroPrime_algebraMap_injective (by simpa only [map_zero] using h))
  rw [hpzero, map_zero] at hzero
  exact mul_ne_zero hn hx hzero

/-- Every actual bundle section space on polynomial Proj uses its actual constant-polynomial action. -/
instance homogeneousPolynomialBundleSectionsModule
    (L : (Proj (MvPolynomial.homogeneousSubmodule I K)).Modules)
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) : Module K Γ(L, U) :=
  Module.compHom _ (homogeneousPolynomialProjConstants U)

/-- Actual structural constants have their native base-field values in the actual full localization. -/
theorem homogeneousPolynomialFunctionFieldToFraction_constants
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) [Nonempty U] (r : K) :
    homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField U
        (homogeneousPolynomialProjConstants U r)) =
      algebraMap K (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
        homogeneousPolynomialZeroPrime) r := by
  rw [homogeneousPolynomialFunctionFieldToFraction_germ]
  exact homogeneousPolynomialLocalization_algebraMap_val _ r

variable {L : (Proj (MvPolynomial.homogeneousSubmodule I K)).Modules}
  {W : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens} [Nonempty W]

/-- All true local sections have coefficients in one true generic frame and the same full fraction ring. -/
def homogeneousPolynomialFixedFrameFullCoefficients (e : LocalBundleFrame L W)
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) [Nonempty U] :
    Γ(L, U) →ₗ[K]
      projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
        homogeneousPolynomialZeroPrime where
  toFun s := homogeneousPolynomialFunctionFieldToFraction (fixedFrameGenericCoefficients e U s)
  map_add' s t := by rw [map_add, map_add]
  map_smul' r s := by
    change homogeneousPolynomialFunctionFieldToFraction
      (fixedFrameGenericCoefficients e U (homogeneousPolynomialProjConstants U r • s)) = _
    rw [(fixedFrameGenericCoefficients e U).map_smul]
    change homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField U
        (homogeneousPolynomialProjConstants U r) * fixedFrameGenericCoefficients e U s) = _
    rw [map_mul, homogeneousPolynomialFunctionFieldToFraction_constants]
    exact (Algebra.smul_def r _).symm

/-- The actual full fraction coefficients in the fixed frame commute with every genuine restriction. -/
theorem homogeneousPolynomialFixedFrameFullCoefficients_restrict (e : LocalBundleFrame L W)
    {U V : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens} [Nonempty U] [Nonempty V]
    (i : V ⟶ U) (s : Γ(L, U)) :
    homogeneousPolynomialFixedFrameFullCoefficients e V (L.presheaf.map i.op s) =
      homogeneousPolynomialFixedFrameFullCoefficients e U s := by
  apply congrArg homogeneousPolynomialFunctionFieldToFraction
  exact fixedFrameGenericCoefficients_restrict e i s

/-- Actual global coefficients in the fixed generic frame are faithful from the genuine line atlas. -/
theorem homogeneousPolynomialFixedFrameFullCoefficients_global_injective
    (a : LineBundleAtlas L) (e : LocalBundleFrame L W) :
    Function.Injective (homogeneousPolynomialFixedFrameFullCoefficients e ⊤) := by
  intro s t h
  apply bundleGenericGerm_global_injective a
  apply (genericBundleFiberFrame e).injective
  exact homogeneousPolynomialFunctionFieldToFraction_injective h

/-- Finitely generated true affine sections produce true homogeneous denominator bounds,
in one fixed generic frame on every actual coordinate chart. -/
theorem LineBundleAtlas.homogeneousCoordinateDenominator (a : LineBundleAtlas L)
    (e : LocalBundleFrame L W) (i : I) :
    ∃ (n : ℕ) (p : MvPolynomial I K), p ∈ MvPolynomial.homogeneousSubmodule I K n ∧ p ≠ 0 ∧
      ∀ s : Γ(L, Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)),
      ∃ r : Γ(Proj (MvPolynomial.homogeneousSubmodule I K),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)),
        algebraMap (MvPolynomial I K)
          (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
            homogeneousPolynomialZeroPrime) p * homogeneousPolynomialFixedFrameFullCoefficients e _ s =
        algebraMap (MvPolynomial I K)
          (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
            homogeneousPolynomialZeroPrime) (MvPolynomial.X i ^ n) *
          homogeneousPolynomialFunctionFieldToFraction
            ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField _ r) := by
  obtain ⟨b, hb⟩ := a.affineOpenFixedFrame_clearDenominator e
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule I K)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) (by decide))
  obtain ⟨n, p, hp, hpn, hpeq⟩ := homogeneousPolynomialChart_nonzeroNumerator i b.val
    ((mem_nonZeroDivisors_iff_ne_zero).mp b.property)
  refine ⟨n, p, hp, hpn, fun s => ?_⟩
  obtain ⟨r, hr⟩ := hb s
  refine ⟨r, ?_⟩
  have he := congrArg homogeneousPolynomialFunctionFieldToFraction hr
  change homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField _ r) =
    homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField _ b.val *
        fixedFrameGenericCoefficients e _ s) at he
  rw [map_mul] at he
  change _ * homogeneousPolynomialFunctionFieldToFraction (fixedFrameGenericCoefficients e _ s) = _
  rw [← hpeq, he]
  ring

section FiniteCoordinates

variable [Fintype I]

omit [Nonempty I] in
/-- A true degree-zero coordinate fraction multiplied by a genuine homogeneous polynomial
has its derived total degree in the actual coordinate localization. -/
theorem homogeneousPolynomialAway_multiplyDegree (i : I) (k : ℕ)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i))
    (p : MvPolynomial I K) (hp : p ∈ MvPolynomial.homogeneousSubmodule I K k) :
    z.val * algebraMap (MvPolynomial I K)
      (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) p ∈
      coordinateHomogeneousLocalization (K := K) k i := by
  classical
  change coordinateLocalizationToLaurent i
    (z.val * algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i)) p) ∈
    AddMonoidAlgebra.supported K K {d : I → ℤ | (∑ j, d j) = (k : ℤ)}
  rw [map_mul, coordinateLocalizationToLaurent_algebraMap]
  apply AddMonoidAlgebra.mem_supported.mpr
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset _ _ hd)
  have hza := (AddMonoidAlgebra.mem_supported.mp (homogeneousPolynomialAway_degree_zero i z)) ha
  have hpb := (AddMonoidAlgebra.mem_supported.mp (polynomialToProjectiveLaurent_homogeneous p hp)) hb
  change (∑ j, a j) = 0 at hza
  change (∑ j, b j) = (k : ℤ) at hpb
  change (∑ j, (a + b) j) = (k : ℤ)
  simp only [Pi.add_apply, Finset.sum_add_distrib, hza, hpb, zero_add]

/-- The actual homogeneous multiplier on chart i replaces its own numerator by its coordinate power. -/
def homogeneousCoordinateBoundPolynomial (n : I → ℕ) (p : I → MvPolynomial I K) (i : I) :
    MvPolynomial I K := by
  classical
  exact MvPolynomial.X i ^ n i * ∏ j ∈ Finset.univ.erase i, p j

omit [Nonempty I] in
/-- Each actual chart multiplier has the common sum degree. -/
theorem homogeneousCoordinateBoundPolynomial_degree (n : I → ℕ) (p : I → MvPolynomial I K)
    (hp : ∀ i, p i ∈ MvPolynomial.homogeneousSubmodule I K (n i)) (i : I) :
    homogeneousCoordinateBoundPolynomial n p i ∈ MvPolynomial.homogeneousSubmodule I K (∑ j, n j) := by
  classical
  have hx : MvPolynomial.X i ^ n i ∈ MvPolynomial.homogeneousSubmodule I K (n i) := by
    simpa only [smul_eq_mul, mul_one] using
      SetLike.pow_mem_graded (A := MvPolynomial.homogeneousSubmodule I K) (n i)
        (show MvPolynomial.X i ∈ MvPolynomial.homogeneousSubmodule I K 1 from
          MvPolynomial.isHomogeneous_X K i)
  have hrest := SetLike.prod_mem_graded (MvPolynomial.homogeneousSubmodule I K) n p
    (F := Finset.univ.erase i) (fun j _ => hp j)
  have hd : n i + ∑ j ∈ Finset.univ.erase i, n j = ∑ j, n j := by
    rw [add_comm]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
  exact hd ▸ SetLike.mul_mem_graded hx hrest

/-- True affine generic denominators produce one genuine nonzero homogeneous bound
for every true global section, uniformly on all true coordinate charts. -/
theorem LineBundleAtlas.homogeneousGlobalSectionBound (a : LineBundleAtlas L)
    (e : LocalBundleFrame L W) :
    ∃ (m : ℕ) (h : MvPolynomial I K), h ∈ MvPolynomial.homogeneousSubmodule I K m ∧ h ≠ 0 ∧
      ∀ s : Γ(L, ⊤), ∀ i : I, ∃ z : coordinateHomogeneousLocalization (K := K) m i,
        homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
          (homogeneousPolynomialZeroPrime_mem i) z.val =
        algebraMap (MvPolynomial I K)
          (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
            homogeneousPolynomialZeroPrime) h * homogeneousPolynomialFixedFrameFullCoefficients e ⊤ s := by
  classical
  choose n p hp hpn hb using a.homogeneousCoordinateDenominator e
  let m := ∑ i, n i
  let h := ∏ i, p i
  refine ⟨m, h, SetLike.prod_mem_graded _ _ _ (fun i _ => hp i),
    Finset.prod_ne_zero_iff.mpr (fun i _ => hpn i), fun s i => ?_⟩
  obtain ⟨r, hr⟩ := hb i (L.presheaf.map (homOfLE le_top).op s)
  let z := (homogeneousPolynomialBasicOpenAwayEquiv i).symm r
  let q := homogeneousCoordinateBoundPolynomial n p i
  refine ⟨⟨z.val * algebraMap (MvPolynomial I K)
    (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) q,
      homogeneousPolynomialAway_multiplyDegree i m z q
        (homogeneousCoordinateBoundPolynomial_degree n p hp i)⟩, ?_⟩
  rw [homogeneousPolynomialFixedFrameFullCoefficients_restrict] at hr
  have hrz : homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField _ r) =
      homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
        (homogeneousPolynomialZeroPrime_mem i) z.val := by
    rw [← homogeneousPolynomialFunctionFieldToFraction_away]
    exact congrArg (fun t => homogeneousPolynomialFunctionFieldToFraction
      ((Proj (MvPolynomial.homogeneousSubmodule I K)).germToFunctionField _ t))
      ((homogeneousPolynomialBasicOpenAwayEquiv i).apply_symm_apply r).symm
  rw [hrz] at hr
  change homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
    (homogeneousPolynomialZeroPrime_mem i)
    (z.val * algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i)) q) = _
  rw [map_mul, homogeneousPolynomialCoordinateAtPoint_algebraMap]
  have hh : h = p i * ∏ j ∈ Finset.univ.erase i, p j := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [hh, map_mul]
  change _ = _
  dsimp only [q, homogeneousCoordinateBoundPolynomial]
  rw [map_mul]
  linear_combination - (algebraMap (MvPolynomial I K)
    (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
      homogeneousPolynomialZeroPrime) (∏ j ∈ Finset.univ.erase i, p j)) * hr

/-- Actual full-fraction evaluation of an actual coordinate homogeneous degree piece. -/
def coordinateHomogeneousEvaluationAtZero (k : ℕ) (i : I) :
    coordinateHomogeneousLocalization (K := K) k i →ₗ[K]
      projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
        homogeneousPolynomialZeroPrime where
  toFun z := homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
    (homogeneousPolynomialZeroPrime_mem i) z.val
  map_add' z w := map_add _ z.val w.val
  map_smul' r z := by
    change homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
      (homogeneousPolynomialZeroPrime_mem i) (r • z.val) = r • _
    rw [Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply K (MvPolynomial I K)
        (Localization.Away (MvPolynomial.X i)) r,
      homogeneousPolynomialCoordinateAtPoint_algebraMap,
      ← IsScalarTower.algebraMap_apply K (MvPolynomial I K)
        (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
          homogeneousPolynomialZeroPrime) r]

/-- Actual zero-prime evaluation is faithful on each actual localized homogeneous degree piece. -/
theorem coordinateHomogeneousEvaluationAtZero_injective (k : ℕ) (i : I) :
    Function.Injective (coordinateHomogeneousEvaluationAtZero (K := K) k i) :=
  (homogeneousPolynomialCoordinateAtZero_injective i).comp Subtype.val_injective

/-- The derived homogeneous bound produces an actual faithful map of genuine global sections
into the actual degree-m homogeneous coordinate Cech module. -/
theorem LineBundleAtlas.exists_globalCechEmbedding (a : LineBundleAtlas L)
    (e : LocalBundleFrame L W) :
    ∃ m : ℕ, ∃ q : Γ(L, ⊤) →ₗ[K] coordinateHomogeneousCech (K := K) (I := I) m,
      Function.Injective q := by
  classical
  obtain ⟨m, h, _, hne, hz⟩ := a.homogeneousGlobalSectionBound e
  choose z hz using hz
  let H := algebraMap (MvPolynomial I K)
    (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
      homogeneousPolynomialZeroPrime) h
  have hH : H ≠ 0 := by
    intro hh
    exact hne (homogeneousPolynomialZeroPrime_algebraMap_injective (by simpa only [map_zero] using hh))
  let q : Γ(L, ⊤) →ₗ[K] coordinateHomogeneousCech (K := K) (I := I) m := {
    toFun s := ⟨fun i => z s i, fun i j =>
      homogeneousPolynomialCoordinateAtZero_compare i j (z s i).val (z s j).val
        ((hz s i).trans (hz s j).symm)⟩
    map_add' s t := by
      apply Subtype.ext
      funext i
      apply coordinateHomogeneousEvaluationAtZero_injective m i
      change coordinateHomogeneousEvaluationAtZero m i (z (s + t) i) =
        coordinateHomogeneousEvaluationAtZero m i (z s i + z t i)
      rw [map_add]
      dsimp only [coordinateHomogeneousEvaluationAtZero, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hz, hz, hz, map_add, mul_add]
    map_smul' r s := by
      apply Subtype.ext
      funext i
      apply coordinateHomogeneousEvaluationAtZero_injective m i
      change coordinateHomogeneousEvaluationAtZero m i (z (r • s) i) =
        coordinateHomogeneousEvaluationAtZero m i (r • z s i)
      rw [map_smul]
      dsimp only [coordinateHomogeneousEvaluationAtZero, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hz, hz, map_smul, mul_smul_comm] }
  refine ⟨m, q, fun s t hst => ?_⟩
  apply homogeneousPolynomialFixedFrameFullCoefficients_global_injective a e
  let i : I := Classical.arbitrary I
  have he := congrArg (fun v : coordinateHomogeneousCech (K := K) (I := I) m =>
    coordinateHomogeneousEvaluationAtZero m i (v.val i)) hst
  change homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
      (homogeneousPolynomialZeroPrime_mem i) (z s i).val =
    homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
      (homogeneousPolynomialZeroPrime_mem i) (z t i).val at he
  rw [hz, hz] at he
  exact mul_left_cancel₀ hH he

/-- Genuine global sections embed in the genuine O(m) sheaf sections through the accepted actual Cech gluing equivalence. -/
theorem LineBundleAtlas.exists_globalTwistingEmbedding [Nontrivial I]
    (a : LineBundleAtlas L) :
    ∃ m : ℕ, ∃ q : Γ(L, ⊤) →ₗ[K]
      bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) m) ⊤,
      Function.Injective q := by
  obtain ⟨m, q, hq⟩ := a.exists_globalCechEmbedding (a.frame a.genericIndex)
  let e := homogeneousPolynomialTwistingGlobalCechEquiv (K := K) (I := I) m
  exact ⟨m, e.symm.toLinearMap.comp q, e.symm.injective.comp hq⟩

/-- Actual global sections of every genuine line atlas on polynomial projective space are finite-dimensional. -/
theorem LineBundleAtlas.polynomialProjGlobalSections_finite [Nontrivial I]
    (a : LineBundleAtlas L) : Module.Finite K Γ(L, ⊤) := by
  obtain ⟨m, q, hq⟩ := a.exists_globalCechEmbedding (a.frame a.genericIndex)
  let := coordinateHomogeneousCech_finite (K := K) (I := I) m
  exact FiniteDimensional.of_injective (K := K) (V := Γ(L, ⊤))
    (V₂ := coordinateHomogeneousCech (K := K) (I := I) m) q hq

/-- Actual polynomial-projective tensor-power section spaces are finite-dimensional from genuine power atlases. -/
theorem LineBundleAtlas.polynomialProjPowerGlobalSections_finite [Nontrivial I]
    (a : LineBundleAtlas L) (n : ℕ) : Module.Finite K Γ(bundleTensorPower L n, ⊤) :=
  (a.tensorPower n).polynomialProjGlobalSections_finite

end FiniteCoordinates

end

end SGPT.Foundations.Schemes

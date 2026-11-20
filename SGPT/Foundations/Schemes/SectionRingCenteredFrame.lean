import SGPT.Foundations.Schemes.SectionRingValuation

/-! # Genuine frames at an arbitrary valuation center

The atlas cover chooses a chart through the actual center. Integral geometry
puts the generic point in that chart. All powers use the same actual frame,
and local-stalk units prove independence of the section values.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsIntegral X]

/-- The genuine atlas cover chooses a chart through the specified actual center. -/
def LineBundleAtlas.centerIndex {L : X.Modules} (a : LineBundleAtlas L) (x : X) : a.I :=
  Classical.choose (a.covers x)

omit [IsIntegral X] in
/-- The chosen chart contains the actual center by the atlas cover theorem. -/
theorem LineBundleAtlas.centerIndex_mem {L : X.Modules} (a : LineBundleAtlas L) (x : X) :
    x ∈ a.opens (a.centerIndex x) := Classical.choose_spec (a.covers x)

/-- A chart through the actual center is genuinely nonempty. -/
instance LineBundleAtlas.centerOpenNonempty {L : X.Modules} (a : LineBundleAtlas L) (x : X) :
    Nonempty (a.opens (a.centerIndex x)) := ⟨⟨x, a.centerIndex_mem x⟩⟩

/-- Integral geometry puts the actual generic point in the chosen center chart. -/
theorem LineBundleAtlas.centerOpen_genericPoint {L : X.Modules} (a : LineBundleAtlas L)
    (x : X) : genericPoint X ∈ a.opens (a.centerIndex x) :=
  genericPoint_mem_nonempty_open _

/-- The actual transition on the overlap maps to an actual unit of the center's local ring. -/
def localBundleFrameTransitionAtCenter {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (x : X)
    (hx : x ∈ U) (hy : x ∈ V) : (X.presheaf.stalk x)ˣ :=
  Units.map (X.presheaf.germ (U ⊓ V) x ⟨hx, hy⟩).hom.toMonoidHom
    (localBundleFrameTransition e f (homOfLE inf_le_left) (homOfLE inf_le_right))

omit [IsIntegral X] in
/-- The actual local-stalk transition of the power frames is the power of the actual transition unit. -/
theorem localBundleFrameTransitionAtCenter_tensorPower {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (x : X)
    (hx : x ∈ U) (hy : x ∈ V) (n : ℕ) :
    localBundleFrameTransitionAtCenter (e.tensorPower n) (f.tensorPower n) x hx hy =
      localBundleFrameTransitionAtCenter e f x hx hy ^ n := by
  unfold localBundleFrameTransitionAtCenter
  rw [localBundleFrameTransition_tensorPower, map_pow]

/-- The native function-field transition is the native image of that actual local-stalk unit. -/
theorem localBundleFrameTransitionAtCenter_functionField {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (x : X)
    (hx : x ∈ U) (hy : x ∈ V) :
    letI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx, hy⟩⟩
    algebraMap (X.presheaf.stalk x) X.functionField
      (localBundleFrameTransitionAtCenter e f x hx hy : X.presheaf.stalk x) =
      X.germToFunctionField (U ⊓ V)
        (localBundleFrameTransition e f (homOfLE inf_le_left) (homOfLE inf_le_right) :
          X.sheaf.obj.obj (op (U ⊓ V))) := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx, hy⟩⟩
  exact X.algebraMap_germ_eq_germToFunctionField (U := U ⊓ V) (x := x) ⟨hx, hy⟩ _

/-- Every genuine transition between frames through the center has valuation zero. -/
theorem localBundleFrameTransitionAtCenter_valuation_zero {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (x : X)
    (hx : x ∈ U) (hy : x ∈ V) (v : AddValuation X.functionField (WithTop ℝ))
    (hcenter : ∀ r : X.presheaf.stalk x,
      (0 : WithTop ℝ) ≤ v (algebraMap (X.presheaf.stalk x) X.functionField r)) :
    letI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx, hy⟩⟩
    v (X.germToFunctionField (U ⊓ V)
      (localBundleFrameTransition e f (homOfLE inf_le_left) (homOfLE inf_le_right) :
        X.sheaf.obj.obj (op (U ⊓ V)))) = 0 := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx, hy⟩⟩
  rw [← localBundleFrameTransitionAtCenter_functionField e f x hx hy]
  exact valuation_unit_eq_zero v (algebraMap (X.presheaf.stalk x) X.functionField) hcenter
    (localBundleFrameTransitionAtCenter e f x hx hy)

/-- Actual SAME-frame power coefficients obey the native function-field transition law. -/
theorem LocalBundleFrame.globalGenericPowerCoefficient_transition {L : X.Modules}
    {U V W : X.Opens} [Nonempty U] [Nonempty V] [Nonempty W]
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V)
    (n : ℕ) (s : bundlePowerGlobalSections L n) :
    globalSectionToFunctionField (f.tensorPower n) s =
      X.germToFunctionField W (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) ^ n *
        globalSectionToFunctionField (e.tensorPower n) s := by
  change X.germToFunctionField V ((f.tensorPower n).coefficients (𝟙 _)
      ((bundleTensorPower L n).val.map (homOfLE le_top).op s)) =
    X.germToFunctionField W (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) ^ n *
      X.germToFunctionField U ((e.tensorPower n).coefficients (𝟙 _)
        ((bundleTensorPower L n).val.map (homOfLE le_top).op s))
  rw [← germToFunctionField_restrict j, ← germToFunctionField_restrict i]
  have h := LocalBundleFrame.global_coefficients_transition e f i j n s
  have hg := congrArg (fun r : X.sheaf.obj.obj (op W) => X.germToFunctionField W r) h
  simpa only [Scheme.sheaf, SheafedSpace.sheaf, map_mul, map_pow] using hg

/-- Section values in every tensor degree are intrinsically independent of the genuine frame at the center. -/
theorem LocalBundleFrame.globalGenericPowerCoefficient_valuation_independent
    {L : X.Modules} {U V : X.Opens} [Nonempty U] [Nonempty V]
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (x : X)
    (hx : x ∈ U) (hy : x ∈ V) (v : AddValuation X.functionField (WithTop ℝ))
    (hcenter : ∀ r : X.presheaf.stalk x,
      (0 : WithTop ℝ) ≤ v (algebraMap (X.presheaf.stalk x) X.functionField r))
    (n : ℕ) (s : bundlePowerGlobalSections L n) :
    v (globalSectionToFunctionField (f.tensorPower n) s) =
      v (globalSectionToFunctionField (e.tensorPower n) s) := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx, hy⟩⟩
  rw [LocalBundleFrame.globalGenericPowerCoefficient_transition e f
    (homOfLE inf_le_left : U ⊓ V ⟶ U) (homOfLE inf_le_right : U ⊓ V ⟶ V),
    v.map_mul, v.map_pow,
    localBundleFrameTransitionAtCenter_valuation_zero e f x hx hy v hcenter,
    nsmul_zero, zero_add]

/-- The actual center coefficient in every degree uses the tensor power of ONE genuine center frame. -/
def IntrinsicLineBundle.centerCoefficient (L : IntrinsicLineBundle X) (x : X) (n : ℕ) :
    bundlePowerGlobalSections L.sheaf n →ₗ[Γ(X, ⊤)] X.functionField :=
  globalSectionToFunctionField ((L.atlas.frame (L.atlas.centerIndex x)).tensorPower n)

/-- The actual center coefficient is the native germ of the actual native chart coefficient. -/
theorem IntrinsicLineBundle.centerCoefficient_eq_germ (L : IntrinsicLineBundle X)
    (x : X) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    L.centerCoefficient x n s = X.germToFunctionField (L.atlas.opens (L.atlas.centerIndex x))
      (atlasPowerGlobalCoefficients L.atlas n (L.atlas.centerIndex x) s) := rfl

/-- Genuine integral-scheme geometry makes center-frame evaluation faithful. -/
theorem IntrinsicLineBundle.centerCoefficient_injective (L : IntrinsicLineBundle X)
    (x : X) (n : ℕ) : Function.Injective (L.centerCoefficient x n) :=
  globalSectionToFunctionField_injective (L.atlas.tensorPower n)
    ((L.atlas.frame (L.atlas.centerIndex x)).tensorPower n)

/-- The actual sheaf-glued section product multiplies the SAME-center-frame coefficients. -/
theorem IntrinsicLineBundle.centerCoefficient_mul (L : IntrinsicLineBundle X) (x : X)
    (m n : ℕ) (s : bundlePowerGlobalSections L.sheaf m)
    (t : bundlePowerGlobalSections L.sheaf n) :
    L.centerCoefficient x (m + n) (atlasPowerGlobalMul L.atlas m n s t) =
      L.centerCoefficient x m s * L.centerCoefficient x n t := by
  simp only [L.centerCoefficient_eq_germ, atlasPowerGlobalMul_coefficients, map_mul]

/-- The actual section-ring unit has center coefficient one. -/
theorem IntrinsicLineBundle.centerCoefficient_one (L : IntrinsicLineBundle X) (x : X) :
    L.centerCoefficient x 0 (bundlePowerGlobalOne L.sheaf) = 1 := by
  rw [L.centerCoefficient_eq_germ, atlasPowerGlobalCoefficients_one, map_one]

/-- The actual degree-zero regular section has its intrinsic native generic germ. -/
theorem IntrinsicLineBundle.centerCoefficient_degree_zero (L : IntrinsicLineBundle X)
    (x : X) (r : Γ(X, ⊤)) : L.centerCoefficient x 0 r = X.germToFunctionField ⊤ r := by
  rw [L.centerCoefficient_eq_germ, atlasPowerGlobalCoefficients_degree_zero]
  exact germToFunctionField_restrict (homOfLE le_top) r

/-- An actual valuation center on the native local ring gives nonnegative coefficients in every degree. -/
theorem IntrinsicLineBundle.centerCoefficient_nonneg (L : IntrinsicLineBundle X) (x : X)
    (v : AddValuation X.functionField (WithTop ℝ))
    (hcenter : ∀ r : X.presheaf.stalk x,
      (0 : WithTop ℝ) ≤ v (algebraMap (X.presheaf.stalk x) X.functionField r))
    (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    (0 : WithTop ℝ) ≤ v (L.centerCoefficient x n s) := by
  rw [L.centerCoefficient_eq_germ,
    ← X.algebraMap_germ_eq_germToFunctionField (L.atlas.centerIndex_mem x)]
  exact hcenter _

/-- Any genuine local frame through the actual center gives the same intrinsic section value. -/
theorem IntrinsicLineBundle.centerCoefficient_valuation_eq_frame
    (L : IntrinsicLineBundle X) (x : X) {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L.sheaf U) (hx : x ∈ U)
    (v : AddValuation X.functionField (WithTop ℝ))
    (hcenter : ∀ r : X.presheaf.stalk x,
      (0 : WithTop ℝ) ≤ v (algebraMap (X.presheaf.stalk x) X.functionField r))
    (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    v (L.centerCoefficient x n s) = v (globalSectionToFunctionField (e.tensorPower n) s) :=
  LocalBundleFrame.globalGenericPowerCoefficient_valuation_independent e
    (L.atlas.frame (L.atlas.centerIndex x)) x hx (L.atlas.centerIndex_mem x) v hcenter n s

/-- A genuine homogeneous section gives the monomial of its actual center coefficient. -/
def IntrinsicLineBundle.centerMonomial (L : IntrinsicLineBundle X) (x : X) (n : ℕ) :
    bundlePowerGlobalSections L.sheaf n →+ Polynomial X.functionField :=
  (Polynomial.monomial n).toAddMonoidHom.comp (L.centerCoefficient x n).toAddMonoidHom

/-- The actual section ring maps to the function-field polynomial ring in a genuine center frame. -/
def IntrinsicLineBundle.centerPolynomial (L : IntrinsicLineBundle X) (x : X) :
    L.sectionRing →+* Polynomial X.functionField := by
  let := atlasPowerGradedCommRing L.atlas
  exact DirectSum.toSemiring (L.centerMonomial x)
    (by
      change Polynomial.monomial 0 (L.centerCoefficient x 0 (bundlePowerGlobalOne L.sheaf)) = 1
      rw [L.centerCoefficient_one]
      rfl)
    (by
      intro m n s t
      change Polynomial.monomial (m + n)
        (L.centerCoefficient x (m + n) (atlasPowerGlobalMul L.atlas m n s t)) =
          Polynomial.monomial m (L.centerCoefficient x m s) *
            Polynomial.monomial n (L.centerCoefficient x n t)
      rw [L.centerCoefficient_mul, Polynomial.monomial_mul_monomial])

/-- The genuine homogeneous section has its literal actual center-frame monomial. -/
theorem IntrinsicLineBundle.centerPolynomial_ofSection (L : IntrinsicLineBundle X)
    (x : X) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    L.centerPolynomial x (L.ofSection n s) = Polynomial.monomial n (L.centerCoefficient x n s) := by
  let := atlasPowerGradedCommRing L.atlas
  change DirectSum.toAddMonoid (L.centerMonomial x)
    (DirectSum.of (bundlePowerGlobalSections L.sheaf) n s) = _
  exact DirectSum.toAddMonoid_of _ n s

/-- Actual polynomial coefficients are the actual center coefficients of the actual degree components. -/
theorem IntrinsicLineBundle.centerPolynomial_coeff (L : IntrinsicLineBundle X)
    (x : X) (s : L.sectionRing) (n : ℕ) :
    (L.centerPolynomial x s).coeff n = L.centerCoefficient x n (L.degreeComponent n s) := by
  classical
  induction s using DirectSum.induction_on with
  | zero => simp
  | of j s =>
    change (L.centerPolynomial x (L.ofSection j s)).coeff n = _
    rw [L.centerPolynomial_ofSection]
    by_cases h : j = n
    · subst j
      simp [IntrinsicLineBundle.degreeComponent]
    · simp [Polynomial.coeff_monomial, h, IntrinsicLineBundle.degreeComponent,
        DirectSum.of_eq_of_ne j n s (Ne.symm h)]
  | add s t hs ht => simp only [map_add, Polynomial.coeff_add, hs, ht]

/-- Integral geometry produces the faithful actual section-ring polynomial embedding at the center. -/
theorem IntrinsicLineBundle.centerPolynomial_injective (L : IntrinsicLineBundle X) (x : X) :
    Function.Injective (L.centerPolynomial x) := by
  intro s t h
  apply DFinsupp.ext
  intro n
  apply L.centerCoefficient_injective x n
  exact (L.centerPolynomial_coeff x s n).symm.trans
    ((congrArg (fun p : Polynomial X.functionField => p.coeff n) h).trans
      (L.centerPolynomial_coeff x t n))

/-- The actual section Gauss valuation is constructed from the actual polynomial embedding at the center. -/
def IntrinsicLineBundle.centerGaussValuation (L : IntrinsicLineBundle X) (x : X)
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) :
    AddValuation L.sectionRing (WithTop ℝ) :=
  (gaussAddValuation v c).comap (L.centerPolynomial x)

theorem IntrinsicLineBundle.centerGaussValuation_ofSection (L : IntrinsicLineBundle X)
    (x : X) (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) (n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    L.centerGaussValuation x v c (L.ofSection n s) =
      v (L.centerCoefficient x n s) + (((n : ℝ) * c : ℝ) : WithTop ℝ) := by
  change gaussAddValuation v c (L.centerPolynomial x (L.ofSection n s)) = _
  rw [L.centerPolynomial_ofSection, gaussAddValuation_monomial]

/-- The actual valuation minimum is the literal SAME-center-frame homogeneous coefficient minimum. -/
theorem IntrinsicLineBundle.centerGaussValuation_eq_inf (L : IntrinsicLineBundle X)
    (x : X) (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) (s : L.sectionRing) :
    L.centerGaussValuation x v c s = (L.centerPolynomial x s).support.inf
      (fun n => v (L.centerCoefficient x n (L.degreeComponent n s)) +
        (((n : ℝ) * c : ℝ) : WithTop ℝ)) := by
  change gaussAddValuation v c (L.centerPolynomial x s) = _
  rw [gaussAddValuation_eq_inf]
  simp only [L.centerPolynomial_coeff]

/-- A native local valuation center and nonnegative fiber weight center the entire actual section ring. -/
theorem IntrinsicLineBundle.centerGaussValuation_nonneg (L : IntrinsicLineBundle X)
    (x : X) (v : AddValuation X.functionField (WithTop ℝ)) {c : ℝ} (hc : 0 ≤ c)
    (hcenter : ∀ r : X.presheaf.stalk x,
      (0 : WithTop ℝ) ≤ v (algebraMap (X.presheaf.stalk x) X.functionField r))
    (s : L.sectionRing) : (0 : WithTop ℝ) ≤ L.centerGaussValuation x v c s := by
  rw [L.centerGaussValuation_eq_inf]
  apply Finset.le_inf
  intro n _
  exact add_nonneg (L.centerCoefficient_nonneg x v hcenter n _)
    (WithTop.coe_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) hc))

section BaseField

variable {K : Type u} [Field K]

/-- Center-frame evaluation is K-linear for the actual native base-field actions. -/
def IntrinsicLineBundle.centerCoefficientOverBase (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
    letI := schemeFunctionFieldAlgebra f
    bundlePowerGlobalSections L.sheaf n →ₗ[K] X.functionField :=
  globalSectionToFunctionFieldOverBase f ((L.atlas.frame (L.atlas.centerIndex x)).tensorPower n)

theorem IntrinsicLineBundle.centerCoefficientOverBase_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    L.centerCoefficientOverBase f x n s = L.centerCoefficient x n s := rfl

theorem IntrinsicLineBundle.centerCoefficientOverBase_injective (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) :
    Function.Injective (L.centerCoefficientOverBase f x n) := L.centerCoefficient_injective x n

/-- The center coefficient space is the literal actual K-linear image of genuine global sections. -/
def IntrinsicLineBundle.centerCoefficientSpace (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) :
    letI := schemeFunctionFieldAlgebra f
    Submodule K X.functionField := by
  letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  letI := schemeFunctionFieldAlgebra f
  exact LinearMap.range (L.centerCoefficientOverBase f x n)

/-- Integral-scheme geometry identifies the actual section module with its actual center coefficient image. -/
def IntrinsicLineBundle.centerCoefficientEquiv (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
    letI := schemeFunctionFieldAlgebra f
    bundlePowerGlobalSections L.sheaf n ≃ₗ[K] L.centerCoefficientSpace f x n := by
  letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  letI := schemeFunctionFieldAlgebra f
  exact LinearEquiv.ofInjective (L.centerCoefficientOverBase f x n)
    (L.centerCoefficientOverBase_injective f x n)

theorem IntrinsicLineBundle.centerCoefficientEquiv_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    (L.centerCoefficientEquiv f x n s : X.functionField) = L.centerCoefficient x n s := rfl

/-- Multiplication of genuine section coefficients stays in the actual sum-degree center image. -/
theorem IntrinsicLineBundle.centerCoefficientSpace_mul_mem (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (m n : ℕ) {r q : X.functionField} :
    r ∈ L.centerCoefficientSpace f x m → q ∈ L.centerCoefficientSpace f x n →
      r * q ∈ L.centerCoefficientSpace f x (m + n) := by
  rintro ⟨s, hs⟩ ⟨t, ht⟩
  refine ⟨atlasPowerGlobalMul L.atlas m n s t, ?_⟩
  change L.centerCoefficient x (m + n) (atlasPowerGlobalMul L.atlas m n s t) = r * q
  exact (L.centerCoefficient_mul x m n s t).trans (congrArg₂ (· * ·) hs ht)

/-- The actual center coefficient image in degree zero contains the actual unit. -/
theorem IntrinsicLineBundle.centerCoefficientSpace_one_mem (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) : (1 : X.functionField) ∈ L.centerCoefficientSpace f x 0 :=
  ⟨bundlePowerGlobalOne L.sheaf, L.centerCoefficient_one x⟩

/-- The actual local-ring valuation center gives nonnegativity on the entire literal actual image space. -/
theorem IntrinsicLineBundle.centerCoefficientSpace_nonneg (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (v : AddValuation X.functionField (WithTop ℝ))
    (hcenter : ∀ r : X.presheaf.stalk x,
      (0 : WithTop ℝ) ≤ v (algebraMap (X.presheaf.stalk x) X.functionField r))
    (n : ℕ) (s : L.centerCoefficientSpace f x n) : (0 : WithTop ℝ) ≤ v (s : X.functionField) := by
  obtain ⟨t, ht⟩ := s.property
  change L.centerCoefficient x n t = (s : X.functionField) at ht
  exact ht ▸ L.centerCoefficient_nonneg x v hcenter n t

/-- The actual section-ring representation at the center preserves the actual structural K-algebra. -/
def IntrinsicLineBundle.centerPolynomialOverBase (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) :
    letI := L.sectionRingAlgebra f
    letI := schemeFunctionFieldAlgebra f
    L.sectionRing →ₐ[K] Polynomial X.functionField := by
  letI := L.sectionRingAlgebra f
  letI := schemeFunctionFieldAlgebra f
  exact { L.centerPolynomial x with
    commutes' := fun r => by
      change L.centerPolynomial x (L.sectionRingBaseMap f r) =
        Polynomial.C (X.germToFunctionField ⊤ (schemeGlobalConstants f r))
      rw [L.sectionRingBaseMap_apply, L.centerPolynomial_ofSection,
        L.centerCoefficient_degree_zero, Polynomial.monomial_zero_left]
      rfl }

theorem IntrinsicLineBundle.centerPolynomialOverBase_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (s : L.sectionRing) :
    L.centerPolynomialOverBase f x s = L.centerPolynomial x s := rfl

theorem IntrinsicLineBundle.centerPolynomialOverBase_injective (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) : Function.Injective (L.centerPolynomialOverBase f x) :=
  L.centerPolynomial_injective x

/-- Every genuine homogeneous section has actual center-coefficient-times-fiber factorization. -/
theorem IntrinsicLineBundle.centerPolynomialOverBase_ofSection (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    L.centerPolynomialOverBase f x (L.ofSection n s) =
      Polynomial.C (L.centerCoefficient x n s) * Polynomial.X ^ n :=
  (L.centerPolynomial_ofSection x n s).trans Polynomial.C_mul_X_pow_eq_monomial.symm

/-- Every coefficient of the actual polynomial embedding belongs to the actual center image space. -/
theorem IntrinsicLineBundle.centerPolynomial_coeff_mem (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (s : L.sectionRing) (n : ℕ) :
    (L.centerPolynomialOverBase f x s).coeff n ∈ L.centerCoefficientSpace f x n :=
  ⟨L.degreeComponent n s, (L.centerPolynomial_coeff x s n).symm⟩

/-- The actual native section ring decomposes over the literal actual center coefficient images. -/
def IntrinsicLineBundle.centerImageDecomposition (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) :
    letI := schemeFunctionFieldAlgebra f
    letI := L.sectionRingAlgebra f
    (⨁ n : ℕ, L.centerCoefficientSpace f x n) ≃ₗ[K] L.sectionRing := by
  letI := schemeFunctionFieldAlgebra f
  letI := L.sectionRingAlgebra f
  letI : ∀ n, Module K (bundlePowerGlobalSections L.sheaf n) :=
    fun n => schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  exact (DirectSum.congrLinearEquiv (fun n => (L.centerCoefficientEquiv f x n).symm)).trans
    (L.sectionRingDecomposition f)

theorem IntrinsicLineBundle.centerImageDecomposition_of (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) (s : L.centerCoefficientSpace f x n) :
    L.centerImageDecomposition f x (DirectSum.of (fun j => L.centerCoefficientSpace f x j) n s) =
      L.ofSection n ((L.centerCoefficientEquiv f x n).symm s) := by
  change DirectSum.map (fun j => (L.centerCoefficientEquiv f x j).symm.toAddMonoidHom)
    (DirectSum.of (fun j => L.centerCoefficientSpace f x j) n s) = _
  exact DirectSum.map_of (α := fun j => L.centerCoefficientSpace f x j)
    (β := bundlePowerGlobalSections L.sheaf)
    (fun j => (L.centerCoefficientEquiv f x j).symm.toAddMonoidHom) n s

/-- The actual image-space factorization uses the genuine selected frame at the actual center. -/
theorem IntrinsicLineBundle.centerPolynomial_image_factorization (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (n : ℕ) (s : L.centerCoefficientSpace f x n) :
    L.centerPolynomialOverBase f x (L.centerImageDecomposition f x
      (DirectSum.of (fun j => L.centerCoefficientSpace f x j) n s)) =
      Polynomial.C (s : X.functionField) * Polynomial.X ^ n := by
  rw [L.centerImageDecomposition_of, L.centerPolynomialOverBase_ofSection]
  apply congrArg (fun r : X.functionField => Polynomial.C r * Polynomial.X ^ n)
  exact (L.centerCoefficientEquiv_apply f x n ((L.centerCoefficientEquiv f x n).symm s)).symm.trans
    (congrArg (fun t : L.centerCoefficientSpace f x n => (t : X.functionField))
      ((L.centerCoefficientEquiv f x n).apply_symm_apply s))

/-- Actual center-image decomposition coordinates are literally the actual polynomial coefficients. -/
theorem IntrinsicLineBundle.centerPolynomial_image_coefficient (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X)
    (s : ⨁ n : ℕ, L.centerCoefficientSpace f x n) (n : ℕ) :
    (L.centerPolynomial x (L.centerImageDecomposition f x s)).coeff n = (s n : X.functionField) := by
  rw [L.centerPolynomial_coeff]
  change L.centerCoefficient x n ((L.centerCoefficientEquiv f x n).symm (s n)) =
    (s n : X.functionField)
  exact (L.centerCoefficientEquiv_apply f x n ((L.centerCoefficientEquiv f x n).symm (s n))).symm.trans
    (congrArg (fun t : L.centerCoefficientSpace f x n => (t : X.functionField))
      ((L.centerCoefficientEquiv f x n).apply_symm_apply (s n)))

/-- The genuine centered section filtration uses the native K-action and an actual valuation. -/
def IntrinsicLineBundle.centerCoefficientFiltration (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (v : AddValuation X.functionField (WithTop ℝ))
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) (n : ℕ) (a : ℝ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
    Submodule K (bundlePowerGlobalSections L.sheaf n) := by
  letI := schemeFunctionFieldAlgebra f
  letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  exact valuationFiltration v (L.centerCoefficientOverBase f x n) htrivial a

theorem IntrinsicLineBundle.mem_centerCoefficientFiltration (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (v : AddValuation X.functionField (WithTop ℝ))
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) (n : ℕ) (a : ℝ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    s ∈ L.centerCoefficientFiltration f x v htrivial n a ↔
      (a : WithTop ℝ) ≤ v (L.centerCoefficient x n s) := Iff.rfl

/-- Actual centered section threshold subspaces multiply into the actual sum-degree sum threshold. -/
theorem IntrinsicLineBundle.centerCoefficientFiltration_mul (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) (v : AddValuation X.functionField (WithTop ℝ))
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    (m n : ℕ) (a b : ℝ) {s : bundlePowerGlobalSections L.sheaf m}
    {t : bundlePowerGlobalSections L.sheaf n}
    (hs : s ∈ L.centerCoefficientFiltration f x v htrivial m a)
    (ht : t ∈ L.centerCoefficientFiltration f x v htrivial n b) :
    atlasPowerGlobalMul L.atlas m n s t ∈
      L.centerCoefficientFiltration f x v htrivial (m + n) (a + b) := by
  change ((a + b : ℝ) : WithTop ℝ) ≤ v (L.centerCoefficient x (m + n)
    (atlasPowerGlobalMul L.atlas m n s t))
  rw [L.centerCoefficient_mul]
  exact valuation_product_threshold v hs ht

/-- The actual threshold submodule is independent of any genuine local frame at the actual center. -/
theorem IntrinsicLineBundle.centerCoefficientFiltration_eq_frame (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : X) {U : X.Opens} [Nonempty U]
    (e : LocalBundleFrame L.sheaf U) (hx : x ∈ U)
    (v : AddValuation X.functionField (WithTop ℝ))
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    (hcenter : ∀ r : X.presheaf.stalk x,
      (0 : WithTop ℝ) ≤ v (algebraMap (X.presheaf.stalk x) X.functionField r)) (n : ℕ) (a : ℝ) :
    letI := schemeFunctionFieldAlgebra f
    letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
    L.centerCoefficientFiltration f x v htrivial n a =
      valuationFiltration v (globalSectionToFunctionFieldOverBase f (e.tensorPower n)) htrivial a := by
  let := schemeFunctionFieldAlgebra f
  let := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  ext s
  change ((a : WithTop ℝ) ≤ v (L.centerCoefficient x n s)) ↔
    ((a : WithTop ℝ) ≤ v (globalSectionToFunctionField (e.tensorPower n) s))
  rw [L.centerCoefficient_valuation_eq_frame x e hx v hcenter]

end BaseField

end

end SGPT.Foundations.Schemes

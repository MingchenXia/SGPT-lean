import SGPT.Foundations.Schemes.SectionRingGenericEmbedding
import SGPT.Foundations.Schemes.GaussWeights
import SGPT.Foundations.Schemes.GradedColength
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing

/-! # Actual Gauss valuations of the intrinsic section ring

The polynomial and fraction-field valuations are constructed from the actual
function-field valuation. Their restriction to the actual sheaf section ring
uses the checked same-frame generic embedding. Base triviality and actual
coefficient nonnegativity are visible hypotheses where needed.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum nonZeroDivisors

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false

section FractionGauss

variable {F : Type*} [Field F]

/-- A finite real logarithmic weight is top exactly at zero. -/
theorem logWeight_eq_top_iff (r : ℝ) : logWeight r = ⊤ ↔ r = 0 := by
  by_cases hr : r = 0 <;> simp [logWeight, hr]

/-- The constructed polynomial Gauss valuation is finite on every nonzero polynomial. -/
theorem gaussAddValuation_top_iff (v : AddValuation F (WithTop ℝ)) (c : ℝ)
    (p : Polynomial F) : gaussAddValuation v c p = ⊤ ↔ p = 0 := by
  change logWeight (gaussAbsoluteValue v c p) = ⊤ ↔ p = 0
  exact (logWeight_eq_top_iff _).trans ((gaussAbsoluteValue v c).eq_zero (x := p))

/-- Equal actual coefficient valuations give equal constructed Gauss valuations. -/
theorem gaussAddValuation_eq_of_coefficient_values (v : AddValuation F (WithTop ℝ))
    (c : ℝ) (p q : Polynomial F) (h : ∀ n, v (p.coeff n) = v (q.coeff n)) :
    gaussAddValuation v c p = gaussAddValuation v c q := by
  apply le_antisymm
  · rw [gaussAddValuation_eq_inf v c q]
    apply Finset.le_inf
    intro n _
    rw [← h n]
    exact gaussAddValuation_le_coefficient v c p n
  · rw [gaussAddValuation_eq_inf v c p]
    apply Finset.le_inf
    intro n _
    rw [h n]
    exact gaussAddValuation_le_coefficient v c q n

/-- All actual fraction-field denominators lie outside the support of the constructed valuation. -/
theorem gaussDenominators_nonvanishing (v : AddValuation F (WithTop ℝ)) (c : ℝ) :
    (Polynomial F)⁰ ≤ (gaussAddValuation v c).toValuation.supp.primeCompl := by
  intro p hp
  change gaussAddValuation v c p ≠ ⊤
  exact mt (gaussAddValuation_top_iff v c p).mp (nonZeroDivisors.ne_zero hp)

/-- The actual polynomial Gauss valuation extended to the actual rational function field. -/
def fractionGaussValuation (v : AddValuation F (WithTop ℝ)) (c : ℝ) :
    AddValuation (FractionRing (Polynomial F)) (WithTop ℝ) :=
  (gaussAddValuation v c).toValuation.extendToLocalization
    (gaussDenominators_nonvanishing v c) (FractionRing (Polynomial F))

/-- Restriction of the constructed rational valuation recovers the constructed polynomial valuation. -/
theorem fractionGaussValuation_polynomial (v : AddValuation F (WithTop ℝ)) (c : ℝ)
    (p : Polynomial F) :
    fractionGaussValuation v c (algebraMap (Polynomial F) (FractionRing (Polynomial F)) p) =
      gaussAddValuation v c p :=
  Valuation.extendToLocalization_apply_map_apply (gaussAddValuation v c).toValuation
    (gaussDenominators_nonvanishing v c) (FractionRing (Polynomial F)) p

end FractionGauss

variable {X : Scheme.{u}} [IsIntegral X]

/-- The actual section ring is a domain because its actual polynomial representation is injective. -/
instance intrinsicLineBundleSectionRingIsDomain (L : IntrinsicLineBundle X) :
    IsDomain L.sectionRing :=
  Function.Injective.isDomain L.genericPolynomial L.genericPolynomial_injective

/-- The actual section Gauss valuation is the comap of the constructed polynomial valuation. -/
def IntrinsicLineBundle.sectionGaussValuation (L : IntrinsicLineBundle X)
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) :
    AddValuation L.sectionRing (WithTop ℝ) :=
  (gaussAddValuation v c).comap L.genericPolynomial

theorem IntrinsicLineBundle.sectionGaussValuation_apply (L : IntrinsicLineBundle X)
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) (x : L.sectionRing) :
    L.sectionGaussValuation v c x = gaussAddValuation v c (L.genericPolynomial x) := rfl

/-- Literal homogeneous source weights are a consequence of actual section multiplication and Gauss. -/
theorem IntrinsicLineBundle.sectionGaussValuation_ofSection (L : IntrinsicLineBundle X)
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) (n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    L.sectionGaussValuation v c (L.ofSection n s) =
      v (L.genericCoefficient n s) + (((n : ℝ) * c : ℝ) : WithTop ℝ) := by
  rw [L.sectionGaussValuation_apply, L.genericPolynomial_ofSection,
    gaussAddValuation_monomial]

/-- Multiplicativity is produced by the actual section-ring valuation. -/
theorem IntrinsicLineBundle.sectionGaussValuation_mul (L : IntrinsicLineBundle X)
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) (x y : L.sectionRing) :
    L.sectionGaussValuation v c (x * y) =
      L.sectionGaussValuation v c x + L.sectionGaussValuation v c y :=
  (L.sectionGaussValuation v c).map_mul x y

/-- The actual finite-support Gauss minimum on the intrinsic ring. -/
theorem IntrinsicLineBundle.sectionGaussValuation_eq_inf (L : IntrinsicLineBundle X)
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) (x : L.sectionRing) :
    L.sectionGaussValuation v c x = (L.genericPolynomial x).support.inf
      (fun n => v (L.genericCoefficient n (L.degreeComponent n x)) +
        (((n : ℝ) * c : ℝ) : WithTop ℝ)) := by
  rw [L.sectionGaussValuation_apply, gaussAddValuation_eq_inf]
  simp only [L.genericPolynomial_coeff]

/-- A literal ring threshold is equivalent to all literal homogeneous coefficient thresholds. -/
theorem IntrinsicLineBundle.sectionGaussValuation_threshold_iff (L : IntrinsicLineBundle X)
    (v : AddValuation X.functionField (WithTop ℝ)) (c a : ℝ) (x : L.sectionRing) :
    (a : WithTop ℝ) ≤ L.sectionGaussValuation v c x ↔
      ∀ n, (a : WithTop ℝ) ≤ v (L.genericCoefficient n (L.degreeComponent n x)) +
        (((n : ℝ) * c : ℝ) : WithTop ℝ) := by
  constructor
  · intro h n
    have hn := gaussAddValuation_le_coefficient v c (L.genericPolynomial x) n
    rw [L.genericPolynomial_coeff] at hn
    exact h.trans hn
  · intro h
    rw [L.sectionGaussValuation_eq_inf]
    exact Finset.le_inf (fun n _ => h n)

section BaseField

variable {K : Type u} [Field K]

/-- The actual section-ring representation in the actual rational function field. -/
def IntrinsicLineBundle.genericRationalFunction (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) :
    letI := L.sectionRingAlgebra f
    letI := schemeFunctionFieldAlgebra f
    L.sectionRing →ₐ[K] FractionRing (Polynomial X.functionField) := by
  letI := L.sectionRingAlgebra f
  letI := schemeFunctionFieldAlgebra f
  exact (IsScalarTower.toAlgHom K (Polynomial X.functionField)
    (FractionRing (Polynomial X.functionField))).comp (L.genericPolynomialOverBase f)

theorem IntrinsicLineBundle.genericRationalFunction_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (x : L.sectionRing) :
    L.genericRationalFunction f x =
      algebraMap (Polynomial X.functionField) (FractionRing (Polynomial X.functionField))
        (L.genericPolynomial x) := rfl

/-- Integral generic evaluation and fraction-ring injectivity produce the actual field embedding. -/
theorem IntrinsicLineBundle.genericRationalFunction_injective (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) : Function.Injective (L.genericRationalFunction f) :=
  (IsFractionRing.injective (Polynomial X.functionField)
    (FractionRing (Polynomial X.functionField))).comp L.genericPolynomial_injective

/-- The actual fiber coordinate is the image of the polynomial indeterminate. -/
def genericRationalFiber (X : Scheme.{u}) [IsIntegral X] :
    FractionRing (Polynomial X.functionField) :=
  algebraMap (Polynomial X.functionField) (FractionRing (Polynomial X.functionField)) Polynomial.X

/-- Actual coefficient images are mapped by the native constant-field inclusion. -/
def IntrinsicLineBundle.genericRationalCoefficient (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) (s : L.genericCoefficientSpace f n) :
    FractionRing (Polynomial X.functionField) :=
  algebraMap X.functionField (FractionRing (Polynomial X.functionField)) (s : X.functionField)

/-- Homogeneous field representatives factor into actual coefficients and powers of the actual fiber. -/
theorem IntrinsicLineBundle.genericRational_image_factorization (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (n : ℕ) (s : L.genericCoefficientSpace f n) :
    L.genericRationalFunction f (L.genericImageDecomposition f
        (DirectSum.of (fun j => L.genericCoefficientSpace f j) n s)) =
      L.genericRationalCoefficient f n s * genericRationalFiber X ^ n := by
  rw [L.genericRationalFunction_apply]
  have h := L.genericPolynomial_image_factorization f n s
  change L.genericPolynomial _ = _ at h
  rw [h, map_mul, map_pow]
  change _ = algebraMap X.functionField (FractionRing (Polynomial X.functionField))
    (s : X.functionField) * _
  congr 1

/-- The constructed rational valuation has the chosen literal fiber weight. -/
theorem fractionGaussValuation_fiber (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ) :
    fractionGaussValuation v c (genericRationalFiber X) = (c : WithTop ℝ) :=
  (fractionGaussValuation_polynomial v c Polynomial.X).trans (gaussAddValuation_X v c)

/-- The rational coefficient valuation is the original actual function-field valuation. -/
theorem IntrinsicLineBundle.fractionGaussValuation_coefficient (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (n : ℕ) (s : L.genericCoefficientSpace f n) :
    fractionGaussValuation v c (L.genericRationalCoefficient f n s) = v (s : X.functionField) := by
  unfold IntrinsicLineBundle.genericRationalCoefficient
  rw [IsScalarTower.algebraMap_apply X.functionField (Polynomial X.functionField)
    (FractionRing (Polynomial X.functionField)), Polynomial.algebraMap_apply,
    fractionGaussValuation_polynomial, gaussAddValuation_C]
  rfl

/-- The actual field-valued ring representation restricts the actual rational Gauss valuation. -/
theorem IntrinsicLineBundle.fractionGaussValuation_section (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (x : L.sectionRing) :
    fractionGaussValuation v c (L.genericRationalFunction f x) = L.sectionGaussValuation v c x :=
  fractionGaussValuation_polynomial v c (L.genericPolynomial x)

/-- Triviality on the actual base field passes to the CONSTRUCTED rational Gauss valuation. -/
theorem fractionGaussValuation_base_trivial (f : X ⟶ Spec (.of K))
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) :
    letI := schemeFunctionFieldAlgebra f
    ∀ t : K, t ≠ 0 → fractionGaussValuation v c
      (algebraMap K (FractionRing (Polynomial X.functionField)) t) = 0 := by
  let := schemeFunctionFieldAlgebra f
  intro t ht
  rw [IsScalarTower.algebraMap_apply K (Polynomial X.functionField)
    (FractionRing (Polynomial X.functionField)), fractionGaussValuation_polynomial,
    Polynomial.algebraMap_apply, gaussAddValuation_C]
  exact htrivial t ht

/-- The genuine section coefficient filtration, with the native K action through the scheme base. -/
def IntrinsicLineBundle.coefficientFiltration (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) (n : ℕ) (a : ℝ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
    Submodule K (bundlePowerGlobalSections L.sheaf n) := by
  letI := schemeFunctionFieldAlgebra f
  letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  exact valuationFiltration v (L.genericCoefficientOverBase f n) htrivial a

theorem IntrinsicLineBundle.mem_coefficientFiltration (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) (n : ℕ) (a : ℝ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    s ∈ L.coefficientFiltration f v htrivial n a ↔
      (a : WithTop ℝ) ≤ v (L.genericCoefficient n s) := Iff.rfl

/-- Multiplicativity of the genuine section filtration comes from actual sheaf multiplication. -/
theorem IntrinsicLineBundle.coefficientFiltration_mul (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) (m n : ℕ) (a b : ℝ)
    {s : bundlePowerGlobalSections L.sheaf m} {t : bundlePowerGlobalSections L.sheaf n}
    (hs : s ∈ L.coefficientFiltration f v htrivial m a)
    (ht : t ∈ L.coefficientFiltration f v htrivial n b) :
    atlasPowerGlobalMul L.atlas m n s t ∈ L.coefficientFiltration f v htrivial (m + n) (a + b) := by
  change ((a + b : ℝ) : WithTop ℝ) ≤ v (L.genericCoefficient (m + n)
    (atlasPowerGlobalMul L.atlas m n s t))
  rw [L.genericCoefficient_mul]
  exact valuation_product_threshold v hs ht

/-- A literal regular-chart center gives nonnegative valuation on all actual section coefficients. -/
theorem IntrinsicLineBundle.genericCoefficient_nonneg_of_chart_center
    (L : IntrinsicLineBundle X) (v : AddValuation X.functionField (WithTop ℝ))
    (hchart : ∀ r : Γ(X, L.atlas.opens L.atlas.genericIndex),
      (0 : WithTop ℝ) ≤ v (X.germToFunctionField (L.atlas.opens L.atlas.genericIndex) r))
    (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s) := by
  rw [L.genericCoefficient_eq_germ]
  exact hchart _

/-- A genuine center on the actual local ring gives nonnegative SAME-frame section coefficients. -/
theorem IntrinsicLineBundle.genericCoefficient_nonneg_of_local_center
    (L : IntrinsicLineBundle X) (v : AddValuation X.functionField (WithTop ℝ))
    (x : X) (hx : x ∈ L.atlas.opens L.atlas.genericIndex)
    (hcenter : ∀ r : X.presheaf.stalk x,
      (0 : WithTop ℝ) ≤ v (algebraMap (X.presheaf.stalk x) X.functionField r))
    (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s) := by
  rw [L.genericCoefficient_eq_germ, ← X.algebraMap_germ_eq_germToFunctionField hx]
  exact hcenter _

/-- Nonnegative actual coefficients and fiber weight derive the center on the entire actual section ring. -/
theorem IntrinsicLineBundle.sectionGaussValuation_nonneg (L : IntrinsicLineBundle X)
    (v : AddValuation X.functionField (WithTop ℝ)) {c : ℝ} (hc : 0 ≤ c)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (x : L.sectionRing) :
    (0 : WithTop ℝ) ≤ L.sectionGaussValuation v c x := by
  apply (L.sectionGaussValuation_threshold_iff v c 0 x).mpr
  intro n
  exact add_nonneg (hcoeff n _) (WithTop.coe_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) hc))

/-- The actual rational field representation is centered when the literal coefficients and fiber are. -/
theorem IntrinsicLineBundle.genericRationalFunction_centered (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    {c : ℝ} (hc : 0 ≤ c)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (x : L.sectionRing) :
    (0 : WithTop ℝ) ≤ fractionGaussValuation v c (L.genericRationalFunction f x) :=
  (L.fractionGaussValuation_section f v c x).symm ▸ L.sectionGaussValuation_nonneg v hc hcoeff x

/-- The literal threshold ideal on the actual intrinsic section ring. -/
def IntrinsicLineBundle.sectionValuationIdeal (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    {c : ℝ} (hc : 0 ≤ c)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (a : ℝ) : Ideal L.sectionRing := by
  letI := L.sectionRingAlgebra f
  letI := schemeFunctionFieldAlgebra f
  exact valuationIdeal (fractionGaussValuation v c) (L.genericRationalFunction f).toRingHom
    (L.genericRationalFunction_centered f v hc hcoeff) a

theorem IntrinsicLineBundle.mem_sectionValuationIdeal (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    {c : ℝ} (hc : 0 ≤ c)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (a : ℝ) (x : L.sectionRing) :
    x ∈ L.sectionValuationIdeal f v hc hcoeff a ↔
      (a : WithTop ℝ) ≤ L.sectionGaussValuation v c x := by
  change (a : WithTop ℝ) ≤ fractionGaussValuation v c (L.genericRationalFunction f x) ↔ _
  rw [L.fractionGaussValuation_section]

/-- Threshold ideal membership decomposes into the actual homogeneous inequalities. -/
theorem IntrinsicLineBundle.mem_sectionValuationIdeal_iff_components (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    {c : ℝ} (hc : 0 ≤ c)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (a : ℝ) (x : L.sectionRing) :
    x ∈ L.sectionValuationIdeal f v hc hcoeff a ↔
      ∀ n, (a : WithTop ℝ) ≤ v (L.genericCoefficient n (L.degreeComponent n x)) +
        (((n : ℝ) * c : ℝ) : WithTop ℝ) :=
  (L.mem_sectionValuationIdeal f v hc hcoeff a x).trans
    (L.sectionGaussValuation_threshold_iff v c a x)

/-- The actual ideals multiply into the sum threshold. -/
theorem IntrinsicLineBundle.sectionValuationIdeal_mul_le (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    {c : ℝ} (hc : 0 ≤ c)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (a b : ℝ) :
    L.sectionValuationIdeal f v hc hcoeff a * L.sectionValuationIdeal f v hc hcoeff b ≤
      L.sectionValuationIdeal f v hc hcoeff (a + b) :=
  valuationIdeal_mul_le _ _ _ a b

/-- Actual positive thresholds yield proper actual section-ring ideals. -/
theorem IntrinsicLineBundle.sectionValuationIdeal_ne_top (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    {c : ℝ} (hc : 0 ≤ c)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) {a : ℝ} (ha : 0 < a) :
    L.sectionValuationIdeal f v hc hcoeff a ≠ ⊤ :=
  valuationIdeal_ne_top _ _ _ ha

/-- The polynomial coefficient of an actual image-space decomposition is literally its component. -/
theorem IntrinsicLineBundle.genericPolynomial_image_coefficient (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K))
    (x : ⨁ n : ℕ, L.genericCoefficientSpace f n) (n : ℕ) :
    (L.genericPolynomial (L.genericImageDecomposition f x)).coeff n =
      (x n : X.functionField) := by
  rw [L.genericPolynomial_coeff]
  change L.genericCoefficient n ((L.genericCoefficientEquiv f n).symm (x n)) =
    (x n : X.functionField)
  exact (L.genericCoefficientEquiv_apply f n ((L.genericCoefficientEquiv f n).symm (x n))).symm.trans
    (congrArg (fun t : L.genericCoefficientSpace f n => (t : X.functionField))
      ((L.genericCoefficientEquiv f n).apply_symm_apply (x n)))

/-- Native image coordinates are exactly the degree components' actual generic coefficients. -/
theorem IntrinsicLineBundle.genericCoefficient_image_component (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K))
    (x : ⨁ n : ℕ, L.genericCoefficientSpace f n) (n : ℕ) :
    L.genericCoefficient n (L.degreeComponent n (L.genericImageDecomposition f x)) =
      (x n : X.functionField) :=
  (L.genericPolynomial_coeff (L.genericImageDecomposition f x) n).symm.trans
    (L.genericPolynomial_image_coefficient f x n)

/-- The actual image-space threshold inequalities contain no chosen graded representation data. -/
theorem IntrinsicLineBundle.sectionGaussValuation_image_threshold_iff (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ)) (c a : ℝ)
    (x : ⨁ n : ℕ, L.genericCoefficientSpace f n) :
    (a : WithTop ℝ) ≤ L.sectionGaussValuation v c (L.genericImageDecomposition f x) ↔
      ∀ n, (a : WithTop ℝ) ≤ v (x n : X.functionField) +
        (((n : ℝ) * c : ℝ) : WithTop ℝ) := by
  rw [L.sectionGaussValuation_threshold_iff]
  simp only [L.genericCoefficient_image_component]

/-- Degree scaling preserves the actual generic coefficient values by base triviality. -/
theorem IntrinsicLineBundle.genericPolynomial_degreeScaling_coefficient_value
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K))
    (v : AddValuation X.functionField (WithTop ℝ))
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    {t : K} (ht : t ≠ 0) (x : ⨁ n : ℕ, L.genericCoefficientSpace f n) (n : ℕ) :
    v ((L.genericPolynomial (L.genericImageDecomposition f
      (gradedDegreeScaling t x))).coeff n) =
      v ((L.genericPolynomial (L.genericImageDecomposition f x)).coeff n) := by
  let := schemeFunctionFieldAlgebra f
  rw [L.genericPolynomial_image_coefficient, L.genericPolynomial_image_coefficient,
    gradedDegreeScaling_apply]
  change v (t ^ n • (x n : X.functionField)) = v (x n : X.functionField)
  rw [Algebra.smul_def, v.map_mul, htrivial (t ^ n) (pow_ne_zero n ht), zero_add]

/-- The actual section Gauss valuation is invariant under the genuine homogeneous degree action. -/
theorem IntrinsicLineBundle.sectionGaussValuation_degreeScaling (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    {t : K} (ht : t ≠ 0) (x : ⨁ n : ℕ, L.genericCoefficientSpace f n) :
    L.sectionGaussValuation v c (L.genericImageDecomposition f (gradedDegreeScaling t x)) =
      L.sectionGaussValuation v c (L.genericImageDecomposition f x) := by
  rw [L.sectionGaussValuation_apply, L.sectionGaussValuation_apply]
  exact gaussAddValuation_eq_of_coefficient_values v c _ _
    (L.genericPolynomial_degreeScaling_coefficient_value f v htrivial ht x)

/-- Degree invariance is produced for the constructed actual rational valuation. -/
theorem IntrinsicLineBundle.fractionGaussValuation_degreeScaling (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    {t : K} (ht : t ≠ 0) (x : ⨁ n : ℕ, L.genericCoefficientSpace f n) :
    fractionGaussValuation v c (L.genericRationalFunction f
      (L.genericImageDecomposition f (gradedDegreeScaling t x))) =
      fractionGaussValuation v c (L.genericRationalFunction f (L.genericImageDecomposition f x)) := by
  rw [L.fractionGaussValuation_section, L.fractionGaussValuation_section]
  exact L.sectionGaussValuation_degreeScaling f v c htrivial ht x

/-- The actual coefficient images inherit finite dimension from the actual global sections. -/
theorem IntrinsicLineBundle.genericCoefficientSpace_finiteDimensional
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K)) (n : ℕ)
    (hfinite : letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
      FiniteDimensional K (bundlePowerGlobalSections L.sheaf n)) :
    letI := schemeFunctionFieldAlgebra f
    FiniteDimensional K (L.genericCoefficientSpace f n) := by
  let := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
  let := schemeFunctionFieldAlgebra f
  let := hfinite
  exact (L.genericCoefficientEquiv f n).finiteDimensional

/-- All actual coefficient images are finite when all actual tensor-power section modules are finite. -/
theorem IntrinsicLineBundle.genericCoefficientSpaces_finiteDimensional
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K))
    (hfinite : ∀ n, letI := schemeGlobalSectionModule f (bundleTensorPower L.sheaf n)
      FiniteDimensional K (bundlePowerGlobalSections L.sheaf n)) :
    letI := schemeFunctionFieldAlgebra f
    ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n) :=
  fun n => L.genericCoefficientSpace_finiteDimensional f n (hfinite n)

/-- The genuine linear representative of the literal actual coefficient-image direct sum. -/
def IntrinsicLineBundle.genericImageRationalMap (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) :
    letI := schemeFunctionFieldAlgebra f
    (⨁ n : ℕ, L.genericCoefficientSpace f n) →ₗ[K]
      FractionRing (Polynomial X.functionField) := by
  letI := schemeFunctionFieldAlgebra f
  letI := L.sectionRingAlgebra f
  exact (L.genericRationalFunction f).toLinearMap.comp (L.genericImageDecomposition f).toLinearMap

theorem IntrinsicLineBundle.genericImageRationalMap_injective (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) : Function.Injective (L.genericImageRationalMap f) :=
  (L.genericRationalFunction_injective f).comp (L.genericImageDecomposition f).injective

/-- The actual graded representative factorization is supplied by genuine same-frame section gluing. -/
theorem IntrinsicLineBundle.genericImageRationalMap_piece_factorization
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K))
    (n : ℕ) (s : L.genericCoefficientSpace f n) :
    letI := schemeFunctionFieldAlgebra f
    gradedPieceRepresentation (L.genericImageRationalMap f) n s =
      L.genericRationalCoefficient f n s * genericRationalFiber X ^ n :=
  L.genericRational_image_factorization f n s

/-- Centered actual section coefficients are centered on their literal linear image spaces. -/
theorem IntrinsicLineBundle.genericCoefficientSpace_nonneg (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ))
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s))
    (n : ℕ) (s : L.genericCoefficientSpace f n) : (0 : WithTop ℝ) ≤ v (s : X.functionField) := by
  obtain ⟨t, ht⟩ := s.property
  change L.genericCoefficient n t = (s : X.functionField) at ht
  exact ht ▸ hcoeff n t

/-- The actual fraction-field coefficient factor is centered, derived from genuine sections. -/
theorem IntrinsicLineBundle.genericRationalCoefficient_nonneg (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s))
    (n : ℕ) (s : L.genericCoefficientSpace f n) :
    (0 : WithTop ℝ) ≤ fractionGaussValuation v c (L.genericRationalCoefficient f n s) := by
  rw [L.fractionGaussValuation_coefficient]
  exact L.genericCoefficientSpace_nonneg f v hcoeff n s

/-- Actual coefficient jumping weights, extracted from the actual adapted homogeneous bases. -/
def IntrinsicLineBundle.sectionCoefficientJumpingWeights (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K))
    (hfinite : letI := schemeFunctionFieldAlgebra f
      ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n))
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) (n : ℕ) :
    letI := schemeFunctionFieldAlgebra f
    Fin (Module.finrank K (L.genericCoefficientSpace f n)) → ℝ := by
  letI := schemeFunctionFieldAlgebra f
  letI : ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n) := hfinite
  exact gradedCoefficientJumpingWeights (fractionGaussValuation v c)
    (L.genericImageRationalMap f) (L.genericImageRationalMap_injective f)
    (fractionGaussValuation_base_trivial f v c htrivial) c n

/-- The actual adapted homogeneous basis, expressed in the literal coefficient-image space. -/
def IntrinsicLineBundle.sectionCoefficientAdaptedBasis (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K))
    (hfinite : letI := schemeFunctionFieldAlgebra f
      ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n))
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) (n : ℕ) :
    letI := schemeFunctionFieldAlgebra f
    Module.Basis (Fin (Module.finrank K (L.genericCoefficientSpace f n))) K
      (L.genericCoefficientSpace f n) := by
  letI := schemeFunctionFieldAlgebra f
  letI : ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n) := hfinite
  exact valuationAdaptedBasis (fractionGaussValuation v c)
    (gradedPieceRepresentation (L.genericImageRationalMap f) n)
    (gradedPieceRepresentation_injective (L.genericImageRationalMap f)
      (L.genericImageRationalMap_injective f) n)
    (fractionGaussValuation_base_trivial f v c htrivial)

/-- Shifted actual homogeneous weights are literally original valuations of actual basis coefficients. -/
theorem IntrinsicLineBundle.coe_sectionCoefficientJumpingWeights
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K))
    (hfinite : letI := schemeFunctionFieldAlgebra f
      ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n))
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0) (n : ℕ) :
    letI := schemeFunctionFieldAlgebra f
    ∀ j : Fin (Module.finrank K (L.genericCoefficientSpace f n)),
      ((L.sectionCoefficientJumpingWeights f hfinite v c htrivial n j : ℝ) : WithTop ℝ) =
        v (L.sectionCoefficientAdaptedBasis f hfinite v c htrivial n j : X.functionField) := by
  let := schemeFunctionFieldAlgebra f
  let : ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n) := hfinite
  intro j
  exact (coe_gradedCoefficientJumpingWeights_of_factorization (fractionGaussValuation v c)
    (L.genericImageRationalMap f) (L.genericImageRationalMap_injective f)
    (fractionGaussValuation_base_trivial f v c htrivial) (genericRationalFiber X) c
    (fractionGaussValuation_fiber v c) (L.genericRationalCoefficient f)
    (L.genericImageRationalMap_piece_factorization f) n j).trans
      (L.fractionGaussValuation_coefficient f v c n _)

/-- Nonnegativity of the actual coefficient jumping weights follows from the actual coefficient center. -/
theorem IntrinsicLineBundle.sectionCoefficientJumpingWeights_nonneg
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K))
    (hfinite : letI := schemeFunctionFieldAlgebra f
      ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n))
    (v : AddValuation X.functionField (WithTop ℝ)) (c : ℝ)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (n : ℕ) :
    letI := schemeFunctionFieldAlgebra f
    ∀ j : Fin (Module.finrank K (L.genericCoefficientSpace f n)),
      0 ≤ L.sectionCoefficientJumpingWeights f hfinite v c htrivial n j := by
  let := schemeFunctionFieldAlgebra f
  intro j
  apply WithTop.coe_le_coe.mp
  rw [L.coe_sectionCoefficientJumpingWeights]
  exact L.genericCoefficientSpace_nonneg f v hcoeff n _

/-- Positive actual fiber weight produces finite dimension of the actual threshold-ideal quotient. -/
theorem IntrinsicLineBundle.sectionValuationIdeal_quotient_finiteDimensional [Infinite K]
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K))
    (hfinite : letI := schemeFunctionFieldAlgebra f
      ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n))
    (v : AddValuation X.functionField (WithTop ℝ)) {c : ℝ} (hc : 0 < c)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (a : ℝ) :
    letI := L.sectionRingAlgebra f
    FiniteDimensional K (L.sectionRing ⧸ L.sectionValuationIdeal f v hc.le hcoeff a) := by
  let := L.sectionRingAlgebra f
  let := schemeFunctionFieldAlgebra f
  let : ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n) := hfinite
  exact gradedRingValuation_quotient_finiteDimensional_of_factorization
    (fractionGaussValuation v c) (L.genericRationalFunction f) (L.genericImageDecomposition f)
    (L.genericRationalFunction_centered f v hc.le hcoeff)
    (fractionGaussValuation_base_trivial f v c htrivial)
    (fun t ht x => L.fractionGaussValuation_degreeScaling f v c htrivial ht x)
    (genericRationalFiber X) hc (fractionGaussValuation_fiber v c)
    (L.genericRationalCoefficient f) (L.genericImageRationalMap_piece_factorization f)
    (L.genericRationalCoefficient_nonneg f v c hcoeff) a

/-- The actual section-ring colength is the finite count of actual coefficient jumping weights. -/
theorem IntrinsicLineBundle.sectionValuationIdeal_colength_eq_coefficient_count [Infinite K]
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K))
    (hfinite : letI := schemeFunctionFieldAlgebra f
      ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n))
    (v : AddValuation X.functionField (WithTop ℝ)) {c : ℝ} (hc : 0 < c)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (a : ℝ) :
    letI := L.sectionRingAlgebra f
    letI := schemeFunctionFieldAlgebra f
    Module.finrank K (L.sectionRing ⧸ L.sectionValuationIdeal f v hc.le hcoeff a) =
      ∑ n : Fin (Nat.ceil (a / c)), (Finset.univ.filter (fun j => c * (n : ℝ) +
        L.sectionCoefficientJumpingWeights f hfinite v c htrivial n j < a)).card := by
  let := L.sectionRingAlgebra f
  let := schemeFunctionFieldAlgebra f
  let : ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n) := hfinite
  exact gradedRingValuation_colength_eq_coefficient_count_of_factorization
    (fractionGaussValuation v c) (L.genericRationalFunction f) (L.genericImageDecomposition f)
    (L.genericRationalFunction_injective f) (L.genericRationalFunction_centered f v hc.le hcoeff)
    (fractionGaussValuation_base_trivial f v c htrivial)
    (fun t ht x => L.fractionGaussValuation_degreeScaling f v c htrivial ht x)
    (genericRationalFiber X) hc (fractionGaussValuation_fiber v c)
    (L.genericRationalCoefficient f) (L.genericImageRationalMap_piece_factorization f)
    (L.genericRationalCoefficient_nonneg f v c hcoeff) a

/-- The all-degree source colength identity for the literal actual section-ring ideal quotient. -/
theorem IntrinsicLineBundle.sectionValuationIdeal_colength_eq_coefficient_tsum [Infinite K]
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K))
    (hfinite : letI := schemeFunctionFieldAlgebra f
      ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n))
    (v : AddValuation X.functionField (WithTop ℝ)) {c : ℝ} (hc : 0 < c)
    (htrivial : letI := schemeFunctionFieldAlgebra f
      ∀ t : K, t ≠ 0 → v (algebraMap K X.functionField t) = 0)
    (hcoeff : ∀ n (s : bundlePowerGlobalSections L.sheaf n),
      (0 : WithTop ℝ) ≤ v (L.genericCoefficient n s)) (a : ℝ) :
    letI := L.sectionRingAlgebra f
    letI := schemeFunctionFieldAlgebra f
    Module.finrank K (L.sectionRing ⧸ L.sectionValuationIdeal f v hc.le hcoeff a) =
      ∑' n : ℕ, (Finset.univ.filter (fun j => c * (n : ℝ) +
        L.sectionCoefficientJumpingWeights f hfinite v c htrivial n j < a)).card := by
  let := L.sectionRingAlgebra f
  let := schemeFunctionFieldAlgebra f
  let : ∀ n, FiniteDimensional K (L.genericCoefficientSpace f n) := hfinite
  exact gradedRingValuation_colength_eq_coefficient_tsum_of_factorization
    (fractionGaussValuation v c) (L.genericRationalFunction f) (L.genericImageDecomposition f)
    (L.genericRationalFunction_injective f) (L.genericRationalFunction_centered f v hc.le hcoeff)
    (fractionGaussValuation_base_trivial f v c htrivial)
    (fun t ht x => L.fractionGaussValuation_degreeScaling f v c htrivial ht x)
    (genericRationalFiber X) hc (fractionGaussValuation_fiber v c)
    (L.genericRationalCoefficient f) (L.genericImageRationalMap_piece_factorization f)
    (L.genericRationalCoefficient_nonneg f v c hcoeff) a

end BaseField

end

end SGPT.Foundations.Schemes

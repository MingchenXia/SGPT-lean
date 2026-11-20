import SGPT.Hodge.StarPointwise
import SGPT.Hodge.Finite
import SGPT.Foundations.Analysis.Pending.NaturalHermitianFormalAdjoint

/-!
# Constant-trace `(1,1)`-forms are coclosed

Blueprint `claude-hodge` (lane HODGE-STAR, package `HodgeStar`), node
`claude-hodge:prop-constant-trace-coclosed`; source Xia, *Foundations of pluripotential theory*,
q07, `lem:kahler-trace-star`, last assertion.

Let `(X, ω)` be a Kähler manifold (`w : KahlerBackground n X`) and `γ` a closed real
`(1,1)`-form whose trace `tr_ω γ = c` is constant (`γ ∈ constantTraceSubmodule w`).  By the
pointwise star identity (`SGPT.Hodge.degreeStar_two_of_isOneOne`), at every chart point

`*γ = c P_{n-1}(ω) - P_{n-2}(ω) ∧ γ`,   `P_k(ω) = ω^{∧k}/k!`

(`degreeHodgeStarForm_geometricallyEq_starOneOneForm`; the global form `η_γ` is
`starOneOneForm`).  Since `dω = 0` and `dγ = 0`, the Leibniz rule (TN
`exteriorProduct_derivative_geometricallyEq`) gives `d η_γ = 0` (`starOneOneForm_isClosed`), so
`d*γ = -*d*γ = 0`:

* `SGPT.Hodge.constantTraceCoclosed : ConstantTraceCoclosed w` — **the statement of package
  `HodgeStar`, published in `SGPT.Hodge.Finite`, now proved** (no connectedness or compactness
  needed).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.ProductTestForms
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
  SGPT.Foundations.Analysis.Pending.XiaoComplexProducts
  SGPT.Foundations.Analysis.Pending.NaturalHermitianTopFormOrientation
  SGPT.Foundations.Analysis.Pending.NaturalOriginalGradedExteriorProduct
  SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStarSquare
  SGPT.Foundations.Analysis.Pending.NaturalHermitianCodifferential
  SGPT.Foundations.Analysis.Pending.NaturalHermitianFormalAdjoint

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Closed forms -/

theorem isClosed_iff_geometricallyEq_zero {k : ℕ} (X : SmoothRealForm n M k) :
    X.IsClosed ↔ X.exteriorDerivative.GeometricallyEq 0 :=
  Iff.rfl

theorem isClosed_zero' {k : ℕ} : (0 : SmoothRealForm n M k).IsClosed := by
  rw [isClosed_iff_geometricallyEq_zero, exteriorDerivative_zero]
  exact SmoothRealForm.GeometricallyEq.refl _

theorem isClosed_smul' {k : ℕ} (c : ℝ) {X : SmoothRealForm n M k} (hX : X.IsClosed) :
    (c • X).IsClosed := by
  rw [isClosed_iff_geometricallyEq_zero, exteriorDerivative_const_smul]
  have h := smul_geometricallyEq c ((isClosed_iff_geometricallyEq_zero X).mp hX)
  rwa [smul_zero] at h

theorem isClosed_add' {k : ℕ} {X Y : SmoothRealForm n M k} (hX : X.IsClosed)
    (hY : Y.IsClosed) : (X + Y).IsClosed := by
  rw [isClosed_iff_geometricallyEq_zero]
  refine (exteriorDerivative_add_geometricallyEq X Y).trans ?_
  intro e z hz
  simp only [coeff_add, coeff_zero]
  rw [show X.exteriorDerivative.coeff e z = 0 from hX e z hz,
    show Y.exteriorDerivative.coeff e z = 0 from hY e z hz, add_zero]

theorem isClosed_sub' {k : ℕ} {X Y : SmoothRealForm n M k} (hX : X.IsClosed)
    (hY : Y.IsClosed) : (X - Y).IsClosed := by
  have h : X - Y = X + (-1 : ℝ) • Y := by
    apply smoothRealForm_ext
    intro e z
    simp [sub_eq_add_neg]
  rw [h]
  exact isClosed_add' hX (isClosed_smul' _ hY)

theorem isClosed_castSmoothForm {a b : ℕ} (h : a = b) {X : SmoothRealForm n M a}
    (hX : X.IsClosed) : (castSmoothForm h X).IsClosed := by
  subst h
  exact hX

/-- The exterior product of closed forms is closed (Leibniz rule). -/
theorem isClosed_exteriorProduct {p q : ℕ} {A : SmoothRealForm n M p} {B : SmoothRealForm n M q}
    (hA : A.IsClosed) (hB : B.IsClosed) : (exteriorProduct A B).IsClosed := by
  rw [isClosed_iff_geometricallyEq_zero]
  refine (exteriorProduct_derivative_geometricallyEq A B).trans ?_
  intro e z hz
  simp only [coeff_add, coeff_smul, coeff_zero, castSmoothForm_coeff, exteriorProduct_coeff]
  have hA' : A.exteriorDerivative.coeff e z = 0 := hA e z hz
  have hB' : B.exteriorDerivative.coeff e z = 0 := hB e z hz
  rw [hA', hB']
  have h1 : coordinateWedge (0 : RealForm n (p + 1)) (B.coeff e z) = 0 := by
    simpa only [wedgeTo_rfl] using wedgeTo_zero_left (rfl : p + 1 + q = p + 1 + q) (B.coeff e z)
  have h2 : coordinateWedge (A.coeff e z) (0 : RealForm n (q + 1)) = 0 := by
    simpa only [wedgeTo_rfl] using wedgeTo_zero_right (rfl : p + (q + 1) = p + (q + 1)) (A.coeff e z)
  rw [h1, h2, map_zero, map_zero, smul_zero, add_zero]

/-! ### Powers of a closed two-form -/

/-- The recursion of the global powers `ω^{∧(k+2)} = ω^{∧(k+1)} ∧ ω`. -/
theorem tensorPowerForm_add_two (w : SmoothRealForm n M 2) (k : ℕ) :
    tensorPowerForm w (k + 2) = castSmoothForm (by ring : (k + 1) * 2 + 2 = (k + 2) * 2)
      (exteriorProduct (tensorPowerForm w (k + 1)) w) := by
  apply smoothRealForm_ext
  intro e z
  ext v
  rw [castSmoothForm_coeff, castForm_apply, exteriorProduct_coeff]
  exact coordinateWedgePower_add_two_apply (w.coeff e z) k v

/-- **`d(ω^{∧k}) = 0`** for a closed two-form `ω`. -/
theorem tensorPowerForm_isClosed {w : SmoothRealForm n M 2} (hw : w.IsClosed) :
    ∀ k, (tensorPowerForm w k).IsClosed := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
      intro e z _
      change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
        (fderiv ℝ (fun _ : ComplexModel n => (coordinateWedgeUnit : RealForm n 0)) z) = 0
      rw [fderiv_const_apply, map_zero]
    | 1, _ => exact hw
    | k + 2, ih =>
      rw [tensorPowerForm_add_two]
      exact isClosed_castSmoothForm _ (isClosed_exteriorProduct (ih (k + 1) (by omega)) hw)

/-- The global normalized power `P_k(ω) = ω^{∧k}/k!`. -/
def kahlerPowerForm (w : SmoothRealForm n M 2) (k : ℕ) : SmoothRealForm n M (k * 2) :=
  ((k.factorial : ℝ)⁻¹) • tensorPowerForm w k

theorem kahlerPowerForm_coeff (w : SmoothRealForm n M 2) (k : ℕ) (e : ComplexChart n M)
    (z : ComplexModel n) : (kahlerPowerForm w k).coeff e z = kahlerPowerCoeff (w.coeff e z) k :=
  rfl

theorem kahlerPowerForm_isClosed {w : SmoothRealForm n M 2} (hw : w.IsClosed) (k : ℕ) :
    (kahlerPowerForm w k).IsClosed :=
  isClosed_smul' _ (tensorPowerForm_isClosed hw k)

/-! ### The global star candidate -/

/-- **The form `η_γ = c P_{n-1}(ω) - P_{n-2}(ω) ∧ γ`** (the second term only for `n ≥ 2`). -/
def starOneOneForm (w γ : SmoothRealForm n M 2) (c : ℝ) : SmoothRealForm n M (2 * n - 2) :=
  c • castSmoothForm (by omega : (n - 1) * 2 = 2 * n - 2) (kahlerPowerForm w (n - 1)) -
    (if hn : 2 ≤ n then
      castSmoothForm (by omega : (n - 2) * 2 + 2 = 2 * n - 2)
        (exteriorProduct (kahlerPowerForm w (n - 2)) γ)
    else 0)

theorem starOneOneForm_coeff (w γ : SmoothRealForm n M 2) (c : ℝ) (e : ComplexChart n M)
    (z : ComplexModel n) :
    (starOneOneForm w γ c).coeff e z = starOneOneCoeff (w.coeff e z) (γ.coeff e z) c := by
  unfold starOneOneForm starOneOneCoeff oneOneWedgeTerm
  split_ifs <;> simp only [coeff_sub, coeff_smul, coeff_zero, castSmoothForm_coeff,
    exteriorProduct_coeff, kahlerPowerForm_coeff]

/-- **`d η_γ = 0`** for closed `ω` and `γ`. -/
theorem starOneOneForm_isClosed {w γ : SmoothRealForm n M 2} (hw : w.IsClosed)
    (hγ : γ.IsClosed) (c : ℝ) : (starOneOneForm w γ c).IsClosed := by
  unfold starOneOneForm
  refine isClosed_sub' (isClosed_smul' _ (isClosed_castSmoothForm _
    (kahlerPowerForm_isClosed hw _))) ?_
  split_ifs
  · exact isClosed_castSmoothForm _ (isClosed_exteriorProduct (kahlerPowerForm_isClosed hw _) hγ)
  · exact isClosed_zero'

/-- **The Hodge star of a constant-trace `(1,1)`-form** is the closed form `η_γ`. -/
theorem degreeHodgeStarForm_geometricallyEq_starOneOneForm (w : KahlerBackground n M)
    (γ : ClosedRealOneOneForm n M) {c : ℝ} (hc : ∀ y, trace w.form.val γ.val y = c)
    (hn : 1 ≤ n) :
    (degreeHodgeStarForm w.form.val w.isKahler.1 2 (by omega) γ.val).GeometricallyEq
      (starOneOneForm w.form.val γ.val c) := by
  intro e z hz
  rw [degreeHodgeStarForm_coeff, degreeStar_two_of_isOneOne w.form.val w.isKahler.1 e hz hn _
    (γ.property.2 e z hz), starOneOneForm_coeff]
  congr 1
  have h := trace_symm_eq w.isKahler.1 γ.property.2 hz
  rw [hc] at h
  exact h.symm

/-- `d*γ = 0` as soon as `d(*γ) = 0`. -/
theorem coderivativeForm_two_geometricallyEq_zero (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (hn : 1 ≤ n) (γ : SmoothRealForm n M 2)
    (hd : (degreeHodgeStarForm w hw 2 (by omega) γ).exteriorDerivative.GeometricallyEq 0) :
    (coderivativeForm w hw 2 γ).GeometricallyEq 0 := by
  simp only [coderivativeForm, dif_neg (show (2 : ℕ) ≠ 0 by norm_num),
    dif_pos (show 2 ≤ 2 * n by omega)]
  change ((-1 : ℝ) • castSmoothForm (show 2 * n - (2 * n - 2 + 1) = 1 by omega)
    (degreeHodgeStarForm w hw (2 * n - 2 + 1) (by omega)
      (degreeHodgeStarForm w hw 2 (by omega) γ).exteriorDerivative)).GeometricallyEq 0
  have h1 := degreeHodgeStarForm_geometricallyEq w hw (2 * n - 2 + 1) (by omega) hd
  rw [degreeHodgeStarForm_zero] at h1
  have h2 := castSmoothForm_geometricallyEq (show 2 * n - (2 * n - 2 + 1) = 1 by omega) h1
  rw [map_zero] at h2
  have h3 := smul_geometricallyEq (-1) h2
  rwa [smul_zero] at h3

/-- **Constant-trace forms are coclosed** (`claude-hodge:prop-constant-trace-coclosed`): the
statement `SGPT.Hodge.ConstantTraceCoclosed` of package `HodgeStar` holds for every Kähler
background. -/
theorem constantTraceCoclosed (w : KahlerBackground n M) : ConstantTraceCoclosed w := by
  intro γ hγ
  obtain ⟨c, hc⟩ := hγ
  by_cases hn : 1 ≤ n
  · apply coderivativeForm_two_geometricallyEq_zero w.form.val w.isKahler.1 hn
    exact (degreeHodgeStarForm_geometricallyEq_starOneOneForm w γ hc hn).exteriorDerivative.trans
      (starOneOneForm_isClosed w.isKahler.2 γ.property.1 c)
  · have h : coderivativeForm w.form.val w.isKahler.1 2 γ.val = 0 := by
      simp only [coderivativeForm, dif_neg (show (2 : ℕ) ≠ 0 by norm_num),
        dif_neg (show ¬ 2 ≤ 2 * n by omega)]
    rw [h]
    exact SmoothRealForm.GeometricallyEq.refl _

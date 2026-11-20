import SGPT.Hodge.StarAdapted
import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStarSquare

/-!
# The Hodge star of a real `(1,1)`-covector

Blueprint `claude-hodge` (lane HODGE-STAR, package `HodgeStar`), node
`claude-hodge:lem-star-pointwise`; source Xia, *Foundations of pluripotential theory*, q07,
`lem:kahler-trace-star`.

Let `a` be a strictly positive real `(1,1)`-covector on `ℂⁿ` (`n ≥ 1`), `g(u, v) = a(u, i v)` its
metric, `P_k(a) = a^{∧k}/k!` (`kahlerPowerCoeff`), and `Λ_a G = Re tr(H_a⁻¹ H_G)` the trace of a
real `(1,1)`-covector `G` (`traceCoeff`).  For TN's Hodge star of the metric of `a`
(`NaturalHermitianHodgeStarSquare.degreeStar`):

`*G = (Λ_a G) P_{n-1}(a) - P_{n-2}(a) ∧ G`  (`n ≥ 2`),   `*G = Λ_a G`  (`n = 1`)

(`degreeStar_two_of_isOneOne`; the candidate is `starOneOneCoeff`, whose second term
`oneOneWedgeTerm` is `0` when `n = 1`).

Proof.  By TN's characterization of the star (`star_wedge_unique`) it suffices to show
`ξ ∧ η = ⟨ξ, G⟩_g vol_g` for every real two-covector `ξ`.  Both sides are top-degree, so it
suffices to compare their pullbacks along the adapted frame `T` of `exists_adapted_frame`
(`a ∘ T = ω₀` standard, `G ∘ T` block diagonal with weights `λ`, `Λ_a G = ∑ λ`):

* `⟨ξ, G⟩_g = ∑ₖ λₖ ξ(T e_k, T(i e_k))`, because `G = ∑ₖ λₖ (T e_k)^♭ ∧ (T(i e_k))^♭`
  (`originalFormMetric_eq_sum_of_adapted`, using TN `form_metric_tuple_evaluation`);
* `vol_g(T e) = P_n(ω₀)(e) = 1` (TN `actualTopPowerDensity_eq_factorial_of_apply_eq_im`);
* `(ξ ∧ η)(T e) = (Σλ) ∑ₖ ξ'ₖ - ((Σλ)(Σ ξ') - Σ λₖ ξ'ₖ) = ∑ₖ λₖ ξ'ₖ`
  (`SGPT.Hodge.StarPairing`).
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped Matrix

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
  SGPT.Foundations.Analysis.Pending.TopDegreeDensity
  SGPT.Foundations.Analysis.Pending.NaturalHermitianMetricCoefficients
  SGPT.Foundations.Analysis.Pending.NaturalHermitianOriginalFormMetric
  SGPT.Foundations.Analysis.Pending.NaturalHermitianSmoothFormMetric
  SGPT.Foundations.Analysis.Pending.NaturalHermitianFormRieszContraction
  SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStar
  SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStarSquare
  SGPT.Foundations.Analysis.Pending.NaturalHermitianTopFormOrientation
  SGPT.Foundations.Analysis.Pending.NaturalOriginalGradedExteriorProduct

variable {n : ℕ}

/-! ### Normalized powers and the candidate star -/

/-- The normalized power `P_k(a) = a^{∧k}/k!` of a two-covector. -/
def kahlerPowerCoeff (a : CoordinateRealTwoForm n) (k : ℕ) : RealForm n (k * 2) :=
  ((k.factorial : ℝ)⁻¹) • coordinateWedgePower a k

/-- The trace `Λ_a G = Re tr(H_a⁻¹ H_G)` at a point (the chart form of `SGPT.Hodge.trace`). -/
def traceCoeff (a G : CoordinateRealTwoForm n) : ℝ :=
  (Matrix.trace ((normalizedHermitianMatrix a)⁻¹ * normalizedHermitianMatrix G)).re

/-- The second term `P_{n-2}(a) ∧ G` of the star of `G`, read in degree `2n - 2`; it is `0` for
`n < 2`. -/
def oneOneWedgeTerm (a G : CoordinateRealTwoForm n) : RealForm n (2 * n - 2) :=
  if hn : 2 ≤ n then
    castForm (by omega : (n - 2) * 2 + 2 = 2 * n - 2)
      (coordinateWedge (kahlerPowerCoeff a (n - 2)) G)
  else 0

/-- **The star of a real `(1,1)`-covector**: `c P_{n-1}(a) - P_{n-2}(a) ∧ G` (with `c = Λ_a G`). -/
def starOneOneCoeff (a G : CoordinateRealTwoForm n) (c : ℝ) : RealForm n (2 * n - 2) :=
  c • castForm (by omega : (n - 1) * 2 = 2 * n - 2) (kahlerPowerCoeff a (n - 1)) -
    oneOneWedgeTerm a G

theorem compContinuousLinearMap_smul' {q : ℕ} (L : ComplexModel n →L[ℝ] ComplexModel n)
    (c : ℝ) (A : RealForm n q) :
    (c • A).compContinuousLinearMap L = c • A.compContinuousLinearMap L :=
  map_smul (ContinuousAlternatingMap.compContinuousLinearMapₗ L) c A

theorem compContinuousLinearMap_sub' {q : ℕ} (L : ComplexModel n →L[ℝ] ComplexModel n)
    (A B : RealForm n q) :
    (A - B).compContinuousLinearMap L = A.compContinuousLinearMap L - B.compContinuousLinearMap L :=
  map_sub (ContinuousAlternatingMap.compContinuousLinearMapₗ L) A B

theorem kahlerPowerCoeff_comp (a : CoordinateRealTwoForm n) (k : ℕ)
    (L : ComplexModel n →L[ℝ] ComplexModel n) :
    (kahlerPowerCoeff a k).compContinuousLinearMap L =
      kahlerPowerCoeff (a.compContinuousLinearMap L) k := by
  rw [kahlerPowerCoeff, kahlerPowerCoeff, coordinateWedgePower_compContinuousLinearMap,
    compContinuousLinearMap_smul']

/-- The candidate star is natural under real-linear pullback. -/
theorem starOneOneCoeff_comp (a G : CoordinateRealTwoForm n) (c : ℝ)
    (L : ComplexModel n →L[ℝ] ComplexModel n) :
    (starOneOneCoeff a G c).compContinuousLinearMap L =
      starOneOneCoeff (a.compContinuousLinearMap L) (G.compContinuousLinearMap L) c := by
  unfold starOneOneCoeff oneOneWedgeTerm
  rw [compContinuousLinearMap_sub', compContinuousLinearMap_smul',
    castForm_compContinuousLinearMap, kahlerPowerCoeff_comp]
  congr 1
  split_ifs with hn
  · rw [castForm_compContinuousLinearMap, coordinateWedge_compContinuousLinearMap,
      kahlerPowerCoeff_comp]
  · exact map_zero (ContinuousAlternatingMap.compContinuousLinearMapₗ L)

/-! ### Top-degree evaluations in the standard model -/

theorem topBasis_comp_cast {p : ℕ} (h : p = 2 * n) (h' : p = n * 2) :
    (⇑(topBasis n) ∘ Fin.cast h) = (coordinateRealFrame ∘ Fin.cast h') := by
  funext i
  simp only [Function.comp_apply, topBasis_apply]
  congr 1

theorem neg_one_pow_two_mul (k : ℕ) : (-1 : ℝ) ^ (2 * k) = 1 := by
  rw [pow_mul]
  norm_num

/-- `vol(e) = P_n(ω₀)(e) = 1` on the standard frame. -/
theorem topDensity_kahlerPowerCoeff_standard :
    topDensity (castForm (Nat.mul_comm n 2) (kahlerPowerCoeff (standardHermitianTwoForm n) n)) =
      1 := by
  rw [topDensity, castForm_apply, topBasis_comp_cast (Nat.mul_comm n 2) rfl, kahlerPowerCoeff,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have h : coordinateWedgePower (standardHermitianTwoForm n) n (coordinateRealFrame ∘ Fin.cast rfl)
      = actualTopPowerDensity (standardHermitianTwoForm n) := rfl
  rw [h, actualTopPowerDensity_eq_factorial_of_apply_eq_im _ standardHermitianTwoForm_apply]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- First term: `(ξ ∧ P_{n-1}(ω₀))(e) = ∑ₖ ξ(e_k, i e_k)`. -/
theorem topDensity_wedge_kahlerPower_standard (hn : 1 ≤ n) (ξ : CoordinateRealTwoForm n) :
    topDensity (wedgeTo (show 2 + (2 * n - 2) = 2 * n by omega) ξ
        (castForm (by omega : (n - 1) * 2 = 2 * n - 2)
          (kahlerPowerCoeff (standardHermitianTwoForm n) (n - 1)))) =
      ∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)] := by
  rw [wedgeTo_castForm_right _ _ (show 2 + (n - 1) * 2 = 2 * n by omega),
    wedgeTo_graded_comm _ (show (n - 1) * 2 + 2 = 2 * n by omega), neg_one_pow_two_mul,
    one_smul, kahlerPowerCoeff, wedgeTo_smul_left, topDensity_smul, topDensity, wedgeTo_apply,
    topBasis_comp_cast _ (show (n - 1) * 2 + 2 = n * 2 by omega),
    wedge_power_standard_apply_of_eq (n - 1) (by omega)]
  have hf : ((n - 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Second term: `(ξ ∧ P_{n-2}(ω₀) ∧ D)(e) = (Σ ξ')(Σ λ) - Σ ξ'ₖ λₖ` for block-diagonal `D`. -/
theorem topDensity_wedge_oneOneWedgeTerm_standard (hn : 2 ≤ n) (D ξ : CoordinateRealTwoForm n)
    {d : Fin n → ℝ} (hD : IsBlockDiagonal D d) :
    topDensity (wedgeTo (show 2 + (2 * n - 2) = 2 * n by omega) ξ
        (oneOneWedgeTerm (standardHermitianTwoForm n) D)) =
      (∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)]) * (∑ k, d k) -
        ∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)] * d k := by
  rw [oneOneWedgeTerm, dif_pos hn,
    wedgeTo_castForm_right _ _ (show 2 + ((n - 2) * 2 + 2) = 2 * n by omega),
    ← wedgeTo_castForm_right (show (n - 2) * 2 + 2 = (n - 2 + 1) * 2 by ring)
      (show 2 + (n - 2 + 1) * 2 = 2 * n by omega),
    wedgeTo_graded_comm _ (show (n - 2 + 1) * 2 + 2 = 2 * n by omega), neg_one_pow_two_mul,
    one_smul, kahlerPowerCoeff, coordinateWedge_smul_left, map_smul, wedgeTo_smul_left,
    topDensity_smul, topDensity, wedgeTo_apply,
    topBasis_comp_cast _ (show (n - 2 + 1) * 2 + 2 = n * 2 by omega),
    wedge_power_wedge_standard_apply_of_eq (n - 2) (by omega) D ξ hD]
  have hf : ((n - 2).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The star identity in the standard model**: `(ξ ∧ η)(e) = ∑ₖ λₖ ξ(e_k, i e_k)` for
`η = (Σλ) P_{n-1}(ω₀) - P_{n-2}(ω₀) ∧ D`. -/
theorem topDensity_wedge_starOneOneCoeff_standard (hn : 1 ≤ n) (D ξ : CoordinateRealTwoForm n)
    {d : Fin n → ℝ} (hD : IsBlockDiagonal D d) :
    topDensity (wedgeTo (show 2 + (2 * n - 2) = 2 * n by omega) ξ
        (starOneOneCoeff (standardHermitianTwoForm n) D (∑ k, d k))) =
      ∑ k, d k * ξ ![frameVec (k, 0), frameVec (k, 1)] := by
  rw [starOneOneCoeff, ← wedgeToBilin_apply, map_sub, map_smul, wedgeToBilin_apply,
    wedgeToBilin_apply, topDensity_sub, topDensity_smul, topDensity_wedge_kahlerPower_standard hn]
  by_cases h2 : 2 ≤ n
  · rw [topDensity_wedge_oneOneWedgeTerm_standard h2 D ξ hD, Finset.mul_sum]
    have : ∑ k, d k * ξ ![frameVec (k, 0), frameVec (k, 1)] =
        ∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)] * d k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this, ← Finset.mul_sum]
    ring
  · have h1 : n = 1 := by omega
    subst h1
    rw [oneOneWedgeTerm, dif_neg h2, wedgeTo_zero_right, topDensity_zero, sub_zero]
    simp only [Fin.sum_univ_one]

/-! ### The metric of `G` in the adapted frame -/

/-- The metric of `a` on the images of frame vectors under an adapted `T`. -/
theorem associatedMetricCLM_adapted {a : CoordinateRealTwoForm n}
    {T : ComplexModel n →ₗ[ℂ] ComplexModel n} (haT : compLinearMap a T = standardHermitianTwoForm n)
    (x y : Fin n × Fin 2) :
    associatedMetricCLM a (T (frameVec x)) (T (frameVec y)) = if x = y then 1 else 0 := by
  rw [associatedMetricCLM_apply, associatedMetric, ← T.map_smul, ← compLinearMap_apply, haT,
    standardHermitianTwoForm_apply, inner_smul_right]
  obtain ⟨j, b⟩ := x
  obtain ⟨k, c⟩ := y
  simp only [frameVec, coordinateRealFrame_finProdFinEquiv]
  by_cases hjk : j = k
  · subst hjk
    fin_cases b <;> fin_cases c <;>
      simp [coordinateVector, inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
        -inner_self_eq_norm_sq_to_K]
  · have hne : ∀ b c : Fin 2, ((j, b) : Fin n × Fin 2) ≠ (k, c) := fun b c h =>
      hjk (congrArg Prod.fst h)
    fin_cases b <;> fin_cases c <;>
      simp [coordinateVector, inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
        hjk, hne]

theorem compContinuousLinearMap_injective_of_det_ne_zero {q : ℕ}
    {L : ComplexModel n →L[ℝ] ComplexModel n}
    (hL : LinearMap.det (L : ComplexModel n →ₗ[ℝ] ComplexModel n) ≠ 0) {A B : RealForm n q}
    (h : A.compContinuousLinearMap L = B.compContinuousLinearMap L) : A = B := by
  have hbij : Function.Bijective L :=
    (Module.End.isUnit_iff _).mp ((LinearMap.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hL))
  ext v
  obtain ⟨u, hu⟩ : ∃ u : Fin q → ComplexModel n, L ∘ u = v :=
    ⟨fun i => (hbij.2 (v i)).choose, funext fun i => (hbij.2 (v i)).choose_spec⟩
  rw [← hu]
  exact congrArg (fun C : RealForm n q => C u) h

/-- **The metric pairing with `G` in the adapted frame**: `⟨ξ, G⟩_g = ∑ₖ λₖ ξ(T e_k, T(i e_k))`. -/
theorem originalFormMetric_eq_sum_of_adapted {a G : CoordinateRealTwoForm n} (hJ : IsOneOne a)
    (hp : IsStrictlyPositive a) {T : ComplexModel n →ₗ[ℂ] ComplexModel n} {d : Fin n → ℝ}
    (hdet : LinearMap.det (T.restrictScalars ℝ) ≠ 0)
    (haT : compLinearMap a T = standardHermitianTwoForm n)
    (hblock : IsBlockDiagonal (compLinearMap G T) d) (ξ : CoordinateRealTwoForm n) :
    originalFormMetric a hJ hp 2 ξ G =
      ∑ k, d k * ξ ![T (frameVec (k, 0)), T (frameVec (k, 1))] := by
  have hexp : G = ∑ k, d k • metricTupleForm a hJ hp ![T (frameVec (k, 0)), T (frameVec (k, 1))] := by
    apply compContinuousLinearMap_injective_of_det_ne_zero (L := LinearMap.toContinuousLinearMap
      (T.restrictScalars ℝ)) hdet
    apply twoForm_ext_frame
    intro x y
    change compLinearMap G T ![frameVec x, frameVec y] = _
    rw [hblock x y, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.sum_apply]
    have hv : (⇑(LinearMap.toContinuousLinearMap (T.restrictScalars ℝ)) ∘
        ![frameVec x, frameVec y]) = ![T (frameVec x), T (frameVec y)] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, metricTupleForm_apply,
      Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      associatedMetricCLM_adapted haT]
    obtain ⟨j, b⟩ := x
    obtain ⟨j', b'⟩ := y
    rw [Finset.sum_eq_single j]
    · by_cases hjj : j = j'
      · subst hjj
        fin_cases b <;> fin_cases b' <;> simp
      · fin_cases b <;> fin_cases b' <;> simp [hjj]
    · intro k _ hk
      simp [hk]
    · simp
  conv_lhs => rw [hexp]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, form_metric_tuple_evaluation, smul_eq_mul]

/-! ### The star identity -/

/-- **`ξ ∧ η = ⟨ξ, G⟩_g vol_g`** for the candidate star `η` of a real `(1,1)`-covector `G`. -/
theorem wedge_starOneOneCoeff (a G : CoordinateRealTwoForm n) (hJ : IsOneOne a)
    (hp : IsStrictlyPositive a) (hG : IsOneOne G) (hn : 1 ≤ n) (ξ : CoordinateRealTwoForm n) :
    wedgeTo (show 2 + (2 * n - 2) = 2 * n by omega) ξ (starOneOneCoeff a G (traceCoeff a G)) =
      originalFormMetric a hJ hp 2 ξ G • castForm (Nat.mul_comm n 2) (kahlerPowerCoeff a n) := by
  obtain ⟨T, d, hdet, haT, hblock, htr⟩ := exists_adapted_frame a G hJ hp hG
  set L : ComplexModel n →L[ℝ] ComplexModel n :=
    LinearMap.toContinuousLinearMap (T.restrictScalars ℝ) with hL
  have hLdet : LinearMap.det (L : ComplexModel n →ₗ[ℝ] ComplexModel n) ≠ 0 := hdet
  have haL : a.compContinuousLinearMap L = standardHermitianTwoForm n := haT
  have hGL : IsBlockDiagonal (G.compContinuousLinearMap L) d := hblock
  apply topDensity_injective
  apply mul_left_cancel₀ hLdet
  rw [← topDensity_compContinuousLinearMap, ← topDensity_compContinuousLinearMap,
    wedgeTo_compContinuousLinearMap, starOneOneCoeff_comp, haL, compContinuousLinearMap_smul',
    castForm_compContinuousLinearMap, kahlerPowerCoeff_comp, haL, topDensity_smul,
    topDensity_kahlerPowerCoeff_standard, mul_one,
    originalFormMetric_eq_sum_of_adapted hJ hp hdet haT hblock, traceCoeff, htr,
    topDensity_wedge_starOneOneCoeff_standard hn _ _ hGL]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 2
  funext i
  fin_cases i <;> rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The metric volume of TN is the normalized top power `P_n(a)`. -/
theorem metricVolumeCoefficients_eq_kahlerPowerCoeff (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) :
    metricVolumeCoefficients w e z =
      castForm (Nat.mul_comm n 2) (kahlerPowerCoeff (w.coeff e z) n) := by
  unfold metricVolumeCoefficients
  congr 1

/-- Uniqueness of the star of a two-covector through the wedge identity (TN `star_wedge_unique`
in degree `2`). -/
theorem eq_degreeStar_two_of_wedge (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) (hn : 1 ≤ n)
    (G : RealForm n 2) (θ : RealForm n (2 * n - 2))
    (hθ : ∀ ξ : RealForm n 2, wedgeTo (show 2 + (2 * n - 2) = 2 * n by omega) ξ θ =
      formMetricCoefficients w e z 2 ξ G • metricVolumeCoefficients w e z) :
    degreeStar w e z 2 G = θ := by
  have hfr : Module.finrank ℝ (ComplexModel n) - 2 = 2 * n - 2 := by
    rw [complexModel_real_finrank]
  rw [degreeStar_below w e z 2 (by omega) G]
  have hu := star_wedge_unique w hw e z hz ⟨2, by rw [complexModel_real_finrank]; omega⟩ G
    (castForm hfr.symm θ) (fun ξ => by
      rw [wedgeTo_castForm_right _ _ (show 2 + (2 * n - 2) = 2 * n by omega)]
      exact hθ ξ)
  rw [← hu, castForm_castForm]
  rfl

/-- **The Hodge star of a real `(1,1)`-covector** (`claude-hodge:lem-star-pointwise`): at every
chart point, for TN's Hodge star of a Hermitian form `w`,
`*G = (Λ G) P_{n-1}(w) - P_{n-2}(w) ∧ G` (the second term is absent for `n = 1`). -/
theorem degreeStar_two_of_isOneOne (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) (hn : 1 ≤ n)
    (G : RealForm n 2) (hG : IsOneOne G) :
    degreeStar w e z 2 G = starOneOneCoeff (w.coeff e z) G (traceCoeff (w.coeff e z) G) := by
  apply eq_degreeStar_two_of_wedge w hw e hz hn
  intro ξ
  rw [formMetricCoefficients_eq_original w hw e z hz, metricVolumeCoefficients_eq_kahlerPowerCoeff]
  exact wedge_starOneOneCoeff _ G (hw e z hz).1 (hw e z hz).2 hG hn ξ

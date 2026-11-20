import SGPT.Foundations.Analysis.Pending.XiaoGauduchonKernel
import SGPT.Foundations.Analysis.Pending.XiaoGauduchonYauEstimate
import SGPT.Foundations.Analysis.Pending.XiaoPositiveExtension

set_option autoImplicit false

/-!
# An actual positive current agreeing on the actual Gauduchon kernel

The actual Kähler order unit makes the genuine kernel cofinal for the actual
positive cone. Riesz extension then produces an actual positive product current.
The numerical-gap estimate will supply the positivity of the actual pairing.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoPositiveGauduchonExtension

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents TopDegreeDensity IntegrationCurrent
  XiaoComplexDifferential XiaoGauduchonKernel XiaoGauduchonYauEstimate

noncomputable section

variable {n m q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The actual positive cone admits a positive current extending a positive kernel functional. -/
theorem exists_positive_extension_from_gauduchonKernel (w : KahlerBackground n M) (q : ℕ)
    (ell : gauduchonKernel n M q →ₗ[ℝ] ℝ)
    (hell : ∀ G : gauduchonKernel n M q,
      (G.val : testSpace n M q) ∈ positiveCone n M q → 0 ≤ ell G) :
    ∃ T : ProductCurrent n M q, IsPositive T ∧
      ∀ G : gauduchonKernel n M q, T G.val = ell G := by
  let e : gauduchonKernel n M q :=
    ⟨kahlerTest w q, kahlerTest_mem_gauduchonKernel w q⟩
  have hdense : ∀ G : testSpace n M q, ∃ H : gauduchonKernel n M q,
      (H.val : testSpace n M q) + G ∈ stronglyPositiveTestCone n M q := by
    intro G
    obtain ⟨c, _, _, hplus⟩ := isOrderUnit_kahlerTest w q G
    exact ⟨c • e, hplus⟩
  obtain ⟨T, hext, hpos⟩ := riesz_extension (stronglyPositiveTestCone n M q)
    (⟨gauduchonKernel n M q, ell⟩ : (testSpace n M q) →ₗ.[ℝ] ℝ) hell hdense
  exact ⟨T, hpos, hext⟩

section Pairing

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Actual wedge integration defines a real linear pairing on the actual smooth tensors. -/
def smoothPairing (w : KahlerBackground (m + 1) M) (θ : SmoothRealForm (m + 1) M 2) :
    SmoothRealForm (m + 1) M (2 * m) →ₗ[ℝ] ℝ where
  toFun G := ∫ x, topRatio w.form.val (wedgeTwo G θ) x ∂(kahlerVolume w)
  map_add' G H := by
    have heq : topRatio w.form.val (wedgeTwo (G + H) θ) =
        fun x => topRatio w.form.val (wedgeTwo G θ) x +
          topRatio w.form.val (wedgeTwo H θ) x := by
      funext x
      rw [wedgeTwo_add_left]
      exact topRatio_add w.form.val _ _ x
    rw [heq, integral_add (integrable_topRatio w _) (integrable_topRatio w _)]
  map_smul' c G := by
    have heq : topRatio w.form.val (wedgeTwo (c • G) θ) =
        fun x => c * topRatio w.form.val (wedgeTwo G θ) x := by
      funext x
      rw [wedgeTwo_smul_left]
      exact topRatio_smul w.form.val c _ x
    rw [heq, integral_const_mul]
    rfl

@[simp] theorem smoothPairing_apply (w : KahlerBackground (m + 1) M)
    (θ : SmoothRealForm (m + 1) M 2) (G : SmoothRealForm (m + 1) M (2 * m)) :
    smoothPairing w θ G = ∫ x, topRatio w.form.val (wedgeTwo G θ) x ∂(kahlerVolume w) := rfl

/-- The same actual wedge pairing restricted to the existing actual test space. -/
def smoothTestPairing (w : KahlerBackground (m + 1) M) (θ : SmoothRealForm (m + 1) M 2) :
    ProductCurrent (m + 1) M m := (smoothPairing w θ).comp (testSpace (m + 1) M m).subtype

@[simp] theorem smoothTestPairing_apply (w : KahlerBackground (m + 1) M)
    (θ : SmoothRealForm (m + 1) M 2) (G : testSpace (m + 1) M m) :
    smoothTestPairing w θ G = smoothPairing w θ (G : SmoothRealForm (m + 1) M (2 * m)) := rfl

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
private theorem ddc_smul_zero (c : ℝ) (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : (ddc G).GeometricallyEq 0) : (ddc (c • G)).GeometricallyEq 0 := by
  intro e z hz
  rw [ddc_smul_geometricallyEq c G e hz, coeff_smul, hG e hz]
  exact smul_zero c

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
private theorem ddc_add_zero (G H : SmoothRealForm (m + 1) M (2 * m))
    (hG : (ddc G).GeometricallyEq 0) (hH : (ddc H).GeometricallyEq 0) :
    (ddc (G + H)).GeometricallyEq 0 := by
  intro e z hz
  rw [ddc_add_geometricallyEq G H e hz, coeff_add, hG e hz, hH e hz]
  change (0 : RealForm (m + 1) (2 * m + 1 + 1)) + 0 = 0
  exact zero_add 0

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
private theorem topRatio_testWedge_nonneg (A B : KahlerBackground (m + 1) M)
    (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m) (x : M) :
    0 ≤ topRatio A.form.val (wedgeTwo G B.form.val) x := by
  let e := complexChartAt (n := m + 1) x
  have hz := e.val.map_source (mem_complexChartAt_source x)
  change 0 ≤ topDensity (wedgeTwo G B.form.val |>.coeff e (e.val x)) /
    topDensity ((formPow A.form.val (m + 1)).coeff e (e.val x))
  exact div_nonneg (topDensity_nonneg_of_mem_spCone
    (wedge_mem_spCone (hG e (e.val x) hz)
      ⟨(B.isKahler.1 e (e.val x) hz).1, B.isSemipositive e (e.val x) hz⟩))
    (topDensity_formPow_pos A.isKahler.1 hz).le

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
private theorem topRatio_otherKahlerPower_pos (A B : KahlerBackground (m + 1) M) (x : M) :
    0 < topRatio A.form.val (formPow B.form.val (m + 1)) x := by
  let e := complexChartAt (n := m + 1) x
  have hz := e.val.map_source (mem_complexChartAt_source x)
  exact div_pos (topDensity_formPow_pos B.isKahler.1 hz)
    (topDensity_formPow_pos A.isKahler.1 hz)

variable [ConnectedSpace M]

/-- The actual numerical gap supplies nonnegativity on every actual positive Gauduchon test. -/
theorem exists_uniform_nonneg_gauduchon_test_positivity (A B : KahlerBackground (m + 1) M)
    (hM : 0 < NefMixedMass.slotIntegral A (Fin.cons B.form (fun _ : Fin m => A.form)))
    (hgap : 4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral A
      (Fin.cons B.form (fun _ : Fin m => A.form)) < (kahlerVolume A).real univ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ G : SmoothRealForm (m + 1) M (2 * m),
        (∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m) →
        (ddc G).GeometricallyEq 0 →
        0 ≤ smoothPairing A ((1 - δ) • A.form.val - B.form.val) G := by
  obtain ⟨δ, hδ0, hδ1, hstrict⟩ :=
    exists_uniform_strict_gauduchon_test_positivity A B hM hgap
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro G hG hddc
  let θ := (1 - δ) • A.form.val - B.form.val
  let ell := smoothPairing A θ
  let W := formPow B.form.val m
  have hpos : ∀ t : ℝ, 0 < t → 0 < ell G + t * ell W := by
    intro t ht
    let H := G + t • W
    have hH : ∀ e z, z ∈ e.val.target → H.coeff e z ∈ spCone m := by
      intro e z hz
      exact (spCone m).add_mem (hG e z hz)
        ((spCone m).smul_mem ht.le (XiaoKahlerPowerClosed.formPow_coeff_mem_spCone B m e hz))
    have hHd : (ddc H).GeometricallyEq 0 := ddc_add_zero G (t • W) hddc
      (ddc_smul_zero t W (ddc_formPow_geometricallyEq_zero B m))
    have hv : ∀ x, 0 < topRatio A.form.val (wedgeTwo H B.form.val) x := by
      intro x
      have heq : topRatio A.form.val (wedgeTwo H B.form.val) x =
          topRatio A.form.val (wedgeTwo G B.form.val) x +
            t * topRatio A.form.val (formPow B.form.val (m + 1)) x := by
        change topRatio A.form.val (wedgeTwo (G + t • W) B.form.val) x = _
        rw [wedgeTwo_add_left, topRatio_add, wedgeTwo_smul_left, topRatio_smul]
        rfl
      rw [heq]
      exact add_pos_of_nonneg_of_pos (topRatio_testWedge_nonneg A B G hG x)
        (mul_pos ht (topRatio_otherKahlerPower_pos A B x))
    let b := ∫ x, topRatio A.form.val (wedgeTwo H B.form.val) x ∂(kahlerVolume A)
    have hb : 0 < b := XiaoYauTestVolume.integral_topRatio_pos A (wedgeTwo H B.form.val) hv
    let Hn := b⁻¹ • H
    have hHn : ∀ e z, z ∈ e.val.target → Hn.coeff e z ∈ spCone m :=
      fun e z hz => (spCone m).smul_mem (inv_pos.mpr hb).le (hH e z hz)
    have hHnd : (ddc Hn).GeometricallyEq 0 := ddc_smul_zero b⁻¹ H hHd
    have hratio : topRatio A.form.val (wedgeTwo Hn B.form.val) =
        fun x => b⁻¹ * topRatio A.form.val (wedgeTwo H B.form.val) x := by
      funext x
      rw [wedgeTwo_smul_left]
      exact topRatio_smul A.form.val b⁻¹ _ x
    have hvn : ∀ x, 0 < topRatio A.form.val (wedgeTwo Hn B.form.val) x := by
      rw [hratio]
      exact fun x => mul_pos (inv_pos.mpr hb) (hv x)
    have hnorm : (∫ x, topRatio A.form.val (wedgeTwo Hn B.form.val) x ∂(kahlerVolume A)) = 1 := by
      rw [hratio, integral_const_mul]
      exact inv_mul_cancel₀ hb.ne'
    have hp := hstrict Hn hHn hHnd hvn hnorm
    change 0 < ell (b⁻¹ • H) at hp
    rw [map_smul, smul_eq_mul] at hp
    have hPH : 0 < ell H := (mul_pos_iff_of_pos_left (inv_pos.mpr hb)).mp hp
    simpa only [H, map_add, map_smul, smul_eq_mul] using hPH
  by_contra hneg
  have hg : ell G < 0 := lt_of_not_ge hneg
  let t : ℝ := (-ell G) / (2 * (|ell W| + 1))
  have ht : 0 < t := div_pos (neg_pos.mpr hg) (by positivity)
  have hbound : t * ell W ≤ t * (|ell W| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self (ell W)]) ht.le
  have heq : t * (|ell W| + 1) = -ell G / 2 := by
    dsimp only [t]
    field_simp
  have hp := hpos t ht
  rw [heq] at hbound
  linarith

/-- The actual gap produces a genuine positive current with every actual Gauduchon-kernel pairing. -/
theorem exists_gap_positive_current_eq_on_gauduchonKernel (A B : KahlerBackground (m + 1) M)
    (hM : 0 < NefMixedMass.slotIntegral A (Fin.cons B.form (fun _ : Fin m => A.form)))
    (hgap : 4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral A
      (Fin.cons B.form (fun _ : Fin m => A.form)) < (kahlerVolume A).real univ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ T : ProductCurrent (m + 1) M m, IsPositive T ∧
        ∀ G : gauduchonKernel (m + 1) M m,
          T G.val = smoothTestPairing A ((1 - δ) • A.form.val - B.form.val) G.val := by
  obtain ⟨δ, hδ0, hδ1, hnonneg⟩ := exists_uniform_nonneg_gauduchon_test_positivity A B hM hgap
  let ell := (smoothTestPairing A ((1 - δ) • A.form.val - B.form.val)).comp
    (gauduchonKernel (m + 1) M m).subtype
  have hell : ∀ G : gauduchonKernel (m + 1) M m,
      G.val ∈ positiveCone (m + 1) M m → 0 ≤ ell G := by
    intro G hG
    exact hnonneg G.val.val hG G.property
  obtain ⟨T, hT, hext⟩ := exists_positive_extension_from_gauduchonKernel A m ell hell
  exact ⟨δ, hδ0, hδ1, T, hT, hext⟩

end Pairing

end

end SGPT.Foundations.Analysis.Pending.XiaoPositiveGauduchonExtension

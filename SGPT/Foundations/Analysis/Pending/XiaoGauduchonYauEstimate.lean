import SGPT.Foundations.Analysis.Pending.XiaoGauduchonIntegration
import SGPT.Foundations.Analysis.Pending.XiaoYauTestEstimate

set_option autoImplicit false

/-!
# Xiao's actual test estimate after genuine Gauduchon cancellation

The actual Yau solution and bad-set estimate already use the original actual
mixed mass. Genuine geometric `ddᶜG = 0` removes the correction and produces
uniform strict positivity against the actual normalized Gauduchon tests.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.XiaoGauduchonYauEstimate

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms IntegrationCurrent LocalProductCurrents TopDegreeDensity CoordinateWedgeAssoc
  XiaoComplexDifferential XiaoGauduchonIntegration ManifoldTubePositivity

noncomputable section

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

/-- The actual Xiao estimate after cancellation from the genuine Gauduchon condition. -/
theorem integral_testWedge_ge_of_gauduchon
    (A B : KahlerBackground (m + 1) X) (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m)
    (hddc : (XiaoComplexDifferential.ddc G).GeometricallyEq
      (0 : SmoothRealForm (m + 1) X (2 * (m + 1))))
    (hv : ∀ x, 0 < topRatio A.form.val (wedgeTwo G B.form.val) x)
    (hnorm : ∫ x, topRatio A.form.val (wedgeTwo G B.form.val) x ∂(kahlerVolume A) = 1)
    (hM : 0 < NefMixedMass.slotIntegral A (Fin.cons B.form (fun _ : Fin m => A.form))) :
    (kahlerVolume A).real Set.univ /
      (4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral A
        (Fin.cons B.form (fun _ : Fin m => A.form))) ≤
      ∫ x, topRatio A.form.val (wedgeTwo G A.form.val) x ∂(kahlerVolume A) := by
  obtain ⟨u, hu, _, _, hest⟩ := XiaoYauTestEstimate.exists_kahler_correction_and_test_estimate
    A B G hG hv hnorm hM
  have hc := integral_wedgeTwo_add_ddcForm_eq A A.form.val u hu G
    (fun e z hz => mem_formSpan_of_mem_spCone (hG e z hz)) hddc
  change (∫ x, topRatio A.form.val (wedgeTwo G (A.form + ddcClosedForm u hu).val) x
    ∂(kahlerVolume A)) = _ at hc
  rw [hc] at hest
  exact hest

/-- One explicit number gives strict positivity uniformly over all actual normalized Gauduchon tests. -/
theorem exists_uniform_strict_gauduchon_test_positivity
    (A B : KahlerBackground (m + 1) X)
    (hM : 0 < NefMixedMass.slotIntegral A (Fin.cons B.form (fun _ : Fin m => A.form)))
    (hgap : 4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral A
      (Fin.cons B.form (fun _ : Fin m => A.form)) < (kahlerVolume A).real Set.univ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (G : SmoothRealForm (m + 1) X (2 * m)),
        (∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m) →
        (XiaoComplexDifferential.ddc G).GeometricallyEq
          (0 : SmoothRealForm (m + 1) X (2 * (m + 1))) →
        (∀ x, 0 < topRatio A.form.val (wedgeTwo G B.form.val) x) →
        (∫ x, topRatio A.form.val (wedgeTwo G B.form.val) x ∂(kahlerVolume A)) = 1 →
        0 < ∫ x, topRatio A.form.val
          (wedgeTwo G ((1 - δ) • A.form.val - B.form.val)) x ∂(kahlerVolume A) := by
  let R : ℝ := (kahlerVolume A).real Set.univ /
    (4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral A
      (Fin.cons B.form (fun _ : Fin m => A.form)))
  have hden : 0 < 4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral A
      (Fin.cons B.form (fun _ : Fin m => A.form)) := by positivity
  have hR : 1 < R := (one_lt_div hden).mpr hgap
  have hRp : 0 < R := lt_trans zero_lt_one hR
  let δ : ℝ := (R - 1) / (2 * R)
  have hδp : 0 < δ := div_pos (sub_pos.mpr hR) (mul_pos (by norm_num) hRp)
  have hδlt : δ < 1 := by
    apply (div_lt_one (mul_pos (by norm_num) hRp)).mpr
    linarith
  have hδmul : (1 - δ) * R - 1 = (R - 1) / 2 := by
    dsimp [δ]
    field_simp
    ring
  refine ⟨δ, hδp, hδlt, ?_⟩
  intro G hG hddc hv hnorm
  have hest := integral_testWedge_ge_of_gauduchon A B G hG hddc hv hnorm hM
  change R ≤ _ at hest
  have hforms : wedgeTwo G ((1 - δ) • A.form.val - B.form.val) =
      (1 - δ) • wedgeTwo G A.form.val - wedgeTwo G B.form.val := by
    apply smoothRealForm_ext
    intro e z
    exact (show coordinateWedge (G.coeff e z)
      ((1 - δ) • A.form.val.coeff e z - B.form.val.coeff e z) =
      (1 - δ) • coordinateWedge (G.coeff e z) (A.form.val.coeff e z) -
        coordinateWedge (G.coeff e z) (B.form.val.coeff e z) from by
      rw [sub_eq_add_neg, coordinateWedge_add_right, coordinateWedge_smul_right,
        coordinateWedge_neg_right]
      simp only [sub_eq_add_neg])
  have heq : topRatio A.form.val (wedgeTwo G ((1 - δ) • A.form.val - B.form.val)) =
      fun x => (1 - δ) * topRatio A.form.val (wedgeTwo G A.form.val) x -
        topRatio A.form.val (wedgeTwo G B.form.val) x := by
    funext x
    rw [hforms]
    simp only [topRatio, chartRatio, coeff_sub, coeff_smul, topDensity_sub,
      topDensity_smul, sub_div, mul_div_assoc]
  rw [heq, integral_sub ((integrable_topRatio A _).const_mul _) (integrable_topRatio A _),
    integral_const_mul, hnorm]
  have hscale := mul_le_mul_of_nonneg_left hest (sub_pos.mpr hδlt).le
  have hpos : 0 < (1 - δ) * R - 1 := by rw [hδmul]; positivity
  linarith

end

end SGPT.Foundations.Analysis.Pending.XiaoGauduchonYauEstimate

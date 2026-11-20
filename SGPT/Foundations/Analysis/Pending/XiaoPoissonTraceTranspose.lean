import SGPT.Foundations.Analysis.Pending.XiaoPositiveGauduchonExtension
import SGPT.Foundations.Analysis.Pending.XiaoTopDDCPrimitive
import SGPT.Foundations.Analysis.Pending.CurrentTraceMeasure

set_option autoImplicit false

/-!
# An actual continuous Poisson transpose from the positive trace measure

Actual finite trace integration and the actual bounded Poisson inverse produce
a continuous scalar functional. Its actual smooth inputs recover the current
difference on genuine Gauduchon tests.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace SGPT.Foundations.Analysis.Pending.XiaoPoissonTraceTranspose

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents CurrentTraceMeasure TopDegreeDensity IntegrationCurrent
  TopBidimensionCurrents XiaoComplexDifferential XiaoGauduchonKernel XiaoKahlerScalarDDC
  XiaoPositiveGauduchonExtension XiaoTopDDCPrimitive XiaoPoissonProducer
  KahlerLaplacianChart KahlerLaplacianSolvability HolderAtlas.HolderMap

noncomputable section

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] {r : ℝ≥0}

/-- The actual weighted scalar trace integral is genuinely continuous on every existing Hölder space. -/
def weightedTraceCLM (w : KahlerBackground (m + 1) M) (A : HolderAtlas (m + 1) M)
    (θ : SmoothRealForm (m + 1) M 2) (k : ℕ) (r : ℝ≥0) :
    A.HolderMap k r ℝ →L[ℝ] ℝ := by
  let p : C(M, ℝ) := ⟨topRatio w.form.val (wedgeTwo (formPow w.form.val m) θ),
    continuous_topRatio w.isKahler.1 _⟩
  have hi (u : A.HolderMap k r ℝ) : Integrable (fun x => u x * p x) (kahlerVolume w) :=
    ((HolderAtlas.HolderMap.continuous u).mul p.continuous).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  refine LinearMap.mkContinuous
    { toFun := fun u => ∫ x, u x * p x ∂(kahlerVolume w)
      map_add' := fun u v => by
        simp only [coe_add, Pi.add_apply, add_mul]
        exact integral_add (hi u) (hi v)
      map_smul' := fun c u => by
        simp only [coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
    ((kahlerVolume w).real univ * ‖p‖) ?_
  intro u
  have hbound : ∀ x, ‖u x * p x‖ ≤ ‖u‖ * ‖p‖ := by
    intro x
    rw [norm_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using ManifoldContinuity.abs_apply_le_norm u x)
      (p.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
  have hb := norm_integral_le_of_norm_le_const (μ := kahlerVolume w)
    (Eventually.of_forall hbound)
  change ‖∫ x, u x * p x ∂(kahlerVolume w)‖ ≤ _
  calc
    _ ≤ (‖u‖ * ‖p‖) * (kahlerVolume w).real univ := hb
    _ = _ := by ring

@[simp] theorem weightedTraceCLM_apply (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (θ : SmoothRealForm (m + 1) M 2)
    (k : ℕ) (r : ℝ≥0) (u : A.HolderMap k r ℝ) :
    weightedTraceCLM w A θ k r u = ∫ x, u x *
      topRatio w.form.val (wedgeTwo (formPow w.form.val m) θ) x ∂(kahlerVolume w) := rfl

/-- The actual weighted integral is the actual smooth scalar-power pairing. -/
theorem smoothPairing_smulFun_formPow (w : KahlerBackground (m + 1) M)
    (θ : SmoothRealForm (m + 1) M 2) (u : M → ℝ) (hu : ChartSmooth (n := m + 1) u) :
    smoothPairing w θ (smulFun u hu (formPow w.form.val m)) =
      ∫ x, u x * topRatio w.form.val (wedgeTwo (formPow w.form.val m) θ) x ∂(kahlerVolume w) := by
  have heq : topRatio w.form.val (wedgeTwo (smulFun u hu (formPow w.form.val m)) θ) =
      fun x => u x * topRatio w.form.val (wedgeTwo (formPow w.form.val m) θ) x := by
    funext x
    rw [← smulFun_wedgeTwo]
    simp only [topRatio, chartRatio, smulFun_coeff, topDensity_smul, mul_div_assoc]
    rw [(complexChartAt (n := m + 1) x).val.left_inv (mem_complexChartAt_source x)]
  rw [smoothPairing_apply, heq]

variable [ConnectedSpace M]

/-- The actual finite positive trace measure and actual Poisson inverse give a continuous transpose. -/
def poissonTraceTransposeCLM (w : KahlerBackground (m + 1) M) (A : HolderAtlas (m + 1) M)
    (hr0 : 0 < r) (hr1 : r < 1) (T : ProductCurrent (m + 1) M m) (hT : IsPositive T)
    (θ : SmoothRealForm (m + 1) M 2) : A.HolderMap 0 r ℝ →L[ℝ] ℝ :=
  (((integralCLM (A := A) (k := 2) (r := r) (traceMeasure w T hT) -
    weightedTraceCLM w A θ 2 r).comp
      (integralCLM (A := A) (k := 2) (r := r) (kahlerVolume w)).ker.subtypeL).comp
        (meanZeroPoissonCLM w A hr0 hr1 0)).comp
          ((m + 1 : ℝ) • ContinuousLinearMap.id ℝ (A.HolderMap 0 r ℝ))

@[simp] theorem poissonTraceTransposeCLM_apply (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr0 : 0 < r) (hr1 : r < 1)
    (T : ProductCurrent (m + 1) M m) (hT : IsPositive T)
    (θ : SmoothRealForm (m + 1) M 2) (h : A.HolderMap 0 r ℝ) :
    let u := (meanZeroPoissonCLM w A hr0 hr1 0 ((m + 1 : ℝ) • h)).val
    poissonTraceTransposeCLM w A hr0 hr1 T hT θ h =
      (∫ x, u x ∂(traceMeasure w T hT)) -
        ∫ x, u x * topRatio w.form.val (wedgeTwo (formPow w.form.val m) θ) x ∂(kahlerVolume w) := rfl

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- A genuine actual Laplacian solution identifies the entire higher-degree `ddᶜ` tensor. -/
theorem ddc_smulFun_formPow_geometricallyEq_of_laplacian_eq
    (w : KahlerBackground (m + 1) M) (u : M → ℝ) (hu : ChartSmooth (n := m + 1) u)
    (Φ : SmoothRealForm (m + 1) M (2 * (m + 1)))
    (hLap : ∀ x, laplacian w.form.val u x = (m + 1 : ℝ) * topRatio w.form.val Φ x) :
    (ddc (smulFun u hu (formPow w.form.val m))).GeometricallyEq Φ := by
  intro e z hz
  calc
    (ddc (smulFun u hu (formPow w.form.val m))).coeff e z =
        topRatio w.form.val (ddc (smulFun u hu (formPow w.form.val m))) (e.val.symm z) •
          (formPow w.form.val (m + 1)).coeff e z :=
      coeff_eq_topRatio_smul w.isKahler.1 _ e hz
    _ = topRatio w.form.val Φ (e.val.symm z) • (formPow w.form.val (m + 1)).coeff e z := by
      rw [topRatio_ddc_smulFun_formPow_eq_laplacian w u hu, hLap]
      rw [mul_div_cancel_left₀ _ (by positivity : (m + 1 : ℝ) ≠ 0)]
    _ = Φ.coeff e z := (coeff_eq_topRatio_smul w.isKahler.1 Φ e hz).symm

/-- The actual continuous Poisson transpose recovers the actual current difference on all tests. -/
theorem poissonTraceTransposeCLM_eq_current_difference (w : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr0 : 0 < r) (hr1 : r < 1)
    (T : ProductCurrent (m + 1) M m) (hT : IsPositive T) (θ : SmoothRealForm (m + 1) M 2)
    (hext : ∀ G : gauduchonKernel (m + 1) M m, T G.val = smoothTestPairing w θ G.val)
    (G : testSpace (m + 1) M m) :
    poissonTraceTransposeCLM w A hr0 hr1 T hT θ
      (ofChartSmooth (A := A) (k := 0) hr1.le
        (topRatio w.form.val (ddc (G : SmoothRealForm (m + 1) M (2 * m))))
        (chartSmooth_topRatio w.isKahler.1 _)) = T G - smoothTestPairing w θ G := by
  let Φ := ddc (G : SmoothRealForm (m + 1) M (2 * m))
  let f := topRatio w.form.val Φ
  have hf : ChartSmooth (n := m + 1) f := chartSmooth_topRatio w.isKahler.1 Φ
  let f0 := ofChartSmooth (A := A) (k := 0) hr1.le f hf
  let h : M → ℝ := fun x => (m + 1 : ℝ) * f x
  have hh : ChartSmooth (n := m + 1) h := fun e => contDiffOn_const.mul (hf e)
  let h0 := ofChartSmooth (A := A) (k := 0) hr1.le h hh
  have hin : (m + 1 : ℝ) • f0 = h0 := by
    apply HolderAtlas.HolderMap.ext
    intro x
    rfl
  have hm : (∫ x, h x ∂(kahlerVolume w)) = 0 := by
    dsimp only [h, f, Φ]
    rw [integral_const_mul]
    exact (congrArg (fun a : ℝ => (m + 1 : ℝ) * a)
      (XiaoGlobalStokes.integral_exteriorDerivative_eq_zero w
        (dc (G : SmoothRealForm (m + 1) M (2 * m))))).trans (mul_zero _)
  let u := (meanZeroPoissonCLM w A hr0 hr1 0 h0).val
  have hu : ChartSmooth (n := m + 1) u :=
    chartSmooth_meanZeroPoissonCLM_of_chartSmooth w A hr0 hr1 h hh hm
  have hLap : ∀ x, laplacian w.form.val u x = (m + 1 : ℝ) * f x :=
    laplacian_meanZeroPoissonCLM_eq_of_integral_eq_zero w A hr0 hr1 0 h0 hm
  let U := smulTest u hu (kahlerTest w m)
  have hUD : (ddc (U : SmoothRealForm (m + 1) M (2 * m))).GeometricallyEq Φ :=
    ddc_smulFun_formPow_geometricallyEq_of_laplacian_eq w u hu Φ hLap
  have hdiff : G - U ∈ gauduchonKernel (m + 1) M m := by
    intro e z hz
    have hforms : ((G - U : testSpace (m + 1) M m) : SmoothRealForm (m + 1) M (2 * m)) =
        (G : SmoothRealForm (m + 1) M (2 * m)) +
          (-1 : ℝ) • (U : SmoothRealForm (m + 1) M (2 * m)) := by
      change (G : SmoothRealForm (m + 1) M (2 * m)) -
        (U : SmoothRealForm (m + 1) M (2 * m)) = _
      simp only [sub_eq_add_neg, neg_one_smul]
    rw [hforms, ddc_add_geometricallyEq _ _ e hz, coeff_add,
      ddc_smul_geometricallyEq (-1 : ℝ) (U : SmoothRealForm (m + 1) M (2 * m)) e hz,
      coeff_smul, hUD e hz]
    change Φ.coeff e z + (-1 : ℝ) • Φ.coeff e z = 0
    ext v
    change Φ.coeff e z v + (-1 : ℝ) * Φ.coeff e z v = 0
    ring
  have hk := hext ⟨G - U, hdiff⟩
  change T (G - U) = smoothTestPairing w θ (G - U) at hk
  rw [map_sub, map_sub] at hk
  have hpU : smoothTestPairing w θ U =
      ∫ x, u x * topRatio w.form.val (wedgeTwo (formPow w.form.val m) θ) x ∂(kahlerVolume w) :=
    smoothPairing_smulFun_formPow w θ u hu
  change poissonTraceTransposeCLM w A hr0 hr1 T hT θ f0 = _
  rw [poissonTraceTransposeCLM_apply]
  rw [hin]
  change (∫ x, u x ∂(traceMeasure w T hT)) -
    (∫ x, u x * topRatio w.form.val (wedgeTwo (formPow w.form.val m) θ) x ∂(kahlerVolume w)) = _
  rw [integral_traceMeasure_chartSmooth w T hT u hu, ← hpU]
  linarith

/-- The actual numerical gap produces both a positive current and its genuine continuous Poisson transpose. -/
theorem exists_gap_positive_current_continuous_transpose (w B : KahlerBackground (m + 1) M)
    (A : HolderAtlas (m + 1) M) (hr0 : 0 < r) (hr1 : r < 1)
    (hM : 0 < NefMixedMass.slotIntegral w (Fin.cons B.form (fun _ : Fin m => w.form)))
    (hgap : 4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral w
      (Fin.cons B.form (fun _ : Fin m => w.form)) < (kahlerVolume w).real univ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ T : ProductCurrent (m + 1) M m, IsPositive T ∧
        ∃ Ψ : A.HolderMap 0 r ℝ →L[ℝ] ℝ,
          ∀ G : testSpace (m + 1) M m,
            Ψ (ofChartSmooth (A := A) (k := 0) hr1.le
              (topRatio w.form.val (ddc (G : SmoothRealForm (m + 1) M (2 * m))))
              (chartSmooth_topRatio w.isKahler.1 _)) =
                T G - smoothTestPairing w ((1 - δ) • w.form.val - B.form.val) G := by
  obtain ⟨δ, hδ0, hδ1, T, hT, hext⟩ :=
    exists_gap_positive_current_eq_on_gauduchonKernel w B hM hgap
  refine ⟨δ, hδ0, hδ1, T, hT,
    poissonTraceTransposeCLM w A hr0 hr1 T hT ((1 - δ) • w.form.val - B.form.val), ?_⟩
  exact fun G => poissonTraceTransposeCLM_eq_current_difference w A hr0 hr1 T hT _ hext G

end

end SGPT.Foundations.Analysis.Pending.XiaoPoissonTraceTranspose

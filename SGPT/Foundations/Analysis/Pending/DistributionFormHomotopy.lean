import SGPT.Foundations.Analysis.Pending.DistributionFormRegularization
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Alternating.Curry

set_option autoImplicit false

/-! # Genuine test homotopy for cohomologous coefficient convolution

The entire mathematical proof was written before this source. Actual compact
parameter integration supplies smoothness and seminorm continuity of the test
homotopy, before any distribution or closed form is provided.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology Interval
open SGPT.Foundations.Analysis.LocalCurrents

namespace SGPT.Foundations.Analysis.Pending.DistributionFormHomotopy

section CompactIntegration

variable {H P F : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ν : Measure P} [IsLocallyFiniteMeasure ν]

omit [CompleteSpace F] in
private theorem compactIntegral_hasFDerivAt
    {G : H → P → F} {G' : H → P → H →L[ℝ] F}
    (hG : Continuous G.uncurry) (hG' : Continuous G'.uncurry)
    (hderiv : ∀ y p, HasFDerivAt (G · p) (G' y p) y)
    {S : Set P} (hS : IsCompact S) (y : H) :
    HasFDerivAt (fun z => ∫ p in S, G z p ∂ν)
      (∫ p in S, G' y p ∂ν) y := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall y 1).prod hS).exists_bound_of_continuousOn
    hG'.continuousOn
  have hc (z : H) : Continuous (G z) :=
    hG.comp (continuous_const.prodMk continuous_id)
  have hc' (z : H) : Continuous (G' z) :=
    hG'.comp (continuous_const.prodMk continuous_id)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := ν.restrict S) (s := Metric.ball y 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds y (by norm_num))
    (Eventually.of_forall fun z => (hc z).aestronglyMeasurable)
    ((hc y).continuousOn.integrableOn_compact hS)
    (hc' y).aestronglyMeasurable
    (by
      filter_upwards [self_mem_ae_restrict hS.measurableSet] with p hp z hz
      exact hC (z,p) ⟨Metric.ball_subset_closedBall hz,hp⟩)
    (integrableOn_const hS.measure_ne_top)
    (Eventually.of_forall fun p z _ => hderiv z p)

private theorem compactIntegral_contDiff_nat (n : ℕ)
    {G : H → P → F} (hG : ContDiff ℝ (⊤ : ℕ∞) G.uncurry)
    {S : Set P} (hS : IsCompact S) :
    ContDiff ℝ n (fun y => ∫ p in S, G y p ∂ν) := by
  induction n generalizing F with
  | zero =>
      change ContDiff ℝ 0 _
      rw [contDiff_zero]
      apply Differentiable.continuous (𝕜 := ℝ)
      intro y
      let G' : H → P → H →L[ℝ] F := fun z p =>
        (fderiv ℝ G.uncurry (z,p)).comp (ContinuousLinearMap.inl ℝ H P)
      have hg' : Continuous G'.uncurry := by
        exact ((hG.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_comp contDiff_const).continuous
      apply (compactIntegral_hasFDerivAt hG.continuous hg' (fun z p => ?_) hS y).differentiableAt
      simpa only [Function.comp_def, Function.uncurry_def, G'] using
        ((hG.differentiable (by simp) (z,p)).hasFDerivAt).comp z
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) z p)
  | succ n ih =>
      let G' : H → P → H →L[ℝ] F := fun z p =>
        (fderiv ℝ G.uncurry (z,p)).comp (ContinuousLinearMap.inl ℝ H P)
      have hg' : ContDiff ℝ (⊤ : ℕ∞) G'.uncurry :=
        (hG.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_comp contDiff_const
      change ContDiff ℝ ((n : ℕ∞ω) + 1) _
      rw [contDiff_succ_iff_hasFDerivAt]
      refine ⟨fun y => ∫ p in S, G' y p ∂ν, ?_, fun y => ?_⟩
      · apply contDiff_clm_apply_iff.mpr
        intro v
        have hv := ih (G := fun z p => G' z p v) (hg'.clm_apply contDiff_const)
        convert hv using 1
        funext y
        exact ContinuousLinearMap.integral_apply
          ((hg'.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hS) v
      · apply compactIntegral_hasFDerivAt hG.continuous hg'.continuous (fun z p => ?_) hS y
        simpa only [Function.comp_def, Function.uncurry_def, G'] using
          ((hG.differentiable (by simp) (z,p)).hasFDerivAt).comp z
            (hasFDerivAt_prodMk_left (𝕜 := ℝ) z p)

private theorem compactIntegral_contDiff
    {G : H → P → F} (hG : ContDiff ℝ (⊤ : ℕ∞) G.uncurry)
    {S : Set P} (hS : IsCompact S) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ∫ p in S, G y p ∂ν) := by
  rw [contDiff_infty]
  intro n
  exact compactIntegral_contDiff_nat n hG hS

end CompactIntegration

section ShiftIntegral

variable {E P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P]
  {ν : Measure P} [IsLocallyFiniteMeasure ν]

private def shiftIntegral (S : Set P) (w : P → ℝ) (d : P → E)
    (f : E → ℝ) (y : E) : ℝ := ∫ p in S, w p * f (y - d p) ∂ν

private theorem shiftIntegral_contDiff {S : Set P} (hS : IsCompact S)
    {w : P → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {d : P → E} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (shiftIntegral (ν := ν) S w d f) := by
  apply compactIntegral_contDiff (G := fun y p => w p * f (y - d p)) _ hS
  exact (hw.comp contDiff_snd).mul (hf.comp (contDiff_fst.sub (hd.comp contDiff_snd)))

private theorem fderiv_shiftIntegral_apply {S : Set P} (hS : IsCompact S)
    {w : P → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {d : P → E} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y v : E) :
    fderiv ℝ (shiftIntegral (ν := ν) S w d f) y v =
      ∫ p in S, w p * fderiv ℝ f (y - d p) v ∂ν := by
  let G : E → P → ℝ := fun z p => w p * f (z - d p)
  let G' : E → P → E →L[ℝ] ℝ := fun z p => w p • fderiv ℝ f (z - d p)
  have hg : ContDiff ℝ (⊤ : ℕ∞) G.uncurry :=
    (hw.comp contDiff_snd).mul (hf.comp (contDiff_fst.sub (hd.comp contDiff_snd)))
  have hg' : ContDiff ℝ (⊤ : ℕ∞) G'.uncurry :=
    (hw.comp contDiff_snd).smul
      ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp
        (contDiff_fst.sub (hd.comp contDiff_snd)))
  have hh := compactIntegral_hasFDerivAt (ν := ν) hg.continuous hg'.continuous
    (fun z p => by
      have hfz : HasFDerivAt (fun q => f (q - d p)) (fderiv ℝ f (z - d p)) z := by
        simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
          ((hf.differentiable (by simp) (z - d p)).hasFDerivAt).comp z
            ((hasFDerivAt_id z).sub_const (d p))
      simpa only [G, G'] using hfz.const_mul (w p)) hS y
  change (fderiv ℝ (fun z => ∫ p in S, G z p ∂ν) y) v = _
  have hI : Integrable (fun p => G' y p) (ν.restrict S) :=
    ((hg'.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hS)
  rw [hh.fderiv, ContinuousLinearMap.integral_apply hI v]
  rfl

private theorem iteratedFDeriv_shiftIntegral_apply {S : Set P} (hS : IsCompact S)
    {w : P → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {d : P → E} (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (y : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (shiftIntegral (ν := ν) S w d f) y v =
      ∫ p in S, w p * iteratedFDeriv ℝ n f (y - d p) v ∂ν := by
  induction n generalizing y with
  | zero => simp only [iteratedFDeriv_zero_apply, shiftIntegral]
  | succ n ih =>
      let q : Fin n → E := Fin.tail v
      let g : E → ℝ := fun z => iteratedFDeriv ℝ n f z q
      have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
        (continuousMultilinearApplyCLM q).contDiff.comp
          (hf.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (i := n) (by
            exact WithTop.coe_le_coe.mpr le_top))
      have hdiff := (shiftIntegral_contDiff (ν := ν) hS hw hd hf).differentiable_iteratedFDeriv
        (m := n) (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
      rw [(hdiff y).iteratedFDeriv_succ_apply_left']
      have heq : (fun z => iteratedFDeriv ℝ n (shiftIntegral (ν := ν) S w d f) z q) =
          shiftIntegral (ν := ν) S w d g := by
        funext z
        exact ih z q
      rw [heq, fderiv_shiftIntegral_apply hS hw hd hg]
      apply integral_congr_ae
      filter_upwards [] with p
      congr 1
      exact ((hf.differentiable_iteratedFDeriv (m := n)
        (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) (y - d p)).iteratedFDeriv_succ_apply_left'
          (m := v)).symm

end ShiftIntegral

section Adapted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

private def homotopySupport (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) : Set (E × ℝ) :=
  tsupport (D.kernel j) ×ˢ Icc (0 : ℝ) 1

private theorem homotopySupport_compact (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) :
    IsCompact (homotopySupport D j) :=
  (D.kernel_hasCompactSupport j).prod isCompact_Icc

private def homotopyWeight (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (p : E × ℝ) : ℝ := D.kernel j p.1 * ell p.1

private theorem homotopyWeight_contDiff (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (homotopyWeight D ell j) :=
  ((D.kernel_contDiff j).comp contDiff_fst).mul (ell.contDiff.comp contDiff_fst)

private def homotopyValue (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (f : E → ℝ) : E → ℝ :=
  shiftIntegral (ν := μ.prod (volume : Measure ℝ)) (homotopySupport D j)
    (homotopyWeight D ell j) (fun p => p.2 • p.1) f

private theorem homotopyValue_contDiff (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (homotopyValue D ell j f) :=
  shiftIntegral_contDiff (homotopySupport_compact D j) (homotopyWeight_contDiff D ell j)
    (by fun_prop) hf

private theorem homotopyValue_zero_outside (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) {y : E}
    (hy : y ∉ D.compact) : homotopyValue D ell j φ y = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [self_mem_ae_restrict (homotopySupport_compact D j).measurableSet] with p hp
  change D.kernel j p.1 * ell p.1 * φ (y - p.2 • p.1) = 0
  have hφ : φ (y - p.2 • p.1) = 0 := by
    by_contra hne
    have hz : y - p.2 • p.1 ∈ closure (D.inner : Set E) :=
      subset_closure (φ.tsupport_subset (subset_tsupport φ hne))
    apply hy (D.coordinate_buffer _ hz y ?_)
    have hk := D.kernel_tsupport_subset j hp.1
    have hscale : D.radius / ((j : ℝ) + 1) ≤ D.radius :=
      div_le_self D.radius_pos.le (by have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith)
    have hh : ‖adaptedComplexModelEquiv p.1‖ ≤ D.radius := hk.trans hscale
    have hmul : y - (y - p.2 • p.1) = p.2 • p.1 := by abel
    rw [hmul, map_real_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp.2.1]
    · exact (mul_le_mul_of_nonneg_right hp.2.2 (norm_nonneg _)).trans (by simpa using hh)
    · exact adaptedComplexModelEquiv.continuous
  rw [hφ, mul_zero]

private theorem homotopyValue_add (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) {f g : E → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    homotopyValue D ell j (f + g) = homotopyValue D ell j f + homotopyValue D ell j g := by
  funext y
  simp only [homotopyValue, shiftIntegral, Pi.add_apply, mul_add]
  apply integral_add
  · exact ((homotopyWeight_contDiff D ell j).continuous.mul
      (hf.comp (by fun_prop))).continuousOn.integrableOn_compact (homotopySupport_compact D j)
  · exact ((homotopyWeight_contDiff D ell j).continuous.mul
      (hg.comp (by fun_prop))).continuousOn.integrableOn_compact (homotopySupport_compact D j)

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem homotopyValue_smul (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (f : E → ℝ) (c : ℝ) :
    homotopyValue D ell j (c • f) = c • homotopyValue D ell j f := by
  funext y
  simp only [homotopyValue, shiftIntegral, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (homotopyWeight D ell j _) c, mul_assoc, integral_const_mul]

private theorem homotopyValue_jet_bound (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (K : Compacts E)
    (f : ContDiffMapSupportedIn E ℝ ⊤ K) (n : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ n (homotopyValue D ell j f) y‖ ≤
      (∫ p in homotopySupport D j, ‖homotopyWeight D ell j p‖ ∂μ.prod (volume : Measure ℝ)) *
        ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K n f := by
  let N := ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K n f
  let C := ∫ p in homotopySupport D j, ‖homotopyWeight D ell j p‖ ∂μ.prod (volume : Measure ℝ)
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hN : 0 ≤ N := apply_nonneg _ _
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC hN)
  intro v
  dsimp only [homotopyValue]
  rw [iteratedFDeriv_shiftIntegral_apply (homotopySupport_compact D j)
    (homotopyWeight_contDiff D ell j) (by fun_prop) f.contDiff]
  calc
    ‖∫ p in homotopySupport D j, homotopyWeight D ell j p *
      iteratedFDeriv ℝ n f (y - p.2 • p.1) v ∂μ.prod (volume : Measure ℝ)‖ ≤
      ∫ p in homotopySupport D j, ‖homotopyWeight D ell j p‖ * (N * ∏ i, ‖v i‖)
          ∂μ.prod (volume : Measure ℝ) := by
      apply norm_integral_le_of_norm_le
        (((homotopyWeight_contDiff D ell j).continuous.norm.continuousOn.integrableOn_compact
          (homotopySupport_compact D j)).mul_const _)
      filter_upwards [] with p
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((iteratedFDeriv ℝ n f (y - p.2 • p.1)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right
          (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    _ = C * N * ∏ i, ‖v i‖ := by rw [integral_mul_const]; ring

private def homotopySupportedIn (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) :
    ContDiffMapSupportedIn E ℝ ⊤ D.compact :=
  .of_support_subset (homotopyValue_contDiff D ell j φ.contDiff) (by
    intro y hy
    by_contra hnot
    exact hy (homotopyValue_zero_outside D ell j φ hnot))

private def homotopyFixedSupportCLM (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (K : Compacts E) (hK : (K : Set E) ⊆ D.inner) :
    ContDiffMapSupportedIn E ℝ ⊤ K →L[ℝ] ContDiffMapSupportedIn E ℝ ⊤ D.compact :=
  ContDiffMapSupportedIn.mkCLM ℝ (fun f => homotopyValue D ell j f)
    (fun f g y => congrFun (homotopyValue_add D ell j f.continuous g.continuous) y)
    (fun c f y => congrFun (homotopyValue_smul D ell j f c) y)
    (fun f => homotopyValue_contDiff D ell j f.contDiff)
    (fun f y hy => homotopyValue_zero_outside D ell j (TestFunction.ofSupportedIn hK f) hy)
    (fun n _ => ⟨{n},
      ∫ p in homotopySupport D j, ‖homotopyWeight D ell j p‖ ∂μ.prod (volume : Measure ℝ),
      integral_nonneg (fun _ => norm_nonneg _), fun f y _ => by
        simpa only [Finset.sup_singleton] using homotopyValue_jet_bound D ell j K f n y⟩)

private def homotopyCLM (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) : 𝓓(D.inner, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.limitCLM ℝ
    (fun φ => TestFunction.ofSupportedIn D.compact_subset (homotopySupportedIn D ell j φ))
    (fun K hK => (TestFunction.ofSupportedInCLM ℝ D.compact_subset).comp
      (homotopyFixedSupportCLM D ell j K hK)) (fun _ _ _ => by ext; rfl)

private theorem homotopyCLM_apply (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) (y : E) :
    homotopyCLM D ell j φ y = homotopyValue D ell j φ y := rfl

private theorem homotopyCLM_commute (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) (v : E) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (homotopyCLM D ell j φ) =
      homotopyCLM D ell j (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ) := by
  ext y
  rw [TestFunction.lineDerivCLM_apply]
  simp only [le_top, ↓reduceIte]
  rw [((homotopyCLM D ell j φ).contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv]
  change fderiv ℝ (homotopyValue D ell j φ) y v = _
  dsimp only [homotopyValue]
  rw [fderiv_shiftIntegral_apply (homotopySupport_compact D j)
    (homotopyWeight_contDiff D ell j) (by fun_prop) φ.contDiff]
  apply integral_congr_ae
  filter_upwards [] with p
  congr 1

private theorem homotopyValue_eq_double (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) {f : E → ℝ} (hf : Continuous f) (y : E) :
    homotopyValue D ell j f y =
      ∫ h, D.kernel j h * ell h * (∫ t in (0 : ℝ)..1, f (y - t • h)) ∂μ := by
  change (∫ p in tsupport (D.kernel j) ×ˢ Icc (0 : ℝ) 1,
    D.kernel j p.1 * ell p.1 * f (y - p.2 • p.1) ∂μ.prod (volume : Measure ℝ)) = _
  have hI : IntegrableOn (fun p : E × ℝ => D.kernel j p.1 * ell p.1 * f (y - p.2 • p.1))
      (tsupport (D.kernel j) ×ˢ Icc (0 : ℝ) 1) (μ.prod (volume : Measure ℝ)) :=
    ((homotopyWeight_contDiff D ell j).continuous.mul (hf.comp (by fun_prop))).continuousOn.integrableOn_compact
      (homotopySupport_compact D j)
  rw [setIntegral_prod _ hI]
  have ht : ∀ h : E, (∫ t in Icc (0 : ℝ) 1, f (y - t • h)) =
      ∫ t in (0 : ℝ)..1, f (y - t • h) := by
    intro h
    rw [intervalIntegral.integral_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
  simp_rw [integral_const_mul, ht]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro h hh
  rw [image_eq_zero_of_notMem_tsupport hh, zero_mul, zero_mul]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem segment_derivative_integral (φ : 𝓓(Ω, ℝ)) (y h : E) :
    (∫ t in Icc (0 : ℝ) 1, fderiv ℝ φ (y - t • h) h) = φ y - φ (y - h) := by
  let g : ℝ → ℝ := fun t => φ (y - t • h)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := φ.contDiff.comp (by fun_prop)
  have hgd (t : ℝ) : deriv g t = -fderiv ℝ φ (y - t • h) h := by
    have hd : HasDerivAt (fun t : ℝ => y - t • h) (-h) t := by
      convert (hasDerivAt_const t y).sub ((hasDerivAt_id t).smul_const h) using 1
      · funext a; rfl
      · simp
    have hc := ((φ.contDiff.differentiable (by simp) (y - t • h)).hasFDerivAt).comp_hasDerivAt t hd
    simpa only [g, Function.comp_def, map_neg] using hc.deriv
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    ((hg.of_le (by norm_num : (1 : ℕ∞ω) ≤ (⊤ : ℕ∞))).contDiffOn) zero_le_one
  calc
    (∫ t in Icc (0 : ℝ) 1, fderiv ℝ φ (y - t • h) h) =
        -(∫ t in (0 : ℝ)..1, deriv g t) := by
      simp_rw [hgd, intervalIntegral.integral_neg, neg_neg,
        intervalIntegral.integral_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
    _ = φ y - φ (y - h) := by rw [hFTC]; simp [g]

private def realBasisCoordinate (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap

private theorem homotopyCLM_divergence (D : AdaptedRadialKernelData μ Ω x)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) :
    (∑ i, TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (b i)
      (homotopyCLM D (realBasisCoordinate b i) j φ)) =
      (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) -
        TestFunction.ofSupportedIn D.cutoffCompact_subset (D.convolutionTestFunctionSupportedIn j φ) := by
  classical
  ext y
  have hI (i : Fin (Module.finrank ℝ E)) :
      IntegrableOn (fun p : E × ℝ => D.kernel j p.1 * b.coord i p.1 *
        fderiv ℝ φ (y - p.2 • p.1) (b i)) (homotopySupport D j) (μ.prod (volume : Measure ℝ)) := by
    have hc : Continuous (fun p : E × ℝ => D.kernel j p.1 * b.coord i p.1 *
        fderiv ℝ φ (y - p.2 • p.1) (b i)) :=
      ((homotopyWeight_contDiff D (realBasisCoordinate b i) j).continuous.mul
        (((φ.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp
          (by fun_prop : Continuous (fun p : E × ℝ => y - p.2 • p.1))).clm_apply continuous_const))
    exact hc.continuousOn.integrableOn_compact (homotopySupport_compact D j)
  have hsum (h z : E) : ∑ i, b.coord i h * fderiv ℝ φ z (b i) = fderiv ℝ φ z h := by
    conv_rhs => rw [← b.sum_repr h, map_sum]
    simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply]
  calc
    _ = ∫ p in homotopySupport D j, D.kernel j p.1 *
        fderiv ℝ φ (y - p.2 • p.1) p.1 ∂μ.prod (volume : Measure ℝ) := by
      simp only [sum_apply, homotopyCLM_commute, homotopyCLM_apply,
        homotopyValue, shiftIntegral]
      simp only [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply,
        le_top, ↓reduceIte]
      change (∑ i, ∫ p in homotopySupport D j, D.kernel j p.1 * b.coord i p.1 *
        fderiv ℝ φ (y - p.2 • p.1) (b i) ∂μ.prod (volume : Measure ℝ)) = _
      rw [← integral_finsetSum _ (fun i _ => hI i)]
      apply integral_congr_ae
      filter_upwards [] with p
      change (∑ i, D.kernel j p.1 * b.coord i p.1 * fderiv ℝ φ (y - p.2 • p.1) (b i)) = _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, hsum]
    _ = ∫ h in tsupport (D.kernel j), D.kernel j h * (φ y - φ (y - h)) ∂μ := by
      have hf : Continuous (fun p : E × ℝ => D.kernel j p.1 *
          fderiv ℝ φ (y - p.2 • p.1) p.1) := by
        exact ((D.kernel_contDiff j).continuous.comp continuous_fst).mul
          (((φ.contDiff.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp
            (by fun_prop)).clm_apply continuous_fst)
      change (∫ p in tsupport (D.kernel j) ×ˢ Icc (0 : ℝ) 1, D.kernel j p.1 *
        fderiv ℝ φ (y - p.2 • p.1) p.1 ∂μ.prod (volume : Measure ℝ)) = _
      rw [setIntegral_prod _ (hf.continuousOn.integrableOn_compact (homotopySupport_compact D j))]
      simp_rw [integral_const_mul, segment_derivative_integral φ]
    _ = ∫ h, D.kernel j h * (φ y - φ (y - h)) ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun h hh => by
        rw [image_eq_zero_of_notMem_tsupport hh, zero_mul])
    _ = φ y - ∫ h, φ (y - h) * D.kernel j h ∂μ := by
      have hc : Continuous (fun h : E => D.kernel j h * φ (y - h)) :=
        (D.kernel_contDiff j).continuous.mul (φ.continuous.comp (continuous_const.sub continuous_id))
      have hp : HasCompactSupport (fun h : E => D.kernel j h * φ (y - h)) :=
        (D.kernel_hasCompactSupport j).mul_right
      simp_rw [mul_sub]
      rw [integral_sub ((D.kernel_integrable j).mul_const (φ y))
        (hc.integrable_of_hasCompactSupport hp), integral_mul_const, D.kernel_integral_one, one_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with h
      exact mul_comm _ _
    _ = _ := by
      have hm : (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) y = φ y := by
        simp [TestFunction.monoCLM_apply, D.inner_le]
      change _ = (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) y - D.convolutionTestFunctionSupportedIn j φ y
      rw [hm]
      congr 1
      exact (convolution_eq_swap (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := μ) (f := (φ : E → ℝ)) (g := D.kernel j)).symm

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem derivative_curryLeft_of_closed {k : ℕ}
    (A : DistributionForm Ω (k+1)) (hA : IsClosed A) (b : E) (v : Fin (k+1) → E) :
    exteriorDerivative (A.curryLeft b) v =
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) b (A v) := by
  have hc := congrArg (fun C : DistributionForm Ω (k+2) => C (Fin.cons b v)) hA
  rw [exteriorDerivative_apply, Fin.sum_univ_succ] at hc
  have hr (i : Fin (k+1)) :
      (i.succ.removeNth (Fin.cons b v : Fin (k+2) → E) : Fin (k+1) → E) =
        (Fin.cons b (i.removeNth v) : Fin (k+1) → E) := by
    exact Fin.cons_comp_succ_succAbove b v i
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.removeNth_zero, Fin.tail_cons,
    Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, hr, pow_succ,
    mul_zsmul, neg_one_zsmul, smul_neg, Finset.sum_neg_distrib] at hc
  rw [exteriorDerivative_apply]
  have h := (eq_neg_of_add_eq_zero_left hc).symm
  simpa only [AlternatingMap.curryLeft_apply_apply, Matrix.vecCons, neg_neg] using h

/-- The finite real basis and all actual test homotopies are produced internally,
before any original coefficient distribution is given. -/
theorem exists_test_homotopy (D : AdaptedRadialKernelData μ Ω x) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
      (H : ℕ → Fin (Module.finrank ℝ E) → (𝓓(D.inner, ℝ) →L[ℝ] 𝓓(Ω, ℝ))),
      (∀ j i (φ : 𝓓(D.inner, ℝ)) y, H j i φ y =
        ∫ h, D.kernel j h * b.coord i h * (∫ t in (0 : ℝ)..1, φ (y - t • h)) ∂μ) ∧
      (∀ j i (φ : 𝓓(D.inner, ℝ)), tsupport (H j i φ) ⊆ D.compact) ∧
      (∀ j i (φ : 𝓓(D.inner, ℝ)) v,
        TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (H j i φ) =
          H j i (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)) ∧
      (∀ j (φ : 𝓓(D.inner, ℝ)),
        (∑ i, TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (b i) (H j i φ)) =
          (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) -
            TestFunction.ofSupportedIn D.cutoffCompact_subset
              (D.convolutionTestFunctionSupportedIn j φ)) := by
  let b := Module.finBasis ℝ E
  refine ⟨b, fun j i => homotopyCLM D (realBasisCoordinate b i) j, ?_, ?_, ?_, ?_⟩
  · intro j i φ y
    exact homotopyValue_eq_double D (realBasisCoordinate b i) j φ.continuous y
  · intro j i φ
    apply (D.compact.isCompact.isClosed).closure_subset_iff.mpr
    intro y hy
    by_contra hn
    exact hy (homotopyValue_zero_outside D (realBasisCoordinate b i) j φ hn)
  · intro j i φ v
    exact homotopyCLM_commute D (realBasisCoordinate b i) j φ v
  · intro j φ
    exact homotopyCLM_divergence D b j φ

private def transposeHomotopyLM (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) : 𝓓'(Ω, ℝ) →ₗ[ℝ] 𝓓'(D.inner, ℝ) where
  toFun T := T.comp (homotopyCLM D ell j)
  map_add' T S := by ext φ; rfl
  map_smul' c T := by ext φ; rfl

private theorem transposeHomotopyLM_derivative (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) (T : 𝓓'(Ω, ℝ)) (v : E) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v (transposeHomotopyLM D ell j T) =
      transposeHomotopyLM D ell j (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v T) := by
  ext φ
  simp only [Distribution.lineDerivCLM_apply]
  change -T (homotopyCLM D ell j (TestFunction.lineDerivCLM ℝ v φ)) =
    -T (TestFunction.lineDerivCLM ℝ v (homotopyCLM D ell j φ))
  rw [homotopyCLM_commute]

private theorem exteriorDerivative_transposeHomotopy (D : AdaptedRadialKernelData μ Ω x)
    (ell : E →L[ℝ] ℝ) (j : ℕ) {k : ℕ} (A : DistributionForm Ω k) :
    exteriorDerivative ((transposeHomotopyLM D ell j).compAlternatingMap A) =
      (transposeHomotopyLM D ell j).compAlternatingMap (exteriorDerivative A) := by
  apply AlternatingMap.ext
  intro v
  simp only [exteriorDerivative_apply, LinearMap.compAlternatingMap_apply,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact transposeHomotopyLM_derivative D ell j (A (i.removeNth v)) (v i)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem alternating_sum_apply {I : Type*} (s : Finset I) {k : ℕ}
    (A : I → DistributionForm Ω k) (v : Fin k → E) :
    (∑ i ∈ s, A i) v = ∑ i ∈ s, A i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, AlternatingMap.add_apply, ih]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem exteriorDerivative_sum {I : Type*} (s : Finset I) {k : ℕ}
    (A : I → DistributionForm Ω k) :
    exteriorDerivative (∑ i ∈ s, A i) = ∑ i ∈ s, exteriorDerivative (A i) := by
  ext v
  simp only [exteriorDerivative_apply, alternating_sum_apply, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- Actual alternating distribution-valued primitive for the difference of a
closed form and its fixed adapted smoothing. -/
def primitive (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) {k : ℕ}
    (A : DistributionForm Ω (k+1)) : DistributionForm D.inner k := by
  classical
  let b := Module.finBasis ℝ E
  exact ∑ i, (transposeHomotopyLM D (realBasisCoordinate b i) j).compAlternatingMap
    (A.curryLeft (b i))

/-- Every original closed form supplies a genuine exact difference against
all original tests, with no primitive or exactness certificate as an input. -/
theorem exteriorDerivative_primitive_eq_pairing (D : AdaptedRadialKernelData μ Ω x)
    (j : ℕ) {k : ℕ} (A : DistributionForm Ω (k+1)) (hA : IsClosed A)
    (v : Fin (k+1) → E) (φ : 𝓓(D.inner, ℝ)) :
    exteriorDerivative (primitive D j A) v φ =
      (∫ z, φ z * DistributionFormRegularization.regularizedForm D j A z v ∂μ) -
        A v (TestFunction.monoCLM ℝ φ) := by
  classical
  let b := Module.finBasis ℝ E
  have hc : exteriorDerivative (primitive D j A) v =
      ∑ i, transposeHomotopyLM D (realBasisCoordinate b i) j
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (b i) (A v)) := by
    unfold primitive
    rw [exteriorDerivative_sum]
    simp only [alternating_sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [exteriorDerivative_transposeHomotopy, LinearMap.compAlternatingMap_apply,
      derivative_curryLeft_of_closed A hA]
  rw [hc, sum_apply]
  change (∑ i, -(A v) (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (b i)
    (homotopyCLM D (realBasisCoordinate b i) j φ))) = _
  rw [Finset.sum_neg_distrib, ← map_sum, homotopyCLM_divergence D b j φ,
    map_sub, neg_sub]
  congr 1
  exact (D.distribution_convolution_transpose (A v) j φ).symm

end Adapted

end SGPT.Foundations.Analysis.Pending.DistributionFormHomotopy

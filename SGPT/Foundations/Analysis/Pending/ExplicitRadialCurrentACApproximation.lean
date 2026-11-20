import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentMollifiedACForm

set_option autoImplicit false

/-! The actual inner-product radial kernel recovers the whole native AC
coefficient form of every original positive current. The full mathematical
statements and ENTIRE proof precede this source. The arbitrary chosen native
bump is not identified with this explicit radial kernel. No closedness,
analytic type, desired approximation or finite mass certificate is an input. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators ComplexOrder MatrixOrder

namespace SGPT.Foundations.Analysis.Pending.ExplicitRadialCurrentACApproximation
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentLebesgue LocalCurrentSemicontinuity LocalCurrentDeterminant
  LocalCurrentDensityMatrix TopDegreeDensity HolomorphicPullback

attribute [local instance] addCommGroupFormSpan

section Kernel
variable {n : ℕ} (R : ℝ) (hR : 0 < R)
local notation "VEC" => ComplexModel n

private def radialMol (j : ℕ) (x y : VEC) : ℝ := explicitRadialKernel R hR j (x-y)

private theorem radialMol_nonneg (j : ℕ) (x y : VEC) :
    0 ≤ radialMol R hR j x y := explicitRadialKernel_nonneg R hR j (x-y)

private theorem radialMol_contDiff (j : ℕ) (x : VEC) :
    ContDiff ℝ (⊤ : ℕ∞) (radialMol R hR j x) :=
  (explicitRadialKernel_contDiff R hR j).comp (contDiff_const.sub contDiff_id)

private theorem radialMol_tsupport_subset (j : ℕ) (x : VEC) :
    tsupport (radialMol R hR j x) ⊆ closedBall x (shrinkingBump (E := VEC) R hR j).rOut := by
  have he : radialMol R hR j x = fun y => explicitRadialKernel R hR j (y-x) := by
    funext y
    rw [radialMol,← neg_sub y x,explicitRadialKernel_neg]
  rw [he]
  exact tsupport_explicitRadialKernel_translate_subset R hR j x

private theorem dist_le_of_radialMol_ne_zero {j : ℕ} {x y : VEC}
    (hy : radialMol R hR j x y ≠ 0) : dist y x ≤ (shrinkingBump (E := VEC) R hR j).rOut :=
  mem_closedBall.mp (radialMol_tsupport_subset R hR j x (subset_closure hy))

private theorem radialMol_eq_zero {j : ℕ} {x y : VEC}
    (hy : y ∉ closedBall x (shrinkingBump (E := VEC) R hR j).rOut) : radialMol R hR j x y = 0 := by
  by_contra h
  exact hy (mem_closedBall.mpr (dist_le_of_radialMol_ne_zero R hR h))

private theorem eventually_radial_radius_lt {r : ℝ} (hr : 0 < r) :
    ∀ᶠ j in atTop, (shrinkingBump (E := VEC) R hR j).rOut < r :=
  (tendsto_order.1 (tendsto_shrinkingBump_rOut R hR)).2 r hr

private theorem eventually_radial_closedBall_subset {U : Opens VEC} {x : VEC} (hx : x ∈ U) :
    ∀ᶠ j in atTop, closedBall x (shrinkingBump (E := VEC) R hR j).rOut ⊆ U := by
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  filter_upwards [eventually_radial_radius_lt R hR hε] with j hj
  exact (closedBall_subset_ball hj).trans hεU

private def radialBumpTest (U : Opens VEC) (j : ℕ) (x : VEC)
    (h : closedBall x (shrinkingBump (E := VEC) R hR j).rOut ⊆ U) : 𝓓(U,ℝ) where
  toFun := radialMol R hR j x
  contDiff' := radialMol_contDiff R hR j x
  hasCompactSupport' := (isCompact_closedBall x _).of_isClosed_subset (isClosed_tsupport _)
    (radialMol_tsupport_subset R hR j x)
  tsupport_subset' := (radialMol_tsupport_subset R hR j x).trans h

private def radialTest (U : Opens VEC) (j : ℕ) (x : VEC) : 𝓓(U,ℝ) := by
  classical
  exact if h : closedBall x (shrinkingBump (E := VEC) R hR j).rOut ⊆ U then
    radialBumpTest R hR U j x h else 0

private theorem radialTest_nonneg {U : Opens VEC} (j : ℕ) (x y : VEC) :
    0 ≤ radialTest R hR U j x y := by
  classical
  unfold radialTest
  split_ifs with h
  · exact radialMol_nonneg R hR j x y
  · exact le_rfl

private theorem ae_tendsto_integral_radial_mul {U : Set VEC} {g : VEC → ℝ}
    (hg : ∀ z ∈ U, ∃ r > 0, IntegrableOn g (closedBall z r)) :
    ∀ᵐ x, x ∈ U → Tendsto (fun j => ∫ y, radialMol R hR j x y * g y)
      atTop (𝓝 (g x)) := by
  refine ae_of_forall_ball fun z hz => ?_
  obtain ⟨r,hr,hgr⟩ := hg z hz
  refine ⟨r/2,by positivity,?_⟩
  set g' : VEC → ℝ := (closedBall z r).indicator g with hg'def
  have hg'i : Integrable g' := (integrable_indicator_iff measurableSet_closedBall).mpr hgr
  have h := ae_tendsto_translationPairing_explicitRadialKernel hg'i.locallyIntegrable R hR
  filter_upwards [h] with x hx hxz
  have hxz' : x ∈ closedBall z r := ball_subset_closedBall (ball_subset_ball (by linarith) hxz)
  have hgx : g' x = g x := indicator_of_mem hxz' g
  rw [hgx] at hx
  refine hx.congr' ?_
  filter_upwards [eventually_radial_radius_lt R hR (half_pos hr)] with j hj
  unfold translationPairing
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [show explicitRadialKernel R hR j (y-x) = radialMol R hR j x y by
    rw [radialMol,← neg_sub x y,explicitRadialKernel_neg]]
  by_cases hy : radialMol R hR j x y = 0
  · simp [hy]
  · have hyx := dist_le_of_radialMol_ne_zero R hR hy
    have hyz : y ∈ closedBall z r := by
      rw [mem_closedBall]
      rw [mem_ball] at hxz
      calc dist y z ≤ dist y x + dist x z := dist_triangle y x z
        _ ≤ (shrinkingBump (E := VEC) R hR j).rOut + r/2 := add_le_add hyx hxz.le
        _ ≤ r/2 + r/2 := add_le_add hj.le le_rfl
        _ = r := by ring
    rw [hg'def,indicator_of_mem hyz]
    exact mul_comm _ _

private theorem ae_tendsto_integral_radial_singular {U : Set VEC} (hU : IsOpen U)
    {ν : Measure VEC} (hν : ν ⟂ₘ volume)
    (hfin : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤) {f : VEC → ℝ} {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) :
    ∀ᵐ x, x ∈ U → Tendsto (fun j => ∫ y, radialMol R hR j x y * f y ∂ν)
      atTop (𝓝 0) := by
  refine ae_of_forall_ball fun z hz => ?_
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU z hz
  set r := ε/2 with hrdef
  have hr : 0 < r := by positivity
  have hrU : closedBall z r ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  set νz : Measure VEC := ν.restrict (closedBall z r) with hνz
  have : IsFiniteMeasure νz := isFiniteMeasure_restrict.mpr
    (hfin _ (isCompact_closedBall z r) hrU).ne
  have hνzs : νz ⟂ₘ volume := hν.restrict _
  have hrn : νz.rnDeriv volume =ᵐ[volume] 0 := hνzs.rnDeriv_ae_eq_zero
  have hB := Besicovitch.ae_tendsto_rnDeriv νz (volume : Measure VEC)
  refine ⟨r/2,by positivity,?_⟩
  filter_upwards [hB,hrn] with x hx hx0 hxz
  rw [hx0,Pi.zero_apply] at hx
  have hrad : Tendsto (fun j => (shrinkingBump (E := VEC) R hR j).rOut)
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_shrinkingBump_rOut R hR,
      Eventually.of_forall fun j => (shrinkingBump (E := VEC) R hR j).rOut_pos⟩
  have hratio := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hx.comp hrad)
  simp only [ENNReal.toReal_zero,Function.comp_def] at hratio
  set K : ℝ := (2:ℝ)^Module.finrank ℝ VEC with hK
  have hbound : Tendsto (fun j => |C| * K*(νz (closedBall x (shrinkingBump (E := VEC) R hR j).rOut) /
      volume (closedBall x (shrinkingBump (E := VEC) R hR j).rOut)).toReal) atTop (𝓝 0) := by
    simpa using hratio.const_mul (|C| * K)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_radial_radius_lt R hR (half_pos hr)] with j hj
  have hsub : closedBall x (shrinkingBump (E := VEC) R hR j).rOut ⊆ closedBall z r := by
    intro y hy
    rw [mem_closedBall] at hy ⊢
    rw [mem_ball] at hxz
    calc dist y z ≤ dist y x + dist x z := dist_triangle y x z
      _ ≤ (shrinkingBump (E := VEC) R hR j).rOut + r/2 := add_le_add hy hxz.le
      _ ≤ r/2 + r/2 := add_le_add hj.le le_rfl
      _ = r := by ring
  have hint : ∫ y, radialMol R hR j x y*f y ∂ν =
      ∫ y, radialMol R hR j x y*f y ∂νz := by
    rw [hνz,setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    rw [radialMol_eq_zero R hR (fun hy' => hy (hsub hy')),zero_mul]
  rw [hint,Real.norm_eq_abs]
  have hmolle : ∀ y, radialMol R hR j x y ≤
      K/volume.real (closedBall x (shrinkingBump (E := VEC) R hR j).rOut) := by
    intro y
    have h := explicitRadialKernel_le_div_measure_closedBall R hR j (x-y)
    rwa [Measure.addHaar_real_closedBall_center volume (0:VEC),
      ← Measure.addHaar_real_closedBall_center volume x] at h
  calc |∫ y, radialMol R hR j x y*f y ∂νz|
      ≤ ∫ y, |C| * ((K/volume.real (closedBall x (shrinkingBump (E := VEC) R hR j).rOut))*
          (closedBall x (shrinkingBump (E := VEC) R hR j).rOut).indicator 1 y) ∂νz := by
        refine abs_integral_le_integral_abs |>.trans (integral_mono_of_nonneg
          (Eventually.of_forall fun y => abs_nonneg _) ?_ (Eventually.of_forall fun y => ?_))
        · exact ((integrable_const _).indicator measurableSet_closedBall).const_mul _ |>.const_mul _
        · dsimp only
          rw [abs_mul,abs_of_nonneg (radialMol_nonneg R hR j x y),mul_comm]
          by_cases hy : y ∈ closedBall x (shrinkingBump (E := VEC) R hR j).rOut
          · rw [indicator_of_mem hy,Pi.one_apply,mul_one]
            exact mul_le_mul ((hf y).trans (le_abs_self C)) (hmolle y)
              (radialMol_nonneg R hR j x y) (abs_nonneg C)
          · rw [indicator_of_notMem hy,mul_zero,mul_zero,radialMol_eq_zero R hR hy,mul_zero]
    _ = |C| * K*(νz.real (closedBall x (shrinkingBump (E := VEC) R hR j).rOut) /
        volume.real (closedBall x (shrinkingBump (E := VEC) R hR j).rOut)) := by
        rw [integral_const_mul,integral_const_mul,integral_indicator_one measurableSet_closedBall]
        ring
    _ = |C| * K*(νz (closedBall x (shrinkingBump (E := VEC) R hR j).rOut) /
        volume (closedBall x (shrinkingBump (E := VEC) R hR j).rOut)).toReal := by
        rw [ENNReal.toReal_div]
        rfl

private theorem apply_radialBumpTest {U : Opens VEC} {q : ℕ}
    {T : LocalProductCurrent n U q} (hT : IsPositive T) (γ : formSpan n q)
    {j : ℕ} {x : VEC} (h : closedBall x (shrinkingBump (E := VEC) R hR j).rOut ⊆ U) :
    T γ (radialBumpTest R hR U j x h) =
      (∫ y, radialMol R hR j x y*(acWeight hT y*densityForm hT y γ)) +
      ∫ y, radialMol R hR j x y*densityForm hT y γ ∂(sgMeasure hT) := by
  conv_lhs => rw [← sgPart_add_acPart hT]
  rw [LinearMap.add_apply,_root_.add_apply,acPart_apply,sgPart,ofMeasure_apply,add_comm]
  rfl

private theorem ae_tendsto_radial_coefficients {U : Opens VEC} {q : ℕ}
    {T : LocalProductCurrent n U q} (hT : IsPositive T) (γ : formSpan n q) :
    ∀ᵐ x, x ∈ U → Tendsto (fun j => T γ (radialTest R hR U j x)) atTop
      (𝓝 (acWeight hT x*densityForm hT x γ)) := by
  obtain ⟨C,-,hC⟩ := exists_abs_densityForm_le hT γ
  have hac := ae_tendsto_integral_radial_mul R hR (U := (U:Set VEC))
    (g := fun y => acWeight hT y*densityForm hT y γ) fun z hz => by
      obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp U.isOpen z hz
      exact ⟨ε/2,by positivity,(locallyIntegrableOn_acDensity hT γ).integrableOn_compact_subset
        ((closedBall_subset_ball (by linarith)).trans hεU) (isCompact_closedBall z _)⟩
  have hsg := ae_tendsto_integral_radial_singular R hR U.isOpen
    (sgMeasure_mutuallySingular hT)
    (fun K hK hKU => (Measure.le_iff'.mp (sgMeasure_le hT) K).trans_lt
      (hT.traceMeasure_lt_top hK hKU)) hC
  filter_upwards [hac,hsg] with x h1 h2 hxU
  have h := (h1 hxU).add (h2 hxU)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_radial_closedBall_subset R hR hxU] with j hj
  rw [radialTest,dif_pos hj,apply_radialBumpTest R hR hT]

end Kernel

variable {m : ℕ} {U : Opens (ComplexModel (m+1))}

/-- The whole complementary-dual form of the SAME original current tested on
actual explicit radial kernels, with the zero test outside the buffer. -/
def radialMollifiedForm (T : LocalProductCurrent (m+1) U m) (R : ℝ) (hR : 0 < R)
    (j : ℕ) (x : ComplexModel (m+1)) : RealForm (m+1) 2 :=
  ∑ i, T (formBasis (m+1) m i) (radialTest R hR U j x) • dualForm m i

private def evaluation (T : LocalProductCurrent (m+1) U m) (φ : 𝓓(U,ℝ)) :
    formSpan (m+1) m →ₗ[ℝ] ℝ where
  toFun γ := T γ φ
  map_add' γ δ := by simp
  map_smul' c γ := by simp

private theorem radialMollifiedForm_rep (T : LocalProductCurrent (m+1) U m)
    (R : ℝ) (hR : 0 < R) (j : ℕ) (x : ComplexModel (m+1)) (γ : formSpan (m+1) m) :
    T γ (radialTest R hR U j x) =
      topDensity (coordinateWedge (γ : RealForm (m+1) (2*m))
        (radialMollifiedForm T R hR j x)) := by
  classical
  have hexpand : T γ (radialTest R hR U j x) =
      ∑ i, (formBasis (m+1) m).repr γ i *
        T (formBasis (m+1) m i) (radialTest R hR U j x) := by
    change evaluation T (radialTest R hR U j x) γ =
      ∑ i, (formBasis (m+1) m).repr γ i *
        evaluation T (radialTest R hR U j x) (formBasis (m+1) m i)
    conv_lhs => rw [← (formBasis (m+1) m).sum_repr γ,map_sum]
    simp only [map_smul,smul_eq_mul]
  rw [hexpand,← wedgeDensity_apply,radialMollifiedForm,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,wedgeDensity_apply,topDensity_dualForm,smul_eq_mul,mul_comm]

/-- For every original positive current, actual radial reconstruction is
positive at ALL points and indices, and on ONE Lebesgue-full set its entire
form, normalized matrix and genuine top exterior density recover the same
native AC part. No approximation, closedness, type or finite mass is assumed. -/
theorem positive_and_ae_tendsto_radial_form_matrix_density
    {T : LocalProductCurrent (m+1) U m} (hT : IsPositive T) (R : ℝ) (hR : 0 < R) :
    (∀ j x, IsOneOne (radialMollifiedForm T R hR j x) ∧
      (normalizedHermitianMatrix (radialMollifiedForm T R hR j x)).PosSemidef) ∧
    ∀ᵐ x ∂volume, x ∈ U →
      Tendsto (fun j => radialMollifiedForm T R hR j x) atTop (𝓝 (acForm hT x)) ∧
      Tendsto (fun j => normalizedHermitianMatrix (radialMollifiedForm T R hR j x)) atTop
        (𝓝 (acMatrix hT x)) ∧
      Tendsto (fun j => actualTopPowerDensity (radialMollifiedForm T R hR j x)) atTop
        (𝓝 (actualTopPowerDensity (acForm hT x))) := by
  classical
  constructor
  · intro j x
    have h11 : IsOneOne (radialMollifiedForm T R hR j x) :=
      isOneOne_sum _ fun i _ => isOneOne_smul (isOneOne_dualForm i) _
    refine ⟨h11,posSemidef_of_nonneg (L := evaluation T (radialTest R hR U j x)) ?_ h11 ?_⟩
    · intro γ hγ
      exact hT.positiveDistribution hγ _ (radialTest_nonneg R hR j x)
    · exact radialMollifiedForm_rep T R hR j x
  · have hall := ae_all_iff.mpr fun i =>
      ae_tendsto_radial_coefficients R hR hT (formBasis (m+1) m i)
    filter_upwards [hall] with x hx hxU
    have hscalar (i : Fin (Module.finrank ℝ (formSpan (m+1) m))) :
        Tendsto (fun j => T (formBasis (m+1) m i) (radialTest R hR U j x)) atTop
          (𝓝 (acWeight hT x*hT.density (formBasis (m+1) m i) x)) := by
      have h := hx i hxU
      have hd : densityForm hT x (formBasis (m+1) m i) =
          hT.density (formBasis (m+1) m i) x := by
        simp [densityForm_apply,Finsupp.single_apply]
      rwa [hd] at h
    have hform : Tendsto (fun j => radialMollifiedForm T R hR j x) atTop (𝓝 (acForm hT x)) := by
      rw [acForm_eq_sum hT]
      exact tendsto_finsetSum Finset.univ fun i _ => (hscalar i).smul_const (dualForm m i)
    have hmatrix : Continuous (normalizedHermitianMatrix : RealForm (m+1) 2 →
        Matrix (Fin (m+1)) (Fin (m+1)) ℂ) := by
      unfold normalizedHermitianMatrix
      fun_prop
    exact ⟨hform,(hmatrix.tendsto _).comp hform,
      ((RegularBranchKahlerJacobian.RegularPatch.continuous_actualTopPowerDensity
        (m+1)).tendsto _).comp hform⟩

end SGPT.Foundations.Analysis.Pending.ExplicitRadialCurrentACApproximation

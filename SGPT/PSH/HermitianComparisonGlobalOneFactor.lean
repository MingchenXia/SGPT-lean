import SGPT.PSH.HermitianComparisonMollifier
import SGPT.PSH.HermitianComparisonGlobalSmoothing
import SGPT.PSH.HermitianGlobalDdcPartitionReadback
import SGPT.PSH.HermitianGlobalPairingReadback
import SGPT.PSH.HermitianBorelCurrentReadback
import SGPT.Foundations.Analysis.Pending.BidimensionOneDdcFullTranspose

/-!
# Global one-factor comparison and cancellation of localization derivatives

The compact local scalar tests and the auxiliary cutoffs are manufactured
from the actual supported manifold partition. Smooth scalar weights read
back as full compact current tests, before bounded Borel passage. All
cutoff derivatives remain in the native differential until the actual
global partition identity cancels them.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonGlobalOneFactor

open Set Metric Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorForms
  LocalBedfordTaylorSmooth LocalBedfordTaylorCollar LocalBedfordTaylorContinuity
  LocalBedfordTaylorDecreasing LocalBedfordTaylorSmoothProductDensity LocalCurrentLebesgue
  CompactVariableCurrentTests CompactDifferentialTests LocalBedfordTaylorMass
  BorelChartWeightedPatchCurrent ChartPartitionRelativeSupports BidimensionOneDdcFullTranspose
  ActualGlobalBidimensionOneDdc ActualBorelWeightedPatchGlobalCurrent ActualCompactGlobalDdcTransposition
  ActualCompactGlobalPairingCalibration ClosedProductCurrents ConstantFormProducts ProductTestForms
open HermitianComparisonCutoff HermitianComparisonOneFactor HermitianComparisonTranspose HermitianComparisonDensity
  HermitianComparisonStrict HermitianComparisonMollifier HermitianGlobalProducts HermitianProductDifferential
open scoped Topology ContDiff Distributions

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

/-- Every smooth local scalar weight gives an actual full compact current
test equal to `χ ddᶜf`; its pairing is the original Hessian-density extension
of `ddᶜ(χ S)`. No global smooth extension of `f` is assumed. -/
theorem localizedDerivativeWeight_smooth_eq_fullTest {n : ℕ} {U : Opens (ComplexModel n)}
    {ι : Type*} [Fintype ι] (D : ι → Residual n U)
    (χ η : 𝓓(U, ℝ)) (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ α : 𝓓(U, RealForm n 2),
      (∀ z, α z = χ z • smoothDDC f z) ∧
      localizedDerivativeWeight D χ η f = pairing (mixedCurrent D) α := by
  let ψ := mulSmoothOnCLM hf η
  let β := ddcFullTest (scalarTest ψ)
  let α := smoothFormTest χ β β.contDiff
  have hpoint : ∀ z, α z = χ z • smoothDDC f z := by
    intro z
    dsimp only [α]
    rw [smoothFormTest_apply, ddcFullTest_scalarTest_apply]
    by_cases hz : z ∈ tsupport χ
    · congr 1
      apply smoothDDC_congr
      filter_upwards [hη.filter_mono (nhds_le_nhdsSet hz)] with y hy
      simp only [ψ, mulSmoothOnCLM_apply, hy, one_mul]
    · have hχz := image_eq_zero_of_notMem_tsupport hz
      simp only [hχz, zero_smul]
  have hderivative : ddc (smoothMulCurrent (mixedCurrent D) χ.contDiff.contDiffOn) scalarUnit ψ =
      localizedDerivativeWeight D χ η f := by
    rw [mixedCurrent, smoothMulCurrent_sum, ddc_sum]
    simp only [LinearMap.sum_apply, _root_.sum_apply, localizedDerivativeWeight]
    apply Finset.sum_congr rfl
    intro i _
    rw [Residual.mixed, smoothMulCurrent_wedgeForm]
    exact ddc_wedgeForm_smooth_weight_eq (by omega) (by omega) (D i).positive (D i).closed
      (χ.contDiff.contDiffOn.smul (D i).smooth) scalarUnit η hf
  refine ⟨α, hpoint, ?_⟩
  rw [← hderivative, ← pairing_scalarTest, pairing_ddc_scalarTest, pairing_smoothMulCurrent]

/-- On actual `(1,1)` compact tests the native full current reader equals
the original coefficient-current pairing. -/
theorem fullTestFunctional_eq_pairing_of_oneOne {n : ℕ} {U : Opens (ComplexModel n)}
    (S : LocalProductCurrent n U 1) (α : 𝓓(U, RealForm n 2))
    (hα : ∀ z, IsOneOne (α z)) :
    BidimensionOneFullTestFunctional.fullTestFunctional S α = pairing S α := by
  classical
  simp only [BidimensionOneFullTestFunctional.fullTestFunctional, _root_.sum_apply, pairing]
  change (∑ i, S (formBasis n 1 i)
      (TestFunction.postcompCLM ((coeffCLM n 1 i).comp (pi11CLM n)) α)) =
    ∑ i, S (formBasis n 1 i) (coeffTest α i)
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (S (formBasis n 1 i))
  apply TestFunction.ext
  intro z
  change coeffCLM n 1 i (pi11 (α z)) = coeffCLM n 1 i (α z)
  rw [pi11_eq_self (hα z)]

/-- The localized smooth scalar readback is a genuine native full test,
including at every point outside the original coordinate domain. -/
theorem localizedDerivativeWeight_smooth_eq_nativeFullTest {n : ℕ} {U : Opens (ComplexModel n)}
    {ι : Type*} [Fintype ι] (D : ι → Residual n U)
    (χ η : 𝓓(U, ℝ)) (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ α : 𝓓(U, RealForm n 2),
      (∀ z, α z = χ z • smoothDDC f z) ∧
      localizedDerivativeWeight D χ η f =
        BidimensionOneFullTestFunctional.fullTestFunctional (mixedCurrent D) α := by
  obtain ⟨α, hα, hp⟩ := localizedDerivativeWeight_smooth_eq_fullTest D χ η hη hf
  refine ⟨α, hα, hp.trans ?_⟩
  apply (fullTestFunctional_eq_pairing_of_oneOne _ α _).symm
  intro z v w
  rw [hα]
  by_cases hz : χ z = 0
  · simp [hz]
  · have hzU := χ.tsupport_subset (subset_tsupport χ hz)
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [smoothDDC_isOneOne ((hf.contDiffAt (U.isOpen.mem_nhds hzU)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v w]

/-- The bounded-density action of the original derivative, with the
partition weight kept outside the residual coefficients. -/
def derivativeWeight {n : ℕ} {U : Opens (ComplexModel n)} {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (χ : 𝓓(U, ℝ)) (f : ComplexModel n → ℝ) : ℝ :=
  ∑ i, ddcWedgePairing (by omega : 0 + (D i).degree = (D i).degree)
    (D i).positive (D i).form scalarUnit χ f

/-- Smooth local weights recover the actual original differential without
any derivative of the partition weight in its residual coefficients. -/
theorem derivativeWeight_smooth_eq_ddc {n : ℕ} {U : Opens (ComplexModel n)}
    {ι : Type*} [Fintype ι] (D : ι → Residual n U) (χ : 𝓓(U, ℝ))
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    derivativeWeight D χ f = ddc (mixedCurrent D) scalarUnit (mulSmoothOnCLM hf χ) := by
  rw [mixedCurrent, ddc_sum]
  simp only [derivativeWeight, LinearMap.sum_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (ddc_wedgeForm_smooth_weight_eq (by omega) (by omega) (D i).positive (D i).closed
    (D i).smooth scalarUnit χ hf).symm

/-- Bounded Borel dominated convergence for the unlocalized original
residual derivative. Every density is the actual closed-factor density. -/
theorem derivativeWeight_tendsto {n : ℕ} {U : Opens (ComplexModel n)}
    {ι : Type*} [Fintype ι] (D : ι → Residual n U) (χ : 𝓓(U, ℝ))
    {f : ℕ → ComplexModel n → ℝ} {f₀ : ComplexModel n → ℝ}
    (hf : ∀ j, Measurable (f j))
    (hlim : ∀ x ∈ U, Tendsto (fun j => f j x) atTop (𝓝 (f₀ x)))
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ j x, x ∈ tsupport χ → |f j x| ≤ B) :
    Tendsto (fun j => derivativeWeight D χ (f j)) atTop (𝓝 (derivativeWeight D χ f₀)) := by
  unfold derivativeWeight
  apply tendsto_finsetSum
  intro i _
  exact ddcWedgePairing_tendsto (by omega) (D i).positive (D i).smooth scalarUnit χ hf hlim hbound

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] {omega : Hermitian.Background (m + 1) M}

omit [CompactSpace M] in
/-- The literal finite residual presentation of an original Hermitian
mixed current on its actual correction patch. -/
def patchResidual (P : BackgroundPatch omega) (u : Fin m → M → EReal)
    (hu : ∀ i, Hermitian.IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    Finset (Fin m) → Residual (m + 1) P.geometry.domain :=
  backgroundResidual m (oneCurrentOf (U := P.geometry.domain) (by omega : 1 + m = m + 1))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) P.residual_smooth

omit [CompactSpace M] in
/-- The manufactured residual presentation is the SAME original local
mixed current, with no incoming presentation identity. -/
theorem mixedCurrent_patchResidual (P : BackgroundPatch omega) (u : Fin m → M → EReal)
    (hu : ∀ i, Hermitian.IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    mixedCurrent (patchResidual P u hu hb) = P.bidimensionOneCurrent u := by
  unfold patchResidual
  rw [mixedCurrent_backgroundResidual, P.bidimensionOneCurrent_eq_currentOfDegree]
  rfl

/-- A supported actual chart partition weight gives a genuine globally
smooth scalar test on the original correction domain. -/
theorem exists_partition_weight_test (P : BackgroundPatch omega)
    (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hsupp : tsupport χ ⊆ P.geometry.source) :
    ∃ θ : 𝓓(P.geometry.domain, ℝ), ∀ z,
      θ z = chartWeight P.geometry.chart χ z := by
  classical
  let e := P.geometry.chart
  let K : Set (ComplexModel (m + 1)) := e.val '' tsupport χ
  have hK : IsCompact K := (isClosed_tsupport χ).isCompact.image_of_continuousOn
    (e.val.continuousOn.mono (fun _ hx => (hsupp hx).1))
  have hKP : K ⊆ P.geometry.domain := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hsupp hx).2
  let F := chartWeight e χ
  have hFK : tsupport F ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    have hzt : z ∈ e.val.target := by
      by_contra ht
      exact hz (indicator_of_notMem ht _)
    have hχz : χ (e.val.symm z) ≠ 0 := by
      intro hzero
      exact hz (by simp only [F, chartWeight, indicator_of_mem hzt, hzero])
    exact ⟨e.val.symm z, subset_tsupport _ hχz, e.val.right_inv hzt⟩
  have hFt : tsupport F ⊆ e.val.target := hFK.trans (hKP.trans P.geometry.domain_le_target)
  have hFsmoothOn : ContDiffOn ℝ ∞ F e.val.target :=
    (hχ e).congr (fun z hz => indicator_of_mem hz _)
  have hFsmooth : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ e.val.target
    · exact hFsmoothOn.contDiffAt (e.val.open_target.mem_nhds hz)
    · have hzero : F =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds (fun h => hz (hFt h))] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  exact ⟨⟨F, hFsmooth, hK.of_isClosed_subset (isClosed_tsupport F) hFK, hFK.trans hKP⟩, fun _ => rfl⟩

/-- A real compact inner domain and the auxiliary cutoff are manufactured
from the original supported partition weight. The weight is unchanged at
every coordinate point and the cutoff is one on a full neighborhood of
its support. -/
theorem exists_compact_partition_weight_tests (P : BackgroundPatch omega)
    (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hsupp : tsupport χ ⊆ P.geometry.source) :
    ∃ (U : Opens (ComplexModel (m + 1))) (_hUV : RelativelyCompactIn U P.geometry.domain)
      (θ η : 𝓓(U, ℝ)),
      (∀ z, θ z = chartWeight P.geometry.chart χ z) ∧
      ∀ᶠ z in 𝓝ˢ (tsupport θ), η z = 1 := by
  obtain ⟨θ, hθ⟩ := exists_partition_weight_test P χ hχ hsupp
  obtain ⟨V, hVo, hθV, hclV, hcV⟩ := exists_open_between_and_isCompact_closure
    θ.hasCompactSupport P.geometry.domain.isOpen θ.tsupport_subset
  let U : Opens (ComplexModel (m + 1)) := ⟨V, hVo⟩
  let θ' : 𝓓(U, ℝ) := ⟨θ, θ.contDiff, θ.hasCompactSupport, hθV⟩
  obtain ⟨W, hWo, hθW, hclW, hcW⟩ := exists_open_between_and_isCompact_closure
    θ.hasCompactSupport hVo hθV
  obtain ⟨η, hηs, hη1, hηsupp, _⟩ := exists_cutoff_unit hcW hVo hclW
  have hηc : HasCompactSupport η := hcV.of_isClosed_subset (isClosed_tsupport η)
    (hηsupp.trans subset_closure)
  let η' : 𝓓(U, ℝ) := ⟨η, hηs, hηc, hηsupp⟩
  refine ⟨U, ⟨hcV, hclV⟩, θ', η', hθ, ?_⟩
  filter_upwards [hWo.mem_nhdsSet.mpr hθW] with z hz
  exact hη1 z (subset_closure hz)

omit [CompactSpace M] in
/-- Global smooth scalar approximations give both actual local derivative
limits, without declaring either arbitrary off-target chart extension
measurable. Zero extension is used only outside the original local domain. -/
theorem global_scalar_weights_tendsto
    (e : ComplexChart (m + 1) M) {U : Opens (ComplexModel (m + 1))}
    (hU : U ≤ chartTarget e) {ι : Type*} [Fintype ι] (D : ι → Residual (m + 1) U)
    (χ η : 𝓓(U, ℝ)) (f : ℕ → M → ℝ) (f₀ : M → ℝ)
    (hf : ∀ j, ChartSmooth (n := m + 1) (f j))
    (hlim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (f₀ x)))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ j x, |f j x| ≤ B) :
    Tendsto (fun j => localizedDerivativeWeight D χ η (fun z => f j (e.val.symm z))) atTop
      (𝓝 (localizedDerivativeWeight D χ η (fun z => f₀ (e.val.symm z)))) ∧
    Tendsto (fun j => derivativeWeight D χ (fun z => f j (e.val.symm z))) atTop
      (𝓝 (derivativeWeight D χ (fun z => f₀ (e.val.symm z)))) := by
  let g := fun j => (U : Set (ComplexModel (m + 1))).indicator (fun z => f j (e.val.symm z))
  have hg : ∀ j, Measurable (g j) := fun j =>
    measurable_indicator_of_continuousOn (((hf j e).mono hU).continuousOn)
  have hglim : ∀ z ∈ U, Tendsto (fun j => g j z) atTop (𝓝 (f₀ (e.val.symm z))) := by
    intro z hz
    simpa only [g, indicator_of_mem hz] using hlim (e.val.symm z)
  have hgbound : ∀ j z, z ∈ U → |g j z| ≤ B := by
    intro j z hz
    simpa only [g, indicator_of_mem hz] using hbound j (e.val.symm z)
  have hloc := localizedDerivativeWeight_tendsto D χ η hg hglim
    ⟨B, hB, fun j z hz => hgbound j z (η.tsupport_subset hz)⟩
  have hunloc := derivativeWeight_tendsto D χ hg hglim
    ⟨B, hB, fun j z hz => hgbound j z (χ.tsupport_subset hz)⟩
  have heqloc (j : ℕ) : localizedDerivativeWeight D χ η (g j) =
      localizedDerivativeWeight D χ η (fun z => f j (e.val.symm z)) :=
    localizedDerivativeWeight_congr_on D χ η (fun _ hz => indicator_of_mem hz _)
  have hequnloc (j : ℕ) : derivativeWeight D χ (g j) =
      derivativeWeight D χ (fun z => f j (e.val.symm z)) := by
    unfold derivativeWeight
    exact Finset.sum_congr rfl (fun i _ => ddcWedgePairing_congr_on _
      (D i).positive _ scalarUnit χ (fun _ hz => indicator_of_mem hz _))
  simpa only [heqloc, hequnloc] using And.intro hloc hunloc

private theorem monoCLM_apply_of_le {N q : ℕ} {U V : Opens (ComplexModel N)}
    (hUV : U ≤ V) (α : LocalCurrents.TestForm U q) (z : ComplexModel N) :
    (TestFunction.monoCLM ℝ α : LocalCurrents.TestForm V q) z = α z := by
  have h : ((TestFunction.monoCLM ℝ α : LocalCurrents.TestForm V q) : ComplexModel N → RealForm N q) = α := by
    rw [TestFunction.monoCLM_apply, if_pos ⟨le_rfl, hUV⟩]
  exact congrFun h z

private theorem test_cast_apply {N a b : ℕ} {U : Opens (ComplexModel N)} (h : a = b)
    (α : LocalCurrents.TestForm U a) (z : ComplexModel N) :
    (h ▸ α : LocalCurrents.TestForm U b) z = (h ▸ α z : RealForm N b) := by cases h; rfl

private theorem form_cast_coeff {N a b : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel N) X] [IsComplexManifold N X] (h : a = b)
    (α : SmoothRealForm N X a) (e : ComplexChart N X) (z : ComplexModel N) :
    (h ▸ α : SmoothRealForm N X b).coeff e z = (h ▸ α.coeff e z : RealForm N b) := by cases h; rfl

private theorem form_cast_smul {N a b : ℕ} (h : a = b) (r : ℝ) (α : RealForm N a) :
    (h ▸ (r • α) : RealForm N b) = r • (h ▸ α : RealForm N b) := by cases h; rfl

private theorem form_cast_zero {N a b : ℕ} (h : a = b) :
    (h ▸ (0 : RealForm N a) : RealForm N b) = 0 := by cases h; rfl

private theorem clm_cast_apply {N a b : ℕ} {U : Opens (ComplexModel N)} (h : a = b)
    (F : LocalCurrents.TestForm U a →L[ℝ] ℝ) (G : LocalCurrents.TestForm U b →L[ℝ] ℝ)
    (hFG : HEq F G) (α : LocalCurrents.TestForm U b) : F (h.symm ▸ α) = G α := by
  cases h
  rw [eq_of_heq hFG]

private theorem fullTestFunctional_scalar_ddc {n : ℕ} {U : Opens (ComplexModel n)}
    (S : LocalProductCurrent n U 1) (ψ : 𝓓(U, ℝ)) :
    BidimensionOneFullTestFunctional.fullTestFunctional S (localDdcTestCLM (scalarTest ψ)) =
      ddc S scalarUnit ψ := by
  rw [fullTestFunctional_localDdc]
  have hcoeff : LocalCurrents.testCoefficientCLM (fun i : Fin 0 => Fin.elim0 i) (scalarTest ψ) = ψ := by
    ext z
    change ψ z * 1 = ψ z
    ring
  rw [hcoeff]
  rfl

variable [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] in
/-- The genuine native derivative of the unweighted original global
Hermitian mixed current recovers the original local scalar derivative on
every compact patch test. This is derived from the proved native reader
and actual test transposition; no compatibility certificate is supplied. -/
theorem globalDdc_local_scalar_test (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, Hermitian.IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (P : BackgroundPatch omega) (ψ : 𝓓(P.geometry.domain, ℝ)) :
    (globalDdc (D.current u hu hb (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩)).inChart
      P.geometry.chart ((top_complement m).symm ▸
        (TestFunction.monoCLM ℝ (scalarTest ψ) : LocalCurrents.TestForm (chartTarget P.geometry.chart) 0)) =
      ddc (P.bidimensionOneCurrent u) scalarUnit ψ := by
  let S := D.current u hu hb (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
  rw [clm_cast_apply (top_complement m) ((globalDdc S).inChart P.geometry.chart)
    ((bidimensionOneChartFunctional S P.geometry.chart).comp localDdcTestCLM)
    (globalDdc_inChart S P.geometry.chart)]
  change bidimensionOneChartFunctional S P.geometry.chart
    (localDdcTestCLM (TestFunction.monoCLM ℝ (scalarTest ψ))) = _
  rw [← localDdcTestCLM_mono P.geometry.domainInChart,
    D.current_one_local_full_test u hu hb P (localDdcTestCLM (scalarTest ψ))]
  exact fullTestFunctional_scalar_ddc _ ψ

/-- The actual smooth global derivative pairing is the sum of original
local derivatives tested against the partition weight times the scalar.
The partition is genuine, and every local/native identification is proved
inside the theorem. -/
theorem pairing_globalDdc_eq_sum_original_derivatives (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, Hermitian.IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (θ : ∀ i, 𝓓((D.patch i).geometry.domain, ℝ))
    (hθ : ∀ i z, θ i z = chartWeight (D.patch i).geometry.chart (D.weight i) z) :
    pairingLM (globalDdc (D.current u hu hb (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩))
      ((top_complement m).symm ▸ (smulFun f hf (unitForm : SmoothRealForm (m + 1) M 0))) =
      ∑ i, ddc ((D.patch i).bidimensionOneCurrent u) scalarUnit
        (mulSmoothOnCLM ((hf (D.patch i).geometry.chart).mono (D.patch i).geometry.domainInChart) (θ i)) := by
  classical
  let S := D.current u hu hb (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
  let β : SmoothRealForm (m + 1) M 0 := smulFun f hf unitForm
  let ψ (i : Fin D.count) :=
    mulSmoothOnCLM ((hf (D.patch i).geometry.chart).mono (D.patch i).geometry.domainInChart) (θ i)
  let τ (i : Fin D.count) : LocalCurrents.TestForm (chartTarget (D.patch i).geometry.chart) 0 :=
    TestFunction.monoCLM ℝ (scalarTest (ψ i))
  have hτ (i : Fin D.count) (z : ComplexModel (m + 1)) :
      τ i z = (D.patch i).geometry.chart.val.target.indicator
        (fun y => D.weight i ((D.patch i).geometry.chart.val.symm y) • β.coeff (D.patch i).geometry.chart y) z := by
    rw [show τ i z = scalarTest (ψ i) z from monoCLM_apply_of_le (D.patch i).geometry.domainInChart _ z]
    by_cases hz : z ∈ (D.patch i).geometry.chart.val.target
    · rw [indicator_of_mem hz]
      change ψ i z • coordinateWedgeUnit = _
      rw [show ψ i z = θ i z * f ((D.patch i).geometry.chart.val.symm z) from rfl,
        hθ i z, chartWeight, indicator_of_mem hz]
      simp only [β, smulFun_coeff, unitForm_coeff, smul_smul]
    · rw [indicator_of_notMem hz]
      change ψ i z • coordinateWedgeUnit = 0
      rw [show ψ i z = θ i z * f ((D.patch i).geometry.chart.val.symm z) from rfl,
        hθ i z, chartWeight, indicator_of_notMem hz, zero_mul, zero_smul]
  let η (i : Fin D.count) : LocalCurrents.TestForm (chartTarget (D.patch i).geometry.chart)
      (Module.finrank ℝ (ComplexModel (m + 1)) - (topDegree (m + 1)).val) :=
    (top_complement m).symm ▸ τ i
  have hη (i : Fin D.count) (z : ComplexModel (m + 1)) :
      η i z = (D.patch i).geometry.chart.val.target.indicator
        (fun y => D.weight i ((D.patch i).geometry.chart.val.symm y) •
          (((top_complement m).symm ▸ β : SmoothRealForm (m + 1) M _).coeff (D.patch i).geometry.chart y)) z := by
    dsimp only [η]
    rw [test_cast_apply, hτ i z]
    by_cases hz : z ∈ (D.patch i).geometry.chart.val.target
    · rw [indicator_of_mem hz, indicator_of_mem hz, form_cast_coeff, form_cast_smul]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, form_cast_zero]
  have hpair := pairing_eq_sum (globalDdc S) ((top_complement m).symm ▸ β) D.count
    (fun i => (D.patch i).geometry.chart) D.weight D.smooth
    (fun i => (isClosed_tsupport (D.weight i)).isCompact)
    (fun i x hx => (D.supported i hx).1) D.sum_one η hη
  rw [hpair]
  apply Finset.sum_congr rfl
  intro i _
  exact globalDdc_local_scalar_test D u hu hb (D.patch i) (ψ i)

/-- The same actual smooth global derivative pairing reads the localized
finite Hessian-density terms, with the native local current presentation
and every full compact test produced inside the proof. -/
theorem pairing_globalDdc_eq_sum_localized_derivatives (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, Hermitian.IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (θ η : ∀ i, 𝓓((D.patch i).geometry.domain, ℝ))
    (hθ : ∀ i z, θ i z = chartWeight (D.patch i).geometry.chart (D.weight i) z)
    (hη : ∀ i, ∀ᶠ z in 𝓝ˢ (tsupport (θ i)), η i z = 1) :
    pairingLM (globalDdc (D.current u hu hb (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩))
      ((top_complement m).symm ▸ (smulFun f hf (unitForm : SmoothRealForm (m + 1) M 0))) =
      ∑ i, localizedDerivativeWeight (patchResidual (D.patch i) u hu hb) (θ i) (η i)
        (fun z => f ((D.patch i).geometry.chart.val.symm z)) := by
  classical
  let S := D.current u hu hb (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
  choose α hα hread using fun i => localizedDerivativeWeight_smooth_eq_nativeFullTest
    (patchResidual (D.patch i) u hu hb) (θ i) (η i) (hη i)
    ((hf (D.patch i).geometry.chart).mono (D.patch i).geometry.domainInChart)
  obtain ⟨A, hA, hpair⟩ := HermitianGlobalDdcPartitionReadback.exists_partition_tests_pairing_globalDdc_scalar
    S f hf D.count (fun i => (D.patch i).geometry.chart) D.weight D.smooth
    (fun i => (isClosed_tsupport (D.weight i)).isCompact)
    (fun i x hx => (D.supported i hx).1) D.sum_one
  have hAeq (i : Fin D.count) : A i = TestFunction.monoCLM ℝ (α i) := by
    ext z
    rw [hA i z, monoCLM_apply_of_le (D.patch i).geometry.domainInChart (α i) z,
      hα i z, hθ i z, chartWeight]
    by_cases hz : z ∈ (D.patch i).geometry.chart.val.target <;> simp [hz]
  rw [hpair]
  apply Finset.sum_congr rfl
  intro i _
  rw [hAeq i, clm_cast_apply (bidimensionOne_complement m) (S.inChart (D.patch i).geometry.chart)
    (bidimensionOneChartFunctional S (D.patch i).geometry.chart)
    (bidimensionOneChartFunctional_actualChart S (D.patch i).geometry.chart).symm,
    D.current_one_local_full_test u hu hb (D.patch i) (α i)]
  have hr := hread i
  rw [mixedCurrent_patchResidual] at hr
  exact hr.symm

/-- All derivatives of the actual partition weights cancel in the smooth
one-factor right-hand side, before any torsion estimate is applied. -/
theorem smooth_partition_derivative_cancellation (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, Hermitian.IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (θ η : ∀ i, 𝓓((D.patch i).geometry.domain, ℝ))
    (hθ : ∀ i z, θ i z = chartWeight (D.patch i).geometry.chart (D.weight i) z)
    (hη : ∀ i, ∀ᶠ z in 𝓝ˢ (tsupport (θ i)), η i z = 1) :
    (∑ i, localizedDerivativeWeight (patchResidual (D.patch i) u hu hb) (θ i) (η i)
      (fun z => f ((D.patch i).geometry.chart.val.symm z))) =
      ∑ i, derivativeWeight (patchResidual (D.patch i) u hu hb) (θ i)
        (fun z => f ((D.patch i).geometry.chart.val.symm z)) := by
  have hleft := pairing_globalDdc_eq_sum_localized_derivatives D u hu hb f hf θ η hθ hη
  have hright := pairing_globalDdc_eq_sum_original_derivatives D u hu hb f hf θ hθ
  apply hleft.symm.trans
  apply hright.trans
  apply Finset.sum_congr rfl
  intro i _
  have h := derivativeWeight_smooth_eq_ddc (patchResidual (D.patch i) u hu hb) (θ i)
    ((hf (D.patch i).geometry.chart).mono (D.patch i).geometry.domainInChart)
  rw [mixedCurrent_patchResidual] at h
  exact h.symm

/-- The actual bounded positive difference of two original Hermitian
potentials retains the complete partition cancellation. Global smooth
bounded approximations and both genuine density limits are internal. -/
theorem bounded_partition_derivative_cancellation (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, Hermitian.IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {a b : M → EReal} (ha : Hermitian.IsHermitianPSH omega a) (hbb : Hermitian.IsHermitianPSH omega b)
    (hab : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal))
    (hbbound : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ b x ∧ b x ≤ (d : EReal))
    {δ : ℝ} (hδ : 0 ≤ δ) (hgap : ∀ x, max ((b x).toReal - (a x).toReal) 0 ≤ δ)
    (θ η : ∀ i, 𝓓((D.patch i).geometry.domain, ℝ))
    (hθ : ∀ i z, θ i z = chartWeight (D.patch i).geometry.chart (D.weight i) z)
    (hη : ∀ i, ∀ᶠ z in 𝓝ˢ (tsupport (θ i)), η i z = 1) :
    (∑ i, localizedDerivativeWeight (patchResidual (D.patch i) u hu hb) (θ i) (η i)
      (fun z => max ((b ((D.patch i).geometry.chart.val.symm z)).toReal -
        (a ((D.patch i).geometry.chart.val.symm z)).toReal) 0)) =
      ∑ i, derivativeWeight (patchResidual (D.patch i) u hu hb) (θ i)
        (fun z => max ((b ((D.patch i).geometry.chart.val.symm z)).toReal -
          (a ((D.patch i).geometry.chart.val.symm z)).toReal) 0) := by
  obtain ⟨f, hfs, hfb, hflim⟩ := HermitianComparisonGlobalSmoothing.exists_bounded_smooth_positive_difference
    omega ha hbb hab hbbound hδ hgap
  let w := fun x => max ((b x).toReal - (a x).toReal) 0
  have ht (i : Fin D.count) := global_scalar_weights_tendsto (D.patch i).geometry.chart
    (D.patch i).geometry.domainInChart (patchResidual (D.patch i) u hu hb) (θ i) (η i)
    f w hfs hflim hδ (fun j x => by rw [abs_of_nonneg (hfb j x).1]; exact (hfb j x).2)
  have hleft := tendsto_finsetSum Finset.univ (fun i _ => (ht i).1)
  have hright := tendsto_finsetSum Finset.univ (fun i _ => (ht i).2)
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro j
  exact (smooth_partition_derivative_cancellation D u hu hb (f j) (hfs j) θ η hθ hη).symm

end SGPT.PSH.HermitianComparisonGlobalOneFactor

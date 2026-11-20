import SGPT.PSH.HermitianComparisonCutoff
import SGPT.PSH.HermitianComparisonWeights
import SGPT.PSH.HermitianComparisonDensity
import SGPT.PSH.HermitianProducts

/-!
# Local one-factor integration by parts and its bounded limit

All products below are actual coefficient currents. The smooth residual
forms may be nonclosed. Positivity is used only for the complete mixed
current in the convex-chain inequality.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonOneFactor

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
  SGPT.Foundations.Analysis.Pending.LocalProductCurrents
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
  SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity
  SGPT.Foundations.Analysis.Pending.TopDegreeDensity
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
  SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
  SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
  SGPT.Foundations.Analysis.Pending.CompactDifferentialTests
open SGPT.PSH.HermitianComparisonCutoff SGPT.PSH.HermitianComparisonTranspose
  SGPT.PSH.HermitianComparisonConvexDDC SGPT.PSH.HermitianComparisonWeights
  SGPT.PSH.HermitianComparisonDensity SGPT.PSH.HermitianProductDifferential
  SGPT.PSH.HermitianProducts
open scoped Distributions ContDiff Topology

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Smooth scalar multiplication commutes with every smooth residual wedge,
including residual forms with signed or nonclosed coefficients. -/
theorem smoothMulCurrent_wedgeForm {r k m : ℕ} (h : r + k = m)
    (R : LocalProductCurrent n U m)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    smoothMulCurrent (wedgeForm h R hα) hf =
      wedgeForm h R (hf.smul hα) := by
  ext γ φ
  change wedgeForm h R hα γ (mulSmoothOnCLM hf φ) = _
  simp only [wedgeForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply TestFunction.ext
  intro z
  simp only [mulSmoothOnCLM_apply, formCoeff]
  change φ z * f z * (coeffCLM n k i) (α z) =
    φ z * (coeffCLM n k i) (f z • α z)
  rw [map_smul, smul_eq_mul]
  ring

theorem wedgeForm_smoothMulCurrent {r k m : ℕ} (h : r + k = m)
    (R : LocalProductCurrent n U m)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    wedgeForm h (smoothMulCurrent R hf) hα =
      smoothMulCurrent (wedgeForm h R hα) hf := by
  ext γ φ
  change wedgeForm h (smoothMulCurrent R hf) hα γ φ =
    wedgeForm h R hα γ (mulSmoothOnCLM hf φ)
  simp only [wedgeForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  change R _ (mulSmoothOnCLM hf (mulSmoothOnCLM _ φ)) = _
  congr 1
  apply TestFunction.ext
  intro z
  simp only [mulSmoothOnCLM_apply]
  ring

/-- Smooth residual wedges exchange with a smooth `(1,1)` factor on actual
currents; no positivity or closedness of either form is used. -/
theorem wedgeForm_exchange_one {k : ℕ} (R : LocalProductCurrent n U (k + 1))
    {α : ComplexModel n → RealForm n (2 * k)}
    {β : ComplexModel n → RealForm n 2}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    wedgeForm (r := 0) (k := 1) rfl
        (wedgeForm (by omega : 1 + k = k + 1) R hα) hβ =
      wedgeForm (r := 0) (k := k) (by omega : 0 + k = k)
        (wedgeForm (r := k) (k := 1) rfl R hβ) hα := by
  classical
  ext γ φ
  simp only [wedgeForm_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : wedgeSpan n (by omega : 1 + k = k + 1)
        (wedgeSpan n rfl γ (formBasis n 1 j)) (formBasis n k i) =
      wedgeSpan n rfl (wedgeSpan n (by omega : 0 + k = k) γ (formBasis n k i))
        (formBasis n 1 j) := by
    apply Subtype.ext
    rw [coe_wedgeSpan_apply _ _ _ (by omega : 2 * 1 + 2 * k = 2 * (k + 1)),
      coe_wedgeSpan_apply _ _ _ (by omega : 2 * 0 + 2 * 1 = 2 * 1),
      coe_wedgeSpan_apply _ _ _ (by omega : 2 * k + 2 * 1 = 2 * (k + 1)),
      coe_wedgeSpan_apply _ _ _ (by omega : 2 * 0 + 2 * k = 2 * k)]
    exact wedgeTo_wedgeTo_comm _ _ (formBasis n k i).property
      (by omega) (by omega) (by omega) (by omega)
  rw [he]
  congr 1
  apply TestFunction.ext
  intro z
  simp only [mulSmoothOnCLM_apply]
  ring

/-- Multiplication of the current and multiplication of its full compact
test give exactly the same pairing, without a positivity hypothesis. -/
theorem pairing_smoothMulCurrent (S : LocalProductCurrent n U 1)
    (χ : 𝓓(U, ℝ)) (α : 𝓓(U, RealForm n (2 * 1))) :
    pairing (smoothMulCurrent S χ.contDiff.contDiffOn) α =
      pairing S (smoothFormTest χ α α.contDiff) := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  change S (formBasis n 1 i) (mulSmoothOnCLM χ.contDiff.contDiffOn (coeffTest α i)) = _
  congr 1
  apply TestFunction.ext
  intro z
  simp only [mulSmoothOnCLM_apply, coeffTest, TestFunction.postcompCLM_apply,
    Function.comp_apply, smoothFormTest_apply, map_smul, smul_eq_mul]
  ring

/-- The scalar pairing of a genuine smooth `(1,1)` wedge is exactly the
full compact two-form pairing. -/
theorem wedgeForm_scalarUnit (S : LocalProductCurrent n U 1)
    {β : ComplexModel n → RealForm n 2} (hβ : ContDiff ℝ ∞ β)
    (χ : 𝓓(U, ℝ)) :
    wedgeForm (r := 0) (k := 1) rfl S hβ.contDiffOn scalarUnit χ =
      pairing S (smoothFormTest χ β hβ) := by
  rw [wedgeForm_apply]
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  have he : wedgeSpan n rfl scalarUnit (formBasis n 1 i) = formBasis n 1 i := by
    apply Subtype.ext
    rw [coe_wedgeSpan_apply _ _ _ (by omega : 2 * 0 + 2 * 1 = 2 * 1),
      scalarUnit, wedgeTo_unit_left _ rfl]
    rfl
  rw [he]
  congr 1
  apply TestFunction.ext
  intro z
  simp only [mulSmoothOnCLM_apply, coeffTest, TestFunction.postcompCLM_apply,
    Function.comp_apply, smoothFormTest_apply, formCoeff, map_smul, smul_eq_mul]


/-- The full compact differential of a scalar test is its literal `ddᶜ`. -/
theorem ddcFullTest_scalarTest_apply (ψ : 𝓓(U, ℝ)) (z : ComplexModel n) :
    ddcFullTest (scalarTest ψ) z = smoothDDC ψ z := by
  change localDdcTestCLM (scalarTest ψ) z = _
  have h := localDdcTestCLM_constForm_apply ψ (scalarUnit (n := n)) z
  change localDdcTestCLM (scalarTest ψ) z = _ at h
  rw [h, scalarUnit, wedgeTo_unit_right _ rfl]
  rfl

/-- A second cutoff equal to one near the first support removes its
derivatives from the localized full compact test. -/
theorem localized_compositeTest_eq (χ η : 𝓓(U, ℝ))
    (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    {F : ℝ → ℝ} {w : ComplexModel n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) :
    smoothFormTest χ
        (ddcFullTest (scalarTest (cutoffScalarTest η F w hF hw)))
        (ddcFullTest (scalarTest (cutoffScalarTest η F w hF hw))).contDiff =
      compositeTest χ F w hF hw := by
  apply TestFunction.ext
  intro z
  simp only [smoothFormTest_apply, compositeTest]
  by_cases hz : z ∈ tsupport χ
  · rw [ddcFullTest_scalarTest_apply]
    congr 1
    apply smoothDDC_congr
    filter_upwards [hη.filter_mono (nhds_le_nhdsSet hz)] with y hy
    simp only [cutoffScalarTest, mulTest_apply, hy, one_mul, Function.comp_apply]
  · have hχz := image_eq_zero_of_notMem_tsupport hz
    simp only [hχz, zero_smul]

/-- The smooth local one-factor inequality with all localization terms
retained inside the actual derivative of `χ S`. Neither `S` nor the
background forms are required to be closed. -/
theorem smooth_local_onefactor
    (S : LocalProductCurrent n U 1) (hS : IsPositive S)
    (χ : 𝓓(U, ℝ)) (hχ : ∀ z, 0 ≤ χ z) (η : 𝓓(U, ℝ))
    (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    {F : ℝ → ℝ} {w : ComplexModel n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w)
    (hF₂ : ∀ z, 0 ≤ deriv (deriv F) (w z)) :
    pairing S (firstDerivativeTest χ F w hF hw) ≤
      ddc (smoothMulCurrent S χ.contDiff.contDiffOn) scalarUnit
        (cutoffScalarTest η F w hF hw) := by
  have hp : 0 ≤ pairing S
      (compositeTest χ F w hF hw - firstDerivativeTest χ F w hF hw) := by
    rw [composite_sub_first_eq_defect]
    exact convex_defect_pairing_nonnegative S hS χ hχ hF hw hF₂
  rw [pairing_sub] at hp
  have ht := pairing_ddc_scalarTest (smoothMulCurrent S χ.contDiff.contDiffOn)
    (cutoffScalarTest η F w hF hw)
  rw [pairing_scalarTest, pairing_smoothMulCurrent,
    localized_compositeTest_eq χ η hη hF hw] at ht
  linarith

/-- A signed smooth weight on one actual positive Bedford--Taylor factor,
followed by the arbitrary smooth residual wedge. Multiplication occurs
before the signed residual wedge, where the coefficient measure is genuine. -/
def weightedDdcResidual {k : ℕ} (R : LocalProductCurrent n U (k + 1))
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (u a b : ComplexModel n → ℝ) (H : ℝ → ℝ) : LocalProductCurrent n U 0 :=
  wedgeForm (by omega : 0 + k = k)
    (mulBorel (ddcMul R u) ((U : Set (ComplexModel n)).indicator
      (fun z => H (b z - a z)))) hα

/-- At smooth distinguished potentials the bounded-weight expression is
the literal smooth wedge against the original residual mixed current. -/
theorem weightedDdcResidual_smooth_eq {k : ℕ}
    (R : LocalProductCurrent n U (k + 1)) (hR : IsPositive R)
    (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    {u a b : ComplexModel n → ℝ} {H : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hup : IsLocallyBoundedPshOn U u)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hH : ContDiff ℝ ∞ H) :
    weightedDdcResidual R hα u a b H =
      wedgeForm rfl (wedgeForm (by omega : 1 + k = k + 1) R hα)
        ((hH.contDiffOn.comp (hb.sub ha) (fun _ _ => mem_univ _)).smul
          (contDiffOn_ddcForm hu)) := by
  have hweight : ContDiffOn ℝ ∞ (fun z => H (b z - a z)) U :=
    hH.comp_contDiffOn (hb.sub ha)
  unfold weightedDdcResidual
  rw [← smoothMulCurrent_eq_mulBorel_indicator (isPositive_ddcMul hR hRc hup).1 hweight,
    wedgeForm_smoothMulCurrent, ddcMul_eq_ddcWedge hR hRc hu,
    ddcWedge_eq_wedgeForm, ← wedgeForm_exchange_one R hα (contDiffOn_ddcForm hu),
    smoothMulCurrent_wedgeForm]

/-- At smooth distinguished potentials, the difference of the two weighted
Bedford--Taylor factors is the first-derivative term in convex integration
by parts, paired with the original mixed residual current. -/
theorem weightedDdcResidual_difference_smooth_pairing {k : ℕ}
    (R : LocalProductCurrent n U (k + 1)) (hR : IsPositive R)
    (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    {a b : ComplexModel n → ℝ} {F : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hF : ContDiff ℝ ∞ F)
    (hap : IsLocallyBoundedPshOn U a) (hbp : IsLocallyBoundedPshOn U b)
    (χ : 𝓓(U, ℝ)) :
    weightedDdcResidual R hα b a b (deriv F) scalarUnit χ -
        weightedDdcResidual R hα a a b (deriv F) scalarUnit χ =
      pairing (wedgeForm (by omega : 1 + k = k + 1) R hα)
        (firstDerivativeTest χ F (fun z => b z - a z) hF (hb.sub ha)) := by
  have hH : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  let S := wedgeForm (by omega : 1 + k = k + 1) R hα
  let βb : ComplexModel n → RealForm n 2 := fun z => deriv F (b z - a z) • smoothDDC b z
  let βa : ComplexModel n → RealForm n 2 := fun z => deriv F (b z - a z) • smoothDDC a z
  have hβb : ContDiff ℝ ∞ βb := (hH.comp (hb.sub ha)).smul (contDiff_smoothDDC hb)
  have hβa : ContDiff ℝ ∞ βa := (hH.comp (hb.sub ha)).smul (contDiff_smoothDDC ha)
  rw [weightedDdcResidual_smooth_eq R hR hRc hα hb.contDiffOn hbp
      ha.contDiffOn hb.contDiffOn hH,
    weightedDdcResidual_smooth_eq R hR hRc hα ha.contDiffOn hap
      ha.contDiffOn hb.contDiffOn hH]
  change wedgeForm (r := 0) (k := 1) rfl S hβb.contDiffOn scalarUnit χ -
      wedgeForm (r := 0) (k := 1) rfl S hβa.contDiffOn scalarUnit χ = _
  rw [wedgeForm_scalarUnit S hβb, wedgeForm_scalarUnit S hβa, ← pairing_sub]
  congr 1
  apply TestFunction.ext
  intro z
  simp only [sub_apply, smoothFormTest_apply, firstDerivativeTest, βb, βa]
  have hsub : smoothDDC (fun z => b z - a z) z = smoothDDC b z - smoothDDC a z := by
    simp only [sub_eq_add_neg]
    rw [smoothDDC_add isOpen_univ hb.contDiffOn ha.neg.contDiffOn (mem_univ z),
      smoothDDC_neg isOpen_univ ha.contDiffOn (mem_univ z)]
  rw [hsub, smul_sub, smul_sub]

/-- The distinguished factor passes to the bounded decreasing limit while
all other mixed-current factors stay fixed. The proof produces weighted
Bedford--Taylor convergence and then wedges the actual smooth residual. -/
theorem weightedDdcResidual_decreasing {k : ℕ}
    (R : LocalProductCurrent n U (k + 1)) (hR : IsPositive R)
    (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (u a b : ℕ → ComplexModel n → ℝ) (u₀ a₀ b₀ : ComplexModel n → ℝ)
    (hu : ∀ j, IsLocallyBoundedPshOn U (u j)) (hu₀ : IsLocallyBoundedPshOn U u₀)
    (has : ∀ j, ContDiffOn ℝ ∞ (a j) U) (hbs : ∀ j, ContDiffOn ℝ ∞ (b j) U)
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (hanti_u : ∀ z ∈ U, Antitone fun j => u j z)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_u : ∀ z ∈ U, Tendsto (fun j => u j z) atTop (𝓝 (u₀ z)))
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {M : ℝ}
    (hbound_a : ∀ j z, z ∈ U → |a j z| ≤ M)
    (hbound_b : ∀ j z, z ∈ U → |b j z| ≤ M) :
    WeakTendsto (fun j => weightedDdcResidual R hα (u j) (a j) (b j) H)
      (weightedDdcResidual R hα u₀ a₀ b₀ H) := by
  apply SGPT.PSH.HermitianProducts.weakTendsto_wedgeForm
  exact weakTendsto_smooth_difference_weight 1 k R hR hRc
    (fun j _ => u j) (fun _ => u₀) (fun j _ => hu j) (fun _ => hu₀)
    (fun _ z hz => hanti_u z hz) (fun _ z hz => hlim_u z hz)
    a b a₀ b₀ has hbs hap hbp hanti_a hanti_b hlim_a hlim_b hH hbound_a hbound_b

/-- The localized derivative is the actual finite Hessian-density extension
at smooth weights, including all derivatives of the first cutoff. -/
theorem localized_derivative_smooth_eq {k : ℕ}
    (R : LocalProductCurrent n U (k + 1)) (hR : IsPositive R)
    (hRc : IsClosedCurrent R)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U)
    (χ η : 𝓓(U, ℝ)) {F : ℝ → ℝ} {w : ComplexModel n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w) :
    ddc (smoothMulCurrent (wedgeForm (by omega : 1 + k = k + 1) R hα)
        χ.contDiff.contDiffOn) scalarUnit (cutoffScalarTest η F w hF hw) =
      ddcWedgePairing (by omega : 0 + k = k) hR (fun z => χ z • α z)
        scalarUnit η (fun z => F (w z)) := by
  rw [smoothMulCurrent_wedgeForm]
  have he : cutoffScalarTest η F w hF hw =
      mulSmoothOnCLM (hF.comp hw).contDiffOn η := by
    apply TestFunction.ext
    intro z
    simp only [cutoffScalarTest, mulTest_apply, Function.comp_apply, mulSmoothOnCLM_apply]
  rw [he]
  exact ddc_wedgeForm_smooth_weight_eq (by omega) (by omega) hR hRc
    (χ.contDiff.contDiffOn.smul hα) scalarUnit η (hF.comp hw).contDiffOn

theorem pairing_sum {ι : Type*} [Fintype ι]
    (S : ι → LocalProductCurrent n U 1) (β : 𝓓(U, RealForm n 2)) :
    pairing (∑ i, S i) β = ∑ i, pairing (S i) β := by
  simp only [pairing, LinearMap.sum_apply, _root_.sum_apply]
  exact Finset.sum_comm

theorem smoothMulCurrent_sum {ι : Type*} [Fintype ι] {m : ℕ}
    (S : ι → LocalProductCurrent n U m)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    smoothMulCurrent (∑ i, S i) hf = ∑ i, smoothMulCurrent (S i) hf := by
  ext γ φ
  change (∑ i, S i) γ (mulSmoothOnCLM hf φ) = _
  simp only [LinearMap.sum_apply, _root_.sum_apply]
  rfl

theorem ddc_sum {ι : Type*} [Fintype ι]
    (S : ι → LocalProductCurrent n U 1) : ddc (∑ i, S i) = ∑ i, ddc (S i) := by
  exact map_sum (ddcLinearMap (m := 0)) S Finset.univ

/-- One genuine local term of a Hermitian mixed product: a closed positive
Bedford--Taylor factor and an arbitrary smooth residual form. This stores
only the native analytical objects, with no comparison conclusion. -/
structure Residual (n : ℕ) (U : Opens (ComplexModel n)) where
  degree : ℕ
  current : LocalProductCurrent n U (degree + 1)
  positive : IsPositive current
  closed : IsClosedCurrent current
  form : ComplexModel n → RealForm n (2 * degree)
  smooth : ContDiffOn ℝ ∞ form U

def Residual.mixed (D : Residual n U) : LocalProductCurrent n U 1 :=
  wedgeForm (by omega : 1 + D.degree = D.degree + 1) D.current D.smooth

def mixedCurrent {ι : Type*} [Fintype ι] (D : ι → Residual n U) :
    LocalProductCurrent n U 1 := ∑ i, (D i).mixed

/-- The actual signed weighted distinguished factor in the finite local
expansion. The common local correction cancels in `b-a`. -/
def weightedDifference {ι : Type*} [Fintype ι] (D : ι → Residual n U)
    (a b : ComplexModel n → ℝ) (H : ℝ → ℝ) : LocalProductCurrent n U 0 :=
  ∑ i, (weightedDdcResidual (D i).current (D i).smooth b a b H -
    weightedDdcResidual (D i).current (D i).smooth a a b H)

/-- The explicit bounded-weight extension of `ddᶜ(χ S)`. Every coefficient
is the actual Hessian of the smooth residual `χ α`, integrated against the
native trace measure of its closed positive factor. -/
def localizedDerivativeWeight {ι : Type*} [Fintype ι] (D : ι → Residual n U)
    (χ η : 𝓓(U, ℝ)) (f : ComplexModel n → ℝ) : ℝ :=
  ∑ i, ddcWedgePairing (by omega : 0 + (D i).degree = (D i).degree)
    (D i).positive (fun z => χ z • (D i).form z) scalarUnit η f

theorem smooth_onefactor_residuals {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (hS : IsPositive (mixedCurrent D))
    (χ : 𝓓(U, ℝ)) (hχ : ∀ z, 0 ≤ χ z) (η : 𝓓(U, ℝ))
    (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    {F : ℝ → ℝ} {a b : ComplexModel n → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hap : IsLocallyBoundedPshOn U a) (hbp : IsLocallyBoundedPshOn U b)
    (hF₂ : ∀ t, 0 ≤ deriv (deriv F) t) :
    weightedDifference D a b (deriv F) scalarUnit χ ≤
      localizedDerivativeWeight D χ η (fun z => F (b z - a z)) := by
  have h := smooth_local_onefactor (mixedCurrent D) hS χ hχ η hη hF (hb.sub ha)
    (fun z => hF₂ _)
  have hleft : weightedDifference D a b (deriv F) scalarUnit χ =
      pairing (mixedCurrent D) (firstDerivativeTest χ F (fun z => b z - a z) hF (hb.sub ha)) := by
    simp only [weightedDifference, LinearMap.sum_apply, _root_.sum_apply,
      LinearMap.sub_apply, _root_.sub_apply]
    rw [mixedCurrent, pairing_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact weightedDdcResidual_difference_smooth_pairing (D i).current (D i).positive
      (D i).closed (D i).smooth ha hb hF hap hbp χ
  have hright : ddc (smoothMulCurrent (mixedCurrent D) χ.contDiff.contDiffOn)
      scalarUnit (cutoffScalarTest η F (fun z => b z - a z) hF (hb.sub ha)) =
      localizedDerivativeWeight D χ η (fun z => F (b z - a z)) := by
    rw [mixedCurrent, smoothMulCurrent_sum, ddc_sum]
    simp only [LinearMap.sum_apply, _root_.sum_apply, localizedDerivativeWeight]
    apply Finset.sum_congr rfl
    intro i _
    exact localized_derivative_smooth_eq (D i).current (D i).positive (D i).closed
      (D i).smooth χ η hF (hb.sub ha)
  rw [← hleft, hright] at h
  exact h

theorem weightedDifference_decreasing {ι : Type*} [Fintype ι]
    (D : ι → Residual n U)
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (has : ∀ j, ContDiff ℝ ∞ (a j)) (hbs : ∀ j, ContDiff ℝ ∞ (b j))
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (ha₀ : IsLocallyBoundedPshOn U a₀) (hb₀ : IsLocallyBoundedPshOn U b₀)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {M : ℝ}
    (hbound_a : ∀ j z, z ∈ U → |a j z| ≤ M)
    (hbound_b : ∀ j z, z ∈ U → |b j z| ≤ M) :
    WeakTendsto (fun j => weightedDifference D (a j) (b j) H)
      (weightedDifference D a₀ b₀ H) := by
  have ha : ∀ j, IsLocallyBoundedPshOn U (a j) := fun j =>
    locallyBoundedPshOn_of_smooth (has j).contDiffOn (hap j)
  have hb : ∀ j, IsLocallyBoundedPshOn U (b j) := fun j =>
    locallyBoundedPshOn_of_smooth (hbs j).contDiffOn (hbp j)
  intro γ φ
  simp only [weightedDifference, LinearMap.sum_apply, _root_.sum_apply,
    LinearMap.sub_apply, _root_.sub_apply]
  apply tendsto_finsetSum
  intro i _
  have hleft := weightedDdcResidual_decreasing (D i).current (D i).positive
    (D i).closed (D i).smooth b a b b₀ a₀ b₀ hb hb₀
    (fun j => (has j).contDiffOn) (fun j => (hbs j).contDiffOn) hap hbp
    hanti_b hanti_a hanti_b hlim_b hlim_a hlim_b hH hbound_a hbound_b
  have hright := weightedDdcResidual_decreasing (D i).current (D i).positive
    (D i).closed (D i).smooth a a b a₀ a₀ b₀ ha ha₀
    (fun j => (has j).contDiffOn) (fun j => (hbs j).contDiffOn) hap hbp
    hanti_a hanti_a hanti_b hlim_a hlim_a hlim_b hH hbound_a hbound_b
  exact (hleft γ φ).sub (hright γ φ)

theorem localizedDerivativeWeight_tendsto {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (χ η : 𝓓(U, ℝ))
    {f : ℕ → ComplexModel n → ℝ} {f₀ : ComplexModel n → ℝ}
    (hf : ∀ j, Measurable (f j))
    (hlim : ∀ x ∈ U, Tendsto (fun j => f j x) atTop (𝓝 (f₀ x)))
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ j x, x ∈ tsupport η → |f j x| ≤ M) :
    Tendsto (fun j => localizedDerivativeWeight D χ η (f j)) atTop
      (𝓝 (localizedDerivativeWeight D χ η f₀)) := by
  unfold localizedDerivativeWeight
  apply tendsto_finsetSum
  intro i _
  exact ddcWedgePairing_tendsto (by omega) (D i).positive
    (χ.contDiff.contDiffOn.smul (D i).smooth) scalarUnit η hf hlim hbound

/-- Bounded one-factor integration by parts for an actual finite local
Bedford--Taylor/smooth-form expansion. Only the complete mixed current is
assumed positive. Neither its residual forms nor the Hermitian background
are assumed closed. Both weighted limits are produced inside this proof. -/
theorem bounded_local_onefactor {ι : Type*} [Fintype ι]
    (D : ι → Residual n U) (hS : IsPositive (mixedCurrent D))
    (χ : 𝓓(U, ℝ)) (hχ : ∀ z, 0 ≤ χ z) (η : 𝓓(U, ℝ))
    (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (has : ∀ j, ContDiff ℝ ∞ (a j)) (hbs : ∀ j, ContDiff ℝ ∞ (b j))
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (ha₀ : IsLocallyBoundedPshOn U a₀) (hb₀ : IsLocallyBoundedPshOn U b₀)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF₂ : ∀ t, 0 ≤ deriv (deriv F) t)
    {M : ℝ} (hbound_a : ∀ j z, z ∈ U → |a j z| ≤ M)
    (hbound_b : ∀ j z, z ∈ U → |b j z| ≤ M) :
    weightedDifference D a₀ b₀ (deriv F) scalarUnit χ ≤
      localizedDerivativeWeight D χ η (fun z => F (b₀ z - a₀ z)) := by
  have hH : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  have hleft := weightedDifference_decreasing D a b a₀ b₀ has hbs hap hbp ha₀ hb₀
    hanti_a hanti_b hlim_a hlim_b hH hbound_a hbound_b scalarUnit χ
  obtain ⟨C, A, B, hC, hA, hF₀, hF₁, hF₂b⟩ := exists_smooth_weight_bounds hF (2 * M)
  have hbound : ∃ B' : ℝ, 0 ≤ B' ∧ ∀ j x, x ∈ tsupport η →
      |F (b j x - a j x)| ≤ B' := by
    refine ⟨|B|, abs_nonneg B, fun j x hx => ?_⟩
    have hxU := η.tsupport_subset hx
    have hsub := abs_sub_le (b j x) 0 (a j x)
    simp only [sub_zero, zero_sub, abs_neg] at hsub
    have hba : |b j x - a j x| ≤ 2 * M := by
      linarith [hbound_a j x hxU, hbound_b j x hxU]
    exact (hF₀ _ (abs_le.mp hba)).trans (le_abs_self B)
  have hright := localizedDerivativeWeight_tendsto D χ η
    (fun j => (hF.comp ((hbs j).sub (has j))).continuous.measurable)
    (fun x hx => hF.continuous.continuousAt.tendsto.comp
      ((hlim_b x hx).sub (hlim_a x hx))) hbound
  exact le_of_tendsto_of_tendsto' hleft hright (fun j =>
    smooth_onefactor_residuals D hS χ hχ η hη hF (has j) (hbs j)
      (locallyBoundedPshOn_of_smooth (has j).contDiffOn (hap j))
      (locallyBoundedPshOn_of_smooth (hbs j).contDiffOn (hbp j)) hF₂)

theorem wedgeForm_castLPC {a b r k : ℕ} (hab : a = b) (h : r + k = a)
    (R : LocalProductCurrent n U a)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm (h.trans hab) (castLPC hab R) hα = wedgeForm h R hα := by
  subst hab
  rfl

/-- The actual subset terms of `backgroundExpansion` supply the finite
residual presentation required by bounded one-factor integration by parts. -/
def backgroundResidual (p : ℕ) (T : LocalProductCurrent n U (1 + p))
    (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) : Residual n U := by
  classical
  have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
  let d := p - s.card
  have hbase : 1 + p = 1 + d + s.card := by dsimp [d]; omega
  let T' := castLPC hbase T
  let u : Fin s.card → ComplexModel n → ℝ := fun i => v (s.orderEmbOfFin rfl i)
  let R := btProduct s.card (1 + d) u T'
  have hR := isPositive_btProduct s.card (1 + d) u T'
    (isPositive_castLPC hbase hT) (isClosedAny_castLPC hbase hTc) (fun i => hv _)
  have hcast : 1 + d = d + 1 := by omega
  exact {
    degree := d
    current := castLPC hcast R
    positive := isPositive_castLPC hcast hR.1
    closed := isClosedAny_castLPC hcast hR.2
    form := fun z => wedgeProd d (fun _ => σ z)
    smooth := contDiffOn_wedgeProd d (fun _ => σ) (fun _ => hσ) }

theorem backgroundResidual_mixed (p : ℕ) (T : LocalProductCurrent n U (1 + p))
    (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    (backgroundResidual p T hT hTc v hv hσ s).mixed =
      SGPT.PSH.HermitianProducts.backgroundExpansionTerm p 1 v hσ T s := by
  classical
  unfold backgroundResidual Residual.mixed SGPT.PSH.HermitianProducts.backgroundExpansionTerm
  exact wedgeForm_castLPC (by omega : 1 + (p - s.card) = p - s.card + 1) rfl _ _

theorem mixedCurrent_backgroundResidual (p : ℕ) (T : LocalProductCurrent n U (1 + p))
    (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    mixedCurrent (backgroundResidual p T hT hTc v hv hσ) =
      SGPT.PSH.HermitianProducts.backgroundExpansion p 1 v hσ T := by
  classical
  exact Finset.sum_congr rfl (fun s _ => backgroundResidual_mixed p T hT hTc v hv hσ s)

/-- Bounded one-factor integration by parts instantiated with the actual
nonclosed-background expansion. Positivity of that complete product is the
only product-positivity hypothesis; individual residual forms can be signed. -/
theorem bounded_background_onefactor (p : ℕ) (T : LocalProductCurrent n U (1 + p))
    (hT : IsPositive T) (hTc : IsClosedAny (1 + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hS : IsPositive (SGPT.PSH.HermitianProducts.backgroundExpansion p 1 v hσ T))
    (χ : 𝓓(U, ℝ)) (hχ : ∀ z, 0 ≤ χ z) (η : 𝓓(U, ℝ))
    (hη : ∀ᶠ z in 𝓝ˢ (tsupport χ), η z = 1)
    (a b : ℕ → ComplexModel n → ℝ) (a₀ b₀ : ComplexModel n → ℝ)
    (has : ∀ j, ContDiff ℝ ∞ (a j)) (hbs : ∀ j, ContDiff ℝ ∞ (b j))
    (hap : ∀ j, PlurisubharmonicOn (fun z => (a j z : EReal)) U)
    (hbp : ∀ j, PlurisubharmonicOn (fun z => (b j z : EReal)) U)
    (ha₀ : IsLocallyBoundedPshOn U a₀) (hb₀ : IsLocallyBoundedPshOn U b₀)
    (hanti_a : ∀ z ∈ U, Antitone fun j => a j z)
    (hanti_b : ∀ z ∈ U, Antitone fun j => b j z)
    (hlim_a : ∀ z ∈ U, Tendsto (fun j => a j z) atTop (𝓝 (a₀ z)))
    (hlim_b : ∀ z ∈ U, Tendsto (fun j => b j z) atTop (𝓝 (b₀ z)))
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF₂ : ∀ t, 0 ≤ deriv (deriv F) t)
    {M : ℝ} (hbound_a : ∀ j z, z ∈ U → |a j z| ≤ M)
    (hbound_b : ∀ j z, z ∈ U → |b j z| ≤ M) :
    weightedDifference (backgroundResidual p T hT hTc v hv hσ) a₀ b₀ (deriv F) scalarUnit χ ≤
      localizedDerivativeWeight (backgroundResidual p T hT hTc v hv hσ) χ η
        (fun z => F (b₀ z - a₀ z)) := by
  classical
  apply bounded_local_onefactor _ _ χ hχ η hη a b a₀ b₀ has hbs hap hbp ha₀ hb₀
    hanti_a hanti_b hlim_a hlim_b hF hF₂ hbound_a hbound_b
  rw [mixedCurrent_backgroundResidual]
  exact hS

end SGPT.PSH.HermitianComparisonOneFactor

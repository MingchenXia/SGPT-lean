import SGPT.Foundations.Analysis.Pending.NaturalThetaPshSourceCurrent
import SGPT.Foundations.Analysis.Pending.FullLocalSmoothCurrentDensity
import SGPT.Foundations.Analysis.FirstPass.SmoothOffPole

set_option autoImplicit false

/-! # Actual complementary coefficient readings and nonpolar current densities

Boucksom 2.5, a genuine local precursor.  The actual global potential
current supplies positivity and off-pole smooth test integrals; trace
measure uniqueness supplies local absolute continuity internally.
Codimension-two mass nullity and the divisorial/Siu whole theorem are
separate obligations.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticCurrentLocalDensity

open FirstPass FirstPass.MongeAmpere FirstPass.AdmissibleCurrentFormPositivity
  _root_.SGPT.Foundations.Analysis.LocalCurrents GlobalCurrents CanonicalCurrentFrame
  CanonicalComplementaryCurrentTests CanonicalSmoothCurrentDensity
  NaturalThetaPshGeometricCurrent NaturalThetaPshSourceCurrent
  StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentPullbackDdc LocalBedfordTaylorProducts LocalBedfordTaylorLocality
  LocalBedfordTaylorSmooth FullLocalSmoothCurrentDensity ScalarFullTestTranspose
  CompactVariableCurrentTests TopDegreeDensity ConstantFormProducts LocalBedfordTaylorCollar
  GlobalCurrentPotentials NumericalRestrictedVolume NumericalRestrictedVolumeScaffold

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private def castDegreeCLM {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b) :
    TestForm U a →L[ℝ] TestForm U b := h ▸ ContinuousLinearMap.id ℝ (TestForm U a)

private theorem castDegreeCLM_apply {n a b : ℕ} {U : Opens (ComplexModel n)}
    (h : a = b) (α : TestForm U a) : castDegreeCLM h α = castTestDegree h α := by
  subst b
  rfl

private def tensorTestCLM {U : Opens (ComplexModel (m + 1))}
    (γ : RealForm (m + 1) (2 * m)) : 𝓓(U, ℝ) →L[ℝ] TestForm U (2 * m) :=
  TestFunction.postcompCLM ((ContinuousLinearMap.id ℝ ℝ).smulRight γ)

private theorem tensorTestCLM_apply {U : Opens (ComplexModel (m + 1))}
    (γ : RealForm (m + 1) (2 * m)) (φ : 𝓓(U, ℝ)) (x : ComplexModel (m + 1)) :
    tensorTestCLM γ φ x = φ x • γ := rfl

/-- Literal constant complementary-form readings of an actual geometric current. -/
def chartSpanCurrent (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) : LocalProductCurrent (m + 1) (chartTarget e) m where
  toFun γ := (T.inChart e).comp ((castDegreeCLM
    (by rw [complexModel_real_finrank]; omega :
      2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2)).comp
        (tensorTestCLM (γ : RealForm (m + 1) (2 * m))))
  map_add' γ δ := by
    ext φ
    have h : tensorTestCLM ((γ + δ : formSpan (m + 1) m) : RealForm (m + 1) (2 * m)) φ =
        tensorTestCLM (γ : RealForm (m + 1) (2 * m)) φ +
          tensorTestCLM (δ : RealForm (m + 1) (2 * m)) φ := by
      apply DFunLike.ext
      intro x
      change φ x • ((γ : RealForm (m + 1) (2 * m)) + δ) =
        φ x • (γ : RealForm (m + 1) (2 * m)) + φ x • (δ : RealForm (m + 1) (2 * m))
      exact smul_add _ _ _
    change (T.inChart e) (castDegreeCLM _ (tensorTestCLM ↑(γ + δ) φ)) =
      (T.inChart e) (castDegreeCLM _ (tensorTestCLM ↑γ φ)) +
        (T.inChart e) (castDegreeCLM _ (tensorTestCLM ↑δ φ))
    rw [h, map_add, map_add]
  map_smul' c γ := by
    ext φ
    have h : tensorTestCLM ((c • γ : formSpan (m + 1) m) : RealForm (m + 1) (2 * m)) φ =
        c • tensorTestCLM (γ : RealForm (m + 1) (2 * m)) φ := by
      apply DFunLike.ext
      intro x
      change φ x • (c • (γ : RealForm (m + 1) (2 * m))) =
        c • (φ x • (γ : RealForm (m + 1) (2 * m)))
      exact smul_comm _ _ _
    change (T.inChart e) (castDegreeCLM _ (tensorTestCLM ↑(c • γ) φ)) =
      c • (T.inChart e) (castDegreeCLM _ (tensorTestCLM ↑γ φ))
    rw [h, map_smul, map_smul]

/-- Full variable-test positivity of the actual potential current supplies its coefficient positivity. -/
theorem isPositive_chartSpanCurrent (θ : SmoothRealForm (m + 1) M 2)
    (u : M → EReal) (hu : IsThetaPshPotential θ u) (e : ComplexChart (m + 1) M) :
    IsPositive (chartSpanCurrent (thetaPotentialCurrent θ u hu) e) := by
  intro ι _ γ φ hγφ
  let α : TestForm (chartTarget e) (2 * m) :=
    ∑ i, tensorTestCLM (γ i : RealForm (m + 1) (2 * m)) (φ i)
  have hα : ∀ x, α x ∈ spCone m := by
    intro x
    simpa only [α, _root_.sum_apply, tensorTestCLM_apply] using hγφ x
  have hp := thetaPotentialCurrent_full_positive θ u hu e α hα
  rw [← castDegreeCLM_apply] at hp
  change 0 ≤ ∑ i, (thetaPotentialCurrent θ u hu).inChart e
    (castDegreeCLM _ (tensorTestCLM (γ i : RealForm (m + 1) (2 * m)) (φ i)))
  simpa only [α, map_sum] using hp

private theorem castTestDegree_mono {n a b : ℕ} {U V : Opens (ComplexModel n)}
    (h : a = b) (_hUV : U ≤ V) (α : TestForm U a) :
    castTestDegree h (TestFunction.monoCLM ℝ α : TestForm V a) =
      (TestFunction.monoCLM ℝ (castTestDegree h α) : TestForm V b) := by
  subst b
  rfl

private theorem restrict_chartSpanCurrent
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) (γ : formSpan (m + 1) m) (φ : 𝓓(W, ℝ)) :
    restrict hW (chartSpanCurrent T e) γ φ = T.restrictChart e hW
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) (tensorTestCLM ↑γ φ)) := by
  have h : tensorTestCLM (γ : RealForm (m + 1) (2 * m)) (extTest hW φ) =
      (TestFunction.monoCLM ℝ (tensorTestCLM ↑γ φ) : TestForm (chartTarget e) (2 * m)) := by
    apply DFunLike.ext
    intro x
    rw [tensorTestCLM_apply, extTest_apply, testForm_inclusion_apply hW,
      tensorTestCLM_apply]
  change (T.inChart e) (castDegreeCLM _ (tensorTestCLM ↑γ (extTest hW φ))) =
    (T.inChart e) (TestFunction.monoCLM ℝ (castTestDegree _ (tensorTestCLM ↑γ φ)))
  rw [castDegreeCLM_apply, h, castTestDegree_mono _ hW]

private theorem integrable_test_mul_continuousOn
    {W : Opens (ComplexModel (m + 1))} (φ : 𝓓(W, ℝ))
    {f : ComplexModel (m + 1) → ℝ} (hf : ContinuousOn f W) :
    Integrable (fun x => φ x * f x) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left _ _).trans (subset_tsupport φ))).mp
  exact (φ.continuous.continuousOn.mul (hf.mono φ.tsupport_subset)).integrableOn_compact
    φ.hasCompactSupport

private theorem smooth_pairing
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal) (hu : IsThetaPshPotential θ u)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) (g : ComplexModel (m + 1) → ℝ)
    (hg : ContDiffOn ℝ ∞ g W) (heq : ∀ x ∈ W, chartFunction u e x = (g x : EReal))
    (γ : formSpan (m + 1) m) (φ : 𝓓(W, ℝ)) :
    restrict hW (chartSpanCurrent (thetaPotentialCurrent θ u hu) e) γ φ =
      ∫ x, φ x * formDensity (θ.coeff e x + smoothDDC g x) γ := by
  let α : TestForm W (2 * m) := tensorTestCLM ↑γ φ
  have hα : ∀ x, α x ∈ formSpan (m + 1) m := by
    intro x
    exact (formSpan (m + 1) m).smul_mem (φ x) γ.property
  have hbg : (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).restrictChart e hW (castTestDegree
        (by rw [complexModel_real_finrank]; omega :
          2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      ∫ x, φ x * formDensity (θ.coeff e x) γ := by
    change (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).inChart e
        (TestFunction.monoCLM ℝ (castTestDegree _ α)) = _
    rw [← castTestDegree_mono _ hW α, smoothGlobalCurrent_castTestDegree_eq_integral]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [testForm_inclusion_apply hW]
    change topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
      (θ.coeff e x) (α x)) = _
    rw [← wedgeTo_comm_of_mem_formSpan (hα x) (θ.coeff e x) rfl
      (by omega : 2 + 2 * m = 2 * (m + 1))]
    change topDensity (coordinateWedge (φ x • (γ : RealForm (m + 1) (2 * m)))
      (θ.coeff e x)) = _
    rw [coordinateWedge_smul_left, topDensity_smul, formDensity_apply]
  have hdd : (globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) u
      hu.quasiPshPotential).restrictChart e hW (castTestDegree
        (by rw [complexModel_real_finrank]; omega :
          2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      ∫ x, φ x * formDensity (smoothDDC g x) γ := by
    rw [globalDDC_restrictChart_castTestDegree_eq_integral u hu.quasiPshPotential e hW α hα]
    calc
      _ = ∫ x in (W : Set (ComplexModel (m + 1))), scalarAdjointTest α x * g x := by
        apply setIntegral_congr_fun W.isOpen.measurableSet
        intro x hx
        change scalarAdjointTest α x * (chartFunction u e x).toReal =
          scalarAdjointTest α x * g x
        rw [heq x hx, EReal.toReal_coe]
      _ = ∑ i, ddcWedge (oneCurrent W) hg (formBasis (m + 1) m i) (coeffTest α i) :=
        (local_smooth_scalar_full_test_integral hg α).symm
      _ = _ := by
        rw [ddcWedge_oneCurrent_full_test_integral hg α hα]
        apply integral_congr_ae
        filter_upwards [] with x
        change topDensity (coordinateWedge (φ x • (γ : RealForm (m + 1) (2 * m)))
          (smoothDDC g x)) = _
        rw [coordinateWedge_smul_left, topDensity_smul, formDensity_apply]
  have hθint := integrable_test_mul_continuousOn φ
    (continuousOn_formDensity ((θ.smooth e).continuousOn.mono hW) γ)
  have hgint := integrable_test_mul_continuousOn φ
    (continuousOn_formDensity (contDiffOn_ddcForm hg).continuousOn γ)
  rw [restrict_chartSpanCurrent]
  change (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
    (k := degreeTwo (Nat.succ_pos m)) θ).restrictChart e hW (castTestDegree _ α) +
    (globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) u
      hu.quasiPshPotential).restrictChart e hW (castTestDegree _ α) = _
  rw [hbg, hdd, ← integral_add hθint hgint]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [formDensity_apply, formDensity_apply, formDensity_apply,
    coordinateWedge_add_right, topDensity_add, mul_add]

/-- Off every pole, the actual analytic potential current has its genuine smooth
density and its actual canonical absolutely continuous part restricts to itself. -/
theorem exists_nonpolar_local_density (θ : ClosedRealOneOneForm (m + 1) M)
    (u : M → EReal) (hu : IsThetaPshPotential θ.val u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) u)
    (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1))
    (hz : z ∈ e.val.target) (hp : e.val.symm z ∉ poleSet u) :
    ∃ (W : Opens (ComplexModel (m + 1))) (_hzW : z ∈ W)
      (hW : W ≤ chartTarget e) (g : ComplexModel (m + 1) → ℝ),
      ContDiffOn ℝ ∞ g W ∧ (∀ x ∈ W, chartFunction u e x = (g x : EReal)) ∧
      restrict hW (acPart (isPositive_chartSpanCurrent θ.val u hu e)) =
        restrict hW (chartSpanCurrent (thetaPotentialCurrent θ.val u hu) e) ∧
      ∀ (γ : formSpan (m + 1) m) (φ : 𝓓(W, ℝ)),
        restrict hW (chartSpanCurrent (thetaPotentialCurrent θ.val u hu) e) γ φ =
          ∫ x, φ x * formDensity (θ.val.coeff e x + smoothDDC g x) γ := by
  obtain ⟨g, hsg, heq⟩ :=
    SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole han e z hz hp
  have hnear : {x | ContDiffAt ℝ ∞ g x ∧ chartFunction u e x = (g x : EReal)} ∩
      e.val.target ∈ 𝓝 z := inter_mem (hsg.and heq) (e.val.open_target.mem_nhds hz)
  obtain ⟨Wset, hsub, hopen, hzW⟩ := mem_nhds_iff.mp hnear
  let W : Opens (ComplexModel (m + 1)) := ⟨Wset, hopen⟩
  have hW : W ≤ chartTarget e := fun x hx => (hsub hx).2
  have hg : ContDiffOn ℝ ∞ g W := fun x hx => (hsub hx).1.1.contDiffWithinAt
  have hEq : ∀ x ∈ W, chartFunction u e x = (g x : EReal) :=
    fun x hx => (hsub hx).1.2
  let α : ComplexModel (m + 1) → RealForm (m + 1) 2 :=
    fun x => θ.val.coeff e x + smoothDDC g x
  have hαc : ContinuousOn α W :=
    ((θ.val.smooth e).continuousOn.mono hW).add (contDiffOn_ddcForm hg).continuousOn
  have hα : ∀ x ∈ W, IsSemipositiveOneOne (α x) := by
    intro x hx
    have hgnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ g y := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact (hsub hy).1.1
    have heqnear : chartFunction u e =ᶠ[𝓝 x] fun y => (g y : EReal) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    refine ⟨?_, ?_⟩
    · intro a b
      simp only [α, ContinuousAlternatingMap.add_apply]
      rw [θ.property.2 e x (hW hx) a b,
        MongeAmpere.smoothDDC_isOneOne ((hsub hx).1.1.of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) a b]
    · intro v
      simp only [α, ContinuousAlternatingMap.add_apply]
      exact semipositive_add_smoothDDC_of_thetaPlurisubharmonic hu.1 e (hW hx)
        hgnear heqnear v
  let hS := isPositive_chartSpanCurrent θ.val u hu e
  let hSW := isPositive_restrict hS hW
  have hpair : ∀ (γ : formSpan (m + 1) m) (φ : 𝓓(W, ℝ)),
      restrict hW (chartSpanCurrent (thetaPotentialCurrent θ.val u hu) e) γ φ =
        ∫ x, φ x * formDensity (α x) γ :=
    fun γ φ => smooth_pairing θ.val u hu e hW g hg hEq γ φ
  have hω : kahlerPower (m + 1) m ∈ posCone (m + 1) m :=
    formPower_mem_spCone isSemipositiveOneOne_kahlerForm m
  have htr : hSW.traceMeasure =
      volume.withDensity (formWeight W α (kahlerPower (m + 1) m)) :=
    eq_of_forall_testFunction_integral_eq hSW.traceMeasure_compl (formWeight_compl α _)
      (fun K hK hKW => hSW.traceMeasure_lt_top hK hKW) (formWeight_lt_top hαc _)
      fun φ => by rw [hSW.integral_traceMeasure, hpair, integral_formWeight hαc hα hω]
  have hac : hSW.traceMeasure ≪ volume := by
    rw [htr]
    exact withDensity_absolutelyContinuous _ _
  refine ⟨W, hzW, hW, g, hg, hEq, ?_, hpair⟩
  rw [acPart_restrict hS hW]
  exact acPart_eq_self_of_absolutelyContinuous hSW hac

end SGPT.Foundations.Analysis.Pending.ActualAnalyticCurrentLocalDensity

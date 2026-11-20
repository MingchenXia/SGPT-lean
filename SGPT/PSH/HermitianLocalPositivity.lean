import SGPT.PSH.HermitianLocalCorrection
import SGPT.Foundations.Analysis.GermPshLeviPositivity
import SGPT.Foundations.Analysis.Pending.FullGeometricCurrentPositivityGluing

/-!
# Recovering the sharp background inequality from local PSH corrections

If, for every positive error, a genuine local PSH correction has Hessian
bounded above by the background plus that error times the flat form, then
the original background-plus-Hessian current is positive. The proof uses
positivity of actual smooth residual currents, local compact-test gluing,
and the limit of the scalar error to zero. The background need not be closed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.Hermitian

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorSmooth LocalBedfordTaylorForms LocalBedfordTaylorCollar
  LocalSmoothScalarCurrents ScalarLeviPositiveCurrent LocalCurrentLebesgue
  CompactVariableCurrentTests LocalPositiveCurrentGluing
  CanonicalComplementaryCurrentTests CanonicalCurrentFrame GlobalCurrents
  FullGeometricCurrentPositivityGluing

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {m : ℕ}

/-- A PSH correction and a pointwise nonnegative smooth residual give the
full positive local current, on every variable strongly positive test. -/
theorem isPositive_localCurrent_of_psh_add_smooth
    {W : Opens (ComplexModel (m + 1))}
    {a : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (ha : ContDiffOn ℝ ∞ a W) (ha₁ : ∀ z ∈ W, IsOneOne (a z))
    {u : ComplexModel (m + 1) → EReal}
    (huL : LocallyIntegrableOn (fun z => (u z).toReal) W volume)
    (huf : ∀ᵐ z ∂volume.restrict W, u z ≠ ⊤ ∧ u z ≠ ⊥)
    {q : ComplexModel (m + 1) → ℝ} (hq : ContDiffOn ℝ ∞ q W)
    (hp : PlurisubharmonicOn (fun z => u z + (q z : EReal)) W)
    (hdom : ∀ z ∈ W, ∀ v : ComplexModel (m + 1),
      smoothDDC q z ![v, Complex.I • v] ≤ a z ![v, Complex.I • v]) :
    IsPositive (wedgeForm rfl (oneCurrent W) ha +
      ddc (scalarTopCurrent (regularDistribution volume (fun z => (u z).toReal) huL))) := by
  have hqL : LocallyIntegrableOn q W volume :=
    hq.continuousOn.locallyIntegrableOn W.isOpen.measurableSet
  have hreal : (fun z => (u z).toReal + q z) =ᵐ[volume.restrict W]
      (fun z => (u z + (q z : EReal)).toReal) := by
    filter_upwards [huf] with z hz
    rw [EReal.toReal_add hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe]
  have hFL := (huL.add hqL).congr hreal
  let Tu := regularDistribution volume (fun z => (u z).toReal) huL
  let Tq := regularDistribution volume q hqL
  let TF := regularDistribution volume (fun z => (u z + (q z : EReal)).toReal) hFL
  have hdist : TF = Tu + Tq := by
    apply (regularDistribution_congr_ae_on (huL.add hqL) hFL hreal).symm.trans
    ext φ
    change _ = Tu φ + Tq φ
    simp only [Tu, Tq, regularDistribution_apply, Pi.add_apply, mul_add]
    exact integral_add (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) huL)
      (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hqL)
  have hscalar : scalarTopCurrent TF = scalarTopCurrent Tu + scalarTopCurrent Tq := by
    rw [hdist]
    ext γ φ
    simp only [LinearMap.add_apply, _root_.add_apply, scalarTopCurrent_apply, mul_add]
  have hqddc := contDiffOn_ddcForm hq
  let Cq := wedgeForm rfl (oneCurrent W) hqddc
  let Ca := wedgeForm rfl (oneCurrent W) ha
  let R := wedgeForm rfl (oneCurrent W) (ha.sub hqddc)
  have hdiff : ddc (scalarTopCurrent TF) = ddc (scalarTopCurrent Tu) + Cq := by
    rw [hscalar, ddc_add, ddc_scalarTopCurrent_regularDistribution_eq_ddcWedge hq,
      ddcWedge_eq_wedgeForm]
  have hR : R = Ca - Cq := HermitianProducts.wedgeForm_sub rfl (oneCurrent W) ha hqddc
  have hRpos : IsPositive R := by
    apply isPositive_wedgeForm rfl isPositive_oneCurrent (ha.sub hqddc)
    intro z hz
    apply mem_spCone_one
    constructor
    · intro v w
      simp only [ContinuousAlternatingMap.sub_apply]
      rw [ha₁ z hz v w, smoothDDC_isOneOne
        (((hq z hz).contDiffAt (W.isOpen.mem_nhds hz)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v w]
    · intro v
      exact sub_nonneg.mpr (hdom z hz v)
  have hFpos : IsPositive (ddc (scalarTopCurrent TF)) :=
    isPositive_ddc_scalarTopCurrent (hp.hasNonnegativeDistributionalLevi_of_locallyIntegrable
      hFL (huf.mono fun z hz => ⟨EReal.add_ne_top hz.1 (EReal.coe_ne_top _),
        EReal.add_ne_bot_iff.mpr ⟨hz.2, EReal.coe_ne_bot _⟩⟩))
  have heq : Ca + ddc (scalarTopCurrent Tu) = ddc (scalarTopCurrent TF) + R := by
    rw [hdiff, hR]
    abel
  rw [heq]
  exact hFpos.add hRpos

private def currentPairing {W : Opens (ComplexModel (m + 1))}
    (T : LocalProductCurrent (m + 1) W m) :
    TestForm W (2 * m) →L[ℝ] ℝ :=
  ∑ i, (T (formBasis (m + 1) m i)).comp
    (TestFunction.postcompCLM (coeffCLM (m + 1) m i))

private theorem currentPairing_apply {W : Opens (ComplexModel (m + 1))}
    (T : LocalProductCurrent (m + 1) W m) (α : TestForm W (2 * m)) :
    currentPairing T α = ∑ i, T (formBasis (m + 1) m i) (coeffTest α i) := by
  simp only [currentPairing, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

private def flatCurrent (W : Opens (ComplexModel (m + 1))) : LocalProductCurrent (m + 1) W m :=
  wedgeForm rfl (oneCurrent W) (contDiffOn_const :
    ContDiffOn ℝ ∞ (fun _ : ComplexModel (m + 1) => kahlerForm (m + 1)) W)

private theorem flatPairing_mono {W V : Opens (ComplexModel (m + 1))}
    (hWV : W ≤ V) (α : TestForm W (2 * m))
    (hα : ∀ z, α z ∈ formSpan (m + 1) m) :
    currentPairing (flatCurrent V) (TestFunction.monoCLM ℝ α) =
      currentPairing (flatCurrent W) α := by
  have hi : ∀ z, (TestFunction.monoCLM ℝ α : TestForm V (2 * m)) z ∈ formSpan (m + 1) m :=
    fun z => by simpa only [testForm_inclusion_apply hWV] using hα z
  simp only [currentPairing_apply, flatCurrent]
  rw [HermitianProducts.wedgeForm_oneCurrent_full_test_integral _
      (fun _ _ => oneOne_mem_formSpan isSemipositiveOneOne_kahlerForm.1) _ hi,
    HermitianProducts.wedgeForm_oneCurrent_full_test_integral _
      (fun _ _ => oneOne_mem_formSpan isSemipositiveOneOne_kahlerForm.1) _ hα]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [testForm_inclusion_apply hWV]

private def castTestCLM {n a b : ℕ} {W : Opens (ComplexModel n)} (h : a = b) :
    TestForm W a →L[ℝ] TestForm W b := h ▸ ContinuousLinearMap.id ℝ (TestForm W a)

private theorem castTestCLM_apply {n a b : ℕ} {W : Opens (ComplexModel n)}
    (h : a = b) (α : TestForm W a) : castTestCLM h α = castTestDegree h α := by
  subst b
  rfl

private theorem castTestDegree_mono {n a b : ℕ} {W V : Opens (ComplexModel n)}
    (h : a = b) (_hWV : W ≤ V) (α : TestForm W a) :
    castTestDegree h (TestFunction.monoCLM ℝ α : TestForm V a) =
      (TestFunction.monoCLM ℝ (castTestDegree h α) : TestForm V b) := by
  subst b
  rfl

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Local PSH corrections with arbitrarily small upper Hessian error prove
the sharp full current inequality for the original smooth background. -/
theorem isFormPSH_of_approximate_local_psh
    (θ : SmoothRealForm (m + 1) M 2) (hθ₁ : θ.IsTypeOneOne)
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (hlocal : ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target →
      ∀ ε : ℝ, 0 < ε → ∃ (W : Opens (ComplexModel (m + 1))) (_hW : W ≤ chartTarget e)
        (q : ComplexModel (m + 1) → ℝ), z ∈ W ∧ ContDiffOn ℝ ∞ q W ∧
        PlurisubharmonicOn (fun y => chartFunction u e y + (q y : EReal)) W ∧
        ∀ y ∈ W, ∀ v : ComplexModel (m + 1), smoothDDC q y ![v, Complex.I • v] ≤
          θ.coeff e y ![v, Complex.I • v] + ε * ‖v‖ ^ 2) : IsFormPSH θ u := by
  refine ⟨hu, ?_⟩
  intro e α hα
  let T := potentialCurrent θ u hu
  let B := currentPairing (flatCurrent (chartTarget e))
  have hdegree : 2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2 := by
    rw [complexModel_real_finrank]
    omega
  have hε : ∀ ε : ℝ, 0 < ε → 0 ≤ T.inChart e (castTestDegree hdegree α) + ε * B α := by
    intro ε hε
    let S : TestForm (chartTarget e) (2 * m) →L[ℝ] ℝ :=
      (T.inChart e).comp (castTestCLM hdegree) + ε • B
    have hloc : ∀ z ∈ chartTarget e, ∃ (W : Opens (ComplexModel (m + 1)))
        (_hW : W ≤ chartTarget e), z ∈ W ∧
        ∀ β : TestForm W (2 * m), (∀ y, β y ∈ spCone m) →
          0 ≤ S (TestFunction.monoCLM ℝ β : TestForm (chartTarget e) (2 * m)) := by
      intro z hz
      obtain ⟨W, hW, q, hzW, hq, hp, hqdom⟩ := hlocal e z hz ε hε
      refine ⟨W, hW, hzW, ?_⟩
      intro β hβ
      have hβS : ∀ y, β y ∈ formSpan (m + 1) m :=
        fun y => mem_formSpan_of_mem_spCone (hβ y)
      have hθs := (θ.smooth e).mono hW
      have hflat : ContDiffOn ℝ ∞ (fun _ : ComplexModel (m + 1) => kahlerForm (m + 1)) W :=
        contDiffOn_const
      have ha := hθs.add (hflat.const_smul ε)
      have ha₁ : ∀ y ∈ W, IsOneOne (θ.coeff e y + ε • kahlerForm (m + 1)) := by
        intro y hy v w
        simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        rw [hθ₁ e y (hW hy) v w, isSemipositiveOneOne_kahlerForm.1 v w]
      have hi := isPositive_localCurrent_of_psh_add_smooth ha ha₁
        ((hu.locallyIntegrableOn_chart_toReal e).mono_set hW)
        (ae_restrict_of_ae_restrict_of_subset hW (hu.ae_finite_chart e)) hq hp
        (fun y hy v => by simpa only [ContinuousAlternatingMap.add_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul, kahlerForm_apply_I] using hqdom y hy v)
      have hsplit : wedgeForm rfl (oneCurrent W) ha +
          ddc (scalarTopCurrent (regularDistribution volume
            (fun y => (chartFunction u e y).toReal)
            ((hu.locallyIntegrableOn_chart_toReal e).mono_set hW))) =
          (wedgeForm rfl (oneCurrent W) hθs + ddc (scalarTopCurrent
            (regularDistribution volume (fun y => (chartFunction u e y).toReal)
              ((hu.locallyIntegrableOn_chart_toReal e).mono_set hW)))) + ε • flatCurrent W := by
        rw [HermitianProducts.wedgeForm_add rfl (oneCurrent W) hθs (hflat.const_smul ε),
          HermitianProducts.wedgeForm_smul rfl (oneCurrent W) hflat ε]
        dsimp only [flatCurrent]
        abel
      have hn := pairing_nonnegative _ hi β hβ
      rw [hsplit] at hn
      simp only [LinearMap.add_apply, LinearMap.smul_apply, _root_.add_apply,
        _root_.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hn
      have hreading := local_current_full_pairing θ hθ₁ u hu e hW β hβS
      simp only [LinearMap.add_apply, _root_.add_apply, Finset.sum_add_distrib] at hreading
      rw [hreading] at hn
      change 0 ≤ T.inChart e (castTestCLM hdegree (TestFunction.monoCLM ℝ β)) +
        ε * currentPairing (flatCurrent (chartTarget e)) (TestFunction.monoCLM ℝ β)
      rw [castTestCLM_apply, castTestDegree_mono hdegree hW β, flatPairing_mono hW β hβS,
        currentPairing_apply]
      exact hn
    have hn := nonnegative_of_local_full_tests S hloc α hα
    change 0 ≤ T.inChart e (castTestCLM hdegree α) + ε * B α at hn
    rwa [castTestCLM_apply] at hn
  change 0 ≤ T.inChart e (castTestDegree hdegree α)
  by_contra hn
  let A := T.inChart e (castTestDegree hdegree α)
  let b := B α
  have hA : A < 0 := lt_of_not_ge hn
  let r : ℝ := -A / (2 * (|b| + 1))
  have hden : 0 < 2 * (|b| + 1) := by positivity
  have hr : 0 < r := div_pos (neg_pos.mpr hA) hden
  have heq : r * (2 * (|b| + 1)) = -A := div_mul_cancel₀ _ hden.ne'
  have hb : r * b ≤ r * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) hr.le
  have h := hε r hr
  change 0 ≤ A + r * b at h
  nlinarith

end SGPT.PSH.Hermitian

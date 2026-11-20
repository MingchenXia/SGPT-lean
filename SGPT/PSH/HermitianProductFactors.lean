import SGPT.PSH.HermitianProductPatches
import SGPT.PSH.HermitianProductsPositivity
import SGPT.Foundations.Analysis.Pending.ActualBoundedScalarCurrentIdentity

/-!
# Positive local factors of genuine Hermitian PSH potentials

Full variable-test positivity of the original geometric current is converted
to the actual local coefficient current. The real corrected PSH reader gives
the genuine multiplication current, so its Hessian and the smooth residual
cancel to exactly the original background-plus-Hessian current.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality LocalBedfordTaylorCalculus LocalBedfordTaylorForms
  LocalBedfordTaylorCollar ScalarLeviPositiveCurrent LocalSmoothScalarCurrents
  CompactVariableCurrentTests LocalCurrentLebesgue CanonicalComplementaryCurrentTests
open Hermitian

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

private def fullPairing {n r : ℕ} {W : Opens (ComplexModel n)}
    (T : LocalProductCurrent n W r) : TestForm W (2 * r) →L[ℝ] ℝ :=
  ∑ j, (T (formBasis n r j)).comp (TestFunction.postcompCLM (coeffCLM n r j))

private theorem fullPairing_apply {n r : ℕ} {W : Opens (ComplexModel n)}
    (T : LocalProductCurrent n W r) (α : TestForm W (2 * r)) :
    fullPairing T α = ∑ j, T (formBasis n r j) (coeffTest α j) := by
  simp only [fullPairing, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

private theorem coefficient_constant {n r : ℕ} {W : Opens (ComplexModel n)}
    (γ : formSpan n r) (φ : 𝓓(W, ℝ)) (j : Fin (Module.finrank ℝ (formSpan n r))) :
    coeffTest (constantTestFormCLM (γ : RealForm n (2 * r)) φ) j =
      (formBasis n r).repr γ j • φ := by
  ext x
  change coeffCLM n r j (φ x • (γ : RealForm n (2 * r))) =
    ((formBasis n r).repr γ j • φ) x
  rw [map_smul]
  change φ x * (formBasis n r).repr (formProj n r (γ : RealForm n (2 * r))) j =
    (formBasis n r).repr γ j * φ x
  rw [formProj_coe, mul_comm]

private theorem fullPairing_constant {n r : ℕ} {W : Opens (ComplexModel n)}
    (T : LocalProductCurrent n W r) (γ : formSpan n r) (φ : 𝓓(W, ℝ)) :
    fullPairing T (constantTestFormCLM (γ : RealForm n (2 * r)) φ) = T γ φ := by
  classical
  simp only [fullPairing, _root_.sum_apply]
  change (∑ j, T (formBasis n r j)
    (coeffTest (constantTestFormCLM (γ : RealForm n (2 * r)) φ) j)) = T γ φ
  simp only [coefficient_constant, map_smul, smul_eq_mul]
  conv_rhs => rw [← (formBasis n r).sum_repr γ, map_sum, _root_.sum_apply]
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual positive local coefficient current is produced from the
original full geometric inequality; no local positivity input is requested. -/
theorem isPositive_localCurrent_of_isFormPSH
    {θ : SmoothRealForm (m + 1) M 2} (hθ₁ : θ.IsTypeOneOne)
    {u : M → EReal} (hu : IsFormPSH θ u)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) :
    IsPositive (wedgeForm rfl (oneCurrent W) ((θ.smooth e).mono hW) +
      ddc (scalarTopCurrent (regularDistribution volume
        (fun z => (chartFunction u e z).toReal)
        ((hu.quasiPshPotential.locallyIntegrableOn_chart_toReal e).mono_set hW)))) := by
  intro ι _ γ φ hγφ
  let α : TestForm W (2 * m) := ∑ i, constantTestFormCLM (γ i : RealForm (m + 1) (2 * m)) (φ i)
  have hα : ∀ z, α z ∈ spCone m := by
    intro z
    simpa only [α, _root_.sum_apply, constantTestFormCLM_apply] using hγφ z
  have hp := hu.isPositiveCurrent.restrictChart e hW α hα
  rw [← local_current_full_pairing θ hθ₁ u hu.quasiPshPotential e hW α
    (fun z => mem_formSpan_of_mem_spCone (hα z))] at hp
  rw [← fullPairing_apply] at hp
  simpa only [α, map_sum, fullPairing_constant] using hp

private theorem restrict_oneCurrent {n : ℕ} {U V : Opens (ComplexModel n)} (hVU : V ≤ U) :
    restrict hVU (oneCurrent U) = oneCurrent V := by
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply, oneCurrent_apply]
  rw [show (extTest hVU φ : ComplexModel n → ℝ) = φ from funext (extTest_apply hVU φ)]

private theorem restrict_scalarTopCurrent {n : ℕ} {U V : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hU : LocallyIntegrableOn f U volume) (hVU : V ≤ U) :
    restrict hVU (scalarTopCurrent (regularDistribution volume f hU)) =
      scalarTopCurrent (regularDistribution volume f (hU.mono_set hVU)) := by
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply, scalarTopCurrent_apply,
    regularDistribution_apply]
  rw [show (extTest hVU φ : ComplexModel n → ℝ) = φ from funext (extTest_apply hVU φ)]

/-- The nonsmooth scalar multiplication identity holds on its entire
original open PSH domain; relatively compact approximation patches are
constructed internally and eliminated by genuine current locality. -/
theorem scalarTopCurrent_regularDistribution_eq_mulBorel_on_domain
    {n : ℕ} {U : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : IsLocallyBoundedPshOn U f) :
    scalarTopCurrent (regularDistribution volume f
      (locallyIntegrableOn_of_plurisubharmonicOn_real hf.1)) =
      mulBorel (oneCurrent U) ((U : Set (ComplexModel n)).indicator f) := by
  apply LocalBedfordTaylorCalculus.eq_of_local
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let V : Opens (ComplexModel n) := ⟨ball x (a / 2), isOpen_ball⟩
  have hV : RelativelyCompactIn V U := relativelyCompactIn_half_ball ha hball
  have hVU : V ≤ U := subset_closure.trans hV.2
  refine ⟨V, hVU, mem_ball_self (half_pos ha), ?_⟩
  rw [restrict_scalarTopCurrent _ hVU]
  rw [ActualBoundedScalarCurrentIdentity.scalarTopCurrent_regularDistribution_eq_mulBorel_of_locallyBoundedPsh hf hV]
  rw [← mulBorel_restrict isPositive_oneCurrent hVU
    (measurable_indicator_of_isLocallyBoundedPshOn hf) (isLocallyBoundedOn_indicator hf),
    restrict_oneCurrent hVU]
  have hfV := isLocallyBoundedPshOn_mono hf hVU
  apply mulBorel_congr isPositive_oneCurrent
    (measurable_indicator_of_isLocallyBoundedPshOn hfV) (isLocallyBoundedOn_indicator hfV)
    (measurable_indicator_of_isLocallyBoundedPshOn hf)
    (isLocallyBoundedOn_mono (isLocallyBoundedOn_indicator hf) hVU)
  intro y hy
  rw [indicator_of_mem hy, indicator_of_mem (hVU hy)]

namespace BackgroundPatch

variable {omega : Background (m + 1) M}

/-- Every corrected factor plus its literal smooth residual is the original
positive Hermitian current. All distribution and real-reader identities
are produced from genuine class membership and boundedness. -/
theorem factor_isPositive (P : BackgroundPatch omega)
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    IsPositive (ddcMul (oneCurrent P.geometry.domain) (P.correctedReal u) +
      wedgeForm rfl (oneCurrent P.geometry.domain) P.residual_smooth) := by
  let W := P.geometry.domain
  let e := P.geometry.chart
  have hW : W ≤ chartTarget e := P.geometry.domain_le_target
  let f : ComplexModel (m + 1) → ℝ := fun z => (chartFunction u e z).toReal
  have hfL : LocallyIntegrableOn f W volume :=
    (hu.quasiPshPotential.locallyIntegrableOn_chart_toReal e).mono_set hW
  have hqL : LocallyIntegrableOn P.correction W volume :=
    P.smooth.continuousOn.locallyIntegrableOn W.isOpen.measurableSet
  have hc := P.correctedReal_isLocallyBoundedPshOn hu hb
  have hcL : LocallyIntegrableOn (P.correctedReal u) W volume := hfL.add hqL
  let Tu := regularDistribution volume f hfL
  let Tq := regularDistribution volume P.correction hqL
  let Tc := regularDistribution volume (P.correctedReal u) hcL
  have hdist : Tc = Tu + Tq := by
    ext φ
    change _ = Tu φ + Tq φ
    simp only [Tc, Tu, Tq, regularDistribution_apply, correctedReal, mul_add]
    exact integral_add (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hfL)
      (φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hqL)
  have hscalar : scalarTopCurrent Tc = scalarTopCurrent Tu + scalarTopCurrent Tq := by
    rw [hdist]
    ext γ φ
    simp only [LinearMap.add_apply, _root_.add_apply, scalarTopCurrent_apply, mul_add]
  have hdc : ddcMul (oneCurrent W) (P.correctedReal u) =
      ddc (scalarTopCurrent Tc) := by
    change ddc (mulBorel (oneCurrent W) ((W : Set (ComplexModel (m + 1))).indicator
      (P.correctedReal u))) = _
    rw [← scalarTopCurrent_regularDistribution_eq_mulBorel_on_domain hc]
  have hdiff : ddcMul (oneCurrent W) (P.correctedReal u) =
      ddc (scalarTopCurrent Tu) +
        wedgeForm rfl (oneCurrent W) (contDiffOn_ddcForm P.smooth) := by
    rw [hdc, hscalar, ddc_add,
      ddc_scalarTopCurrent_regularDistribution_eq_ddcWedge P.smooth,
      ddcWedge_eq_wedgeForm]
  have hres : wedgeForm rfl (oneCurrent W) P.residual_smooth =
      wedgeForm rfl (oneCurrent W) ((omega.form.smooth e).mono hW) -
        wedgeForm rfl (oneCurrent W) (contDiffOn_ddcForm P.smooth) :=
    HermitianProducts.wedgeForm_sub rfl (oneCurrent W)
      ((omega.form.smooth e).mono hW) (contDiffOn_ddcForm P.smooth)
  have heq : ddcMul (oneCurrent W) (P.correctedReal u) +
      wedgeForm rfl (oneCurrent W) P.residual_smooth =
      wedgeForm rfl (oneCurrent W) ((omega.form.smooth e).mono hW) +
        ddc (scalarTopCurrent Tu) := by
    rw [hdiff, hres]
    abel
  rw [heq]
  exact isPositive_localCurrent_of_isFormPSH omega.isTypeOneOne hu e hW

/-- The residual retains its genuine real `(1,1)` type. -/
theorem residual_isOneOne (P : BackgroundPatch omega) :
    ∀ z ∈ P.geometry.domain, IsOneOne (P.residual z) := by
  intro z hz v w
  simp only [residual, ContinuousAlternatingMap.sub_apply]
  rw [omega.isTypeOneOne P.geometry.chart z (P.geometry.domain_le_target hz) v w,
    smoothDDC_isOneOne (((P.smooth z hz).contDiffAt
      (P.geometry.domain.isOpen.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v w]

/-- Every bounded genuine tuple internally supplies a positive mixed
background-expansion current in every product degree. -/
theorem mixedCurrent_isPositive (P : BackgroundPatch omega) (p : ℕ) (hp : p ≤ m + 1)
    (u : Fin p → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    IsPositive (P.mixedCurrent p hp u) := by
  apply HermitianProducts.isPositive_backgroundExpansion p (m + 1 - p) _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i))
    P.residual_smooth P.residual_isOneOne
  exact fun i => P.factor_isPositive (hu i) (hb i)

/-- The top-degree candidate has a genuine positive Riesz trace for every
bounded actual Hermitian tuple. -/
theorem current_isPositive (P : BackgroundPatch omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    IsPositive (P.current u) := by
  apply HermitianProducts.isPositive_backgroundExpansion (m + 1) 0 _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i))
    P.residual_smooth P.residual_isOneOne
  exact fun i => P.factor_isPositive (hu i) (hb i)

end BackgroundPatch

end SGPT.PSH.HermitianGlobalProducts

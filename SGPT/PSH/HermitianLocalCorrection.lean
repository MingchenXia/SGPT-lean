import SGPT.PSH.HermitianPSH
import SGPT.PSH.HermitianProducts
import SGPT.PSH.HermitianQuadratic
import SGPT.PSH.HermitianExtremalL1Bound
import SGPT.Foundations.Analysis.Pending.QuasiPshPositiveLeviRepresentative
import SGPT.Foundations.Analysis.Pending.FullPositiveScalarCurrentLeviConverse

/-!
# Genuine local corrections for Hermitian-relative PSH functions

A smooth chart function `q` with `ddᶜq ≥ omega` corrects every `omega`-PSH function
to a plurisubharmonic function on that chart domain. The proof adds the
positive smooth residual current `ddᶜq - omega` to `omega + ddᶜu`, recovers the
distributional Levi inequalities, and identifies the original local quasi-PSH
representative, including its poles. No local exact potential for `omega` occurs.

The local quadratics are selected from the smooth coefficients of `omega`,
uniformly for the entire Hermitian-relative PSH family.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.Hermitian

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms TopDegreeDensity ConstantFormProducts
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorForms LocalBedfordTaylorCollar LocalCurrentLebesgue
  CompactVariableCurrentTests ScalarLeviPositiveCurrent ScalarFullTestTranspose
  LocalSmoothScalarCurrents CanonicalCurrentFrame GlobalCurrents
  CanonicalComplementaryCurrentTests

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem regularDistribution_add {W : Opens (ComplexModel (m + 1))}
    {f g : ComplexModel (m + 1) → ℝ}
    (hf : LocallyIntegrableOn f W volume) (hg : LocallyIntegrableOn g W volume) :
    regularDistribution volume (fun z => f z + g z) (hf.add hg) =
      regularDistribution volume f hf + regularDistribution volume g hg := by
  have hint {a : ComplexModel (m + 1) → ℝ} (ha : LocallyIntegrableOn a W volume)
      (φ : 𝓓(W, ℝ)) : Integrable (fun z => φ z * a z) := by
    have hK : IsCompact (tsupport φ) := φ.hasCompactSupport
    have hi : IntegrableOn a (tsupport φ) volume :=
      ha.integrableOn_compact_subset φ.tsupport_subset hK
    exact (hi.continuousOn_mul φ.continuous.continuousOn hK).integrable_of_forall_notMem_eq_zero
      (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz])
  ext φ
  change _ = regularDistribution volume f hf φ + regularDistribution volume g hg φ
  simp only [regularDistribution_apply, mul_add]
  exact integral_add (hint hf φ) (hint hg φ)

/-- The full compact pairing of the chartwise local current agrees with
the actual global background-plus-Hessian current. -/
theorem local_current_full_pairing
    (θ : SmoothRealForm (m + 1) M 2) (hθ₁ : θ.IsTypeOneOne)
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) (α : TestForm W (2 * m))
    (hα : ∀ z, α z ∈ formSpan (m + 1) m) :
    (∑ i, (wedgeForm rfl (oneCurrent W) ((θ.smooth e).mono hW) +
      ddc (scalarTopCurrent (regularDistribution volume
        (fun z => (chartFunction u e z).toReal)
        ((hu.locallyIntegrableOn_chart_toReal e).mono_set hW))))
      (formBasis (m + 1) m i) (coeffTest α i)) =
    (potentialCurrent θ u hu).restrictChart e hW
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) := by
  simp only [LinearMap.add_apply, _root_.add_apply, Finset.sum_add_distrib]
  rw [HermitianProducts.wedgeForm_oneCurrent_full_test_integral
      ((θ.smooth e).mono hW)
      (fun z hz => oneOne_mem_formSpan (hθ₁ e z (hW hz))) α hα,
    ddc_scalarTopCurrent_full_test_transpose, regularDistribution_apply,
    potentialCurrent_restrictChart_eq_integral θ u hu e hW α hα]
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with z
    exact congrArg topDensity (wedgeTo_comm_of_mem_formSpan (hα z)
      (θ.coeff e z) rfl (by omega))
  · symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzero : scalarAdjointTest α z = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hz ((scalarAdjointTest α).tsupport_subset hs))
    rw [hzero, zero_mul]

/-- A genuine coefficient inequality produces actual corrected PSH functions.
The smooth correction is shared by every potential with this background. -/
theorem chart_add_smooth_plurisubharmonicOn
    {θ : SmoothRealForm (m + 1) M 2} (hθ₁ : θ.IsTypeOneOne)
    {u : M → EReal} (hu : IsFormPSH θ u)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) {q : ComplexModel (m + 1) → ℝ}
    (hq : ContDiffOn ℝ ∞ q W)
    (hdom : ∀ z ∈ W, ∀ v : ComplexModel (m + 1),
      θ.coeff e z ![v, Complex.I • v] ≤ smoothDDC q z ![v, Complex.I • v]) :
    PlurisubharmonicOn (fun z => chartFunction u e z + (q z : EReal)) W := by
  let hqu := hu.quasiPshPotential
  have hUL : LocallyIntegrableOn (fun z => (chartFunction u e z).toReal) W volume :=
    (hqu.locallyIntegrableOn_chart_toReal e).mono_set hW
  have hqL : LocallyIntegrableOn q W volume :=
    hq.continuousOn.locallyIntegrableOn W.isOpen.measurableSet
  have hfin : ∀ᵐ z ∂volume.restrict W,
      chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hW (hqu.ae_finite_chart e)
  have hreal : (fun z => (chartFunction u e z).toReal + q z) =ᵐ[volume.restrict W]
      (fun z => (chartFunction u e z + (q z : EReal)).toReal) := by
    filter_upwards [hfin] with z hz
    rw [EReal.toReal_add hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe]
  have hFL : LocallyIntegrableOn
      (fun z => (chartFunction u e z + (q z : EReal)).toReal) W volume :=
    (hUL.add hqL).congr hreal
  let Tu := regularDistribution volume (fun z => (chartFunction u e z).toReal) hUL
  let Tq := regularDistribution volume q hqL
  let TF := regularDistribution volume
    (fun z => (chartFunction u e z + (q z : EReal)).toReal) hFL
  have hdist : TF = Tu + Tq :=
    (regularDistribution_congr_ae_on (hUL.add hqL) hFL hreal).symm.trans
      (regularDistribution_add hUL hqL)
  have hscalar : scalarTopCurrent TF = scalarTopCurrent Tu + scalarTopCurrent Tq := by
    rw [hdist]
    ext γ φ
    simp only [LinearMap.add_apply, _root_.add_apply, scalarTopCurrent_apply, mul_add]
  have hqddc := contDiffOn_ddcForm hq
  have hθs := (θ.smooth e).mono hW
  let Cθ := wedgeForm rfl (oneCurrent W) hθs
  let Cq := wedgeForm rfl (oneCurrent W) hqddc
  let Cr := wedgeForm rfl (oneCurrent W) (hqddc.sub hθs)
  have hdiff : ddc (scalarTopCurrent TF) = ddc (scalarTopCurrent Tu) + Cq := by
    rw [hscalar, ddc_add, ddc_scalarTopCurrent_regularDistribution_eq_ddcWedge hq,
      ddcWedge_eq_wedgeForm]
  have hCr : Cr = Cq - Cθ :=
    HermitianProducts.wedgeForm_sub rfl (oneCurrent W) hqddc hθs
  have hres : ∀ z ∈ W, (smoothDDC q z - θ.coeff e z) ∈ spCone 1 := by
    intro z hz
    apply mem_spCone_one
    constructor
    · intro v w
      simp only [ContinuousAlternatingMap.sub_apply]
      rw [smoothDDC_isOneOne (((hq z hz).contDiffAt (W.isOpen.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v w,
        hθ₁ e z (hW hz) v w]
    · intro v
      change 0 ≤ smoothDDC q z ![v, Complex.I • v] - θ.coeff e z ![v, Complex.I • v]
      exact sub_nonneg.mpr (hdom z hz v)
  have hCrpos : IsPositive Cr :=
    isPositive_wedgeForm rfl isPositive_oneCurrent (hqddc.sub hθs) hres
  have hLevi : HasNonnegativeDistributionalLevi TF := by
    apply FullPositiveScalarCurrentLeviConverse.hasNonnegativeDistributionalLevi_of_full_positive_pairings
    intro α hα
    have hαS : ∀ z, α z ∈ formSpan (m + 1) m :=
      fun z => mem_formSpan_of_mem_spCone (hα z)
    have hbase := hu.isPositiveCurrent.restrictChart e hW α hα
    rw [← local_current_full_pairing θ hθ₁ u hqu e hW α hαS] at hbase
    have herror := pairing_nonnegative Cr hCrpos α hα
    have heq : ddc (scalarTopCurrent TF) =
        (Cθ + ddc (scalarTopCurrent Tu)) + Cr := by
      rw [hdiff, hCr]
      abel
    rw [heq]
    simpa only [LinearMap.add_apply, _root_.add_apply, Finset.sum_add_distrib]
      using add_nonneg hbase herror
  apply QuasiPshPositiveLeviRepresentative.plurisubharmonicOn_of_nonnegative_distributionalLevi
    ((hqu.1 e).mono hW |>.add_smooth (fun z hz =>
      eventually_of_mem (W.isOpen.mem_nhds hz) (fun y hy =>
        (hq y hy).contDiffAt (W.isOpen.mem_nhds hy)))) volume
    (hfin.mono fun z hz => ⟨EReal.add_ne_top hz.1 (EReal.coe_ne_top _),
      EReal.add_ne_bot_iff.mpr ⟨hz.2, EReal.coe_ne_bot _⟩⟩) hFL hLevi

/-- Smooth background coefficients produce fixed local corrections for the
entire Hermitian-relative PSH family. -/
theorem hasCommonLocalCorrections (omega : Background (m + 1) M) :
    HermitianExtremalL1Bound.HasCommonLocalCorrections (n := m + 1)
      (IsHermitianPSH omega) := by
  intro e z hz
  obtain ⟨A, r, _hA, hr, hclosed, hdom⟩ :=
    HermitianQuadratic.exists_chart_quadratic_domination omega.form e hz
  let W : Opens (ComplexModel (m + 1)) := ⟨ball z r, isOpen_ball⟩
  have hW : W ≤ chartTarget e := fun y hy => hclosed (ball_subset_closedBall hy)
  refine ⟨W, ballPot A z 0, mem_ball_self hr, W.isOpen, hW,
    (contDiff_ballPot A z 0).contDiffOn, ?_⟩
  intro u hu
  exact chart_add_smooth_plurisubharmonicOn omega.isTypeOneOne hu e hW
    (contDiff_ballPot A z 0).contDiffOn
    (fun y hy v => hdom y (ball_subset_closedBall hy) v)

end SGPT.PSH.Hermitian

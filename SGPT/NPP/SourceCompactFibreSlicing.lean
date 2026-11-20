import SGPT.NPP.CompactFibreGlobalFubini
import SGPT.NPP.CompactFibreGeometry
import SGPT.Foundations.Analysis.Pending.ProductPshAssembly
import SGPT.Foundations.Analysis.Pending.RelativeEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.SingularPerronUniformRelativeBound
import Lean.Elab.Command

/-! Genuine compact fibre slicing, original source proof fragments under proper canonical module identity. -/

section CompactFibreCanonicalFragment026

/-! The signed smooth-form reader uses the SAME actual original geometric
current. Its value on every product-potential patch is the actual local
Borel-weighted current paired with the FULL original pulled-back top form. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending ProductComplexManifold GlobalNonPluripolar MixedNonPluripolar
open FiniteGeodesicStripCharts LocalProductCurrents LocalBedfordTaylorLocality
open LocalBedfordTaylorForms LocalBedfordTaylorSmooth TopDegreeDensity
open IntegrationCurrent StronglyPositiveForms ProductTestForms
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

def originalSignedProductCurrentIntegral
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    (θ : ClosedRealOneOneForm n X) (γ : ClosedRealOneOneForm m Z)
    (V : Fin n → X × Z → EReal) (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (η : SmoothRealForm m Z (2 * m)) (G : X × Z → ℝ) : ℝ :=
  ∫ p, topRatio omegaZ.form.val η p.2 * G p
    ∂originalJointWedgeMeasure omegaX omegaZ θ γ V hV

def originalSignedTopFormIntegral (omegaZ : KahlerBackground m Z)
    (η : SmoothRealForm m Z (2 * m)) (F : Z → ℝ) : ℝ :=
  ∫ z, topRatio omegaZ.form.val η z * F z ∂kahlerVolume omegaZ

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] in
theorem original_signed_pullback_full_tensor
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (J : OriginalProductPotentialChart θ γ) (η : SmoothRealForm m Z (2 * m))
    {q : ComplexModel (n + m)} (hq : q ∈ J.domain) :
    (SmoothRealForm.pullback (contMDiff_snd (n := n) (m := m) (X := X) (Y := Z)) η).coeff J.chart q =
      (pullbackSnd (η.coeff J.second) q : RealForm (n + m) (2 * m)) :=
  original_pullbackSnd_coeff J η hq

theorem original_signed_current_partition_readback
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (η : SmoothRealForm m Z (2 * m))
    (J : OriginalProductPotentialChart θ γ) {χ : X × Z → ℝ}
    (hχ : ChartSmooth (n := n + m) χ) (hχc : IsCompact (tsupport χ))
    (hχJ : tsupport χ ⊆ (J.source : Set (X × Z)))
    {G : X × Z → ℝ} (hG : Measurable G) {C : ℝ} (hGb : ∀ p, ‖G p‖ ≤ C) :
    (∫ p, χ p * (topRatio omegaZ.form.val η p.2 * G p)
      ∂originalJointWedgeMeasure omegaX omegaZ θ γ V hV) =
    wedgeForm (Nat.zero_add m)
      (mulBorel (restrict J.domain_le_target ((originalJointCurrent omegaX omegaZ θ γ V hV).inChart J.chart))
        (fun q => G (chartInv J.chart q)))
      (contDiffOn_pullbackSnd ((η.smooth J.second).mono J.secondPotential.2.1))
      (kahlerPower (n + m) 0) (productChartTest J hχ hχc hχJ) := by
  let U := originalProductCorrectedTuple J.first J.second J.a J.b V
  let μ := mixedTruncationLimitMeasure J.domain (augmentedFibreTuple U)
    (plurisubharmonicOn_augmentedFibreTuple
      (fun i => plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)))
  let d := basePowerDensity J.Q J.D (omegaZ.form.val.coeff J.second)
  let φ := productChartTest J hχ hχc hχJ
  let R := fun p : X × Z => topRatio omegaZ.form.val η p.2 * G p
  have hU (i : Fin n) : PlurisubharmonicOn (U i) J.domain :=
    plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)
  have hc := originalJointCurrent_local_reading omegaX omegaZ hV J
  have ha : ContDiffOn ℝ ∞ (omegaZ.form.val.coeff J.second) J.D :=
    (omegaZ.form.val.smooth J.second).mono J.secondPotential.2.1
  have hap z (hz : z ∈ J.D) : IsSemipositiveOneOne (omegaZ.form.val.coeff J.second z) :=
    ⟨(omegaZ.isKahler.1 J.second z (J.secondPotential.2.1 hz)).1,
      omegaZ.isSemipositive J.second z (J.secondPotential.2.1 hz)⟩
  have hη := (η.smooth J.second).mono J.secondPotential.2.1
  have hR : Measurable R := ((continuous_topRatio omegaZ.isKahler.1 η).measurable.comp measurable_snd).mul hG
  have hpair := original_joint_partition_chart_pairing omegaX omegaZ hV J hχ hχc hχJ hR
  have hm : wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
      (Nat.add_comm m n) J.domain U) (baseTwoFormPullback (omegaZ.form.val.coeff J.second)) =
      μ.withDensity (fun q => ENNReal.ofReal (d q)) :=
    original_np_wedgePowerMeasure_base_eq_npLimit hU hc.1 ha hap
  have hd0 (q : ComplexModel (n + m)) : 0 ≤ d q := by
    by_cases hq : q ∈ J.domain
    · change q ∈ prodOpens J.Q J.D at hq
      change 0 ≤ basePowerDensity J.Q J.D (omegaZ.form.val.coeff J.second) q
      rw [basePowerDensity, indicator_of_mem hq]
      exact mul_nonneg (pow_pos Real.pi_pos m).le
        (topDensity_nonneg_of_mem_spCone (formPower_mem_spCone (hap _ hq.2) m))
    · change q ∉ prodOpens J.Q J.D at hq
      change 0 ≤ basePowerDensity J.Q J.D (omegaZ.form.val.coeff J.second) q
      rw [basePowerDensity, indicator_of_notMem hq]
  have hdm : Measurable (fun q => ENNReal.ofReal (d q)) :=
    ENNReal.measurable_ofReal.comp (measurable_basePowerDensity ha)
  have hdfin : ∀ᵐ q ∂μ, ENNReal.ofReal (d q) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hdensity (q : ComplexModel (n + m)) (hq : q ∈ J.domain) :
      topDensity (η.coeff J.second (ProductMixedMeasure.projSnd n m q)) =
        topRatio omegaZ.form.val η (chartInv J.chart q).2 *
          topDensity (formPower (omegaZ.form.val.coeff J.second (ProductMixedMeasure.projSnd n m q)) m) := by
    have hpoint : (chartInv J.chart q).2 = J.second.val.symm (ProductMixedMeasure.projSnd n m q) := by
      rw [chartInv_of_mem (J.domain_le_target hq)]
      change ((prodChart J.first.val J.second.val).symm q).2 = _
      rw [prodChart_symm_apply]
      rfl
    rw [hpoint]
    have hf := congrArg topDensity (smooth_top_form_coeff_eq_topRatio_smul omegaZ η J.second
      (ProductMixedMeasure.projSnd n m q) (J.secondPotential.2.1 hq.2))
    simpa only [topDensity_smul, formPow_coeff] using hf
  have hlocal := original_current_pullbackSnd_apply_eq_npLimit hU hc.1 hη
    (hG.comp (measurable_chartInv J.chart))
    (fun _ _ _ => ⟨C, fun q _ => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hGb (chartInv J.chart q)⟩) φ
  have hlast : (∫ q, φ q * (Real.pi ^ m * topDensity (η.coeff J.second (ProductMixedMeasure.projSnd n m q))) *
      G (chartInv J.chart q) ∂μ) =
      wedgeForm (Nat.zero_add m)
        (mulBorel (restrict J.domain_le_target ((originalJointCurrent omegaX omegaZ θ γ V hV).inChart J.chart))
          (fun q => G (chartInv J.chart q))) (contDiffOn_pullbackSnd hη)
        (kahlerPower (n + m) 0) φ := by
    have heq := congrArg (fun S : LocalProductCurrent (n + m) J.domain m =>
      wedgeForm (Nat.zero_add m) (mulBorel S (fun q => G (chartInv J.chart q)))
        (contDiffOn_pullbackSnd hη) (kahlerPower (n + m) 0) φ) hc.2
    exact hlocal.symm.trans heq.symm
  calc
    _ = ∫ q, φ q * R (chartInv J.chart q)
        ∂wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
          (Nat.add_comm m n) J.domain U) (baseTwoFormPullback (omegaZ.form.val.coeff J.second)) := hpair.2
    _ = ∫ q, φ q * R (chartInv J.chart q) ∂μ.withDensity (fun q => ENNReal.ofReal (d q)) :=
      congrArg (fun ν : Measure (ComplexModel (n + m)) => ∫ q, φ q * R (chartInv J.chart q) ∂ν) hm
    _ = ∫ q, φ q * (Real.pi ^ m * topDensity (η.coeff J.second (ProductMixedMeasure.projSnd n m q))) *
        G (chartInv J.chart q) ∂μ := by
      rw [integral_withDensity_eq_integral_toReal_smul hdm hdfin]
      apply integral_congr_ae
      filter_upwards [ae_iff.mpr (mixedTruncationLimitMeasure_compl
        (plurisubharmonicOn_augmentedFibreTuple hU))] with q hq
      rw [ENNReal.toReal_ofReal (hd0 q), smul_eq_mul, hdensity q hq]
      change basePowerDensity J.Q J.D (omegaZ.form.val.coeff J.second) q *
        (φ q * (topRatio omegaZ.form.val η (chartInv J.chart q).2 * G (chartInv J.chart q))) = _
      change q ∈ prodOpens J.Q J.D at hq
      rw [basePowerDensity, indicator_of_mem hq]
      ring
    _ = _ := hlast

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment026

section CompactFibreCanonicalFragment027

/-! Actual whole signed-top-form Fubini, with its scalar factor and all
integrability internally manufactured from the original smooth form. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ProductComplexManifold
open IntegrationCurrent
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

theorem original_signed_compact_fibre_fubini
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (hVF : ∀ z i, IsThetaPshPotential θ.val (fun x => V i (x, z)))
    (η : SmoothRealForm m Z (2 * m))
    {G : X × Z → ℝ} (hG : Measurable G) {C : ℝ} (hGb : ∀ p, ‖G p‖ ≤ C) :
    Integrable (fun p => topRatio omegaZ.form.val η p.2 * G p)
      (originalJointWedgeMeasure omegaX omegaZ θ γ V hV) ∧
    Integrable (fun z => topRatio omegaZ.form.val η z *
      ∫ x, G (x, z) ∂originalFibreMixedMeasure θ V hVF z) (kahlerVolume omegaZ) ∧
    originalSignedProductCurrentIntegral omegaX omegaZ θ γ V hV η G =
      originalSignedTopFormIntegral omegaZ η
        (fun z => ∫ x, G (x, z) ∂originalFibreMixedMeasure θ V hVF z) := by
  let R := fun p : X × Z => topRatio omegaZ.form.val η p.2 * G p
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_topRatio omegaZ.isKahler.1 η).continuousOn
  have hR : Measurable R :=
    ((continuous_topRatio omegaZ.isKahler.1 η).measurable.comp measurable_snd).mul hG
  have hRb (p : X × Z) : ‖R p‖ ≤ B * C := by
    change ‖topRatio omegaZ.form.val η p.2 * G p‖ ≤ B * C
    rw [norm_mul]
    exact mul_le_mul (hB p.2 (mem_univ _)) (hGb p) (norm_nonneg _)
      ((norm_nonneg _).trans (hB p.2 (mem_univ _)))
  have hglobal := original_compact_fibre_fubini omegaX omegaZ hV hVF hR hRb
  have hinner (z : Z) :
      (∫ x, R (x, z) ∂originalFibreMixedMeasure θ V hVF z) =
      topRatio omegaZ.form.val η z * ∫ x, G (x, z) ∂originalFibreMixedMeasure θ V hVF z :=
    by
      change (∫ x, topRatio omegaZ.form.val η z * G (x, z) ∂originalFibreMixedMeasure θ V hVF z) = _
      exact integral_const_mul (topRatio omegaZ.form.val η z) (fun x => G (x, z))
  refine ⟨hglobal.1, hglobal.2.1.congr (Eventually.of_forall hinner), ?_⟩
  exact hglobal.2.2.trans (integral_congr_ae (Eventually.of_forall hinner))

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment027

section CompactFibreCanonicalFragment028

/-! Entire current source cor:compactfibreslicing. The actual joint and fibre
mixed tuples and their PSH membership, reference pullback, and bounded Borel
canonical difference are manufactured from the unchanged original inputs. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ProductComplexManifold
open IntegrationCurrent RelativeEnergyIntegrability
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] in
def sourceSlicingTuple (φ : X → EReal) (W : X × Z → EReal) (j : ℕ) :
    Fin n → X × Z → EReal := fun i p => if i.val < j then W p else φ p.1

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] in
theorem sourceSlicingTuple_joint_psh
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (hγ : γ.val.IsSemipositive) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W) (j : ℕ) :
    ∀ i : Fin n, IsThetaPshPotential (prodForm θ γ).val (sourceSlicingTuple φ W j i) := by
  intro i
  by_cases hi : i.val < j
  · have heq : sourceSlicingTuple φ W j i = W := by
      funext p
      exact if_pos hi
    rw [heq]
    exact hW
  · have heq : sourceSlicingTuple φ W j i = (fun p => φ p.1) := by
      funext p
      exact if_neg hi
    rw [heq]
    exact ProductPshAssembly.isThetaPshPotential_product_reference θ γ hφ hγ

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] in
theorem sourceSlicingTuple_fibre_psh
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W)
    {C : ℝ} (hlo : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p) (j : ℕ) :
    ∀ (z : Z) (i : Fin n), IsThetaPshPotential θ.val (fun x => sourceSlicingTuple φ W j i (x, z)) := by
  intro z i
  by_cases hi : i.val < j
  · simpa only [sourceSlicingTuple, if_pos hi] using
      CompactFibreSlicing.isThetaPshPotential_fibre θ γ hφ hW hlo z
  · simpa only [sourceSlicingTuple, if_neg hi] using hφ

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] in
def sourceSlicingDifference (φ : X → EReal) (W : X × Z → EReal) : X × Z → ℝ :=
  fun p => canonicalERealDiffToReal (W p) (φ p.1)

def sourceSlicingFibreMeasure
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W)
    {C : ℝ} (hlo : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p) (j : ℕ) (z : Z) : Measure X :=
  originalFibreMixedMeasure θ (sourceSlicingTuple φ W j) (sourceSlicingTuple_fibre_psh hφ hW hlo j) z

omit [CompactSpace X] [CompactSpace Z] in
theorem sourceSlicingDifference_measurable
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W) :
    Measurable (sourceSlicingDifference φ W) :=
  measurable_canonicalERealDiffToReal.comp
    ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hW.1).prodMk
      ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hφ.1).comp measurable_fst))

omit [TopologicalSpace Z] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] in
theorem sourceSlicingDifference_norm_le
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} {C : ℝ} (hC : 0 < C)
    (hlo : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p)
    (hhi : ∀ p : X × Z, W p ≤ φ p.1 + (C : EReal)) (p : X × Z) :
    ‖sourceSlicingDifference φ W p‖ ≤ C := by
  rw [Real.norm_eq_abs]
  exact SingularPerronUniformRelativeBound.canonicalDiff_le_of_extended_bounds
    (hφ.1.quasiPlurisubharmonic.ne_top p.1) hC.le
    (by simpa only [EReal.coe_neg, sub_eq_add_neg] using hlo p) (hhi p)

theorem source_compact_relative_energy_slicing
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (hγ : γ.val.IsSemipositive) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W)
    {C : ℝ} (hC : 0 < C)
    (hlo : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p)
    (hhi : ∀ p : X × Z, W p ≤ φ p.1 + (C : EReal))
    (j : ℕ) (η : SmoothRealForm m Z (2 * m)) :
    originalSignedProductCurrentIntegral omegaX omegaZ θ γ (sourceSlicingTuple φ W j)
      (sourceSlicingTuple_joint_psh hγ hφ hW j) η (sourceSlicingDifference φ W) =
    originalSignedTopFormIntegral omegaZ η
      (fun z => ∫ x, sourceSlicingDifference φ W (x, z) ∂sourceSlicingFibreMeasure hφ hW hlo j z) :=
  (original_signed_compact_fibre_fubini omegaX omegaZ
    (sourceSlicingTuple_joint_psh hγ hφ hW j) (sourceSlicingTuple_fibre_psh hφ hW hlo j) η
    (sourceSlicingDifference_measurable hφ hW) (sourceSlicingDifference_norm_le hφ hC hlo hhi)).2.2

theorem source_compact_fibre_slicing_constant
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (hγ : γ.val.IsSemipositive) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W)
    {C : ℝ} (hlo : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p)
    (η : SmoothRealForm m Z (2 * m)) :
    originalSignedProductCurrentIntegral omegaX omegaZ θ γ (sourceSlicingTuple φ W n)
      (sourceSlicingTuple_joint_psh hγ hφ hW n) η (fun _ => 1) =
    originalSignedTopFormIntegral omegaZ η (fun z => (sourceSlicingFibreMeasure hφ hW hlo n z).real univ) := by
  have h := (original_signed_compact_fibre_fubini omegaX omegaZ
    (sourceSlicingTuple_joint_psh hγ hφ hW n) (sourceSlicingTuple_fibre_psh hφ hW hlo n) η
    (G := fun _ : X × Z => (1 : ℝ)) measurable_const (C := 1) (fun _ => by simp)).2.2
  have heq : (fun z => ∫ x, (1 : ℝ) ∂sourceSlicingFibreMeasure hφ hW hlo n z) =
      (fun z => (sourceSlicingFibreMeasure hφ hW hlo n z).real univ) := by
    funext z
    simp only [integral_const, smul_eq_mul, mul_one]
  exact h.trans (congrArg (originalSignedTopFormIntegral omegaZ η) heq)

theorem source_compact_fibre_slicing
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (hγ : γ.val.IsSemipositive) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W)
    {C : ℝ} (hC : 0 < C)
    (hlo : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p)
    (hhi : ∀ p : X × Z, W p ≤ φ p.1 + (C : EReal)) :
    (∀ z, IsThetaPshPotential θ.val (fun x => W (x, z))) ∧
    (∀ j ≤ n, ∀ η : SmoothRealForm m Z (2 * m),
      originalSignedProductCurrentIntegral omegaX omegaZ θ γ (sourceSlicingTuple φ W j)
        (sourceSlicingTuple_joint_psh hγ hφ hW j) η (sourceSlicingDifference φ W) =
      originalSignedTopFormIntegral omegaZ η
        (fun z => ∫ x, sourceSlicingDifference φ W (x, z) ∂sourceSlicingFibreMeasure hφ hW hlo j z)) ∧
    (∀ η : SmoothRealForm m Z (2 * m),
      originalSignedProductCurrentIntegral omegaX omegaZ θ γ (sourceSlicingTuple φ W n)
        (sourceSlicingTuple_joint_psh hγ hφ hW n) η (fun _ => 1) =
      originalSignedTopFormIntegral omegaZ η (fun z => (sourceSlicingFibreMeasure hφ hW hlo n z).real univ)) :=
  ⟨CompactFibreSlicing.isThetaPshPotential_fibre θ γ hφ hW hlo,
    (fun j _ η => source_compact_relative_energy_slicing omegaX omegaZ hγ hφ hW hC hlo hhi j η),
    (fun η => source_compact_fibre_slicing_constant omegaX omegaZ hγ hφ hW hlo η)⟩

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment028

section CompactFibreCanonicalFragment029

/-! Literal source output: the degree-n constant formula uses n copies of
W itself and its genuine global fibre Monge--Ampere measure. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ProductComplexManifold GlobalNonPluripolar
open IntegrationCurrent
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

omit [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] in
theorem sourceSlicingTuple_top (φ : X → EReal) (W : X × Z → EReal) :
    sourceSlicingTuple (n := n) φ W n = fun _ => W := by
  funext i p
  exact if_pos i.isLt

omit [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] in
theorem sourceSlicingTuple_zero (φ : X → EReal) (W : X × Z → EReal) :
    sourceSlicingTuple (n := n) φ W 0 = fun _ p => φ p.1 := by
  funext i p
  exact if_neg (Nat.not_lt_zero i.val)

theorem source_compact_fibre_slicing_constant_literal
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (hγ : γ.val.IsSemipositive) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W)
    {C : ℝ} (hlo : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p)
    (η : SmoothRealForm m Z (2 * m)) :
    originalSignedProductCurrentIntegral omegaX omegaZ θ γ (fun _ => W) (fun _ => hW) η (fun _ => 1) =
    originalSignedTopFormIntegral omegaZ η
      (fun z => (globalMixedMeasure (fun _ => θ) (fun _ x => W (x, z))
        (fun _ => (CompactFibreSlicing.isThetaPshPotential_fibre θ γ hφ hW hlo z).1)).real univ) := by
  have h := source_compact_fibre_slicing_constant omegaX omegaZ hγ hφ hW hlo η
  simpa only [sourceSlicingFibreMeasure, originalFibreMixedMeasure, sourceSlicingTuple_top] using h

theorem source_compact_fibre_slicing_literal
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    (hγ : γ.val.IsSemipositive) {φ : X → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {W : X × Z → EReal} (hW : IsThetaPshPotential (prodForm θ γ).val W)
    {C : ℝ} (hC : 0 < C)
    (hlo : ∀ p : X × Z, φ p.1 - (C : EReal) ≤ W p)
    (hhi : ∀ p : X × Z, W p ≤ φ p.1 + (C : EReal)) :
    (∀ z, IsThetaPshPotential θ.val (fun x => W (x, z))) ∧
    (∀ j ≤ n, ∀ η : SmoothRealForm m Z (2 * m),
      originalSignedProductCurrentIntegral omegaX omegaZ θ γ (sourceSlicingTuple φ W j)
        (sourceSlicingTuple_joint_psh hγ hφ hW j) η (sourceSlicingDifference φ W) =
      originalSignedTopFormIntegral omegaZ η
        (fun z => ∫ x, sourceSlicingDifference φ W (x, z) ∂sourceSlicingFibreMeasure hφ hW hlo j z)) ∧
    (∀ η : SmoothRealForm m Z (2 * m),
      originalSignedProductCurrentIntegral omegaX omegaZ θ γ (fun _ => W) (fun _ => hW) η (fun _ => 1) =
      originalSignedTopFormIntegral omegaZ η
        (fun z => (globalMixedMeasure (fun _ => θ) (fun _ x => W (x, z))
          (fun _ => (CompactFibreSlicing.isThetaPshPotential_fibre θ γ hφ hW hlo z).1)).real univ)) :=
  ⟨CompactFibreSlicing.isThetaPshPotential_fibre θ γ hφ hW hlo,
    (fun j _ η => source_compact_relative_energy_slicing omegaX omegaZ hγ hφ hW hC hlo hhi j η),
    (fun η => source_compact_fibre_slicing_constant_literal omegaX omegaZ hγ hφ hW hlo η)⟩

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment029

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.mainModule == `SGPT.NPP.SourceCompactFibreSlicing do throwError "Wrong proper module identity: {env.mainModule}"
  let forbidden : Array Name := #[`OriginalCurrentProductDictionaryDraft, `AllDimensionCurrentProductDraft, `GlobalWedgeChartDictionaryDraft, `OriginalProductPotentialsDraft, `OriginalProductPartitionDraft, `PositiveCoefficientMeasureDraft, `FibreTruncationDictionaryDraft, `FibreTruncationMeasureDraft, `CurrentBasePowerMeasureDraft, `SmoothBaseWedgeMeasureDraft, `OriginalBaseFormDictionaryDraft, `PositiveFibreMRegularizationDraft, `NonPluripolarFibreMPositiveDraft, `FibreOriginalMeasureDictionaryDraft, `OriginalGlobalCurrentMeasureDraft, `OriginalFibreIntegralDraft, `BaseVolumeBorelDictionaryDraft, `OriginalOuterFibreIntegralDraft, `RealNonPluripolarFibreDraft, `SignedMultiplierFibreDraft, `LocalSignedCurrentDictionaryDraft, `OriginalLocalCurrentFubiniDraft, `OriginalWedgeMeasureFubiniDraft, `OriginalPartitionTermDraft, `OriginalCompactFubiniDraft, `SignedTopFormDictionaryDraft, `OriginalSignedCurrentDictionaryDraft, `OriginalSignedFubiniDraft, `OriginalCompactSlicingSourceDraft, `LiteralCompactSlicingContractDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m then throwError "Historical flat private provider leaked: {m}"
  logInfo m!"CANONICAL_COMPACT_FIBRE_PAYLOAD module={env.mainModule} proper_root=true old_flat_modules=0"

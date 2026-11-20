import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Okounkov.SmoothDivisorResidualCurrent
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion

set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition
variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Genuine smooth-divisor nullity in every original chart; this is
produced from original geometry, not a measurability or nullity hypothesis. -/
theorem smooth_divisor_chart_ae_notMem
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (e : ComplexChart (m + 1) M) :
    ∀ᵐ z ∂volume.restrict e.val.target, e.val.symm z ∉ W := by
  have hWa : IsComplexAnalyticSubset (n := m + 1) W :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨hW.1, fun x hx => ⟨m, hW.2.2 x hx⟩⟩
  have hnull := (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
    hWa (smooth_divisor_interior_eq_empty hW)).chart_measure_eq_zero e volume
  rw [ae_restrict_iff' e.val.open_target.measurableSet]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz hzt hw
  exact hz ⟨hzt, hw⟩

/-- The actual original potential is recovered pointwise, including divisor
poles, from the genuine residual and its nonnegative divisor multiple. -/
theorem smooth_divisor_residual_recompose
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W) (c : ℝ≥0)
    (hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E c u))) :
    (fun y => extensionAcross W (smoothDivisorOffResidual E c u) y +
      ((c : ℝ) : EReal) * E.weight y) = u := by
  let v := extensionAcross W (smoothDivisorOffResidual E c u)
  have hscaled : ThetaPlurisubharmonic ((c : ℝ) • E.curvature).val
      (fun y => ((c : ℝ) : EReal) * E.weight y) := by
    by_cases hc : c = 0
    · subst c
      simpa only [NNReal.coe_zero, zero_smul, EReal.coe_zero, EReal.zero_mul] using
        (LocalPotentials.thetaPlurisubharmonic_zero_iff
          (0 : ClosedRealOneOneForm (m + 1) M)).mpr
            (by intro e z hz w; simp)
    · exact GlobalMultilinearExpansion.thetaPlurisubharmonic_smul
        (by exact_mod_cast (pos_iff_ne_zero.mpr hc : 0 < c))
        (MeteredDivisorPositivity.thetaPlurisubharmonic_weight E)
  have hraw : ThetaPlurisubharmonic θ.val
      (fun y => v y + ((c : ℝ) : EReal) * E.weight y) := by
    simpa only [sub_add_cancel] using FirstPass.LocalPotentials.thetaPlurisubharmonic_add hv.1 hscaled
  have hoff : ThetaPshOff (θ - (c : ℝ) • E.curvature).val W
      (smoothDivisorOffResidual E c u) := by
    simpa only [hEW] using thetaPshOff_smoothDivisorOffResidual hu E c
  have hae (e : ComplexChart (m + 1) M) :
      (fun z => v (e.val.symm z) + ((c : ℝ) : EReal) * E.weight (e.val.symm z))
        =ᵐ[volume.restrict e.val.target] (fun z => u (e.val.symm z)) := by
    filter_upwards [smooth_divisor_chart_ae_notMem hW e] with z hzW
    have hzE : e.val.symm z ∉ E.support := by rw [hEW]; exact hzW
    obtain ⟨F, _hF, hFeq⟩ :=
      MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E hzE
    have hweight : E.weight (e.val.symm z) = (F (e.val.symm z) : EReal) :=
      Filter.EventuallyEq.eq_of_nhds
        (show E.weight =ᶠ[𝓝 (e.val.symm z)] (fun y => (F y : EReal)) from hFeq)
    dsimp only [v]
    rw [extensionAcross_eq_of_notMem hW.1 hoff hzW]
    simp only [smoothDivisorOffResidual, if_neg hzE, hweight, ← EReal.coe_mul]
    exact EReal.sub_add_cancel
  exact funext fun y => le_antisymm
    (RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hraw hu.1
      (fun e => (hae e).mono fun _ h => h.le) y)
    (RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hu.1 hraw
      (fun e => (hae e).mono fun _ h => h.ge) y)
end SGPT.Okounkov

set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov
open Set Filter Metric
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending BlowupFlatCoordinates
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition
private theorem euclidean_reader_add_continuous {n : ℕ}
    (u : ComplexModel n → EReal) (h : ComplexModel n → ℝ) (x : ComplexModel n)
    (hh : ContinuousAt h x) :
    lelongNumber (n := n) (fun y => u y + (h y : EReal)) x =
      lelongNumber (n := n) u x := by
  exact LelongChartReaderInvariance.lelongNumber_add_continuous_eq
    (n := n) (M := ComplexModel n) (u := u) (h := h) (x := x) hh

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual unit vanishing ideal, genuine same-generator metric and
original flattening give the original point reader exactly one. -/
theorem squaredLogLelongNumber_divisor_metric_eq_one
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hmetric : DivisorMetric.IsDivisorMetric D E)
    {p : M} (hp : p ∈ W) : squaredLogLelongNumber (n := m + 1) E.weight p = 1 := by
  let e := complexChartAt (n := m + 1) p
  obtain ⟨_hle, _hp, Φ, hΦe, hΦ0, hflat⟩ := hW.2.2 p hp
  obtain ⟨V, ell, hV, hpV, hVF, hell, hweight⟩ :=
    exists_divisor_metric_flat_normal_form Φ hΦe hflat hW D hDI E hmetric
  let Ψ := fun z => e.val.symm (Φ.invFun z)
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hi0 : Φ.invFun (0 : ComplexModel (m + 1)) = e.val p := by
    rw [← hΦ0, Φ.left_inv _ Φ.center_mem_source]
  have h0T : (0 : ComplexModel (m + 1)) ∈ Φ.target := by
    rw [← hΦ0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hΨ : Tendsto Ψ (𝓝 0) (𝓝 p) := by
    have h := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
    change Tendsto Ψ (𝓝 (Φ.toFun (e.val p))) (𝓝 p) at h
    rwa [hΦ0] at h
  have hell0 : ContinuousAt (fun z => ell (Ψ z)) 0 := by
    have hc : ContinuousAt (fun z => ell (e.val.symm z)) (Φ.invFun 0) := by
      rw [hi0]
      exact (hell e).continuousOn.continuousAt
        ((e.val.isOpen_inter_preimage_symm hV).mem_nhds
          ⟨e.val.map_source hpe, by
            change e.val.symm (e.val p) ∈ V
            rwa [e.val.left_inv hpe]⟩)
    exact hc.comp (Φ.invFun_holomorphic.continuousOn.continuousAt
      (Φ.isOpen_target.mem_nhds h0T))
  have hgerm : (fun z => chartFunction E.weight e (Φ.invFun z)) =ᶠ[𝓝 0]
      (fun z : ComplexModel (m + 1) => logNormSq (z (Fin.last m)) + (ell (Ψ z) : EReal)) := by
    filter_upwards [Φ.isOpen_target.mem_nhds h0T, hΨ.eventually (hV.mem_nhds hpV)]
      with z hzT hzV
    change E.weight (Ψ z) = _
    rw [hweight _ hzV]
    have hcoord : flatCoord Φ (Fin.last m) (Ψ z) = z (Fin.last m) :=
      congrArg (fun w => w (Fin.last m)) (flatInverse_mem Φ hzT hΦe).2
    rw [hcoord]
  have hnative : lelongNumber (n := m + 1) E.weight p = 2 := by
    calc
      _ = lelongNumber (n := m + 1) (chartFunction E.weight e) (e.val p) :=
        (LelongChartReaderInvariance.lelongNumber_chartFunction_eq e hpe).symm
      _ = lelongNumber (n := m + 1)
          (fun z => chartFunction E.weight e (Φ.invFun z)) 0 := by
        simpa only [hΦ0] using
          (LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq Φ
            Φ.center_mem_source (u := chartFunction E.weight e)).symm
      _ = lelongNumber (n := m + 1)
          (fun z : ComplexModel (m + 1) => logNormSq (z (Fin.last m)) + (ell (Ψ z) : EReal)) 0 :=
        LelongNumberComparison.lelongNumber_congr hgerm
      _ = lelongNumber (n := m + 1) (fun z : ComplexModel (m + 1) => logNormSq (z (Fin.last m))) 0 :=
        euclidean_reader_add_continuous (n := m + 1)
          (fun z : ComplexModel (m + 1) => logNormSq (z (Fin.last m))) (fun z => ell (Ψ z)) 0 hell0
      _ = 2 := by
        simpa only [NNReal.coe_one, EReal.coe_one, ENNReal.coe_one, one_mul, mul_one] using
          lelongNumber_scaled_logNormSq_eq (Fin.last m) (x := 0) rfl (c := 1) one_pos
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  simpa only [mul_one] using
    (lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m) E.weight p).symm.trans hnative

/-- The actual whole-carrier source infimum has the genuine unit value. -/
theorem sourceGeneric_divisor_metric_eq_one
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hmetric : DivisorMetric.IsDivisorMetric D E) :
    sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) E.weight = 1 := by
  obtain ⟨p, hp⟩ := hW.2.1.nonempty
  let : Nonempty W := ⟨⟨p, hp⟩⟩
  unfold sourceGenericLelongNumber
  simp_rw [squaredLogLelongNumber_divisor_metric_eq_one hW D hDI E hmetric (Subtype.property _)]
  exact ciInf_const
end SGPT.Okounkov


namespace SGPT.Okounkov
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition
variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
/-- The genuine thin support supplies original nondegeneracy of the actual
metered weight, without a nondegeneracy certificate. -/
theorem isThetaPshPotential_divisor_weight_of_smooth_support
    {W : Set M} (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W) :
    IsThetaPshPotential E.curvature.val E.weight := by
  refine ⟨MeteredDivisorPositivity.thetaPlurisubharmonic_weight E, ?_⟩
  intro x U hU hxU
  have hdense : Dense Wᶜ := interior_eq_empty_iff_dense_compl.mp
    (smooth_divisor_interior_eq_empty hW)
  obtain ⟨y, hyU, hyW⟩ := hdense.inter_open_nonempty U hU ⟨x, hxU⟩
  refine ⟨y, hyU, ?_⟩
  change y ∉ E.support
  rwa [hEW]

/-- The original finite source coefficient cancels in the genuine pointwise
recomposition and checked generic arithmetic, producing actual generic zero. -/
theorem sourceGeneric_smooth_divisor_residual_eq_zero
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W)
    (hmetric : DivisorMetric.IsDivisorMetric D E)
    (hv : IsThetaPshPotential
      (θ - ((sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal : ℝ) •
        E.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal u))) :
    sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (extensionAcross W (smoothDivisorOffResidual E
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal u)) = 0 := by
  let c : ℝ≥0 :=
    (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
  let v := extensionAcross W (smoothDivisorOffResidual E c u)
  have hc : (c : ℝ≥0∞) =
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u :=
    ENNReal.coe_toNNReal (sourceGeneric_subtype_ne_top hW hu.quasiPshPotential)
  have hscaled : IsGlobalQuasiPshPotential (n := m + 1)
      (fun y => ((c : ℝ) : EReal) * E.weight y) := by
    by_cases hc0 : c = 0
    · rw [hc0]
      simpa only [NNReal.coe_zero, EReal.coe_zero, EReal.zero_mul] using
        isGlobalQuasiPshPotential_const (n := m + 1) (M := M) 0
    · exact (RestrictedApproximantComparison.isThetaPshPotential_smul
        (isThetaPshPotential_divisor_weight_of_smooth_support hW E hEW)
        (by exact_mod_cast (pos_iff_ne_zero.mpr hc0 : 0 < c))).quasiPshPotential
  have hread : sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
      (fun y => ((c : ℝ) : EReal) * E.weight y) = (c : ℝ≥0∞) := by
    by_cases hc0 : c = 0
    · rw [hc0]
      simpa only [NNReal.coe_zero, EReal.coe_zero, EReal.zero_mul, ENNReal.coe_zero] using
        sourceGeneric_subtype_zero (n := m + 1) hW.2.1.nonempty
    · have hscale := flagGenericLelong_smul_eq (n := m + 1)
        (fun _ : Fin (m + 2) => W) E.weight (0 : Fin (m + 2))
        (by exact_mod_cast (pos_iff_ne_zero.mpr hc0 : 0 < c))
      change sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
        (fun y => ((c : ℝ) : EReal) * E.weight y) =
        ENNReal.ofReal (c : ℝ) *
          sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) E.weight at hscale
      rw [sourceGeneric_divisor_metric_eq_one hW D hDI E hmetric, mul_one,
        ENNReal.ofReal_coe_nnreal] at hscale
      exact hscale
  have hgen := sourceGeneric_subtype_add_eq hW hv.quasiPshPotential hscaled
  rw [smooth_divisor_residual_recompose hu hW E hEW c hv, hread] at hgen
  have hgen' : (c : ℝ≥0∞) =
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v + (c : ℝ≥0∞) :=
    hc.trans hgen
  change sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) v = 0
  apply (ENNReal.add_right_inj (a := (c : ℝ≥0∞)) ENNReal.coe_ne_top).mp
  simpa only [add_comm, add_zero, zero_add] using hgen'.symm

/-- Original geometry and original theta-PSH data internally produce the
normalized residual potential with its genuine source generic zero. -/
theorem exists_normalized_smooth_divisor_residual_generic_zero [CompactSpace M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
        DivisorMetric.IsDivisorMetric D E ∧
        IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
          (extensionAcross W (smoothDivisorOffResidual E c u)) ∧
        sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M)
          (extensionAcross W (smoothDivisorOffResidual E c u)) = 0 := by
  obtain ⟨D, hDI, E, hEW, hmetric, hv⟩ :=
    exists_normalized_smooth_divisor_residual_potential hu hW
  exact ⟨D, hDI, E, hEW, hmetric, hv,
    sourceGeneric_smooth_divisor_residual_eq_zero hu hW D hDI E hEW hmetric hv⟩

end SGPT.Okounkov

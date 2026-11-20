import SGPT.Okounkov.FlattenedDivisorMetric
import SGPT.Foundations.Analysis.Pending.PshRemovableSingularity
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open Set Filter Metric
open scoped Topology Manifold ContDiff ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open ThetaPshCodimTwoExtension
open BlowupFlatCoordinates
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual unbounded off-divisor difference. Values on the divisor are
replaced by bottom solely to form the independently defined upper extension. -/
def smoothDivisorOffResidual (E : MeteredEffectiveQDivisor n M) (c : ℝ) (u : M → EReal) :
    M → EReal := by
  classical
  exact fun x => if x ∈ E.support then ⊥ else u x - (c : EReal) * E.weight x

private theorem sub_real_add_real_cancel (a : EReal) (b r : ℝ) :
    a - (b : EReal) + ((r + b : ℝ) : EReal) = a + (r : EReal) := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => simp only [← EReal.coe_sub, ← EReal.coe_add]; congr 1; ring

/-- Every original theta-PSH potential produces its literal residual theta-PSH
germ off the actual metered divisor, with no finite/bounded residual premise. -/
theorem thetaPshOff_smoothDivisorOffResidual
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (E : MeteredEffectiveQDivisor n M) (c : ℝ) :
    ThetaPshOff (θ - c • E.curvature).val E.support (smoothDivisorOffResidual E c u) := by
  intro e z hz hzsupp
  have hxsource : e.val.symm z ∈ e.val.source := e.val.map_target hz
  obtain ⟨W₁, hzW₁, hpot₁⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature E hzsupp e hxsource
  rw [e.val.right_inv hz] at hzW₁
  obtain ⟨W₂, ρ₂, hzW₂, hpot₂, hpsh₂⟩ := hu.1 e z hz
  obtain ⟨F, _hF, hFeq⟩ :=
    MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E hzsupp
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hFeq
  let W₃ := e.val.target ∩ e.val.symm ⁻¹' U
  have hW₃ : IsOpen W₃ := e.val.isOpen_inter_preimage_symm hU
  let W := (W₁ ∩ W₂) ∩ W₃
  have hW : IsOpen W := (hpot₁.1.inter hpot₂.1).inter hW₃
  have hWW₁ : W ⊆ W₁ := inter_subset_left.trans inter_subset_left
  have hWW₂ : W ⊆ W₂ := inter_subset_left.trans inter_subset_right
  have hzW : z ∈ W := ⟨⟨hzW₁, hzW₂⟩, hz, hxU⟩
  have hpot₁' := hpot₁.mono hW hWW₁
  have hpot₂' := hpot₂.mono hW hWW₂
  refine ⟨W, fun y => ρ₂ y + c * (E.weight (e.val.symm y)).toReal, hzW, ?_, ?_⟩
  · simpa only [smul_neg, sub_eq_add_neg, smul_eq_mul] using
      FirstPass.LocalPotentials.localPotential_add hpot₂'
        (FirstPass.LocalPotentials.localPotential_smul hpot₁' c)
  · refine plurisubharmonicOn_congr hW (hpsh₂.mono hWW₂) ?_
    intro y hy
    have hweight : E.weight (e.val.symm y) =
        (((E.weight (e.val.symm y)).toReal : ℝ) : EReal) := by
      rw [hUsub hy.2.2, EReal.toReal_coe]
    have hyoff : e.val.symm y ∉ E.support := by
      change E.weight (e.val.symm y) ≠ ⊥
      rw [hweight]
      exact EReal.coe_ne_bot _
    simp only [chartFunction, smoothDivisorOffResidual, if_neg hyoff]
    rw [hweight, ← EReal.coe_mul]
    exact (sub_real_add_real_cancel (u (e.val.symm y))
      (c * (E.weight (e.val.symm y)).toReal) (ρ₂ y)).symm

private theorem residual_from_real_decomposition (a q : EReal) (c l r e : ℝ)
    (h : a + (r : EReal) = ((c * l : ℝ) : EReal) + q) :
    a - ((c * (l + e) : ℝ) : EReal) = q - ((r + c * e : ℝ) : EReal) := by
  have hq : q = a + (r : EReal) - ((c * l : ℝ) : EReal) := by
    rw [h, EReal.add_sub_cancel_left]
  rw [hq]
  induction a using EReal.rec with
  | bot => simp
  | top => simp only [EReal.top_sub_coe, EReal.top_add_coe]
  | coe a => simp only [← EReal.coe_sub, ← EReal.coe_add]; congr 1; ring

variable {m : ℕ}

/-- The original local residual and original metric in the SAME chosen
flattening produce an actual finite bound for the literal off-divisor
residual. Smooth lower bounds are produced from continuity, never assumed. -/
theorem exists_flat_residual_upper_bound_of_metric_normal_form
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ : SmoothRealForm (m + 1) M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) (p : M) (hp : p ∈ W)
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) p).val p))
    (hΦe : Φ.source ⊆ (complexChartAt (n := m + 1) p).val.target)
    (hΦ0 : Φ.toFun ((complexChartAt (n := m + 1) p).val p) = 0)
    (hflat : ∀ {y : M}, y ∈ (complexChartAt (n := m + 1) p).val.source →
      (complexChartAt (n := m + 1) p).val y ∈ Φ.source →
      (y ∈ W ↔ Φ.toFun ((complexChartAt (n := m + 1) p).val y) ∈
        complexCoordinatePlane (m + 1) m))
    (E : MeteredEffectiveQDivisor (m + 1) M) {V : Set M}
    (hV : IsOpen V) (hpV : p ∈ V) (_hVF : V ⊆ flatDomain Φ)
    (ell : M → ℝ)
    (hell : ∀ e : ComplexChart (m + 1) M, ContDiffOn ℝ ∞
      (fun z => ell (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' V))
    (hweight : ∀ y ∈ V,
      E.weight y = logNormSq (flatCoord Φ (Fin.last m) y) + (ell y : EReal)) :
    ∃ c : ℝ≥0,
      (c : ℝ≥0∞) = sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u ∧
      ∃ r B : ℝ, 0 < r ∧ ball 0 r ⊆ Φ.target ∧
        ∀ z ∈ ball 0 r,
          (complexChartAt (n := m + 1) p).val.symm (Φ.invFun z) ∉ W →
          smoothDivisorOffResidual E c u
            ((complexChartAt (n := m + 1) p).val.symm (Φ.invFun z)) ≤ (B : EReal) := by
  let e := complexChartAt (n := m + 1) p
  let Ψ := fun z => e.val.symm (Φ.invFun z)
  obtain ⟨c, hc, ρ, r, C, q, hr, hrT, hρ, hWiff, _hq, hqb, heq, _hmin⟩ :=
    exists_smooth_divisor_local_residual_of_flattening hu hW p hp Φ hΦe hΦ0 hflat
  have hi0 : Φ.invFun (0 : ComplexModel (m + 1)) = e.val p := by
    rw [← hΦ0, Φ.left_inv _ Φ.center_mem_source]
  have h0T : (0 : ComplexModel (m + 1)) ∈ Φ.target := hrT (mem_ball_self hr)
  have hΨ : Tendsto Ψ (𝓝 0) (𝓝 p) := by
    have h := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
    change Tendsto Ψ (𝓝 (Φ.toFun (e.val p))) (𝓝 p) at h
    rwa [hΦ0] at h
  have hρc : ContinuousAt (fun z => ρ (Φ.invFun z)) 0 :=
    (hρ 0 (mem_ball_self hr)).continuousAt.comp
      (Φ.invFun_holomorphic.continuousOn.continuousAt (Φ.isOpen_target.mem_nhds h0T))
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  let S := fun z => ρ (Φ.invFun z) + (c : ℝ) * ell (Ψ z)
  have hS : ContinuousAt S 0 := by
    have hchart : ContinuousAt (fun z => ell (e.val.symm z)) (Φ.invFun 0) := by
      rw [hi0]
      exact (hell e).continuousOn.continuousAt
        ((e.val.isOpen_inter_preimage_symm hV).mem_nhds
          ⟨e.val.map_source hpe, by
            change e.val.symm (e.val p) ∈ V
            rwa [e.val.left_inv hpe]⟩)
    exact hρc.add (continuousAt_const.mul
      (hchart.comp (Φ.invFun_holomorphic.continuousOn.continuousAt
        (Φ.isOpen_target.mem_nhds h0T))))
  have hSbound : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), S 0 - 1 < S z :=
    hS.eventually (eventually_gt_nhds (by linarith))
  have hnear : {z | z ∈ ball 0 r ∧ Ψ z ∈ V ∧ S 0 - 1 < S z} ∈ 𝓝 0 :=
    inter_mem (isOpen_ball.mem_nhds (mem_ball_self hr))
      (inter_mem (hΨ.eventually (hV.mem_nhds hpV)) hSbound)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨c, hc, δ, C - (S 0 - 1), hδ, fun z hz => hrT (hδsub hz).1, ?_⟩
  intro z hz hzW
  have hzdata := hδsub hz
  have hzT := hrT hzdata.1
  have hzV := hzdata.2.1
  have hz0 : z (Fin.last m) ≠ 0 := fun h => hzW ((hWiff z hzdata.1).mpr h)
  have hcoord : flatCoord Φ (Fin.last m) (Ψ z) = z (Fin.last m) := by
    have h := (flatInverse_mem Φ hzT hΦe).2
    exact congrArg (fun w => w (Fin.last m)) h
  let l := Real.log (Complex.normSq (z (Fin.last m)))
  have hlog : logNormSq (z (Fin.last m)) = (l : EReal) := by
    rw [logNormSq, ENNReal.log_ofReal_of_pos (pow_pos (norm_pos_iff.mpr hz0) 2)]
    simp only [l, Complex.normSq_eq_norm_sq]
  have hweight' : E.weight (Ψ z) = ((l + ell (Ψ z) : ℝ) : EReal) := by
    rw [hweight _ hzV, hcoord, hlog, ← EReal.coe_add]
  have hzoff : Ψ z ∉ E.support := by
    change E.weight (Ψ z) ≠ ⊥
    rw [hweight']
    exact EReal.coe_ne_bot _
  have heq' : u (Ψ z) + (ρ (Φ.invFun z) : EReal) =
      (((c : ℝ) * l : ℝ) : EReal) + q z := by
    simpa only [chartFunction, Ψ, hlog, ← EReal.coe_mul] using heq z hzdata.1
  have hres : smoothDivisorOffResidual E c u (Ψ z) = q z - (S z : EReal) := by
    simp only [smoothDivisorOffResidual, if_neg hzoff, hweight', ← EReal.coe_mul]
    exact residual_from_real_decomposition _ _ (c : ℝ) l _ _ heq'
  rw [hres]
  have hSle : ((S 0 - 1 : ℝ) : EReal) ≤ (S z : EReal) :=
    EReal.coe_le_coe hzdata.2.2.le
  have hbound := EReal.sub_le_sub (hqb z hzdata.1) hSle
  simpa only [← EReal.coe_sub] using hbound

/-- The same actual metric of the original vanishing ideal supplies the
true residual bound; no coefficient or residual-bound certificate is input. -/
theorem smooth_divisor_off_residual_locallyBounded_of_metric
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M) (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W)
    (hmetric : DivisorMetric.IsDivisorMetric D E) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    PshAnalyticSetExtension.LocallyBoundedAboveOff W (smoothDivisorOffResidual E c u) := by
  let c : ℝ≥0 :=
    (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
  have hc : (c : ℝ≥0∞) =
      sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u :=
    ENNReal.coe_toNNReal (sourceGeneric_subtype_ne_top hW hu.quasiPshPotential)
  change PshAnalyticSetExtension.LocallyBoundedAboveOff W (smoothDivisorOffResidual E c u)
  intro p
  by_cases hp : p ∈ W
  · let e := complexChartAt (n := m + 1) p
    obtain ⟨_hle, _hp, Φ, hΦe, hΦ0, hflat⟩ := hW.2.2 p hp
    obtain ⟨V, ell, hV, hpV, hVF, hell, hweight⟩ :=
      exists_divisor_metric_flat_normal_form Φ hΦe hflat hW D hDI E hmetric
    obtain ⟨c', hc', r, B, hr, _hrT, hbound⟩ :=
      exists_flat_residual_upper_bound_of_metric_normal_form hu hW p hp Φ hΦe hΦ0 hflat
        E hV hpV hVF ell hell hweight
    have hcc : c' = c := ENNReal.coe_injective (hc'.trans hc.symm)
    subst c'
    have hpe : p ∈ e.val.source := mem_complexChartAt_source p
    have hmap : ContinuousAt (fun y => Φ.toFun (e.val y)) p :=
      (Φ.toFun_holomorphic.continuousOn.continuousAt
        (Φ.isOpen_source.mem_nhds Φ.center_mem_source)).comp (e.val.continuousAt hpe)
    let U := {y : M | y ∈ flatDomain Φ ∧ Φ.toFun (e.val y) ∈ ball 0 r}
    have hball : ∀ᶠ y in 𝓝 p, Φ.toFun (e.val y) ∈ ball 0 r :=
      hmap.eventually (show ball 0 r ∈ 𝓝 (Φ.toFun (e.val p)) from by
        rw [hΦ0]
        exact isOpen_ball.mem_nhds (mem_ball_self hr))
    have hU : U ∈ 𝓝 p := inter_mem
      ((isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ))
      hball
    refine ⟨U, hU, B, ?_⟩
    intro y hy hyW
    have hinv : e.val.symm (Φ.invFun (Φ.toFun (e.val y))) = y :=
      flatInverse_flat Φ hy.1
    have h := hbound (Φ.toFun (e.val y)) hy.2 (by rwa [hinv])
    rwa [hinv] at h
  · have hpE : p ∉ E.support := by rwa [hEW]
    obtain ⟨F, _hF, hFeq⟩ :=
      MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E hpE
    have hweightp : E.weight p = (F p : EReal) := Filter.EventuallyEq.eq_of_nhds
      (show E.weight =ᶠ[𝓝 p] (fun y => (F y : EReal)) from hFeq)
    obtain ⟨A, hA, _⟩ := EReal.exists_between_coe_real
      (lt_top_iff_ne_top.mpr (hu.1.quasiPlurisubharmonic.ne_top p))
    have hle : smoothDivisorOffResidual E c u p ≤
        ((A - (c : ℝ) * F p : ℝ) : EReal) := by
      simp only [smoothDivisorOffResidual, if_neg hpE, hweightp, ← EReal.coe_mul]
      simpa only [← EReal.coe_sub] using
        EReal.sub_le_sub hA.le (le_refl (((c : ℝ) * F p : ℝ) : EReal))
    have hnt : smoothDivisorOffResidual E c u p ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
    obtain ⟨B, hB, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hnt)
    have husc := upperSemicontinuousAt_of_thetaPshOff
      (thetaPshOff_smoothDivisorOffResidual hu E c) hpE
    exact ⟨{y | smoothDivisorOffResidual E c u y < (B : EReal)}, husc _ hB,
      B, fun y hy _ => hy.le⟩


/-- Original compact smooth-divisor geometry supplies one global divisor
metric for which the actual original residual is locally bounded above
at EVERY original point. The original generic coefficient is unchanged. -/
theorem exists_normalized_smooth_divisor_off_residual_locallyBounded
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
        DivisorMetric.IsDivisorMetric D E ∧
      PshAnalyticSetExtension.LocallyBoundedAboveOff W (smoothDivisorOffResidual E c u) := by
  obtain ⟨D, hDI, E, hEW, hmetric, _hnormal⟩ :=
    exists_normalized_smooth_divisor_metric_normal_forms hW
  exact ⟨D, hDI, E, hEW, hmetric,
    smooth_divisor_off_residual_locallyBounded_of_metric hu hW D hDI E hEW hmetric⟩


/-- Original compact smooth-divisor geometry supplies one global divisor
metric for which the actual original residual is locally bounded above
at EVERY original point. The original generic coefficient is unchanged. -/
theorem exists_smooth_divisor_off_residual_locallyBounded
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
      PshAnalyticSetExtension.LocallyBoundedAboveOff W (smoothDivisorOffResidual E c u) := by
  obtain ⟨D, _hDI, E, hEW, _hmetric, hbound⟩ :=
    exists_normalized_smooth_divisor_off_residual_locallyBounded hu hW
  exact ⟨E, hEW, hbound⟩

private theorem sub_coe_ne_bot_of_ne_bot {a : EReal} (ha : a ≠ ⊥) (r : ℝ) :
    a - (r : EReal) ≠ ⊥ := by
  induction a using EReal.rec with
  | bot => exact False.elim (ha rfl)
  | top => simp only [EReal.top_sub_coe, ne_eq, top_ne_bot, not_false_eq_true]
  | coe a => rw [← EReal.coe_sub]; exact EReal.coe_ne_bot _

/-- The existing complete residual-extension proof for any SAME genuine
unit metric. All original local bounds and nondegeneracy are produced. -/
theorem isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m)
    (D : EffectiveDivisor (m + 1) M)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) W)
    (E : MeteredEffectiveQDivisor (m + 1) M) (hEW : E.support = W)
    (hmetric : DivisorMetric.IsDivisorMetric D E) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E c u)) := by
  let c : ℝ≥0 :=
    (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
  have hbound := smooth_divisor_off_residual_locallyBounded_of_metric hu hW D hDI E hEW hmetric
  have hoff : ThetaPshOff (θ - (c : ℝ) • E.curvature).val W
      (smoothDivisorOffResidual E c u) := by
    simpa only [hEW] using thetaPshOff_smoothDivisorOffResidual hu E c
  have hWa : IsComplexAnalyticSubset (n := m + 1) W :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨hW.1, fun x hx => ⟨m, hW.2.2 x hx⟩⟩
  have hpot := LocalPotentials.closedRealOneOne_hasLocalPotentials
    (θ - (c : ℝ) • E.curvature)
  have hraw : ThetaPlurisubharmonic (θ - (c : ℝ) • E.curvature).val
      (extensionAcross W (smoothDivisorOffResidual E c u)) :=
    PshAnalyticSetExtension.thetaPlurisubharmonic_extensionAcross_of_localClosure hW.1 hoff
      (PshAnalyticRemovable.thetaPshLocalClosure_of_isComplexAnalyticSubset hpot hWa hoff hbound)
  refine ⟨hraw, ?_⟩
  intro x U hU hxU
  have hdense : Dense Wᶜ := interior_eq_empty_iff_dense_compl.mp
    (smooth_divisor_interior_eq_empty hW)
  obtain ⟨p, hpU, hpW⟩ := hdense.inter_open_nonempty U hU ⟨x, hxU⟩
  obtain ⟨y, hy, huy⟩ := hu.2 p (U ∩ Wᶜ) (hU.inter hW.1.isOpen_compl) ⟨hpU, hpW⟩
  refine ⟨y, hy.1, ?_⟩
  rw [extensionAcross_eq_of_notMem hW.1 hoff hy.2]
  have hyE : y ∉ E.support := by rw [hEW]; exact hy.2
  obtain ⟨F, _hF, hFeq⟩ :=
    MeteredDivisorWeightBounds.exists_real_continuousAt_eventuallyEq_of_notMem_support E hyE
  have hweighty : E.weight y = (F y : EReal) := Filter.EventuallyEq.eq_of_nhds
    (show E.weight =ᶠ[𝓝 y] (fun z => (F z : EReal)) from hFeq)
  simp only [smoothDivisorOffResidual, if_neg hyE, hweighty, ← EReal.coe_mul]
  exact sub_coe_ne_bot_of_ne_bot huy _


/-- The actual original generic coefficient and actual compact smooth
divisor produce the genuine global residual potential by analytic extension.
Both local boundedness and nondegeneracy are consequences of the original
data; neither is supplied as a target certificate. -/
theorem exists_normalized_smooth_divisor_residual_potential
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ D : EffectiveDivisor (m + 1) M, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
        DivisorMetric.IsDivisorMetric D E ∧
      IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
        (extensionAcross W (smoothDivisorOffResidual E c u)) := by
  obtain ⟨D, hDI, E, hEW, hmetric, _hbound⟩ :=
    exists_normalized_smooth_divisor_off_residual_locallyBounded hu hW
  exact ⟨D, hDI, E, hEW, hmetric,
    isThetaPshPotential_smooth_divisor_residual_of_unit_metric hu hW D hDI E hEW hmetric⟩

/-- The actual original generic coefficient and actual compact smooth
divisor produce the genuine global residual potential by analytic extension.
Both local boundedness and nondegeneracy are consequences of the original
data; neither is supplied as a target certificate. -/
theorem exists_smooth_divisor_residual_potential
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {W : Set M}
    (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → M) u).toNNReal
    ∃ E : MeteredEffectiveQDivisor (m + 1) M, E.support = W ∧
      IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
        (extensionAcross W (smoothDivisorOffResidual E c u)) := by
  obtain ⟨D, _hDI, E, hEW, _hmetric, hv⟩ :=
    exists_normalized_smooth_divisor_residual_potential hu hW
  exact ⟨E, hEW, hv⟩

end SGPT.Okounkov

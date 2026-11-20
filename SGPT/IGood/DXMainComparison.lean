import SGPT.IGood.DXMainSections
import SGPT.PSH.MultiplierIdealInfSkoda
import SGPT.Foundations.Analysis.Pending.RestrictedIdealWeight

/-!
# From `𝓘(kψ)` to `𝓘_∞`: normalized section potentials below `(1 - t) ψ`

Infrastructure for the upper bound in the asymptotic Riemann–Roch formula `thm:DXmain1`, blueprint
`claude-dxmain:iinfty-comparison`. Setting as in `SGPT.IGood.DXMainSections`.

## Main results

* `isIdealSection_multiplierIdeal_of_singularityLE`: `φ ⪯ ψ` (`φ ≤ ψ + C`, `ψ` quasi-psh) gives
  `H⁰(X, L^k ⊗ 𝓘(kφ)) ⊆ H⁰(X, L^k ⊗ 𝓘(kψ))`.
* `exists_singularityLE_normalizedPotential` (the use of `lma:IandIinf` in Step 1 of the proof of
  `thm:Gammaasg`): for `ψ` with analytic singularities and `t ∈ (0, 1)`, there is `k₀` such that
  for every `k ≥ k₀` and every nonzero `s ∈ H⁰(X, L^k ⊗ 𝓘(kψ))`, the normalized potential
  `ψ_s = k⁻¹ log |s|²_{H^k}` satisfies `ψ_s ≤ (1 - t) ψ + C_s` on `X`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.DXMain

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.LineBundle SGPT.PSH
open scoped Topology ENNReal

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance dxCompTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxCompCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dxCompManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules}

/-- `φ ⪯ ψ` with `ψ` quasi-psh gives `𝓘(kφ) ⊆ 𝓘(kψ)` on sections. -/
theorem isIdealSection_multiplierIdeal_of_singularityLE {φ ψ : SchemeComplexPoint f → EReal}
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (hle : SingularityLE φ ψ) {k : ℕ} (hk : 0 < k) {s : bundlePowerGlobalSections L k}
    (hs : IsMultiplierSection f n E φ k s) :
    IsIdealSection f n E (multiplierIdeal (n := n) (k : ℝ) ψ) k s := by
  let := E.isSeparated
  let := E.quasiCompact
  rcases hs with h0 | hs
  · exact absurd h0 hk.ne'
  intro U α p hp
  obtain ⟨hhol, hint⟩ := hs U α p hp
  refine ⟨hhol, ?_⟩
  set e := complexChartAt (n := n) p
  have hz := e.val.map_source (mem_complexChartAt_source p)
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real φ ψ).mp hle
  exact multiplierIntegrableAt_of_moreSingularAt (hψ e _ hz)
    ⟨C, Filter.Eventually.of_forall fun z => hC _⟩ hint

/-- The frame weight `log |α|²_H` is bounded above near every point of the frame domain. -/
theorem eventually_log_frameNormSq_le (H : SchemeLineBundleMetric f n E L) {U : X.Opens}
    (α : LocalBundleFrame L U) {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    ∃ B : ℝ, ∀ᶠ q in 𝓝 p, Real.log (H.frameNormSq α q) ≤ B := by
  let := E.isSeparated
  let := E.quasiCompact
  set e := complexChartAt (n := n) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  have hcont : ContinuousAt (fun z => H.frameNormSq α (e.val.symm z)) (e.val p) :=
    ((H.smooth α e).continuousOn).continuousAt (hD.mem_nhds hz0D)
  have he : ContinuousAt e.val p := e.val.continuousAt hpe
  have hcomp : ContinuousAt (fun q => H.frameNormSq α (e.val.symm (e.val q))) p :=
    hcont.comp he
  have hev : (fun q => H.frameNormSq α (e.val.symm (e.val q))) =ᶠ[𝓝 p] H.frameNormSq α := by
    filter_upwards [e.val.open_source.mem_nhds hpe] with q hq
    rw [e.val.left_inv hq]
  have hcont' : ContinuousAt (H.frameNormSq α) p := hcomp.congr hev
  refine ⟨Real.log (H.frameNormSq α p + 1), ?_⟩
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' U) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hcont'.eventually (gt_mem_nhds (lt_add_one (H.frameNormSq α p))),
    hU.mem_nhds hp] with q hq hqU
  exact Real.log_le_log (H.positive α q hqU) hq.le

/-- **From `𝓘` to `𝓘_∞`** (`lma:IandIinf`): for `ψ` with analytic singularities and `t ∈ (0, 1)`
there is `k₀ > 0` such that for all `k ≥ k₀` and every nonzero `s ∈ H⁰(X, L^k ⊗ 𝓘(kψ))`,
`k⁻¹ log |s|²_{H^k} ≤ (1 - t) ψ + C` on `X`. -/
theorem exists_singularityLE_normalizedPotential (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f n E L) {ψ : SchemeComplexPoint f → EReal}
    (hψ : QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) ψ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ s : bundlePowerGlobalSections L k,
      IsIdealSection f n E (multiplierIdeal (n := n) (k : ℝ) ψ) k s →
        SingularityLE (normalizedPotential f n E a H k s)
          (fun x => ((1 - t : ℝ) : EReal) * ψ x) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.analyticCompact
  have h1t : 0 < 1 - t := by linarith
  set ε : ℝ := t / (1 - t) with hε
  have hε0 : 0 < ε := div_pos ht0 h1t
  have hψ' : (VariableComplexAtlas.ofFixedModel n (SchemeComplexPoint f)).HasRationalAnalyticChartType
      ψ := fun e z hz => hψ e z hz
  obtain ⟨s₀, hs₀, hI⟩ := SGPT.PSH.MultiplierIdealInf.exists_multiplierIdeal_le_inftyIdeal hψ' hε0
  refine ⟨⌈s₀ / (1 - t)⌉₊ + 1, Nat.succ_pos _, fun k hk s hs => ?_⟩
  have hkpos : 0 < k := lt_of_lt_of_le (Nat.succ_pos _) hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  set σ : ℝ := k * (1 - t) with hσ
  have hσ0 : 0 < σ := mul_pos hkR h1t
  have hσs₀ : s₀ ≤ σ := by
    have h1 : s₀ / (1 - t) ≤ k := by
      calc s₀ / (1 - t) ≤ ⌈s₀ / (1 - t)⌉₊ := Nat.le_ceil _
        _ ≤ (k : ℝ) := by exact_mod_cast (Nat.le_succ _).trans hk
    rw [div_le_iff₀ h1t] at h1
    linarith
  have hσk : σ * (1 + ε) = k := by
    rw [hσ, hε]
    field_simp
    ring
  have hI' := hI σ hσs₀
  rw [hσk] at hI'
  -- local bounds at every point
  refine RestrictedIdealWeight.moreSingularOn_of_forall_moreSingularAlong_nhdsWithin
    isCompact_univ fun p _ => ?_
  rw [nhdsWithin_univ]
  let U := schemePointFrameOpen f p a
  let α := schemePointFrame f p a
  have hp : schemeComplexPointImage f p ∈ U := schemePointFrame_mem f p a
  have hmem := hs U α p hp
  -- the coefficient lies in `𝓘(1 · (k ψ))`
  have hmem1 : (multiplierIdeal (n := n) 1 fun x => ((k : ℝ) : EReal) * ψ x).mem p
      (sectionFrameCoefficient f n E α k s) := by
    refine ⟨hmem.1, ?_⟩
    have h := hmem.2
    refine (SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff one_pos hkR).mpr ?_
    rw [one_mul]
    exact h
  have hinf := (SGPT.PSH.mem_inftyIdeal_iff_log_bound.mp (hI' p _ hmem1)).2
  obtain ⟨C, hC⟩ := hinf
  obtain ⟨B, hB⟩ := eventually_log_frameNormSq_le f n E H α hp
  have hUo : IsOpen (schemeComplexPointImage f ⁻¹' U) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  refine ⟨(k : ℝ)⁻¹ * C + B, ?_⟩
  filter_upwards [hC, hB, hUo.mem_nhds hp] with q hqC hqB hqU
  have hframe := H.sectionLogNormSq_frame a α k s q hqU
  change (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq a k s q ≤ _
  rw [hframe]
  have hkinv : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  rw [SGPT.PSH.MultiplierIdealInf.coe_mul_add_coe hkinv]
  have hA : (((k : ℝ)⁻¹ : ℝ) : EReal) *
      SGPT.Foundations.Analysis.logNormSq (sectionFrameCoefficient f n E α k s q) ≤
      (((k : ℝ)⁻¹ : ℝ) : EReal) * ((σ : EReal) * ψ q + (C : EReal)) :=
    mul_le_mul_of_nonneg_left hqC (EReal.coe_nonneg.mpr hkinv.le)
  rw [SGPT.PSH.MultiplierIdealInf.coe_mul_add_coe hkinv, ← mul_assoc, ← EReal.coe_mul] at hA
  have hks : (k : ℝ)⁻¹ * σ = 1 - t := by
    rw [hσ]
    field_simp
  rw [hks] at hA
  have hlog : (k : ℝ)⁻¹ * ((k : ℝ) * Real.log (H.frameNormSq α q)) ≤ B := by
    rw [← mul_assoc, inv_mul_cancel₀ hkR.ne', one_mul]
    exact hqB
  calc (((k : ℝ)⁻¹ : ℝ) : EReal) *
        SGPT.Foundations.Analysis.logNormSq (sectionFrameCoefficient f n E α k s q) +
        (((k : ℝ)⁻¹ * ((k : ℝ) * Real.log (H.frameNormSq α q)) : ℝ) : EReal)
      ≤ ((1 - t : ℝ) : EReal) * ψ q + (((k : ℝ)⁻¹ * C : ℝ) : EReal) + (B : EReal) :=
        add_le_add hA (EReal.coe_le_coe_iff.mpr hlog)
    _ = ((1 - t : ℝ) : EReal) * ψ q + (((k : ℝ)⁻¹ * C + B : ℝ) : EReal) := by
        rw [EReal.coe_add, add_assoc]

end SGPT.IGood.DXMain

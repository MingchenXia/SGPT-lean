import SGPT.Bergman.Quant2EnergySmooth

/-!
# Energy quantization on `X`: the limits

Source `prop:quant_I_smooth` (`references/sgpt-d3f272c3/source/author/chapter_Bergman.tex`,
lines 953--1010) and
`cor:Ninfdifflim` (lines 1034--1042).

Let `φ ∈ PSH(X,θ)`, `θ = c₁(L,h)`, have analytic singularities with `θ_φ` a Kähler current. Assuming
the lower-bound half `RiemannRochLowerBound` of `thm:DXmain1` (used in the book through
`prop:smooth_weak_conv`, see `Quant2SmoothWeakConv`), we prove:

* `quant_I_smooth`: for `w, w' ∈ C⁰(X)`,
  `L_{k,φ}(N^k_{w,ωⁿ}) - L_{k,φ}(N^k_{w',ωⁿ}) → E^φ_{θ,X}(w) - E^φ_{θ,X}(w')`
  (`eq:LdiffonXsmoothmeasure`), and `quant_I_smooth_single`: `L_{k,φ}(N^k_{w,ωⁿ}) → E^φ_{θ,X}(w)`
  (`eq:LdiffonXsmoothmeasure2`);
* `Ninfdifflim`: `L_{k,φ}(N^k_{w,X}) → E^φ_{θ,X}(w)` (`cor:Ninfdifflim`).

The proofs follow the book: the smooth case integrates the derivative formula over `[0,1]` and
uses `prop:smooth_weak_conv` with dominated convergence; continuous weights are approximated
uniformly by smooth ones, using the Lipschitz bounds of `Quant2EnergySmooth`; `cor:Ninfdifflim`
adds `lma:BML` for `ωⁿ ∈ BM(X,w)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.Quant2

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport SGPT.Bergman.NormAxioms
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SharpLocalUpper SGPT.Bergman.PartialEquilibriumEnergy
open SGPT.Bergman.PartialEnergyDifferentiability SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Bergman.PartialDonaldson SGPT.Bergman.QuantizationFrontier
open SGPT.Bergman.GlobalWeightSmoothApproximation
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal Interval

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Under `RiemannRochLowerBound`, `n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ I(kφ)) ≤ vol(θ_φ) + 1` eventually. -/
theorem eventually_normalizedH0_le
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    ∀ᶠ k in atTop, (normalizedH0 L T φ k).toReal ≤ (sourceIVolume (chernForm L hL) φ hφ).toReal + 1 := by
  obtain ⟨hφ', hlim⟩ := tendsto_normalizedH0_of_lowerBound omega hvol L T hL hT hcurrent han hRR
  have hfin : sourceIVolume (chernForm L hL) φ hφ ≠ ⊤ := by
    let := sourcePotentialMeasure_finite omega (isThetaPSH_sourceIEnvelope hφ)
    exact measure_ne_top _ _
  have hr := (ENNReal.tendsto_toReal hfin).comp hlim
  filter_upwards [(tendsto_order.1 hr).2 _ (lt_add_one _)] with k hk
  exact hk.le

/-- Source `prop:quant_I_smooth` for smooth weights `w, w'` (the first step of the book's proof),
assuming `RiemannRochLowerBound`. -/
theorem quant_I_smooth_of_chartSmooth
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (w w' : C(X, ℝ)) (hw : ChartSmooth (n := n) w) (hw' : ChartSmooth (n := n) w') :
    Tendsto (fun k => donaldsonL2 omega hvol L T φ w k - donaldsonL2 omega hvol L T φ w' k) atTop
      (𝓝 (energyX omega hφ hφpos w - energyX omega hφ hφpos w')) := by
  set u : C(X, ℝ) := w - w' with hu_def
  have hww : w = w' + u := by ext x; simp [u]
  have hu : ChartSmooth (n := n) u := fun e => by
    simpa only [u, ContinuousMap.sub_apply] using (hw e).sub (hw' e)
  have hwt (t : ℝ) : ChartSmooth (n := n) (w' + t • u) := fun e => by
    simpa only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul] using
      (hw' e).add ((hu e).const_smul t)
  let V : ℝ := (sourceIVolume (chernForm L hL) φ hφ).toReal
  let d : ℕ → ℝ → ℝ := fun k t => ∫ x, u x ∂bergmanX omega L T φ (w' + t • u) k
  let g : ℝ → ℝ := deriv fun s : ℝ => energyX omega hφ hφpos (w' + s • u)
  -- pointwise convergence of the derivatives (`prop:smooth_weak_conv` at the weight `w' + t u`)
  have hlim (t : ℝ) : Tendsto (fun k => d k t) atTop (𝓝 (g t)) := by
    obtain ⟨_hP, hPI, _hMA, hconv⟩ :=
      smooth_weak_conv omega hvol L T hL hT (w' + t • u) (hwt t) hcurrent han hRR
    obtain ⟨hPI', hderiv⟩ := hasDerivAt_energyX omega hφ hφpos w' u t
    have hg : g t = ∫ x, u x ∂sourcePotentialNonPluripolarMeasure (chernForm L hL)
        (partialIEnvelope (chernForm L hL) φ univ
          (fun y : (univ : Set X) => ((w' + t • u) y.val : EReal))) hPI := hderiv.deriv
    rw [hg]
    exact hconv u
  have hbound : ∀ᶠ k in atTop, ∀ t, ‖d k t‖ ≤ ‖u‖ * (V + 1) := by
    filter_upwards [eventually_normalizedH0_le omega hvol L T hL hT hcurrent han hRR hφ,
      eventually_gt_atTop 0] with k hk hk0 t
    rw [Real.norm_eq_abs]
    exact (abs_integral_bergmanX_le omega hvol L T φ (w' + t • u) u k hk0).trans
      (mul_le_mul_of_nonneg_left hk (norm_nonneg u))
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable (d k)
      (MeasureTheory.volume.restrict (Ι (0:ℝ) 1)) := by
    filter_upwards [eventually_gt_atTop 0] with k hk0
    have hdd : d k = deriv (fun s => donaldsonL2 omega hvol L T φ (w' + s • u) k) :=
      funext fun t => (hasDerivAt_donaldsonL2 omega hvol L T φ k hk0 w' u t).deriv.symm
    rw [hdd]
    exact (measurable_deriv _).aestronglyMeasurable
  have hDCT : Tendsto (fun k => ∫ t in (0:ℝ)..1, d k t) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => ‖u‖ * (V + 1)) hmeas
      (hbound.mono fun k hk => Filter.Eventually.of_forall fun t _ => hk t)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun t _ => hlim t)
  have hE : energyX omega hφ hφpos w - energyX omega hφ hφpos w' = ∫ t in (0:ℝ)..1, g t := by
    rw [hww]
    exact (energyX_sub_eq_integral omega hφ hφpos w' u).2
  rw [hE]
  apply hDCT.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk0
  rw [hww]
  exact ((donaldsonL2_sub_eq_integral omega hvol L T φ k hk0 w' u).2).symm

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- Smooth functions are uniformly dense in `C⁰(X)`. -/
theorem exists_chartSmooth_near (w : C(X, ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : C(X, ℝ), ChartSmooth (n := n) g ∧ ‖w - g‖ ≤ δ := by
  obtain ⟨g, hg, hgb⟩ := exists_chartSmooth_strict_between (n := n)
    (a := fun x => w x - δ) (b := fun x => w x + δ) (by fun_prop)
    (by fun_prop : Continuous fun x => w x + δ).lowerSemicontinuous
    (fun x => by linarith)
  refine ⟨⟨g, continuous_of_chartSmooth hg⟩, hg, ?_⟩
  refine (ContinuousMap.norm_le _ hδ.le).mpr fun x => ?_
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, abs_le]
  have := hgb x
  change w x - δ < g x ∧ g x < w x + δ at this
  constructor <;> simp only [ContinuousMap.coe_mk] <;> linarith [this.1, this.2]

/-- Source `prop:quant_I_smooth`, `eq:LdiffonXsmoothmeasure`: for `w, w' ∈ C⁰(X)` and `φ` with
analytic singularities such that `θ_φ` is a Kähler current,
`L_{k,φ}(N^k_{w,ωⁿ}) - L_{k,φ}(N^k_{w',ωⁿ}) → E^φ_{θ,X}(w) - E^φ_{θ,X}(w')`, assuming the
lower-bound half `RiemannRochLowerBound` of `thm:DXmain1`. -/
theorem quant_I_smooth
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (w w' : C(X, ℝ)) :
    Tendsto (fun k => donaldsonL2 omega hvol L T φ w k - donaldsonL2 omega hvol L T φ w' k) atTop
      (𝓝 (energyX omega hφ hφpos w - energyX omega hφ hφpos w')) := by
  let V : ℝ := (sourceIVolume (chernForm L hL) φ hφ).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (8 * (V + 1)) with hδ_def
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hg, hgw⟩ := exists_chartSmooth_near (n := n) w hδ
  obtain ⟨g', hg', hgw'⟩ := exists_chartSmooth_near (n := n) w' hδ
  have hsm := quant_I_smooth_of_chartSmooth omega hvol L T hL hT hcurrent han hRR hφ hφpos g g' hg hg'
  have hev := (Metric.tendsto_atTop.mp hsm) (ε / 2) (half_pos hε)
  obtain ⟨N₁, hN₁⟩ := hev
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (eventually_normalizedH0_le omega hvol L T hL hT hcurrent han hRR hφ)
  refine ⟨max (max N₁ N₂) 1, fun k hk => ?_⟩
  have hk1 : N₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk2 : N₂ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hk)
  have hS := hN₁ k hk1
  rw [Real.dist_eq] at hS ⊢
  have hH := hN₂ k hk2
  have hLw := abs_donaldsonL2_sub_le omega hvol L T φ k hk0 g (w - g)
  have hLw' := abs_donaldsonL2_sub_le omega hvol L T φ k hk0 g' (w' - g')
  have hEw := abs_energyX_sub_le omega hφ hφpos g (w - g)
  have hEw' := abs_energyX_sub_le omega hφ hφpos g' (w' - g')
  simp only [add_sub_cancel] at hLw hLw' hEw hEw'
  have hN : 0 ≤ (normalizedH0 L T φ k).toReal := ENNReal.toReal_nonneg
  have b1 : ‖w - g‖ * (normalizedH0 L T φ k).toReal ≤ δ * (V + 1) :=
    mul_le_mul hgw hH hN hδ.le
  have b2 : ‖w' - g'‖ * (normalizedH0 L T φ k).toReal ≤ δ * (V + 1) :=
    mul_le_mul hgw' hH hN hδ.le
  have b3 : ‖w - g‖ * V ≤ δ * V := mul_le_mul_of_nonneg_right hgw hV
  have b4 : ‖w' - g'‖ * V ≤ δ * V := mul_le_mul_of_nonneg_right hgw' hV
  have hδV : δ * (V + 1) = ε / 8 := by
    rw [hδ_def]; field_simp
  have hδV' : δ * V ≤ ε / 8 := by
    rw [← hδV]; exact mul_le_mul_of_nonneg_left (by linarith) hδ.le
  have key : |donaldsonL2 omega hvol L T φ w k - donaldsonL2 omega hvol L T φ w' k -
      (energyX omega hφ hφpos w - energyX omega hφ hφpos w')| ≤
      |donaldsonL2 omega hvol L T φ g k - donaldsonL2 omega hvol L T φ g' k -
        (energyX omega hφ hφpos g - energyX omega hφ hφpos g')| +
      |donaldsonL2 omega hvol L T φ w k - donaldsonL2 omega hvol L T φ g k| +
      |donaldsonL2 omega hvol L T φ w' k - donaldsonL2 omega hvol L T φ g' k| +
      |energyX omega hφ hφpos w - energyX omega hφ hφpos g| +
      |energyX omega hφ hφpos w' - energyX omega hφ hφpos g'| := by
    have := abs_add_le (donaldsonL2 omega hvol L T φ g k - donaldsonL2 omega hvol L T φ g' k -
        (energyX omega hφ hφpos g - energyX omega hφ hφpos g'))
      (donaldsonL2 omega hvol L T φ w k - donaldsonL2 omega hvol L T φ g k)
    have h2 := abs_sub_le (donaldsonL2 omega hvol L T φ w k) (donaldsonL2 omega hvol L T φ g k)
      (donaldsonL2 omega hvol L T φ g' k)
    calc _ = |(donaldsonL2 omega hvol L T φ g k - donaldsonL2 omega hvol L T φ g' k -
            (energyX omega hφ hφpos g - energyX omega hφ hφpos g')) +
          (donaldsonL2 omega hvol L T φ w k - donaldsonL2 omega hvol L T φ g k) -
          (donaldsonL2 omega hvol L T φ w' k - donaldsonL2 omega hvol L T φ g' k) -
          (energyX omega hφ hφpos w - energyX omega hφ hφpos g) +
          (energyX omega hφ hφpos w' - energyX omega hφ hφpos g')| := by ring_nf
      _ ≤ _ := by
          refine (abs_add_le _ _).trans ?_
          refine add_le_add ?_ le_rfl
          refine (abs_sub _ _).trans ?_
          refine add_le_add ?_ le_rfl
          refine (abs_sub _ _).trans ?_
          refine add_le_add ?_ le_rfl
          exact abs_add_le _ _
  have hS' : |donaldsonL2 omega hvol L T φ g k - donaldsonL2 omega hvol L T φ g' k -
      (energyX omega hφ hφpos g - energyX omega hφ hφpos g')| < ε / 2 := hS
  linarith

/-- Source `prop:quant_I_smooth`, `eq:LdiffonXsmoothmeasure2`:
`L_{k,φ}(N^k_{w,ωⁿ}) → E^φ_{θ,X}(w)`, assuming `RiemannRochLowerBound`. -/
theorem quant_I_smooth_single
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (w : C(X, ℝ)) :
    Tendsto (fun k => donaldsonL2 omega hvol L T φ w k) atTop (𝓝 (energyX omega hφ hφpos w)) := by
  have h := quant_I_smooth omega hvol L T hL hT hcurrent han hRR hφ hφpos w 0
  simpa only [donaldsonL2_zero, energyX_zero, sub_zero] using h

/-- `L_{k,φ}(N^k_{w,X})`, the partial Donaldson functional of the weighted sup norm on `X`
(value `0` at `k = 0`). -/
def supDonaldson (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle n X) (φ : X → EReal)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (k : ℕ) : ℝ :=
  if hk : 0 < k then partialDonaldsonFunctional L T omega hvol k hk φ (supNorm L T W k φ) else 0

/-- Source `cor:Ninfdifflim`: for `w ∈ C⁰(X)` and `φ` with analytic singularities such that
`θ_φ` is a Kähler current, `L_{k,φ}(N^k_{w,X}) → E^φ_{θ,X}(w)`, assuming `RiemannRochLowerBound`.
-/
theorem Ninfdifflim
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (hRR : RiemannRochLowerBound (chernForm L hL) L T φ)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (chernForm L hL) φ hφ univ)
    (w : C(X, ℝ)) :
    Tendsto (fun k => supDonaldson omega hvol L T φ (wholeWeightedSubset w) k) atTop
      (𝓝 (energyX omega hφ hφpos w)) := by
  have hBML := tendsto_partialDonaldson_sup_sub_l2 L T hL hT omega hvol (wholeWeightedSubset w)
    (volX omega) (volX_BM omega hvol L T w) φ
  have h := hBML.add (quant_I_smooth_single omega hvol L T hL hT hcurrent han hRR hφ hφpos w)
  rw [zero_add] at h
  apply h.congr
  intro k
  by_cases hk : 0 < k
  · simp only [supDonaldson, donaldsonL2, dif_pos hk]
    ring
  · simp only [supDonaldson, donaldsonL2, dif_neg hk, add_zero]

end SGPT.Bergman.Quant2

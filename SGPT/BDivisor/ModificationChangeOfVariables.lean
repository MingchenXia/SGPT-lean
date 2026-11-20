import SGPT.BDivisor.ClassPushforward
import SGPT.BDivisor.ClassPullback
import SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity
import SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Change of variables along a modification and `g_* g^* = id`

Let `g : Z → Y` be a modification (a proper holomorphic bimeromorphic map,
`IsAnalyticModification`) between compact complex manifolds of dimension `n`. Off closed nowhere
dense analytic sets `A = g⁻¹(B)` the map `g` is a biholomorphism `Z \ A → Y \ B`, and analytic
sets are Lebesgue null in charts. The classical change of variables formula for injective
`C¹` maps therefore gives, for smooth forms `a, γ` on `Y` of complementary degrees,

`∫_Z g^*a ∧ g^*γ = ∫_Y a ∧ γ`,

i.e. `⟨[g^*a], g^*γ⟩ = ⟨[a], γ⟩` for the global pairing of the smooth currents
(`pairingLM_smoothGlobalCurrent_pullback`). No Kähler form is needed on either manifold: the
computation is done chart by chart with finite chart partitions of unity on `Z` and `Y`; the real
Jacobian of a holomorphic map is `|det_ℂ|² ≥ 0`, so no orientation sign appears.

Consequences:

* `currentPushforward_smoothGlobalCurrent_pullback` — `g_*[g^*a] = [a]` as currents;
* `classPushforward_classPullback` — **`g_* g^* α = α`** for every real `(1,1)`-class `α` on `Y`
  (the identity used throughout `chap:bdiv`, e.g. to see that a class `α_Y` on a model defines a
  Cartier b-divisor, `def:bdiv:L116`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold Distributions

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.TopDegreeDensity
  SGPT.Foundations.Analysis.Pending.ConstantFormProducts
  SGPT.Foundations.Analysis.Pending.ProductTestForms
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity
  SGPT.Foundations.Analysis.Pending.GlobalCurrents
  SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

variable {n : ℕ}

/-! ### Auxiliary algebra -/

/-- Complementary current degrees add up to the top degree `2n`. -/
theorem degree_add_complement (k : CurrentDegree n) :
    k.val + (Module.finrank ℝ (ComplexModel n) - k.val) = 2 * n := by
  have hk := k.is_lt
  rw [← complexModel_real_finrank n]
  omega

/-- The density of `A ∧ B` in top degree, as a continuous bilinear map in `(B, A)`. -/
def topWedgeCLM {p q : ℕ} (h : p + q = 2 * n) :
    ((ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ] ((ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  haveI := realForm_finiteDimensional (n := n) p
  haveI := realForm_finiteDimensional (n := n) q
  LinearMap.toContinuousLinearMap
    { toFun := fun B => LinearMap.toContinuousLinearMap (TopDegreeDensity.topDensityLM (n := n) ∘ₗ (wedgeToBilin n h).flip B)
      map_add' := fun B B' => by
        ext A
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
          Function.comp_apply, map_add, LinearMap.add_apply, add_apply]
      map_smul' := fun c B => by
        ext A
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
          Function.comp_apply, map_smul, LinearMap.smul_apply, smul_apply, RingHom.id_apply] }

@[simp] theorem topWedgeCLM_apply {p q : ℕ} (h : p + q = 2 * n)
    (B : (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) (A : (ComplexModel n) [⋀^Fin p]→L[ℝ] ℝ) :
    topWedgeCLM h B A = topDensity (wedgeTo h A B) := rfl

section Forms

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Coefficients of a finite sum of smooth forms. -/
theorem smoothRealForm_coeff_sum {q : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → SmoothRealForm n M q) (e : ComplexChart n M) (z : ComplexModel n) :
    (∑ i ∈ s, f i).coeff e z = ∑ i ∈ s, (f i).coeff e z := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, coeff_add, ih]

/-- The global pairing splits along any finite family of chart-smooth weights summing to one. -/
theorem pairingLM_eq_sum_smulFun [CompactSpace M] {k : CurrentDegree n}
    (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    {ι : Type*} [Fintype ι] (φ : ι → M → ℝ) (hφ : ∀ i, ChartSmooth (n := n) (φ i))
    (h1 : ∀ x, ∑ i, φ i x = 1) :
    pairingLM T γ = ∑ i, pairingLM T (smulFun (φ i) (hφ i) γ) := by
  have hγ : γ = ∑ i, smulFun (φ i) (hφ i) γ := by
    apply smoothRealForm_ext
    intro e z
    rw [smoothRealForm_coeff_sum]
    simp only [smulFun_coeff]
    rw [← Finset.sum_smul, h1, one_smul]
  conv_lhs => rw [hγ]
  exact map_sum _ _ _

/-- The pairing of the smooth current `[a]` with a weighted form `χ γ` supported in one chart is
the chart integral of `χ · (a ∧ γ)`; the integrand is integrable. -/
theorem pairingLM_smulFun_eq_integral [CompactSpace M] {k : CurrentDegree n}
    (a : SmoothRealForm n M k.val)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    (e : ComplexChart n M) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source) :
    Integrable (e.val.target.indicator fun z => χ (e.val.symm z) *
        topDensity (wedgeTo (degree_add_complement k) (a.coeff e z) (γ.coeff e z))) ∧
    pairingLM (smoothGlobalCurrent (canonicalBasis n) a) (smulFun χ hχ γ) =
      ∫ z, e.val.target.indicator (fun z => χ (e.val.symm z) *
        topDensity (wedgeTo (degree_add_complement k) (a.coeff e z) (γ.coeff e z))) z := by
  obtain ⟨η, hη, -, hpair⟩ :=
    exists_testForm_with_pairing (smoothGlobalCurrent (canonicalBasis n) a) γ e χ hχ hc hs
  have hpt : (fun z => topDensity (wedgeTo (degree_add_complement k) (a.coeff e z) (η z))) =
      e.val.target.indicator (fun z => χ (e.val.symm z) *
        topDensity (wedgeTo (degree_add_complement k) (a.coeff e z) (γ.coeff e z))) := by
    funext z
    rw [hη z]
    by_cases hz : z ∈ e.val.target
    · rw [indicator_of_mem hz, indicator_of_mem hz, wedgeTo_smul_right, topDensity_smul]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, wedgeTo_zero_right, topDensity_zero]
  have hloc : LocallyIntegrableOn (a.coeff e) (chartTarget e) volume := by
    have h := smoothForm_coeff_locallyIntegrable (canonicalBasis n) a e
    rwa [addHaar_canonicalBasis] at h
  refine ⟨?_, ?_⟩
  · rw [← hpt]
    exact TestFunction.integrable_bilin (topWedgeCLM (degree_add_complement k)) hloc η
  · rw [hpair, smoothGlobalCurrent_apply_eq_integral_topDensity]
    exact congrArg (fun F : ComplexModel n → ℝ => ∫ z, F z) hpt

end Forms

/-! ### The change of variables in one pair of charts -/

section ChartPair

variable {Z Y : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Change of variables in one pair of charts.** Let `g` be holomorphic with a two-sided
inverse `s` off the null closed set `A = g⁻¹(B)`. For weights `ψ` on `Z` supported in the chart
`e` and `χ` on `Y` supported in the chart `d`, the chart integral of
`ψ · (χ ∘ g) · (g^*a ∧ g^*γ)` over `e` equals the chart integral of `(ψ ∘ s) · χ · (a ∧ γ)` over
`d`, and the latter integrand is integrable. -/
theorem integral_chart_pullback_eq {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {A : Set Z} {B : Set Y} {s : Y → Z} (hAc : IsClosed A)
    (hAnull : ∀ e : ComplexChart n Z, volume (pluripolarChartSet A e) = 0)
    (hBnull : ∀ d : ComplexChart n Y, volume (pluripolarChartSet B d) = 0)
    (hpre : g ⁻¹' B = A) (hright : ∀ x ∉ B, g (s x) = x) (hleft : ∀ y ∉ A, s (g y) = y)
    (e : ComplexChart n Z) (d : ComplexChart n Y) {ψ : Z → ℝ} {χ : Y → ℝ}
    (hψ : ∀ z, ψ z ≠ 0 → z ∈ e.val.source) (hχ : ∀ y, χ y ≠ 0 → y ∈ d.val.source)
    {p q : ℕ} (h : p + q = 2 * n) (a : SmoothRealForm n Y p) (γ : SmoothRealForm n Y q)
    (hint : Integrable (e.val.target.indicator fun z => ψ (e.val.symm z) *
        χ (g (e.val.symm z)) * topDensity (wedgeTo h ((SmoothRealForm.pullback hg a).coeff e z)
          ((SmoothRealForm.pullback hg γ).coeff e z)))) :
    Integrable (d.val.target.indicator fun w => ψ (s (d.val.symm w)) * χ (d.val.symm w) *
        topDensity (wedgeTo h (a.coeff d w) (γ.coeff d w))) ∧
    ∫ z, e.val.target.indicator (fun z => ψ (e.val.symm z) * χ (g (e.val.symm z)) *
        topDensity (wedgeTo h ((SmoothRealForm.pullback hg a).coeff e z)
          ((SmoothRealForm.pullback hg γ).coeff e z))) z =
      ∫ w, d.val.target.indicator (fun w => ψ (s (d.val.symm w)) * χ (d.val.symm w) *
        topDensity (wedgeTo h (a.coeff d w) (γ.coeff d w))) w := by
  set L : ComplexModel n → ℝ := e.val.target.indicator fun z => ψ (e.val.symm z) *
    χ (g (e.val.symm z)) * topDensity (wedgeTo h ((SmoothRealForm.pullback hg a).coeff e z)
      ((SmoothRealForm.pullback hg γ).coeff e z)) with hL
  set H : ComplexModel n → ℝ := d.val.target.indicator fun w => ψ (s (d.val.symm w)) *
    χ (d.val.symm w) * topDensity (wedgeTo h (a.coeff d w) (γ.coeff d w)) with hH
  set G := coordinateMap g e d with hG
  set U := coordinateDomain g e d ∩ e.val.symm ⁻¹' Aᶜ with hU
  have hUo : IsOpen U :=
    (e.val.continuousOn_symm.mono fun z hz => hz.1).isOpen_inter_preimage
      (coordinateDomain_isOpen hg e d) hAc.isOpen_compl
  have hUm : MeasurableSet U := hUo.measurableSet
  have hderiv : ∀ z ∈ U, HasFDerivWithinAt G (fderiv ℝ G z) U z := fun z hz =>
    ((coordinateMap_contDiffAt_real hg e d hz.1).differentiableAt (by simp)).hasFDerivAt
      |>.hasFDerivWithinAt
  have hinj : InjOn G U := by
    intro z hz z' hz' hzz
    have h1 : g (e.val.symm z) = g (e.val.symm z') := by
      have h2 := congrArg d.val.symm hzz
      simp only [hG, coordinateMap, Function.comp_apply] at h2
      rwa [d.val.left_inv hz.1.2, d.val.left_inv hz'.1.2] at h2
    have h2 : e.val.symm z = e.val.symm z' := by
      rw [← hleft _ hz.2, ← hleft _ hz'.2, h1]
    rw [← e.val.right_inv hz.1.1, ← e.val.right_inv hz'.1.1, h2]
  have hdet : ∀ z ∈ U, 0 ≤ (fderiv ℝ G z).det := by
    intro z hz
    rw [hG, coordinateMap_fderiv_restrictScalars hg e d hz.1,
      DivisorialChangeOfVariables.det_restrictScalars_eq_normSq]
    exact Complex.normSq_nonneg _
  have hpt : EqOn L (fun z => |(fderiv ℝ G z).det| • H (G z)) U := by
    intro z hz
    have hzt : z ∈ e.val.target := hz.1.1
    have hGt : G z ∈ d.val.target := coordinateMap_mem_target hz.1
    have hds : d.val.symm (G z) = g (e.val.symm z) := d.val.left_inv hz.1.2
    have hsg : s (g (e.val.symm z)) = e.val.symm z := hleft _ hz.2
    simp only [hL, hH]
    rw [indicator_of_mem hzt, indicator_of_mem hGt, hds, hsg, abs_of_nonneg (hdet z hz),
      smul_eq_mul, SmoothRealForm.pullback_coeff hg _ e d hz.1,
      SmoothRealForm.pullback_coeff hg _ e d hz.1, ← wedgeTo_compContinuousLinearMap,
      topDensity_compContinuousLinearMap]
    change _ = (fderiv ℝ G z).det * _
    ring
  -- `L` vanishes off `U` up to the null set `e(A)`.
  have hLoff : ∀ᵐ z, z ∉ U → L z = 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hAnull e)] with z hzN hzU
    by_cases hzt : z ∈ e.val.target
    · have hzA : e.val.symm z ∉ A := fun h' => hzN ⟨hzt, h'⟩
      have hgz : g (e.val.symm z) ∉ d.val.source := fun h' => hzU ⟨⟨hzt, h'⟩, hzA⟩
      have hχ0 : χ (g (e.val.symm z)) = 0 := by
        by_contra h0
        exact hgz (hχ _ h0)
      simp only [hL]
      rw [indicator_of_mem hzt, hχ0]
      ring
    · simp only [hL]
      rw [indicator_of_notMem hzt]
  -- `H` vanishes off `G(U)` up to the null set `d(B)`.
  have hHoff : ∀ᵐ w, w ∉ G '' U → H w = 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hBnull d)] with w hwN hwU
    by_cases hwt : w ∈ d.val.target
    · have hwB : d.val.symm w ∉ B := fun h' => hwN ⟨hwt, h'⟩
      simp only [hH]
      rw [indicator_of_mem hwt]
      by_contra hne
      have hψ0 : ψ (s (d.val.symm w)) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
      have hye : s (d.val.symm w) ∈ e.val.source := hψ _ hψ0
      have hgy : g (s (d.val.symm w)) = d.val.symm w := hright _ hwB
      have hyA : s (d.val.symm w) ∉ A := by
        intro hA
        rw [← hpre] at hA
        apply hwB
        have hA' : g (s (d.val.symm w)) ∈ B := hA
        rwa [hgy] at hA'
      apply hwU
      refine ⟨e.val (s (d.val.symm w)), ⟨⟨e.val.map_source hye, ?_⟩, ?_⟩, ?_⟩
      · change g (e.val.symm (e.val (s (d.val.symm w)))) ∈ d.val.source
        rw [e.val.left_inv hye, hgy]
        exact d.val.map_target hwt
      · change e.val.symm (e.val (s (d.val.symm w))) ∉ A
        rw [e.val.left_inv hye]
        exact hyA
      · change d.val (g (e.val.symm (e.val (s (d.val.symm w))))) = w
        rw [e.val.left_inv hye, hgy, d.val.right_inv hwt]
    · simp only [hH]
      rw [indicator_of_notMem hwt]
  -- integrability
  have hcomp : IntegrableOn (fun z => |(fderiv ℝ G z).det| • H (G z)) U :=
    hint.integrableOn.congr_fun hpt hUm
  have himg : IntegrableOn H (G '' U) :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hUm hderiv hinj H).mpr hcomp
  refine ⟨himg.integrable_of_ae_notMem_eq_zero hHoff, ?_⟩
  calc ∫ z, L z = ∫ z in U, L z := (setIntegral_eq_integral_of_ae_compl_eq_zero hLoff).symm
    _ = ∫ z in U, |(fderiv ℝ G z).det| • H (G z) := setIntegral_congr_fun hUm hpt
    _ = ∫ w in G '' U, H w :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj H).symm
    _ = ∫ w, H w := setIntegral_eq_integral_of_ae_compl_eq_zero hHoff

end ChartPair

/-! ### The global change of variables -/

section Global

variable {Z Y : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [CompactSpace Z] [CompactSpace Y]

/-- **Change of variables along a modification**: for a modification `g : Z → Y` of compact
complex manifolds and smooth forms `a, γ` on `Y` of complementary degrees,
`⟨[g^*a], g^*γ⟩ = ⟨[a], γ⟩`, i.e. `∫_Z g^*a ∧ g^*γ = ∫_Y a ∧ γ`. -/
theorem pairingLM_smoothGlobalCurrent_pullback {g : Z → Y}
    (hg : IsAnalyticModification (n := n) g) {k : CurrentDegree n}
    (a : SmoothRealForm n Y k.val)
    (γ : SmoothRealForm n Y (Module.finrank ℝ (ComplexModel n) - k.val)) :
    pairingLM (smoothGlobalCurrent (canonicalBasis n) (SmoothRealForm.pullback hg.1 a))
        (SmoothRealForm.pullback hg.1 γ) =
      pairingLM (smoothGlobalCurrent (canonicalBasis n) a) γ := by
  obtain ⟨A, B, s, hAc, hAa, hAi, _hBc, hBa, hBi, hpre, -, hright, hleft⟩ := hg.2.2
  have hAnull : ∀ e : ComplexChart n Z, volume (pluripolarChartSet A e) = 0 := fun e =>
    (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hAa
      hAi).chart_measure_eq_zero e volume
  have hBnull : ∀ d : ComplexChart n Y, volume (pluripolarChartSet B d) = 0 := fun d =>
    (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hBa
      hBi).chart_measure_eq_zero d volume
  let P : ChartPartitionOfUnity n Z := ChartPartitionOfUnity.choice
  let Q : ChartPartitionOfUnity n Y := ChartPartitionOfUnity.choice
  have hdeg := degree_add_complement k
  -- the right-hand side, chart by chart on `Y`
  have hR : pairingLM (smoothGlobalCurrent (canonicalBasis n) a) γ =
      ∑ j, ∫ w, (Q.chart j).val.target.indicator (fun w => Q.weight j ((Q.chart j).val.symm w) *
        topDensity (wedgeTo hdeg (a.coeff (Q.chart j) w) (γ.coeff (Q.chart j) w))) w := by
    rw [pairingLM_eq_sum_smulFun _ γ Q.weight Q.smooth Q.sum_eq_one]
    exact Finset.sum_congr rfl fun j _ =>
      (pairingLM_smulFun_eq_integral a γ (Q.chart j) _ (Q.smooth j) (Q.compact j)
        (Q.subset j)).2
  -- the left-hand side, with the product weights `ψᵢ · (χⱼ ∘ g)` on `Z`
  let φ : Fin P.card × Fin Q.card → Z → ℝ := fun ij x => P.weight ij.1 x * Q.weight ij.2 (g x)
  have hφ : ∀ ij, ChartSmooth (n := n) (φ ij) := fun ij e =>
    (P.smooth ij.1 e).mul
      (AdmissiblePresentationPullback.chartSmooth_comp hg.1 (Q.smooth ij.2) e)
  have hφ1 : ∀ x, ∑ ij, φ ij x = 1 := by
    intro x
    rw [Fintype.sum_prod_type]
    simp only [φ, ← Finset.mul_sum, Q.sum_eq_one, mul_one, P.sum_eq_one]
  have hφs : ∀ ij, tsupport (φ ij) ⊆ (P.chart ij.1).val.source := fun ij =>
    (tsupport_mul_subset_left).trans (P.subset ij.1)
  have hφc : ∀ ij, IsCompact (tsupport (φ ij)) := fun ij =>
    (P.compact ij.1).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left
  rw [pairingLM_eq_sum_smulFun _ _ φ hφ hφ1, Fintype.sum_prod_type, Finset.sum_comm, hR]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- for a fixed chart `d = Qⱼ` of `Y`, change variables in every chart `Pᵢ` of `Z`
  have hpiece : ∀ i : Fin P.card,
      Integrable ((Q.chart j).val.target.indicator fun w =>
        P.weight i (s ((Q.chart j).val.symm w)) * Q.weight j ((Q.chart j).val.symm w) *
          topDensity (wedgeTo hdeg (a.coeff (Q.chart j) w) (γ.coeff (Q.chart j) w))) ∧
      pairingLM (smoothGlobalCurrent (canonicalBasis n) (SmoothRealForm.pullback hg.1 a))
          (smulFun (φ (i, j)) (hφ (i, j)) (SmoothRealForm.pullback hg.1 γ)) =
        ∫ w, (Q.chart j).val.target.indicator (fun w =>
          P.weight i (s ((Q.chart j).val.symm w)) * Q.weight j ((Q.chart j).val.symm w) *
            topDensity (wedgeTo hdeg (a.coeff (Q.chart j) w) (γ.coeff (Q.chart j) w))) w := by
    intro i
    obtain ⟨hint, heq⟩ := pairingLM_smulFun_eq_integral (SmoothRealForm.pullback hg.1 a)
      (SmoothRealForm.pullback hg.1 γ) (P.chart i) (φ (i, j)) (hφ (i, j)) (hφc (i, j))
      (hφs (i, j))
    have hψ : ∀ z, P.weight i z ≠ 0 → z ∈ (P.chart i).val.source := fun z hz =>
      P.subset i (subset_tsupport _ hz)
    have hχ : ∀ y, Q.weight j y ≠ 0 → y ∈ (Q.chart j).val.source := fun y hy =>
      Q.subset j (subset_tsupport _ hy)
    obtain ⟨hint', heq'⟩ := integral_chart_pullback_eq hg.1 hAc hAnull hBnull hpre hright hleft
      (P.chart i) (Q.chart j) hψ hχ hdeg a γ hint
    exact ⟨hint', heq.trans heq'⟩
  rw [Finset.sum_congr rfl fun i _ => (hpiece i).2,
    ← integral_finsetSum _ fun i _ => (hpiece i).1]
  congr 1
  funext w
  by_cases hw : w ∈ (Q.chart j).val.target
  · simp only [indicator_of_mem hw]
    rw [← Finset.sum_mul, ← Finset.sum_mul, P.sum_eq_one, one_mul]
  · simp only [indicator_of_notMem hw, Finset.sum_const_zero]

/-- **`g_*[g^*a] = [a]`**: the push-forward of the smooth current of a pulled-back form along a
modification of compact complex manifolds is the smooth current of the form. -/
theorem currentPushforward_smoothGlobalCurrent_pullback {g : Z → Y}
    (hg : IsAnalyticModification (n := n) g) {k : CurrentDegree n}
    (a : SmoothRealForm n Y k.val) :
    currentPushforward hg.1 (smoothGlobalCurrent (canonicalBasis n)
        (SmoothRealForm.pullback hg.1 a)) =
      smoothGlobalCurrent (canonicalBasis n) a := by
  apply GlobalCurrent.ext
  intro e η
  rw [currentPushforward_inChart, pairingLM_smoothGlobalCurrent_pullback hg,
    NaturalFullNativeSmoothDuality.pairing_testExtension]

/-- **`g_* g^* = id` on real `(1,1)`-classes** along a modification `g : Z → Y` of compact
complex manifolds of positive dimension. -/
theorem classPushforward_classPullback {g : Z → Y} (hg : IsAnalyticModification (n := n) g)
    (hn : 0 < n) (α : RealBottChern n Y) :
    classPushforward hg.1 (canonicalBasis n) hn (classPullback hg.1 α) = α := by
  induction α using Quotient.inductionOn with
  | h θ =>
    change classPushforward hg.1 (canonicalBasis n) hn
      (classPullback hg.1 (RealBottChern.ofRepresentative θ)) = RealBottChern.ofRepresentative θ
    rw [classPullback_ofRepresentative, classPushforward_ofRepresentative]
    have hcur : closedCurrentPushforward hg.1 (canonicalBasis n) hn
        (Pending.CurrentBottChernClass.smoothClosedCurrent (canonicalBasis n) hn
          (ClosedRealOneOneForm.pullback hg.1 θ)) =
        Pending.CurrentBottChernClass.smoothClosedCurrent (canonicalBasis n) hn θ :=
      Subtype.ext (currentPushforward_smoothGlobalCurrent_pullback hg (k := degreeTwo hn) θ.val)
    rw [hcur, Pending.CurrentBottChernClass.bottChernClass_smoothClosedCurrent]

end Global

end SGPT.BDivisor

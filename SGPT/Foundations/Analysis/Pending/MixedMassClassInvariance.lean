import SGPT.Foundations.Analysis.Pending.SmoothCurrentClosedness
import SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity

set_option autoImplicit false

/-!
# Total mixed masses of smooth closed forms depend only on the classes

On a compact Kähler manifold `M` of dimension `N`, for closed real `(1,1)`-forms
`θ₀, …, θ_{N-1}` and a chart-smooth function `f`,

`∫_M ddᶜf ∧ θ₁ ∧ ⋯ ∧ θ_{N-1} = 0`             (`integral_topRatio_ddc_eq_zero`),

so `∫_M θ₀ ∧ ⋯ ∧ θ_{N-1}` does not change when each `θᵢ` is replaced by `θᵢ + ddᶜfᵢ`
(`integral_topRatio_slotForm_add_ddc`; no positivity), and for semipositive families the total
masses of the global mixed measures with potentials `0` agree
(`globalMixedMeasure_real_univ_add_ddc`; positivity is needed only for the two end families, not
for the intermediate ones).  This is the class computation used for the bounds
`∫ α_ε^{N-p} ∧ ω_ε^p ≤ (α + {ω})^{N-p} · {ω}^p` in Boucksom's criterion (TN.4, steps B3/B6;
asked by TN-CLASSICAL on I-0831).

Proof: in a slot chart where every `θᵢ` is `ddᶜρᵢ`, the density of
`ddᶜf ∧ ddᶜρ₁ ∧ ⋯` is `Re C(Hess f, Hess ρ₁, …) / πᴺ`, and for `f` compactly supported in the chart
`∫ C(Hess f, Hess ρ₁, …) = ∫ 1 · C(Hess f, …) = ∫ f · C(Hess 1, …) = 0` by the mixed-Hessian
integration by parts (`MixedHessian.integral_mul_mixedCoefficient_swap`)
(`setIntegral_ddcSlots_eq_zero`).  The passage from slot charts to `M` is done once for any
"local slot" (`integral_topRatio_eq_zero_of_local`, `integral_topRatio_eq_zero_of_slot`: signed
change of variables and a partition of unity), the abstract form of the globalisation in
`Pending.SmoothCurrentClosedness`.

## Main results

* `smoothDDC_sum`, `complexHessian_const`.
* `setIntegral_ddcSlots_eq_zero`, `integral_topRatio_eq_zero_of_local`,
  `integral_topRatio_eq_zero_of_slot`, `integral_topRatio_ddc_eq_zero`.
* `formProd`, `formProd_coeff`, `slotForm`, `topDensity_slotForm_coeff`.
* `integral_topRatio_slotForm_update_add_ddc`, `integral_topRatio_slotForm_add_ddc`,
  `globalMixedMeasure_real_univ_eq_integral`, `globalMixedMeasure_real_univ_add_ddc`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FirstPass.PositiveClasses
  StronglyPositiveForms ProductTestForms IntegrationCurrent TopDegreeDensity
  SmoothMixedMeasureDensity GlobalNonPluripolar GlobalSlotStokes ChartPartition
  CurrentTraceMeasure SmoothCurrentClosedness MixedHessian ManifoldTubePositivity

/-! ### `ddᶜ` of finite sums -/

theorem smoothDDC_sum {n : ℕ} {ι : Type*} (s : Finset ι) {h : ι → ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hh : ∀ i ∈ s, ContDiffOn ℝ ∞ (h i) U)
    {z : ComplexModel n} (hz : z ∈ U) :
    smoothDDC (fun y => ∑ i ∈ s, h i y) z = ∑ i ∈ s, smoothDDC (h i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [smoothDDC_add hU (hh a (Finset.mem_insert_self a s))
      (ContDiffOn.sum fun i hi => hh i (Finset.mem_insert_of_mem hi)) hz,
      ih fun i hi => hh i (Finset.mem_insert_of_mem hi)]

theorem normalizedHermitianMatrix_zero {n : ℕ} :
    normalizedHermitianMatrix (0 : RealForm n 2) = 0 := by
  ext j k
  simp [normalizedHermitianMatrix]

theorem complexHessian_const {n : ℕ} (c : ℝ) (z : ComplexModel n) :
    complexHessian (fun _ : ComplexModel n => c) z = 0 := by
  rw [← normalizedHermitianMatrix_smoothDDC (contDiffAt_const (c := c)),
    GlobalPotentialTransforms.smoothDDC_const,
    normalizedHermitianMatrix_zero]

/-! ### Stokes for a `ddᶜ`-slot in one slot chart -/

section Local

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- **Stokes for `ddᶜf ∧ θ₁ ∧ ⋯` in one slot chart**: if `f` is supported in a chart domain on
which every slot `θᵢ` has a smooth potential, the density of the slots with the slot `i₀`
replaced by `ddᶜf` has integral zero over the domain. -/
theorem setIntegral_ddcSlots_eq_zero {θ : Fin N → ClosedRealOneOneForm N M}
    {κ : ClosedRealOneOneForm N M} (J : SlotChart θ κ) (i₀ : Fin N) {f : M → ℝ}
    (hf : ChartSmooth (n := N) f) (hfJ : tsupport f ⊆ (J.source : Set M))
    (hfK : IsCompact (tsupport f)) :
    ∫ z in (J.domain : Set (ComplexModel N)), actualMixedTopDensity
      (Function.update (fun i => (θ i).val.coeff J.chart z) i₀
        (smoothDDC (fun y => f (J.chart.val.symm y)) z)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos i₀.pos).symm⟩
  classical
  set e := J.chart with he
  set D := J.domain with hD
  have hDt : (D : Set (ComplexModel (m + 1))) ⊆ e.val.target := J.domain_le_target
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  obtain ⟨φ, hφs, hφc, hφD, hφeq, -⟩ := J.exists_coordinate_test hf hfJ hfK
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact (Ω := D) hφc hφD
  set ψ : ComplexModel (m + 1) → ℝ := ⇑χ with hψ
  have hψs : ContDiff ℝ ∞ ψ := χ.contDiff
  have hψD : tsupport ψ ⊆ (D : Set (ComplexModel (m + 1))) := χ.tsupport_subset
  set ρt : Fin (m + 1) → ComplexModel (m + 1) → ℝ := fun i z => ψ z * J.potential i z with hρt
  have hρts : ∀ i, ContDiff ℝ ∞ (ρt i) := fun i =>
    contDiff_mul_of_tsupport_subset D.isOpen hψs hψD (J.localPotential i).2.2.1
  set ρ' : Fin m → ComplexModel (m + 1) → ℝ := fun j => ρt (Equiv.swap 0 i₀ j.succ) with hρ'
  have hρ's : ∀ j, ContDiff ℝ ∞ (ρ' j) := fun j => hρts _
  set X : ComplexModel (m + 1) → ℂ := fun z =>
    mixedCoefficient (Fin.cons (complexHessian φ z) (fun i => complexHessian (ρ' i) z) :
      Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) with hX
  have hX0 : ∀ z, z ∉ tsupport φ → X z = 0 := fun z hz =>
    mixedCoefficient_cons_eq_zero_of_notMem_tsupport hz
  have hpt : ∀ z ∈ (D : Set (ComplexModel (m + 1))),
      actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
        (smoothDDC (fun y => f (e.val.symm y)) z)) = (X z).re / Real.pi ^ (m + 1) := by
    intro z hz
    have hzt := hDt hz
    have hFeq : (fun y => f (e.val.symm y)) =ᶠ[𝓝 z] φ := by
      filter_upwards [D.isOpen.mem_nhds hz] with y hy
      exact (hφeq hy).symm
    have hFC : ContDiffAt ℝ 2 (fun y => f (e.val.symm y)) z :=
      (((hf e).contDiffAt (e.val.open_target.mem_nhds hzt))).of_le h2
    have hρC : ∀ i, ContDiffAt ℝ 2 (J.potential i) z := fun i =>
      ((J.localPotential i).2.2.1.contDiffAt (D.isOpen.mem_nhds hz)).of_le h2
    rw [actualMixedTopDensity_update_eq (fun i => (θ i).2.2 e z hzt) i₀ (smoothDDC_isOneOne hFC),
      normalizedHermitianMatrix_smoothDDC hFC]
    have hθρ : ∀ i, smoothDDC (J.potential i) z = (θ i).val.coeff e z := fun i =>
      (J.localPotential i).2.2.2 hz
    simp only [← hθρ, normalizedHermitianMatrix_smoothDDC (hρC _)]
    have hHF : complexHessian (fun y => f (e.val.symm y)) z = complexHessian φ z := by
      rw [← normalizedHermitianMatrix_smoothDDC hFC,
        ← normalizedHermitianMatrix_smoothDDC ((hφs.contDiffAt).of_le h2), smoothDDC_congr hFeq]
    rw [hHF]
    congr 2
    by_cases hzφ : z ∈ tsupport φ
    · have hψ1 : ∀ᶠ y in 𝓝 z, ψ y = 1 := hχ1.filter_mono (nhds_le_nhdsSet hzφ)
      have hhess : ∀ i, complexHessian (J.potential i) z = complexHessian (ρt i) z := by
        intro i
        have hloc : J.potential i =ᶠ[𝓝 z] ρt i := by
          filter_upwards [hψ1] with y hy
          simp [hρt, hy]
        rw [← normalizedHermitianMatrix_smoothDDC (hρC i),
          ← normalizedHermitianMatrix_smoothDDC ((hρts i).contDiffAt.of_le h2),
          smoothDDC_congr hloc]
      rw [hX]
      simp only [hhess, hρ']
    · rw [hX0 z hzφ, MixedHessian.mixedCoefficient_cons, complexHessian_eq_zero_of_notMem_tsupport hzφ]
      simp
  rw [setIntegral_congr_fun D.isOpen.measurableSet hpt]
  have hXc : Continuous X := continuous_mixedCoefficient_cons hρ's hφs
  have hXcs : HasCompactSupport X :=
    hφc.mono' fun z hz => by_contra fun h => hz (hX0 z h)
  have hXi : Integrable X := hXc.integrable_of_hasCompactSupport hXcs
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    rw [hX0 z fun h => hz (hφD h), Complex.zero_re, zero_div]]
  rw [integral_div]
  have hre : ∫ z, (X z).re = (∫ z, X z).re := integral_re (𝕜 := ℂ) hXi
  have hswap := integral_mul_mixedCoefficient_swap hρ's (a := φ) (b := fun _ => (1 : ℝ)) hφs
    contDiff_const hφc
  simp only [complexHessian_const, Complex.ofReal_one, one_mul] at hswap
  have hzero : ∫ z, X z = 0 := by
    rw [hX, ← hswap]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
    simp [MixedHessian.mixedCoefficient_cons]
  rw [hre, hzero]
  simp

end Local

/-! ### From slot charts to the manifold, for any local slot -/

section Global

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The chart-supported case, for any slot.**  If the slot `A` vanishes where `f` vanishes
and the slot-chart integral of the density vanishes, then `∫_M Φ = 0` for every top-degree
form `Φ` with that density. -/
theorem integral_topRatio_eq_zero_of_local (w : KahlerBackground N M)
    {θ : Fin N → ClosedRealOneOneForm N M} {κ : ClosedRealOneOneForm N M} (J : SlotChart θ κ)
    (i₀ : Fin N) {f : M → ℝ} (hfJ : tsupport f ⊆ (J.source : Set M))
    (A : ComplexChart N M → ComplexModel N → RealForm N 2)
    (hA0 : ∀ (e : ComplexChart N M) z, z ∈ e.val.target →
      (fun y => f (e.val.symm y)) =ᶠ[𝓝 z] 0 → A e z = 0)
    (hAloc : ∫ z in (J.domain : Set (ComplexModel N)), actualMixedTopDensity
      (Function.update (fun i => (θ i).val.coeff J.chart z) i₀ (A J.chart z)) = 0)
    (Φ : SmoothRealForm N M (2 * N))
    (hΦ : ∀ (e : ComplexChart N M) z, z ∈ e.val.target → topDensity (Φ.coeff e z) =
      actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀ (A e z))) :
    ∫ x, topRatio w.form.val Φ x ∂(kahlerVolume w) = 0 := by
  classical
  set e := J.chart with he
  set D := J.domain with hD
  have hDt : (D : Set (ComplexModel N)) ⊆ e.val.target := J.domain_le_target
  have hzero : ∀ x, x ∉ (J.source : Set M) → topRatio w.form.val Φ x = 0 := by
    intro x hx
    have hxf : x ∉ tsupport f := fun h => hx (hfJ h)
    have hxs := mem_complexChartAt_source (n := N) x
    have hz := (complexChartAt (n := N) x).val.map_source hxs
    have hslot : A (complexChartAt (n := N) x) ((complexChartAt (n := N) x).val x) = 0 :=
      hA0 _ _ hz (chart_eventuallyEq_zero hxf hxs)
    simp only [topRatio, chartRatio]
    rw [hΦ _ _ hz, hslot, ← actualMixedTopDensityMultilinear_apply,
      actualMixedTopDensityMultilinear.map_coord_zero i₀ (by simp), zero_div]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have himage : (J.source : Set M) = e.val.symm '' D := by
    rw [e.val.symm_image_eq_source_inter_preimage hDt]
    rfl
  have hω : ∀ _ : Fin N, ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin N => w.form) (fun _ _ => 0) hω := rfl
  rw [himage, hvol, setIntegral_image_eq hω e D.isOpen.measurableSet hDt
    (continuous_topRatio w.isKahler.1 Φ)]
  have hpt : ∀ z ∈ (D : Set (ComplexModel N)),
      (chartDensity (fun _ : Fin N => w.form) e z).toReal * topRatio w.form.val Φ (e.val.symm z) =
        actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀ (A e z)) := by
    intro z hz
    have hzt : z ∈ e.val.target := hDt hz
    have hx : e.val.symm z ∈ e.val.source := e.val.map_target hzt
    have hR : topRatio w.form.val Φ (e.val.symm z) = chartRatio w.form.val Φ e z := by
      rw [topRatio_eq_chartRatio w.isKahler.1 Φ hx, e.val.right_inv hzt]
    have hden : topDensity ((formPow w.form.val N).coeff e z) =
        actualMixedTopDensity fun _ => w.form.val.coeff e z := by
      rw [formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]
    have hpos := topDensity_formPow_pos w.isKahler.1 hzt
    rw [hR, chartRatio, chartDensity, ← hden, ENNReal.toReal_ofReal hpos.le,
      mul_div_cancel₀ _ hpos.ne', hΦ e z hzt]
  rw [setIntegral_congr_fun D.isOpen.measurableSet hpt]
  exact hAloc

/-- **Stokes on the manifold for a local slot.**  Let `S f` be a slot two-form, built from `f`,
which vanishes where `f` vanishes, is additive along partitions of unity, and has vanishing
slot-chart integrals for `f` supported in a slot chart.  Then `∫_M Φ f = 0` for every family
of top-degree forms `Φ f` whose density is the mixed density of the slots `θ` with the slot `i₀`
replaced by `S f`. -/
theorem integral_topRatio_eq_zero_of_slot (w : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M) (i₀ : Fin N)
    (S : (f : M → ℝ) → ChartSmooth (n := N) f → ComplexChart N M → ComplexModel N → RealForm N 2)
    (hS0 : ∀ (f : M → ℝ) (hf : ChartSmooth (n := N) f) (e : ComplexChart N M) z,
      z ∈ e.val.target → (fun y => f (e.val.symm y)) =ᶠ[𝓝 z] 0 → S f hf e z = 0)
    (hSsum : ∀ (r : ℕ) (χ : Fin r → M → ℝ) (hχ : ∀ a, ChartSmooth (n := N) (χ a)),
      (∀ x, ∑ a, χ a x = 1) → ∀ (f : M → ℝ) (hf : ChartSmooth (n := N) f)
        (e : ComplexChart N M) z, z ∈ e.val.target →
          S f hf e z = ∑ a, S (fun x => χ a x * f x) (chartSmooth_mul (hχ a) hf) e z)
    (hSloc : ∀ (J : SlotChart θ w.form) (f : M → ℝ) (hf : ChartSmooth (n := N) f),
      tsupport f ⊆ (J.source : Set M) → IsCompact (tsupport f) →
        ∫ z in (J.domain : Set (ComplexModel N)), actualMixedTopDensity
          (Function.update (fun i => (θ i).val.coeff J.chart z) i₀ (S f hf J.chart z)) = 0)
    (Φ : (f : M → ℝ) → ChartSmooth (n := N) f → SmoothRealForm N M (2 * N))
    (hΦ : ∀ (f : M → ℝ) (hf : ChartSmooth (n := N) f) (e : ComplexChart N M) z,
      z ∈ e.val.target → topDensity ((Φ f hf).coeff e z) =
        actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀ (S f hf e z)))
    {f : M → ℝ} (hf : ChartSmooth (n := N) f) :
    ∫ x, topRatio w.form.val (Φ f hf) x ∂(kahlerVolume w) = 0 := by
  classical
  obtain ⟨r, χ, idx, hχs, -, hχS, hχK, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := N)
      (fun J : SlotChart θ w.form => J.source) fun x => SlotChart.exists_mem_source θ w.form x
  have hχf : ∀ a, ChartSmooth (n := N) (fun x => χ a x * f x) := fun a =>
    chartSmooth_mul (hχs a) hf
  have hpiece : ∀ a, ∫ x, topRatio w.form.val (Φ _ (hχf a)) x ∂(kahlerVolume w) = 0 := by
    intro a
    have hsupp : tsupport (fun x => χ a x * f x) ⊆ ((idx a).source : Set M) :=
      tsupport_mul_subset_left.trans (hχS a)
    exact integral_topRatio_eq_zero_of_local w (idx a) i₀ hsupp (S _ (hχf a))
      (fun e z hz h0 => hS0 _ _ e z hz h0)
      (hSloc (idx a) _ (hχf a) hsupp
        ((hχK a).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left))
      _ (hΦ _ (hχf a))
  have hsplitc : ∀ (e : ComplexChart N M) z, z ∈ e.val.target →
      chartRatio w.form.val (Φ f hf) e z = ∑ a, chartRatio w.form.val (Φ _ (hχf a)) e z := by
    intro e z hz
    have hΦa : ∀ a, topDensity ((Φ _ (hχf a)).coeff e z) =
        actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
          (S _ (hχf a) e z)) := fun a => hΦ _ (hχf a) e z hz
    unfold chartRatio
    rw [← Finset.sum_div, hΦ f hf e z hz]
    simp only [hΦa]
    rw [hSsum r χ hχs hsum f hf e z hz, ← actualMixedTopDensityMultilinear_apply,
      MultilinearMap.map_update_sum]
    rfl
  have hsplit : ∀ x, topRatio w.form.val (Φ f hf) x =
      ∑ a, topRatio w.form.val (Φ _ (hχf a)) x := fun x =>
    hsplitc _ _ ((complexChartAt (n := N) x).val.map_source (mem_complexChartAt_source x))
  simp_rw [hsplit]
  rw [integral_finsetSum _ fun a _ => integrable_topRatio w _]
  exact Finset.sum_eq_zero fun a _ => hpiece a

/-- **Stokes for `ddᶜf ∧ θ₁ ∧ ⋯` on a compact Kähler manifold** (closed slots, no positivity):
`∫_M Φ = 0` whenever the density of `Φ` is, in every chart, the mixed density of the closed
slots `θ` with the slot `i₀` replaced by `ddᶜf`. -/
theorem integral_topRatio_ddc_eq_zero (w : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M) (i₀ : Fin N)
    (Φ : (f : M → ℝ) → ChartSmooth (n := N) f → SmoothRealForm N M (2 * N))
    (hΦ : ∀ (f : M → ℝ) (hf : ChartSmooth (n := N) f) (e : ComplexChart N M) z,
      z ∈ e.val.target → topDensity ((Φ f hf).coeff e z) =
        actualMixedTopDensity (Function.update (fun i => (θ i).val.coeff e z) i₀
          (smoothDDC (fun y => f (e.val.symm y)) z)))
    {f : M → ℝ} (hf : ChartSmooth (n := N) f) :
    ∫ x, topRatio w.form.val (Φ f hf) x ∂(kahlerVolume w) = 0 := by
  refine integral_topRatio_eq_zero_of_slot w θ i₀
    (fun f _ e z => smoothDDC (fun y => f (e.val.symm y)) z) ?_ ?_
    (fun J f hf hfJ hfK => setIntegral_ddcSlots_eq_zero J i₀ hf hfJ hfK) Φ hΦ hf
  · intro f hf e z _ h0
    rw [smoothDDC_congr h0]
    exact smoothDDC_zero z
  · intro r χ hχ hsum f hf e z hz
    have hfun : (fun y => f (e.val.symm y)) =
        fun y => ∑ a, (fun y => χ a (e.val.symm y) * f (e.val.symm y)) y := by
      funext y
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [hfun, smoothDDC_sum _ e.val.open_target (fun a _ => (chartSmooth_mul (hχ a) hf) e) hz]

end Global

/-! ### Products of smooth two-forms and total mixed masses -/

section Products

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- The product `β₀ ∧ ⋯ ∧ β_{k-1}` of smooth two-forms (unit first, as `wedgeProd`). -/
def formProd : (k : ℕ) → (Fin k → SmoothRealForm N M 2) → SmoothRealForm N M (2 * k)
  | 0, _ => unitForm
  | k + 1, β => wedgeTwo (formProd k fun i => β i.castSucc) (β (Fin.last k))

theorem formProd_coeff : ∀ (k : ℕ) (β : Fin k → SmoothRealForm N M 2) (e : ComplexChart N M)
    (z : ComplexModel N), (formProd k β).coeff e z = wedgeProd k fun i => (β i).coeff e z
  | 0, _, _, _ => rfl
  | k + 1, β, e, z => by
    rw [formProd, wedgeTwo_coeff, formProd_coeff k, wedgeProd_succ]

/-- The top-degree form `θ₀ ∧ ⋯ ∧ θ_{N-1}` of a family of closed `(1,1)`-forms. -/
def slotForm (θ : Fin N → ClosedRealOneOneForm N M) : SmoothRealForm N M (2 * N) :=
  formProd N fun i => (θ i).val

theorem topDensity_slotForm_coeff (θ : Fin N → ClosedRealOneOneForm N M) (e : ComplexChart N M)
    (z : ComplexModel N) :
    topDensity ((slotForm θ).coeff e z) = actualMixedTopDensity fun i => (θ i).val.coeff e z := by
  rw [slotForm, formProd_coeff, topDensity_wedgeProd]

theorem update_coeff (θ : Fin N → ClosedRealOneOneForm N M) (i₀ : Fin N)
    (β : ClosedRealOneOneForm N M) (e : ComplexChart N M) (z : ComplexModel N) :
    (fun i => (Function.update θ i₀ β i).val.coeff e z) =
      Function.update (fun i => (θ i).val.coeff e z) i₀ (β.val.coeff e z) := by
  classical
  funext i
  by_cases h : i = i₀
  · subst h
    simp
  · simp [Function.update_of_ne h]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Changing one slot by `ddᶜf` does not change `∫_M θ₀ ∧ ⋯ ∧ θ_{N-1}`** (closed slots, no
positivity). -/
theorem integral_topRatio_slotForm_update_add_ddc (w : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M) (i₀ : Fin N) {f : M → ℝ}
    (hf : ChartSmooth (n := N) f) :
    ∫ x, topRatio w.form.val (slotForm (Function.update θ i₀ (θ i₀ + ddcClosedForm f hf))) x
        ∂(kahlerVolume w) =
      ∫ x, topRatio w.form.val (slotForm θ) x ∂(kahlerVolume w) := by
  classical
  have hddc := integral_topRatio_ddc_eq_zero w θ i₀
    (fun f hf => slotForm (Function.update θ i₀ (ddcClosedForm f hf)))
    (fun f hf e z _ => by
      rw [topDensity_slotForm_coeff, update_coeff]
      rfl) hf
  have hpt : ∀ x, topRatio w.form.val
      (slotForm (Function.update θ i₀ (θ i₀ + ddcClosedForm f hf))) x =
      topRatio w.form.val (slotForm θ) x +
        topRatio w.form.val (slotForm (Function.update θ i₀ (ddcClosedForm f hf))) x := by
    intro x
    simp only [topRatio, chartRatio]
    rw [← add_div]
    congr 1
    rw [topDensity_slotForm_coeff, topDensity_slotForm_coeff, topDensity_slotForm_coeff,
      update_coeff, update_coeff]
    set B := fun i => (θ i).val.coeff (complexChartAt (n := N) x) ((complexChartAt (n := N) x).val x)
    have hsum : (θ i₀ + ddcClosedForm f hf).val.coeff (complexChartAt (n := N) x)
        ((complexChartAt (n := N) x).val x) =
        B i₀ + (ddcClosedForm f hf).val.coeff (complexChartAt (n := N) x)
          ((complexChartAt (n := N) x).val x) := rfl
    rw [hsum, ← actualMixedTopDensityMultilinear_apply, MultilinearMap.map_update_add,
      Function.update_eq_self]
    rfl
  simp_rw [hpt]
  rw [integral_add (integrable_topRatio w _) (integrable_topRatio w _), hddc, add_zero]

/-- **Changing every slot by a `ddᶜ` does not change `∫_M θ₀ ∧ ⋯ ∧ θ_{N-1}`** (closed slots, no
positivity). -/
theorem integral_topRatio_slotForm_add_ddc (w : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M) (f : Fin N → M → ℝ)
    (hf : ∀ i, ChartSmooth (n := N) (f i)) :
    ∫ x, topRatio w.form.val (slotForm fun i => θ i + ddcClosedForm (f i) (hf i)) x
        ∂(kahlerVolume w) =
      ∫ x, topRatio w.form.val (slotForm θ) x ∂(kahlerVolume w) := by
  classical
  set η : Finset (Fin N) → Fin N → ClosedRealOneOneForm N M := fun s i =>
    if i ∈ s then θ i + ddcClosedForm (f i) (hf i) else θ i with hη
  have key : ∀ s : Finset (Fin N), ∫ x, topRatio w.form.val (slotForm (η s)) x ∂(kahlerVolume w) =
      ∫ x, topRatio w.form.val (slotForm θ) x ∂(kahlerVolume w) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      congr 3
    | insert a s ha ih =>
      have hupd : η (insert a s) = Function.update (η s) a (η s a + ddcClosedForm (f a) (hf a)) := by
        funext i
        by_cases h : i = a
        · subst h
          simp [hη, ha]
        · simp [hη, Finset.mem_insert, h]
      rw [hupd, integral_topRatio_slotForm_update_add_ddc w (η s) a (hf a), ih]
  have huniv : (fun i => θ i + ddcClosedForm (f i) (hf i)) = η Finset.univ := by
    funext i
    simp [hη]
  rw [huniv, key]

/-- For semipositive closed slots with potentials `0`, the total mixed mass is `∫_M θ₀ ∧ ⋯`. -/
theorem globalMixedMeasure_real_univ_eq_integral (w : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M)
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) :
    (globalMixedMeasure θ (fun _ _ => 0) hθ).real univ =
      ∫ x, topRatio w.form.val (slotForm θ) x ∂(kahlerVolume w) := by
  have hnn : ∀ x, 0 ≤ topRatio w.form.val (slotForm θ) x := by
    intro x
    have hz := (complexChartAt (n := N) x).val.map_source (mem_complexChartAt_source x)
    simp only [topRatio, chartRatio]
    rw [topDensity_slotForm_coeff]
    exact div_nonneg (actualMixedTopDensity_nonneg fun i => isSemipositiveOneOne_coeff (hθ i) hz)
      (topDensity_formPow_pos w.isKahler.1 hz).le
  rw [← SmoothCurrentTraceMeasure.withDensity_topRatio_eq_globalMixedMeasure w (slotForm θ) hθ
      fun e z _ => topDensity_slotForm_coeff θ e z,
    measureReal_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn)
      (continuous_topRatio w.isKahler.1 _).aestronglyMeasurable]

/-- **Total mixed masses of smooth closed semipositive forms depend only on the classes**:
if `θᵢ` and `θᵢ + ddᶜfᵢ` are semipositive closed real `(1,1)`-forms, the global mixed measures
with potentials `0` of the two families have the same total mass. -/
theorem globalMixedMeasure_real_univ_add_ddc (w : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M)
    (hθ : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0)) (f : Fin N → M → ℝ)
    (hf : ∀ i, ChartSmooth (n := N) (f i))
    (hθ' : ∀ i, ThetaPlurisubharmonic (θ i + ddcClosedForm (f i) (hf i)).val (fun _ => 0)) :
    (globalMixedMeasure (fun i => θ i + ddcClosedForm (f i) (hf i)) (fun _ _ => 0) hθ').real univ =
      (globalMixedMeasure θ (fun _ _ => 0) hθ).real univ := by
  rw [globalMixedMeasure_real_univ_eq_integral w _ hθ', globalMixedMeasure_real_univ_eq_integral w _ hθ,
    integral_topRatio_slotForm_add_ddc w θ f hf]

end Products

end SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance

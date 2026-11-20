import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes
import SGPT.Foundations.Analysis.Pending.MixedHessianDivergence
import SGPT.Foundations.Analysis.Pending.ManifoldHolderSpace
import SGPT.Foundations.Analysis.Pending.DistributionRegularization
import SGPT.Foundations.Analysis.Pending.YauUniformEstimate

/-!
# Green's identity for the Kähler Laplacian

Lane LAP-CLASS (`claude-lap-class`, node `lap-class:green`).  On a compact Kähler manifold
`(M, ω)` (`w : KahlerBackground N M`, Kähler volume `ω^N`) the Laplacian
`Δ_ω u = Re tr(H⁻¹ ∂∂̄u)` (TN `KahlerLaplacianChart.laplacian`) is symmetric:

* `integral_mul_laplacian_symm`: `∫ u Δ_ω v ω^N = ∫ v Δ_ω u ω^N` for chart-smooth `u, v`.

This is what makes `χ ↦ ∫ f Δ_ω χ ω^N` the distribution `Δ_ω f` (FPT,
`sec:penalized-kahler-envelopes`: `D_h` is formally self-adjoint), the definition of the bounded
metric Laplacian in `SGPT.Envelopes.LapClassDef`.

## Proof

TN proves Stokes `∫ Δ_ω u ω^N = 0` (`KahlerLaplacianStokes.integral_laplacian_eq_zero`) through a
partition of unity subordinate to charts carrying a local potential `ρ` of `ω` and the chart
identity `Δ_ω v · ω^N = N ddᶜv ∧ ω^{N-1}`, i.e. `(density) · Δ_ω v = N Re C(∂∂̄v, ∂∂̄ρ, …)/π^N`
(`chartDensity_mul_chartLaplacian`).  The same reduction, with TN's integration by parts for mixed
complex Hessians `∫ a C(∂∂̄b, …) = ∫ b C(∂∂̄a, …)` (`integral_mul_mixedCoefficient_swap`, `a` with
compact support) in place of `∫ C(∂∂̄a, …) = 0`, gives the symmetry.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart KahlerLaplacianStokes FirstPass.PositiveClasses ProductTestForms
  IntegrationCurrent TopDegreeDensity SmoothMixedMeasureDensity GlobalNonPluripolar GlobalSlotStokes
  ChartPartition SmoothCurrentClosedness MixedHessian

section Green

theorem chartSmooth_two' {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {u : M → ℝ}
    (hu : ChartSmooth (n := n) u) :
    ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun w => u (e.val.symm w)) e.val.target :=
  fun e => (hu e).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Green's identity in a slot chart**: for chart-smooth `f, v` with `f` supported in a compact
subset of the source of a slot chart, `∫ f Δ_ω v ω^N = ∫ v Δ_ω f ω^N`. -/
theorem integral_mul_laplacian_symm_of_slotChart (w : KahlerBackground (m + 1) M)
    (J : SlotChart (fun _ : Fin (m + 1) => w.form) w.form) {f v : M → ℝ}
    (hf : ChartSmooth (n := m + 1) f) (hv : ChartSmooth (n := m + 1) v)
    (hfJ : tsupport f ⊆ (J.source : Set M)) (hfK : IsCompact (tsupport f)) :
    ∫ x, f x * laplacian w.form.val v x ∂(kahlerVolume w) =
      ∫ x, v x * laplacian w.form.val f x ∂(kahlerVolume w) := by
  classical
  have hg : w.form.val.IsHermitian := w.isKahler.1
  have hf2 := chartSmooth_two' hf
  have hv2 := chartSmooth_two' hv
  set e := J.chart with he
  set D := J.domain with hD
  have hDt : (D : Set (ComplexModel (m + 1))) ⊆ e.val.target := J.domain_le_target
  -- both integrands vanish off the source of `J`
  have hz1 : ∀ x, x ∉ (J.source : Set M) → f x * laplacian w.form.val v x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hfJ h)), zero_mul]
  have hz2 : ∀ x, x ∉ (J.source : Set M) → v x * laplacian w.form.val f x = 0 := fun x hx => by
    rw [laplacian_eq_zero_of_notMem_tsupport _ (fun h => hx (hfJ h)), mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hz2]
  have himage : (J.source : Set M) = e.val.symm '' D := by
    rw [e.val.symm_image_eq_source_inter_preimage hDt]
    rfl
  have hω : ∀ _ : Fin (m + 1), ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin (m + 1) => w.form) (fun _ _ => 0) hω := rfl
  have hc1 : Continuous fun x => f x * laplacian w.form.val v x :=
    (YauUniformEstimate.continuous_of_chartSmooth hf).mul (continuous_laplacian hg hv2)
  have hc2 : Continuous fun x => v x * laplacian w.form.val f x :=
    (YauUniformEstimate.continuous_of_chartSmooth hv).mul (continuous_laplacian hg hf2)
  rw [himage, hvol, setIntegral_image_eq hω e D.isOpen.measurableSet hDt hc1,
    setIntegral_image_eq hω e D.isOpen.measurableSet hDt hc2]
  -- the chart representative `V` of `f`
  have hfe : tsupport f ⊆ e.val.source := hfJ.trans fun x hx => hx.1
  obtain ⟨hVs, hVc, -⟩ := HolderAtlas.HolderMap.contDiff_indicator_comp_symm e hf hfK hfe
  obtain ⟨-, -, hVt⟩ := contDiff_indicator_comp_symm_two e (hf2 e) hfK hfe
  set V : ComplexModel (m + 1) → ℝ := e.val.target.indicator (f ∘ e.val.symm) with hVdef
  have hVt' : tsupport V ⊆ e.val '' tsupport f := hVt
  have hVD : tsupport V ⊆ D := hVt'.trans (by rintro _ ⟨x, hx, rfl⟩; exact (hfJ hx).2)
  -- cut-offs equal to `1` near the support of `V`
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := D) hVc hVD
  set ψ : ComplexModel (m + 1) → ℝ := ⇑χ with hψ
  have hψs : ContDiff ℝ ∞ ψ := χ.contDiff
  have hψD : tsupport ψ ⊆ (D : Set (ComplexModel (m + 1))) := χ.tsupport_subset
  set ρt : ComplexModel (m + 1) → ℝ := fun z => ψ z * J.potential 0 z with hρt
  have hρts : ContDiff ℝ ∞ ρt :=
    SmoothCurrentClosedness.contDiff_mul_of_tsupport_subset D.isOpen hψs hψD
      (J.localPotential 0).2.2.1
  set vt : ComplexModel (m + 1) → ℝ := fun z => ψ z * v (e.val.symm z) with hvt
  have hvts : ContDiff ℝ ∞ vt :=
    SmoothCurrentClosedness.contDiff_mul_of_tsupport_subset D.isOpen hψs hψD ((hv e).mono hDt)
  have hswap := MixedHessian.integral_mul_mixedCoefficient_swap
    (g := fun _ : Fin m => ρt) (fun _ => hρts) hVs hvts hVc
  -- the germs near the support of `V`
  have hgerm : ∀ z ∈ tsupport V, ∀ᶠ y in 𝓝 z, ψ y = 1 := fun z hz =>
    hχ1.filter_mono (nhds_le_nhdsSet hz)
  have hH : ∀ z ∈ tsupport V,
      normalizedHermitianMatrix (w.form.val.coeff e z) = complexHessian ρt z := by
    intro z hz
    have hzD : z ∈ (D : Set (ComplexModel (m + 1))) := hVD hz
    have hloc : J.potential 0 =ᶠ[𝓝 z] ρt := by
      filter_upwards [hgerm z hz] with y hy
      simp [hρt, hy]
    have hρC : ContDiffAt ℝ 2 (J.potential 0) z :=
      ((J.localPotential 0).2.2.1.contDiffAt (D.isOpen.mem_nhds hzD)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    rw [← complexHessian_congr' hloc, ← normalizedHermitianMatrix_smoothDDC hρC,
      (J.localPotential 0).2.2.2 hzD]
  have hVeq : ∀ z ∈ (D : Set (ComplexModel (m + 1))), V z = f (e.val.symm z) := fun z hz => by
    rw [hVdef, indicator_of_mem (hDt hz)]
    rfl
  have hVgerm : ∀ z ∈ (D : Set (ComplexModel (m + 1))),
      V =ᶠ[𝓝 z] fun y => f (e.val.symm y) := fun z hz => by
    filter_upwards [e.val.open_target.mem_nhds (hDt hz)] with y hy
    rw [hVdef, indicator_of_mem hy]
    rfl
  -- pointwise identities on `D`
  have hpt1 : ∀ z ∈ (D : Set (ComplexModel (m + 1))),
      (chartDensity (fun _ : Fin (m + 1) => w.form) e z).toReal *
          (f (e.val.symm z) * laplacian w.form.val v (e.val.symm z)) =
        (m + 1) * (((V z : ℂ) * mixedCoefficient (Fin.cons (complexHessian vt z)
          (fun _ : Fin m => complexHessian ρt z) :
            Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re) / Real.pi ^ (m + 1) := by
    intro z hz
    have hzt := hDt hz
    by_cases hzV : z ∈ tsupport V
    · have hl : laplacian w.form.val v (e.val.symm z) =
          chartLaplacian w.form.val e (fun y => v (e.val.symm y)) z := by
        rw [laplacian_eq hg hv2 (e.val.map_target hzt), e.val.right_inv hzt]
      have hvloc : vt =ᶠ[𝓝 z] fun y => v (e.val.symm y) := by
        filter_upwards [hgerm z hzV] with y hy
        simp [hvt, hy]
      rw [hl, ← hVeq z hz, mul_left_comm, chartDensity_mul_chartLaplacian w e hzt,
        complexHessian_congr' hvloc, hH z hzV, Complex.re_ofReal_mul]
      ring
    · have hV0 : V z = 0 := image_eq_zero_of_notMem_tsupport hzV
      rw [← hVeq z hz, hV0]
      simp
  have hpt2 : ∀ z ∈ (D : Set (ComplexModel (m + 1))),
      (chartDensity (fun _ : Fin (m + 1) => w.form) e z).toReal *
          (v (e.val.symm z) * laplacian w.form.val f (e.val.symm z)) =
        (m + 1) * (((vt z : ℂ) * mixedCoefficient (Fin.cons (complexHessian V z)
          (fun _ : Fin m => complexHessian ρt z) :
            Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re) / Real.pi ^ (m + 1) := by
    intro z hz
    have hzt := hDt hz
    have hl : laplacian w.form.val f (e.val.symm z) = chartLaplacian w.form.val e V z := by
      rw [laplacian_eq hg hf2 (e.val.map_target hzt), e.val.right_inv hzt]
      unfold chartLaplacian
      rw [complexHessian_congr' (hVgerm z hz)]
    by_cases hzV : z ∈ tsupport V
    · have hψ1 : ψ z = 1 := (hgerm z hzV).self_of_nhds
      have hvz : vt z = v (e.val.symm z) := by simp [hvt, hψ1]
      rw [hl, mul_left_comm, chartDensity_mul_chartLaplacian w e hzt, hH z hzV, hvz,
        Complex.re_ofReal_mul]
      ring
    · rw [hl]
      unfold chartLaplacian
      rw [complexHessian_eq_zero_of_notMem_tsupport hzV]
      simp [MixedHessian.mixedCoefficient_cons]
  rw [setIntegral_congr_fun D.isOpen.measurableSet hpt1,
    setIntegral_congr_fun D.isOpen.measurableSet hpt2]
  -- extend to the whole space
  have hzero1 : ∀ z ∉ (D : Set (ComplexModel (m + 1))),
      (m + 1) * (((V z : ℂ) * mixedCoefficient (Fin.cons (complexHessian vt z)
        (fun _ : Fin m => complexHessian ρt z) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re) / Real.pi ^ (m + 1) = 0 := by
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hVD h))]
    simp
  have hzero2 : ∀ z ∉ (D : Set (ComplexModel (m + 1))),
      (m + 1) * (((vt z : ℂ) * mixedCoefficient (Fin.cons (complexHessian V z)
        (fun _ : Fin m => complexHessian ρt z) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re) / Real.pi ^ (m + 1) = 0 := by
    intro z hz
    rw [MixedHessian.mixedCoefficient_cons_eq_zero_of_notMem_tsupport
      (fun h => hz (hVD h))]
    simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  -- integrability and the swap
  have hi1 : Integrable fun z => (V z : ℂ) * mixedCoefficient (Fin.cons (complexHessian vt z)
      (fun _ : Fin m => complexHessian ρt z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :=
    ((Complex.continuous_ofReal.comp hVs.continuous).mul
      (MixedHessian.continuous_mixedCoefficient_cons (fun _ => hρts) hvts)).integrable_of_hasCompactSupport
      (hVc.comp_left Complex.ofReal_zero).mul_right
  have hi2 : Integrable fun z => (vt z : ℂ) * mixedCoefficient (Fin.cons (complexHessian V z)
      (fun _ : Fin m => complexHessian ρt z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    refine ((Complex.continuous_ofReal.comp hvts.continuous).mul
      (MixedHessian.continuous_mixedCoefficient_cons (fun _ => hρts)
        hVs)).integrable_of_hasCompactSupport (hVc.mono' fun z hz => ?_)
    by_contra h
    have h0 := MixedHessian.mixedCoefficient_cons_eq_zero_of_notMem_tsupport
      (g := fun _ : Fin m => ρt) h
    apply hz
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [h0, mul_zero]
  have hre1 : ∫ z, ((V z : ℂ) * mixedCoefficient (Fin.cons (complexHessian vt z)
      (fun _ : Fin m => complexHessian ρt z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re =
      (∫ z, (V z : ℂ) * mixedCoefficient (Fin.cons (complexHessian vt z)
      (fun _ : Fin m => complexHessian ρt z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re := integral_re hi1
  have hre2 : ∫ z, ((vt z : ℂ) * mixedCoefficient (Fin.cons (complexHessian V z)
      (fun _ : Fin m => complexHessian ρt z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re =
      (∫ z, (vt z : ℂ) * mixedCoefficient (Fin.cons (complexHessian V z)
      (fun _ : Fin m => complexHessian ρt z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)).re := integral_re hi2
  simp only [mul_div_assoc]
  rw [integral_const_mul, integral_const_mul, integral_div, integral_div, hre1, hre2, hswap]

/-- **Green's identity on a compact Kähler manifold**: `∫ u Δ_ω v ω^N = ∫ v Δ_ω u ω^N` for
chart-smooth `u, v`. -/
theorem integral_mul_laplacian_symm (w : KahlerBackground (m + 1) M) {u v : M → ℝ}
    (hu : ChartSmooth (n := m + 1) u) (hv : ChartSmooth (n := m + 1) v) :
    ∫ x, u x * laplacian w.form.val v x ∂(kahlerVolume w) =
      ∫ x, v x * laplacian w.form.val u x ∂(kahlerVolume w) := by
  classical
  have hg : w.form.val.IsHermitian := w.isKahler.1
  obtain ⟨r, χ, idx, hχs, -, hχS, hχK, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := m + 1)
      (fun J : SlotChart (fun _ : Fin (m + 1) => w.form) w.form => J.source)
      fun x => SlotChart.exists_mem_source _ w.form x
  have hpiece : ∀ a, ChartSmooth (n := m + 1) (fun y => χ a y * u y) := fun a e =>
    ((hχs a) e).mul (hu e)
  have hfun : u = fun y => ∑ a, χ a y * u y := funext fun y => by
    rw [← Finset.sum_mul, hsum, one_mul]
  have hsplitL : ∀ x, u x * laplacian w.form.val v x =
      ∑ a, χ a x * u x * laplacian w.form.val v x := fun x => by
    conv_lhs => rw [hfun]
    rw [Finset.sum_mul]
  have hsplitR : ∀ x, v x * laplacian w.form.val u x =
      ∑ a, v x * laplacian w.form.val (fun y => χ a y * u y) x := fun x => by
    conv_lhs => rw [hfun]
    rw [laplacian_sum _ _ (fun a _ => chartSmooth_two' (hpiece a)), Finset.mul_sum]
  have hcomp : ∀ (g : M → ℝ), Continuous g → Integrable g (kahlerVolume w) := fun g hg =>
    hg.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have h1 : ∫ x, u x * laplacian w.form.val v x ∂(kahlerVolume w) =
      ∑ a, ∫ x, χ a x * u x * laplacian w.form.val v x ∂(kahlerVolume w) := by
    rw [← integral_finsetSum]
    · congr 1
      funext x
      exact hsplitL x
    · intro a _
      exact hcomp _ ((YauUniformEstimate.continuous_of_chartSmooth
        (hpiece a)).mul (continuous_laplacian hg (chartSmooth_two' hv)))
  have h2 : ∫ x, v x * laplacian w.form.val u x ∂(kahlerVolume w) =
      ∑ a, ∫ x, v x * laplacian w.form.val (fun y => χ a y * u y) x ∂(kahlerVolume w) := by
    rw [← integral_finsetSum]
    · congr 1
      funext x
      exact hsplitR x
    · intro a _
      exact hcomp _ ((YauUniformEstimate.continuous_of_chartSmooth
        hv).mul (continuous_laplacian hg (chartSmooth_two' (hpiece a))))
  rw [h1, h2]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact integral_mul_laplacian_symm_of_slotChart w (idx a) (hpiece a) hv
    (tsupport_mul_subset_left.trans (hχS a))
    ((hχK a).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)

end Green

end SGPT.Envelopes.LapClass

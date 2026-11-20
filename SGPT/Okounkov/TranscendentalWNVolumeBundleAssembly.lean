import SGPT.Okounkov.TranscendentalWNVolumeBundleChart
import SGPT.Okounkov.TranscendentalWNVolumeGlobalExcInput

/-!
# The bundle Legendre identity and the restricted volume along `ℰ` (package WN-VF4)

Blueprint `claude-tok-wn-vf3`, nodes `tok-wn-vf3:bundle-legendre-ma` and `tok-wn-wn:formula-E`
route; `claude-tok-wn-vf4`, node `tok-wn-vf4:bundle-chart`.

* `excBundleChart : ExcBundleChartStatement F` — the bundle charts of `ℰ` exist over a chart
  domain around every point of `Z` (WN21 §4: the `τ`-monomial chart `z₁ = z̃₁ τ` at `τ = 0`), with
  the fibre norm `S₂ / S₁ = |w|² e^{-g}` and the twist `g = -log(|s_Z|²_h / |z₁|²)`, a local
  potential of `η|_Z`.
* `excBundleLegendreMA : ExcBundleLegendreMAStatement F` — WN21 Theorem 3.5 on
  `ℰ \ (X' ∪ Z̃)`.
* `exceptionalRestrictedVolume_formula : ExceptionalRestrictedVolumeStatement F` —
  `tok-wn:formula-E` (WN21 Theorem 1.6 (4)), with the `excLegendreInput` and lane
  WN-VF3's reduction `exceptionalRestrictedVolume_of_bundleLegendre`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN.LSC

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-vf4:bundle-chart`**: the bundle charts of `ℰ` exist. -/
theorem excBundleChart : ExcBundleChartStatement F := by
  intro E hE 𝒳 _ _ _ μ hμ y₀
  classical
  obtain ⟨S⟩ := nonempty_bundleSetup F hμ y₀
  obtain ⟨hΦsrc, -, hflat⟩ := zFlat_spec F y₀
  obtain ⟨N, hN, hx₀N, hNf, G, hGpos, hGc, hGs, hfac⟩ := exists_weight_factor F hE hΦsrc hflat
  have hpotη := isSmoothLocalPotential_neg_log_factor F hE hflat hN hNf hGpos hGs hfac
  set e : ComplexChart (m + 1) F.carrier := complexChartAt (n := m + 1) y₀.1 with hedef
  set U' := e.val.target ∩ e.val.symm ⁻¹' N with hU'
  set eZ : ComplexChart m F.tail.carrier := complexChartAt (n := m) y₀ with heZ
  have hι := contMDiff_firstFlagInclusion F
  set Ω := potentialDomain (firstFlagInclusion F) eZ e U' with hΩdef
  have hΩo : IsOpen Ω := potentialDomain_isOpen hι eZ e hpotη.1
  have hΩt : Ω ⊆ eZ.val.target := fun ζ h => h.1.1
  have hΩN : ∀ ζ ∈ Ω, firstFlagInclusion F (eZ.val.symm ζ) ∈ N := by
    intro ζ h
    have h2 : e.val.symm (e.val (firstFlagInclusion F (eZ.val.symm ζ))) ∈ N := h.2.2
    rwa [e.val.left_inv h.1.2] at h2
  set g : ComplexModel m → ℝ := fun ζ => -Real.log (G (firstFlagInclusion F (eZ.val.symm ζ)))
    with hgdef
  have htwist : IsSmoothLocalPotential
      (ClosedRealOneOneForm.pullback (contMDiff_firstFlagInclusion F) E.curvature).val eZ Ω g := by
    refine IsSmoothLocalPotential.of_eqOn_sub_const (K := 0)
      (isSmoothLocalPotential_pullback hι eZ hpotη) fun ζ h => ?_
    simp only [hgdef, Function.comp_apply, coordinateMap, sub_zero]
    rw [e.val.left_inv h.1.2]
  have hw : ∀ ζ ∈ Ω, ∀ w : ℂ, strictWeight F E μ (S.Λ ζ w) =
      1 / (‖w‖ ^ 2 * G (firstFlagInclusion F (eZ.val.symm ζ)) + 1) ∧
      zStrictWeight F E μ (S.Λ ζ w) = ‖w‖ ^ 2 * G (firstFlagInclusion F (eZ.val.symm ζ)) /
        (‖w‖ ^ 2 * G (firstFlagInclusion F (eZ.val.symm ζ)) + 1) := fun ζ hζ w =>
    S.weights_eq hμ hE hN hGpos hGc hfac (hΩt hζ) (hΩN ζ hζ) w
  have hS1pos : ∀ ζ ∈ Ω, ∀ w : ℂ, 0 < strictWeight F E μ (S.Λ ζ w) := by
    intro ζ hζ w
    rw [(hw ζ hζ w).1]
    have := hGpos _ (hΩN ζ hζ)
    positivity
  -- the `τ`-chart data at a point of `ℰ \ X'` over the chart
  have hflatΛ : ∀ ζ ∈ Ω, ∀ w : ℂ, μ (S.Λ ζ w) ∈ flatDomain S.Ψ := fun ζ hζ w =>
    (S.flat_μ_ℓ _).1
  have hnotX : ∀ ζ ∈ Ω, ∀ w : ℂ, S.Λ ζ w ∉ strictCentralFibre F μ := fun ζ hζ w =>
    notMem_strict_of_strictWeight_pos hμ hE (hS1pos ζ hζ w)
  refine ⟨eZ, Ω, S.Λ, g, ⟨hΩo, hΩt, fun ζ hζ w => S.Λ_mem (hΩt hζ) w,
    fun ζ hζ w => by rw [S.μ_Λ (hΩt hζ) w]; rfl, ?_, ?_, ?_, htwist, ?_⟩,
    mem_chart_source _ _, ?_⟩
  · -- injectivity in the fibre coordinate
    intro ζ hζ w w' hww'
    obtain ⟨O, hO, hzO, W, hW, hWμ, hℓW⟩ := S.exists_tau_inverse hμ (hflatΛ ζ hζ w)
      (S.Λ_mem (hΩt hζ) w) (hnotX ζ hζ w)
    let C : ExcChart F μ (S.Λ ζ w) := ⟨y₀.1, S.Ψ, S.hΨsrc, fun hy hy' => S.hΨflat hy hy',
      S.hΨτ, idxT m, Or.inr rfl, S.ℓ, S.hℓ, S.hμℓ, O, hO, hzO, W, hW, hWμ, hℓW⟩
    have e1 : W (S.Λ ζ w) = bvec ζ w 0 := C.W_ℓ (S.bvec_mem_zero (hΩt hζ) w) hzO
    have e2 : W (S.Λ ζ w') = bvec ζ w' 0 :=
      C.W_ℓ (S.bvec_mem_zero (hΩt hζ) w') (show S.Λ ζ w' ∈ O by rw [← hww']; exact hzO)
    have h3 : bvec ζ w 0 = bvec ζ w' 0 := by rw [← e1, ← e2, hww']
    have h4 := congrArg (fun v => (stripModelEquiv m ((splitL m).symm v).1).2) h3
    simpa [bvec] using h4
  · -- the cover
    intro p hp h1 h2 ζ hζ hpζ
    have hpX : p ∉ strictCentralFibre F μ := notMem_strict_of_strictWeight_pos hμ hE h1
    have hp0 : (μ p).2 = projectiveZero := ((mem_deformationCentre_iff F).mp hp).2
    have hζt := hΩt hζ
    set u := (zFlat F y₀).invFun (RegularLocusDense.coordinateInclusion (m + 1) m ζ) with hudef
    have hut : RegularLocusDense.coordinateInclusion (m + 1) m ζ ∈ (zFlat F y₀).target := hζt
    have hus : u ∈ (zFlat F y₀).source := (zFlat F y₀).mapsTo_invFun hut
    have hx : (μ p).1 = (chartAt (ComplexModel (m + 1)) y₀.1).symm u := by
      rw [hpζ]; exact chartAt_tail_symm F y₀ hζt
    have hxs : (μ p).1 ∈ (chartAt (ComplexModel (m + 1)) y₀.1).source := by
      rw [hx]; exact (chartAt (ComplexModel (m + 1)) y₀.1).map_target (hΦsrc hus)
    have hcx : chartAt (ComplexModel (m + 1)) y₀.1 (μ p).1 = u := by
      rw [hx]; exact (chartAt (ComplexModel (m + 1)) y₀.1).right_inv (hΦsrc hus)
    have hbc : baseChart F y₀.1 (μ p) =
        splitL m (chartAt (ComplexModel (m + 1)) y₀.1 (μ p).1, zeroChart (μ p).2) := rfl
    have hpf : μ p ∈ flatDomain S.Ψ := by
      refine ⟨?_, ?_⟩
      · show μ p ∈ (baseChart F y₀.1).source
        simp only [baseChart, ProductComplexManifold.chartAt_prod,
          ProductComplexManifold.prodChart_source]
        exact ⟨hxs, by rw [hp0]; exact mem_chart_source _ _⟩
      · show baseChart F y₀.1 (μ p) ∈ S.Ψ.source
        rw [S.hΨsrc_iff, hbc, ContinuousLinearEquiv.symm_apply_apply]
        exact ⟨by rw [hcx]; exact hus, by rw [hp0]; exact zeroChart.map_source (mem_chart_source _ _)⟩
    obtain ⟨O, hO, hpO, W, hW, hWμ, hℓW⟩ := S.exists_tau_inverse hμ hpf hp hpX
    let C : ExcChart F μ p := ⟨y₀.1, S.Ψ, S.hΨsrc, fun hy hy' => S.hΨflat hy hy',
      S.hΨτ, idxT m, Or.inr rfl, S.ℓ, S.hℓ, S.hμℓ, O, hO, hpO, W, hW, hWμ, hℓW⟩
    have hWd := C.W_mem_monomialDomain hpO
    have hℓp : S.ℓ (liftMk _ S.p₀ (W p)) = p := C.ℓ_W hpO
    have hWT : W p (idxT m) = 0 := (C.mem_exceptional_iff hpO).mp hp
    set y := ((splitL m).symm (W p)).1 with hy
    have hWp : W p = splitL m (y, 0) := by
      apply (splitL m).symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      refine Prod.ext rfl ?_
      rw [splitL_symm_snd_eq, hWT]
      ext i; fin_cases i; simp
    have hmon := (hWμ p hpO).2
    rw [hWp, monomial_idxT_split, S.hΨfun, hbc, ContinuousLinearEquiv.symm_apply_apply, hcx,
      (zFlat F y₀).right_inv _ hut, hp0, sub_self] at hmon
    have hmon1 := congrArg Prod.fst (congrArg (splitL m).symm hmon)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hmon1
    have hy' : y = (stripModelEquiv m).symm (ζ, (stripModelEquiv m y).2) := by
      have h5 : scaleLast ((stripModelEquiv m).symm ((stripModelEquiv m y).1,
          (stripModelEquiv m y).2)) 0 = (stripModelEquiv m).symm (ζ, 0) := by
        rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, stripModelEquiv_symm_zero]
        simpa using hmon1
      rw [scaleLast_stripModelEquiv_symm, mul_zero] at h5
      have h6 := congrArg (fun v => (stripModelEquiv m v).1) h5
      simp only [ContinuousLinearEquiv.apply_symm_apply] at h6
      conv_lhs => rw [← (stripModelEquiv m).symm_apply_apply y]
      rw [← h6]
    set w' := (stripModelEquiv m y).2 with hw'
    have hpΛ : S.Λ ζ w' = p := by
      have : bvec ζ w' 0 = W p := by
        rw [hWp, bvec, ← hy', BundleSetup.single_zero']
      show S.ℓ (liftMk _ S.p₀ (bvec ζ w' 0)) = p
      rw [this, hℓp]
    refine ⟨w', fun h0 => ?_, hpΛ⟩
    have := (hw ζ hζ w').2
    rw [hpΛ, h0, norm_zero] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div] at this
    exact h2.ne' this
  · -- the weights
    intro ζ hζ w hw0
    obtain ⟨h1, h2⟩ := hw ζ hζ w
    have hG := hGpos _ (hΩN ζ hζ)
    have hwn : 0 < ‖w‖ ^ 2 := by have := norm_pos_iff.mpr hw0; positivity
    have hden : 0 < ‖w‖ ^ 2 * G (firstFlagInclusion F (eZ.val.symm ζ)) + 1 := by positivity
    refine ⟨hS1pos ζ hζ w, by rw [h2]; positivity, ?_⟩
    rw [h1, h2, Real.log_div (by positivity) hden.ne', Real.log_div one_ne_zero hden.ne',
      Real.log_one, Real.log_mul hwn.ne' hG.ne', hgdef, logNormSq]
    ring
  · -- the charts
    intro v hv hv0
    set ζ := (stripModelEquiv m v).1
    set w := (stripModelEquiv m v).2
    obtain ⟨Ech, hEch, hEchT⟩ := S.exists_flatChart hμ (hflatΛ ζ hv w) (S.Λ_mem (hΩt hv) w)
      (hnotX ζ hv w)
    have hD : IsOpen (Ech.val.target ∩ stripModelEquiv m ⁻¹' (Ω ×ˢ univ)) :=
      Ech.val.open_target.inter ((hΩo.prod isOpen_univ).preimage (stripModelEquiv m).continuous)
    have hvT : v ∈ Ech.val.target := by
      refine hEchT v ?_ ?_
      · rw [← bvec_strip]; exact S.bvec_mem_zero (hΩt hv) w
      · rw [← bvec_strip]; rfl
    refine ⟨Ech, Ech.val.target ∩ stripModelEquiv m ⁻¹' (Ω ×ˢ univ), hD, ⟨hvT, hv, mem_univ _⟩,
      inter_subset_left, fun v' hv' => ⟨hv'.2.1, ?_⟩⟩
    rw [hEch v' hv'.1, bundleMap, ← bvec_strip]
    rfl
  · -- the base point
    refine ⟨⟨eZ.val.map_source (mem_chart_source _ _), ?_⟩, ?_⟩
    · show firstFlagInclusion F (eZ.val.symm (eZ.val y₀)) ∈ e.val.source
      rw [eZ.val.left_inv (mem_chart_source _ _)]
      exact mem_chart_source _ _
    · show e.val (firstFlagInclusion F (eZ.val.symm (eZ.val y₀))) ∈ U'
      rw [eZ.val.left_inv (mem_chart_source _ _)]
      refine ⟨e.val.map_source (mem_chart_source _ _), ?_⟩
      show e.val.symm (e.val y₀.1) ∈ N
      rw [e.val.left_inv (mem_chart_source _ _)]
      exact hx₀N

/-- **`tok-wn-vf3:bundle-legendre-ma`** (WN21 Theorem 3.5 on `ℰ \ (X' ∪ Z̃)`). -/
theorem excBundleLegendreMA : ExcBundleLegendreMAStatement F :=
  excBundleLegendreMA_of_charts F (excBundleChart F)

/-- **`tok-wn:formula-E`** (WN21 Theorem 1.6 (4)): `vol_{𝒳|ℰ}(β) = n ∫₀^c vol_{X|Z}(ξ_t) dt`. -/
theorem exceptionalRestrictedVolume_formula : ExceptionalRestrictedVolumeStatement F :=
  exceptionalRestrictedVolume_of_bundleLegendre F (excLegendreInput F) (excBundleLegendreMA F)

end SGPT.Okounkov.TranscendentalWN

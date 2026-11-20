import SGPT.Envelopes.MADirichlet2Boundary

/-!
# The Dirichlet problem with `C²` density on an arbitrary polydisk

Xia, *Foundations of pluripotential theory* (FPT), `thm:continuous-density-ball-dirichlet`
(data of class `C²`, boundary values `0`), on the polydisk
`Q = a + R P = {z : ∀ j, |zⱼ - aⱼ| < R}` (`polydiskAt a R`), deduced from the unit polydisk
(`polydisk_dirichlet_C2`) by the affine change of variables `τ(ξ) = a + Rξ`, as FPT does with
`τ(ξ) = a + Rξ` on balls: `(ddᶜ(u ∘ τ))ⁿ ≥ f ηⁿ` iff the density `R²ⁿ f ∘ τ` is a lower bound, so
the problem for `Fⁿ` on `Q` is the problem for `(R² F ∘ τ)ⁿ` on `P`
(`polydiskAt_dirichlet_C2`). These polydisks of arbitrary centre and radius are needed for the
localization step of FPT's proof of `thm:bounded-multifactor-common-measure`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- The affine map `τ(ξ) = a + Rξ`. -/
def affineTo (a : ComplexModel n) (R : ℝ) (ξ : ComplexModel n) : ComplexModel n := a + R • ξ

/-- Its inverse `σ(z) = R⁻¹(z - a)`. -/
def affineFrom (a : ComplexModel n) (R : ℝ) (z : ComplexModel n) : ComplexModel n := R⁻¹ • (z - a)

section Affine

variable (a : ComplexModel n) {R : ℝ}

theorem affineFrom_affineTo (hR : R ≠ 0) (ξ : ComplexModel n) : affineFrom a R (affineTo a R ξ) = ξ := by
  simp [affineFrom, affineTo, smul_smul, inv_mul_cancel₀ hR]

theorem affineTo_affineFrom (hR : R ≠ 0) (z : ComplexModel n) : affineTo a R (affineFrom a R z) = z := by
  simp [affineFrom, affineTo, smul_smul, mul_inv_cancel₀ hR]

theorem continuous_affineTo : Continuous (affineTo a R) := by
  unfold affineTo
  exact continuous_const.add (continuous_const_smul _)

theorem continuous_affineFrom : Continuous (affineFrom a R) := by
  unfold affineFrom
  exact ((continuous_id (X := ComplexModel n)).sub continuous_const).const_smul (R⁻¹ : ℝ)

theorem contDiff_affineTo : ContDiff ℂ ∞ (affineTo a R) := by
  unfold affineTo
  exact contDiff_const.add (contDiff_id.const_smul R)

theorem contDiff_affineFrom : ContDiff ℂ ∞ (affineFrom a R) := by
  unfold affineFrom
  exact (contDiff_id.sub contDiff_const).const_smul R⁻¹

/-- `σ` as a homeomorphism. -/
def affineHomeomorph (hR : R ≠ 0) : ComplexModel n ≃ₜ ComplexModel n where
  toFun := affineFrom a R
  invFun := affineTo a R
  left_inv := affineTo_affineFrom a hR
  right_inv := affineFrom_affineTo a hR
  continuous_toFun := continuous_affineFrom a
  continuous_invFun := continuous_affineTo a

end Affine

/-- The polydisk `a + R P = σ⁻¹(P)`. -/
def polydiskAt (a : ComplexModel n) (R : ℝ) : Set (ComplexModel n) :=
  affineFrom a R ⁻¹' unitPolydisk n

theorem isOpen_polydiskAt (a : ComplexModel n) (R : ℝ) : IsOpen (polydiskAt a R) :=
  isOpen_unitPolydisk.preimage (continuous_affineFrom a)

/-- `a + R P` as an object of `Opens`. -/
def polydiskAtOpens (a : ComplexModel n) (R : ℝ) : Opens (ComplexModel n) :=
  ⟨polydiskAt a R, isOpen_polydiskAt a R⟩

theorem mem_polydiskAt {a z : ComplexModel n} {R : ℝ} (hR : 0 < R) :
    z ∈ polydiskAt a R ↔ ∀ j, ‖z j - a j‖ < R := by
  simp only [polydiskAt, mem_preimage, unitPolydisk, mem_ofPred_eq, affineFrom]
  refine forall_congr' fun j => ?_
  have : (R⁻¹ • (z - a)) j = (R⁻¹ : ℝ) • (z j - a j) := rfl
  rw [this, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_mul_lt_iff₀ hR, mul_one]

theorem isBiholomorphicPair_affine (a : ComplexModel n) {R : ℝ} (hR : R ≠ 0) :
    IsBiholomorphicPair (polydiskAtOpens a R) (unitPolydiskOpens n) (affineFrom a R)
      (affineTo a R) where
  holo := (contDiff_affineFrom a).contDiffOn
  holo_inv := (contDiff_affineTo a).contDiffOn
  mapsTo := fun _ hz => hz
  mapsTo_inv := fun ξ hξ => by
    show affineFrom a R (affineTo a R ξ) ∈ unitPolydisk n
    rwa [affineFrom_affineTo a hR]
  left_inv := fun z _ => affineTo_affineFrom a hR z
  right_inv := fun ξ _ => affineFrom_affineTo a hR ξ

theorem finrank_real_complexModel : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

/-- The real Jacobian of `τ` is `R²ⁿ`. -/
theorem det_smul_id (R : ℝ) :
    (R • ContinuousLinearMap.id ℝ (ComplexModel n)).det = R ^ (2 * n) := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
    ContinuousLinearMap.coe_id, LinearMap.det_id, finrank_real_complexModel, mul_one]

/-- **The Dirichlet problem with `C²` density and zero boundary values on `a + R P`** (FPT
`thm:continuous-density-ball-dirichlet` for `C²` data and `φ = 0`, on polydisks; the affine change
of variables of FPT's proof). -/
theorem polydiskAt_dirichlet_C2 (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F) (hF0 : ∀ z, 0 ≤ F z)
    (hK : HasCompactSupport F) (hKQ : tsupport F ⊆ polydiskAt a R) :
    ∃ U : ComplexModel n → ℝ, ∃ hU : IsLocallyBoundedPshOn (polydiskAtOpens a R) U,
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) U hU =
        (volume.restrict (polydiskAt a R)).withDensity
          (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) ∧
      (∀ ζ ∈ frontier (polydiskAt a R), Tendsto U (𝓝[polydiskAt a R] ζ) (𝓝 0)) ∧
      (∀ z ∈ polydiskAt a R, U z ≤ 0) ∧
      ∀ (V : ComplexModel n → ℝ) (hV : IsLocallyBoundedPshOn (polydiskAtOpens a R) V),
        canonicalBedfordTaylorMeasure (polydiskAtOpens a R) V hV =
          (volume.restrict (polydiskAt a R)).withDensity
            (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) →
        (∀ ζ ∈ frontier (polydiskAt a R), Tendsto V (𝓝[polydiskAt a R] ζ) (𝓝 0)) →
        ∀ z ∈ polydiskAt a R, V z = U z := by
  classical
  have hR0 : R ≠ 0 := hR.ne'
  set τ := affineTo a R with hτdef
  set σ := affineFrom a R with hσdef
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  set P : Opens (ComplexModel n) := unitPolydiskOpens n with hPdef
  have hb : IsBiholomorphicPair Q P σ τ := isBiholomorphicPair_affine a hR0
  have hστ : ∀ ξ, σ (τ ξ) = ξ := affineFrom_affineTo a hR0
  have hτσ : ∀ z, τ (σ z) = z := affineTo_affineFrom a hR0
  -- the transported density
  set G : ComplexModel n → ℝ := fun ξ => R ^ 2 * F (τ ξ) with hGdef
  have hG : ContDiff ℝ 2 G :=
    contDiff_const.mul (hF.comp (((contDiff_affineTo a (R := R)).restrict_scalars ℝ).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => mul_nonneg (by positivity) (hF0 _)
  have hGK : HasCompactSupport G :=
    (hK.comp_homeomorph (affineHomeomorph a hR0).symm).mul_left
  have hGP : tsupport G ⊆ unitPolydisk n := by
    refine (tsupport_mul_subset_right (f := fun _ => R ^ 2) (g := fun ξ => F (τ ξ))).trans ?_
    refine (tsupport_comp_subset_preimage F (continuous_affineTo a)).trans fun ξ hξ => ?_
    have := hKQ hξ
    simp only [polydiskAt, mem_preimage] at this
    rwa [affineFrom_affineTo a hR0] at this
  obtain ⟨⟨hH, hHeq⟩, hHbd, -, -, -⟩ := polydisk_dirichlet_C2 hn hG hG0 hGK hGP
  set H := polydiskEnvelope G with hHdef
  have hH0 : ∀ ξ ∈ unitPolydisk n, H ξ ≤ 0 := fun ξ hξ =>
    polydiskEnvelope_nonpos hG.continuous hG0 hξ
  -- the solution on `Q`
  set U : ComplexModel n → ℝ := fun z => H (σ z) with hUdef
  have hU : IsLocallyBoundedPshOn Q U := by
    refine ⟨HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (u := fun z => (H z : EReal))
      Q.isOpen ((contDiff_affineFrom a).differentiable (by simp)).differentiableOn hb.mapsTo hH.1,
      fun z hz => ?_⟩
    obtain ⟨V, hzV, -, C, hC⟩ := hH.2 _ (hb.mapsTo hz)
    have hopen : IsOpen ((Q : Set (ComplexModel n)) ∩ σ ⁻¹' V) :=
      Q.isOpen.inter (V.isOpen.preimage (continuous_affineFrom a))
    exact ⟨⟨_, hopen⟩, ⟨hz, hzV⟩, fun y hy => hy.1, C, fun y hy => hC _ hy.2⟩
  -- its Monge–Ampère measure
  have hlim : IsBTLimit Q (fun _ x => H (σ x))
      (((canonicalBedfordTaylorMeasure P H hH).restrict P).map τ) :=
    (isBTLimit_canonicalBedfordTaylorMeasure hH).comp_biholomorphic hb
  have hUeq : canonicalBedfordTaylorMeasure Q U hU =
      (volume.restrict (polydiskAt a R)).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) := by
    rw [(isBTLimit_canonicalBedfordTaylorMeasure hU).unique hlim, hHeq]
    have hτm : Measurable τ := (continuous_affineTo a).measurable
    ext E hE
    rw [Measure.map_apply hτm hE, Measure.restrict_apply (hτm hE), polydiskDensityMeasure,
      withDensity_apply _ ((hτm hE).inter P.isOpen.measurableSet),
      Measure.restrict_restrict ((hτm hE).inter P.isOpen.measurableSet),
      withDensity_apply _ hE, Measure.restrict_restrict hE]
    set S : Set (ComplexModel n) := τ ⁻¹' E ∩ unitPolydisk n with hSdef
    have hS : MeasurableSet S := (hτm hE).inter isOpen_unitPolydisk.measurableSet
    have hS' : S ∩ unitPolydisk n = S := inter_eq_left.mpr inter_subset_right
    have hSP : (τ ⁻¹' E ∩ ↑P) ∩ unitPolydisk n = S := by
      rw [hSdef]; exact inter_eq_left.mpr inter_subset_right
    rw [hSP]
    have hf' : ∀ x ∈ S, HasFDerivWithinAt τ (R • ContinuousLinearMap.id ℝ (ComplexModel n)) S x :=
      fun x _ => (((hasFDerivAt_id x).const_smul R).const_add a).hasFDerivWithinAt
    have hinj : InjOn τ S := fun x _ y _ hxy => by
      have := congrArg σ hxy
      rwa [hστ, hστ] at this
    have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hf' hinj
      (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n))
    have himage : τ '' S = E ∩ polydiskAt a R := by
      ext z
      constructor
      · rintro ⟨ξ, ⟨hξE, hξP⟩, rfl⟩
        refine ⟨hξE, ?_⟩
        show σ (τ ξ) ∈ unitPolydisk n
        rwa [hστ]
      · rintro ⟨hzE, hzQ⟩
        refine ⟨σ z, ⟨?_, hzQ⟩, hτσ z⟩
        show τ (σ z) ∈ E
        rwa [hτσ]
    rw [himage] at hcv
    rw [hcv]
    refine setLIntegral_congr_fun hS fun ξ _ => ?_
    rw [det_smul_id, abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [hGdef, mul_pow, ← pow_mul]
    ring
  -- boundary values
  have hσfr : ∀ ζ ∈ frontier (polydiskAt a R), σ ζ ∈ closedUnitPolydisk n \ unitPolydisk n := by
    intro ζ hζ
    have h1 : frontier (polydiskAt a R) = σ ⁻¹' frontier (unitPolydisk n) :=
      ((affineHomeomorph a hR0).preimage_frontier (unitPolydisk n)).symm
    rw [h1] at hζ
    exact frontier_unitPolydisk_subset hζ
  have hUbd : ∀ ζ ∈ frontier (polydiskAt a R), Tendsto U (𝓝[polydiskAt a R] ζ) (𝓝 0) := by
    intro ζ hζ
    have htend : Tendsto σ (𝓝[polydiskAt a R] ζ) (𝓝[unitPolydisk n] (σ ζ)) :=
      ContinuousWithinAt.tendsto_nhdsWithin (continuous_affineFrom a).continuousWithinAt
        fun z hz => hz
    exact (hHbd _ (hσfr ζ hζ)).comp htend
  refine ⟨U, hU, hUeq, hUbd, fun z hz => hH0 _ hz, fun V hV hVeq hVbd => ?_⟩
  -- uniqueness
  have hbdd : Bornology.IsBounded ((Q : Opens (ComplexModel n)) : Set (ComplexModel n)) := by
    refine (Metric.isBounded_iff_subset_closedBall a).2 ⟨R * (n + 1), fun z hz => ?_⟩
    rw [mem_closedBall, dist_eq_norm]
    have hz' : σ z ∈ unitPolydisk n := hz
    have h1 := norm_sq_le_of_mem_unitPolydisk hz'
    have h2 : ‖σ z‖ ≤ n + 1 := by nlinarith [norm_nonneg (σ z)]
    have h3 : z - a = R • σ z := by
      simp only [hσdef, affineFrom, smul_smul, mul_inv_cancel₀ hR0, one_smul]
    rw [h3, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left h2 hR.le
  obtain ⟨C, hC⟩ := hF.continuous.bounded_above_of_compact_support hK
  have hfin : canonicalBedfordTaylorMeasure Q V hV ((Q : Opens (ComplexModel n)) :
      Set (ComplexModel n)) < ⊤ := by
    have hset : ((Q : Opens (ComplexModel n)) : Set (ComplexModel n)) = polydiskAt a R := rfl
    rw [hset, hVeq, withDensity_apply _ (isOpen_polydiskAt a R).measurableSet]
    refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal
      (mongeAmpereConst n * C ^ n)) measurable_const fun z _ => ?_) ?_
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ mongeAmpereConst_pos.le)
      have := hC z
      rw [Real.norm_eq_abs] at this
      calc F z ^ n ≤ |F z ^ n| := le_abs_self _
        _ = |F z| ^ n := abs_pow _ _
        _ ≤ C ^ n := pow_le_pow_left₀ (abs_nonneg _) this n
    · rw [setLIntegral_const]
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      rw [Measure.restrict_apply' (isOpen_polydiskAt a R).measurableSet, inter_self]
      exact hbdd.measure_lt_top
  refine eq_of_ma_eq hn hbdd hV hU (fun ζ hζ δ hδ => ?_) hfin (hVeq.trans hUeq.symm)
  have h1 := (hVbd ζ hζ).sub (hUbd ζ hζ)
  rw [sub_zero] at h1
  filter_upwards [(h1.abs).eventually (gt_mem_nhds (by simpa using hδ))] with z hz
  simpa using hz

end SGPT.Envelopes.MADirichlet

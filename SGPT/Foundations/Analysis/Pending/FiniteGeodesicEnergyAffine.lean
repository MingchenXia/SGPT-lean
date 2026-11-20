import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyEndpoints
import SGPT.Foundations.Analysis.Pending.AffineOfWeakSecondDerivative

set_option autoImplicit false

/-!
# The Monge--Ampère energy is affine along bounded geodesics

Let `X` be a compact complex manifold of dimension `n`, `θ` a closed real `(1,1)`-form, `φ` a
bounded `θ`-PSH model potential and `E = E^φ` the relative Monge--Ampère energy
(`RelativeEnergy.relativeEnergyOfMinimalType`).

* `integral_energyCurve_mul_timeLaplacian_eq_zero` — for a curve `U` of `θ`-PSH potentials with
  uniformly bounded slices, covered by strip charts (`FiniteGeodesicStripCharts.StripChart`: the
  corrected complexification is plurisubharmonic and maximal), `t ↦ E(U_t)` is weakly harmonic:
  `∫ E(U_{Re τ}) Δψ(τ) dλ(τ) = 0` for every `ψ ∈ C_c^∞(0 < Re τ < 1)`.
  Proof: read `ψ(τ)` as a slot on each strip chart; the time slot
  (`BedfordTaylorStripIBP.isDefectPairing_timeLift`) and the slicing of Bedford--Taylor limits along
  `τ` (`BedfordTaylorFibreSlicing.integral_mul_isBTLimit_eq_fibre`) turn the chartwise pairings into
  `(1/π) ∫ (Δψ/4)(τ) ∫_X χ_a (U_{Re τ} - φ) dMA_j(U_{Re τ}) dλ(τ)`, the fibre measures being the
  global mixed measures of `X` (`integral_fibre_eq_energyTerm`, through
  `GlobalSlotStokes.SlotChart.exists_isBTLimit`); summed over `j` and over a partition of unity
  `(χ_a)` this is `((n + 1)/π) ∫ (Δψ/4) E(U_{Re τ})`, and the sum vanishes by the gluing identity
  `FiniteGeodesicStripCharts.sum_sum_defectPairing_eq_zero`.
* `exists_affine_energyCurve` — hence `E(U_t) = c₀ + c₁ t` on `(0, 1)`
  (`AffineOfWeakSecondDerivative.exists_affine_of_integral_timeLaplacian`).
* `relativeEnergyOfMinimalType_finiteGeodesic` — **for bounded endpoints whose Perron geodesic is a
  subgeodesic between them, `E(U_t) = (1 - t) E(u₀) + t E(u₁)`**: strip charts exist at every point
  (`FiniteGeodesicEnergyEndpoints.exists_isBTLimit_eq_zero_finiteGeodesic_of_bounded`), the energy
  is Lipschitz on `(0, 1)` and continuous at the endpoints
  (`abs_energy_finiteGeodesic_sub_le`, `_left_le`, `_right_le`).
  `relativeEnergyOfMinimalType_finiteGeodesic_of_relativeEInfinity`: the same for endpoints in
  `E^∞(X, θ; φ)`, where the subgeodesic property is automatic.

Source: Xia, SGPT, Proposition 4.3.3 and its proof (`xia-sgpt:page-0169` to `xia-sgpt:page-0173`),
in the bounded case (the step "`t ↦ E(φ_t)` is affine for bounded geodesics").
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyAffine

open FirstPass FirstPass.MongeAmpere FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
  BedfordTaylor BedfordTaylorDefectPairing BedfordTaylorTimeSlot MixedDensityRankOneSlot
  BedfordTaylorFibreSlicing BedfordTaylorStripCovariance BedfordTaylorStripIBP
  FiniteGeodesicMaximality GlobalSlotStokes BoundedGlobalProduct FiniteGeodesicStripCharts
  GlobalNonPluripolar RelativeEnergy BoundedMongeAmpereEnergy FiniteGeodesicEnergyEndpoints
  AffineOfWeakSecondDerivative StripChart

noncomputable section

/-! ### Fibres of strips -/

section Fibre

variable {n : ℕ}

theorem fibreMap_mem_stripLift {A : Opens (ComplexModel n)} {S : Set ℂ} {hS : IsOpen S} {τ : ℂ}
    {y : ComplexModel n} : fibreMap n τ y ∈ stripLift A S hS ↔ y ∈ A ∧ τ ∈ S := by
  rw [mem_stripLift, stripFst_fibreMap, stripModelEquiv_fibreMap]

theorem fibreMap_last (τ : ℂ) (y : ComplexModel n) : fibreMap n τ y (Fin.last n) = τ := by
  rw [← stripModelEquiv_snd, stripModelEquiv_fibreMap]

theorem fibreOpens_stripLift {A : Opens (ComplexModel n)} {S : Set ℂ} {hS : IsOpen S} {τ : ℂ}
    (hτ : τ ∈ S) : fibreOpens (stripLift A S hS) τ = A := by
  ext y
  show fibreMap n τ y ∈ stripLift A S hS ↔ y ∈ A
  exact (fibreMap_mem_stripLift (hS := hS)).trans (and_iff_left hτ)

/-- `χ w` is integrable against a locally finite measure, for `w` locally bounded psh. -/
theorem integrable_mul_of_isLocallyBoundedPshOn {N : ℕ} {Ω : Opens (ComplexModel N)}
    {w : ComplexModel N → ℝ} (hw : IsLocallyBoundedPshOn Ω w) {μ : Measure (ComplexModel N)}
    (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) {χ : ComplexModel N → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) :
    Integrable (fun q => χ q * w q) μ := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hχc Ω.isOpen hχΩ
  obtain ⟨G, hG⟩ := exists_isDecApprox_of_isLocallyBoundedPshOn hw ⟨V, hVo⟩ ⟨hVc, hVΩ⟩
  exact hG.integrable_mul (fun K hK hKV' => hμ K hK (hKV'.trans (subset_closure.trans hVΩ)))
    hχ hχc hKV

/-- The fibre version: `χ(·, τ) w(·, τ)` is integrable against a locally finite measure on the
fibre `Ω_τ`. -/
theorem integrable_fibreRestrict_mul {Ω : Opens (ComplexModel (n + 1))}
    {w : ComplexModel (n + 1) → ℝ} (hw : IsLocallyBoundedPshOn Ω w)
    {χ : ComplexModel (n + 1) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (τ : ℂ) {μ : Measure (ComplexModel n)}
    (hμ : ∀ K, IsCompact K → K ⊆ fibreOpens Ω τ → μ K < ⊤) :
    Integrable (fun y => fibreRestrict χ τ y * fibreRestrict w τ y) μ := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hχc Ω.isOpen hχΩ
  set VO : Opens (ComplexModel (n + 1)) := ⟨V, hVo⟩
  have hVOΩ : VO ≤ Ω := subset_closure.trans hVΩ
  obtain ⟨G, hG⟩ := exists_isDecApprox_of_isLocallyBoundedPshOn hw VO ⟨hVc, hVΩ⟩
  have hsupp : tsupport (fibreRestrict χ τ) ⊆ fibreOpens VO τ := fun y hy =>
    hKV (tsupport_fibreRestrict_subset χ τ hy)
  have hc : HasCompactSupport (fibreRestrict χ τ) :=
    (isCompact_preimage_fibreMap hχc τ).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_fibreRestrict_subset χ τ)
  exact (IsDecApprox.fibre hG τ).integrable_mul
    (fun K hK hKV' => hμ K hK (hKV'.trans (fibreOpens_mono hVOΩ τ)))
    (hχ.comp (continuous_fibreMap τ)) hc hsupp

end Fibre

/-! ### The fibre measures are the global mixed measures -/

section Energy

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {U : ℝ → M → EReal} {φ : M → EReal} {A B : ℝ}

/-- A strip chart as a slot chart: every slot, and the Kähler slot, use `ρ`. -/
def slotChartOf (J : StripChart θ U) : SlotChart (fun _ : Fin n => θ) θ where
  chart := J.chart
  domain := J.domain
  domain_le_target := J.domain_subset_target
  potential := fun _ => J.potential
  localPotential := fun _ => J.localPotential
  kahler := J.potential
  kahlerLocal := J.localPotential

/-- `∫ f (U_t - φ) dMA_j(U_t)` for `t ∈ (0, 1)` (`j` slots `U_t`, `n - j` slots `φ`), `0`
otherwise. -/
def energyTerm (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (U : ℝ → M → EReal)
    (hφ : IsThetaPshPotential θ.val φ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ.val (U t)) (f : M → ℝ) (j : Fin (n + 1))
    (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) 1 then
    ∫ x, f x * ((U t x).toReal - (φ x).toReal) ∂(endpointMixedMeasure θ φ (U t) hφ (hU t ht) j)
  else 0

/-- `t ↦ E(U_t)` on `(0, 1)`, `0` otherwise. -/
def energyCurve (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (U : ℝ → M → EReal)
    (hφ : IsThetaPshPotential θ.val φ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ.val (U t)) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) 1 then relativeEnergyOfMinimalType θ φ (U t) hφ (hU t ht) else 0

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem isBoundedPotential_endpointMixedPotential
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφb : IsBoundedPotential φ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (j : Fin (n + 1)) (i : Fin n) :
    IsBoundedPotential (endpointMixedPotential j (U t) φ i) := by
  unfold endpointMixedPotential
  split_ifs
  exacts [⟨A, B, hbd t ht⟩, hφb]

/-- **The fibre measures are the global mixed measures.** Over `τ` in the strip, the
Bedford--Taylor limit of `(h, …, h, Φ, …, Φ)` (`j` copies of `h`) restricted to the fibre is the
chart image of `MA_j(U_{Re τ}) = θ_{U}^j ∧ θ_φ^{n-j}`. -/
theorem integral_fibre_eq_energyTerm
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφ : IsThetaPshPotential θ.val φ) (hφb : IsBoundedPotential φ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ.val (U t)) (J : StripChart θ U)
    (j : Fin (n + 1)) {f : M → ℝ} (hf : J.IsCutoff f) {τ : ℂ} (hτ : τ ∈ complexTimeStrip)
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (fibreOpens J.strip τ) (fibreTuple (Function.update
      (endpointTuple J.liftCurve (J.liftModel φ) j) (Fin.last n) (lastNormSq n)) τ) μ) :
    ∫ y, chartRead J.chart f y *
        (fibreRestrict J.liftCurve τ y - fibreRestrict (J.liftModel φ) τ y) ∂μ =
      energyTerm θ φ U hφ hU f j τ.re := by
  have ht : τ.re ∈ Ioo (0 : ℝ) 1 := hτ
  rw [energyTerm, dif_pos ht]
  have hu := endpointMixedPotential_thetaPlurisubharmonic θ j (U τ.re) φ (hU τ.re ht) hφ
  have hub := isBoundedPotential_endpointMixedPotential hbd hφb ht j
  obtain ⟨μ', hμ', hglob⟩ := (slotChartOf J).exists_isBTLimit hu hub
  rw [show fibreOpens J.strip τ = J.domain from fibreOpens_stripLift hτ] at hμ
  have htup : ∀ i, EqOn (fun z => (endpointMixedPotential j (U τ.re) φ i
      (J.chart.val.symm z)).toReal + (slotChartOf J).potential i z)
      (fibreTuple (Function.update (endpointTuple J.liftCurve (J.liftModel φ) j) (Fin.last n)
        (lastNormSq n)) τ i) J.domain := by
    intro i y hy
    have hmem : fibreMap n τ y ∈ J.strip := fibreMap_mem_stripLift.mpr ⟨hy, hτ⟩
    simp only [fibreTuple, fibreRestrict, Function.update_of_ne (Fin.castSucc_ne_last i),
      endpointTuple, Fin.val_castSucc, endpointMixedPotential]
    by_cases hij : (i : ℕ) < j
    · rw [if_pos hij, if_pos hij, J.liftCurve_eq hbd hmem, stripFst_fibreMap, fibreMap_last]
      rfl
    · rw [if_neg hij, if_neg hij]
      simp only [StripChart.liftModel, StripChart.modelFn, stripFst_fibreMap]
      rfl
  have hμeq : μ' = μ := (hμ'.congr htup).unique hμ
  subst hμeq
  have hsupp : ∀ x ∉ (J.region : Set M), f x * ((U τ.re x).toReal - (φ x).toReal) = 0 :=
    fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hf.2.2 h)), zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  change _ = ∫ x, _ ∂((globalMixedMeasure (fun _ => θ) (endpointMixedPotential j (U τ.re) φ)
    hu).restrict ((slotChartOf J).source : Set M))
  rw [hglob, Patch.integral_pushMeasure _ hμ'.1]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ y ∂μ', y ∈ (J.domain : Set (ComplexModel n)) := by
    rw [ae_iff]
    exact hμ'.1
  filter_upwards [hae] with y hy
  have hmem : fibreMap n τ y ∈ J.strip := fibreMap_mem_stripLift.mpr ⟨hy, hτ⟩
  simp only [fibreRestrict]
  rw [chartRead_of_mem (J.domain_subset_target hy), J.liftCurve_eq hbd hmem, stripFst_fibreMap,
    fibreMap_last]
  simp only [StripChart.liftModel, StripChart.modelFn, stripFst_fibreMap]
  change _ = f (J.chart.val.symm y) *
    ((U τ.re (J.chart.val.symm y)).toReal - (φ (J.chart.val.symm y)).toReal)
  ring

/-- **One strip chart.** The pairing of `f (h - Φ)` (cut off in `τ` by `ζ = 1` near `supp ψ`) with
`ddᶜψ(τ) ∧ (ddᶜh)ʲ ∧ (ddᶜΦ)ⁿ⁻ʲ` is `(1/π) ∫ (Δψ/4)(τ) ∫_X f (U_{Re τ} - φ) dMA_j(U_{Re τ}) dλ(τ)`. -/
theorem defectPairing_timeLift_eq
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφ : IsThetaPshPotential θ.val φ) (hφb : IsBoundedPotential φ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ.val (U t)) (J : StripChart θ U)
    (j : Fin (n + 1)) {f : M → ℝ} (hf : J.IsCutoff f) {ψ ζ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψS : tsupport ψ ⊆ complexTimeStrip) (hζ : Continuous ζ)
    (hζc : HasCompactSupport ζ) (hζS : tsupport ζ ⊆ complexTimeStrip)
    (hζψ : ∀ τ ∈ tsupport ψ, ζ τ = 1) :
    Integrable (fun τ : ℂ => timeLaplacian ψ τ * energyTerm θ φ U hφ hU f j τ.re) ∧
      defectPairing J.strip (endpointTuple J.liftCurve (J.liftModel φ) j) (Fin.last n)
        (timeLift n ψ) (J.weight φ ζ f) =
      (∫ τ : ℂ, timeLaplacian ψ τ * energyTerm θ φ U hφ hU f j τ.re) / Real.pi := by
  classical
  have hh := J.isLocallyBoundedPshOn_liftCurve hbd
  have hΦ := J.isLocallyBoundedPshOn_liftModel hφ.1 hφb
  have hslots : ∀ i, IsLocallyBoundedPshOn J.strip (Function.update
      (endpointTuple J.liftCurve (J.liftModel φ) j) (Fin.last n) (lastNormSq n) i) := fun i => by
    by_cases hi : i = Fin.last n
    · subst hi
      simpa using (isSmoothPsdOn_lastNormSq J.strip).isLocallyBoundedPshOn
    · simpa [Function.update_of_ne hi] using isLocallyBoundedPshOn_endpointTuple hh hΦ j i
  obtain ⟨ν, hν⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn hslots
  choose μ hμ using exists_isBTLimit_fibre hν
  have hκ := hf.continuous_stripCutoff hζ
  have hκc := hf.hasCompactSupport_stripCutoff hζc
  have hκS := hf.tsupport_stripCutoff hζc hζS
  set χ' : ComplexModel (n + 1) → ℝ := fun q =>
    stripCutoff (chartRead J.chart f) ζ q * timeLaplacian ψ (q (Fin.last n)) with hχ'_def
  have hχ' : Continuous χ' :=
    hκ.mul ((continuous_timeLaplacian hψ).comp (lastCoordinate n).continuous)
  have hχ'c : HasCompactSupport χ' := hκc.mul_right
  have hχ'S : tsupport χ' ⊆ J.strip := tsupport_mul_subset_left.trans hκS
  -- the pairing is an integral against `ν`
  have hpair := isDefectPairing_timeLift (v := endpointTuple J.liftCurve (J.liftModel φ) j)
    (fun i _ => isLocallyBoundedPshOn_endpointTuple hh hΦ j i) hψ hψc hν hh hΦ hκ hκc hκS
  rw [defectPairing_eq (isBoundedTest_weight hbd hφ.1 hφb hf hζ hζc hζS) hpair]
  -- slicing
  have hdec : ∀ {w : ComplexModel (n + 1) → ℝ}, IsLocallyBoundedPshOn J.strip w →
      ∀ V, RelativelyCompactIn V J.strip → ∃ G, IsDecApprox V w G := fun hw V hV =>
    exists_isDecApprox_of_isLocallyBoundedPshOn hw V hV
  have hlast : Function.update (endpointTuple J.liftCurve (J.liftModel φ) j) (Fin.last n)
      (lastNormSq n) (Fin.last n) = lastNormSq n := Function.update_self _ _ _
  obtain ⟨hI₁, e₁⟩ := integral_mul_isBTLimit_eq_fibre hlast hν hμ (hdec hh) hχ' hχ'c hχ'S
  obtain ⟨hI₂, e₂⟩ := integral_mul_isBTLimit_eq_fibre hlast hν hμ (hdec hΦ) hχ' hχ'c hχ'S
  -- the fibre integrals
  have hfib : ∀ τ : ℂ, (∫ y, fibreRestrict χ' τ y * fibreRestrict J.liftCurve τ y ∂μ τ) -
      ∫ y, fibreRestrict χ' τ y * fibreRestrict (J.liftModel φ) τ y ∂μ τ =
      timeLaplacian ψ τ * energyTerm θ φ U hφ hU f j τ.re := by
    intro τ
    by_cases hlap : timeLaplacian ψ τ = 0
    · have h0 : ∀ y, fibreRestrict χ' τ y = 0 := fun y => by
        simp [fibreRestrict, hχ'_def, fibreMap_last, hlap]
      simp [h0, hlap]
    · have hτψ : τ ∈ tsupport ψ := by
        by_contra hc
        exact hlap (timeLaplacian_eq_zero_of_notMem_tsupport hc)
      have hτ : τ ∈ complexTimeStrip := hψS hτψ
      have hfχ : ∀ y, fibreRestrict χ' τ y = timeLaplacian ψ τ * chartRead J.chart f y := by
        intro y
        simp only [fibreRestrict, hχ'_def, stripCutoff, stripFst_fibreMap, fibreMap_last,
          hζψ τ hτψ]
        ring
      rw [← integral_sub (integrable_fibreRestrict_mul hh hχ' hχ'c hχ'S τ (hμ τ).2.1)
        (integrable_fibreRestrict_mul hΦ hχ' hχ'c hχ'S τ (hμ τ).2.1),
        ← integral_fibre_eq_energyTerm hbd hφ hφb hU J j hf hτ (hμ τ), ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hfχ]
      ring
  have hint : Integrable (fun τ : ℂ => timeLaplacian ψ τ * energyTerm θ φ U hφ hU f j τ.re) :=
    (hI₁.sub hI₂).congr (Eventually.of_forall hfib)
  refine ⟨hint, ?_⟩
  have hsplit : (∫ q, χ' q * (J.liftCurve q - J.liftModel φ q) ∂ν) =
      (∫ q, χ' q * J.liftCurve q ∂ν) - ∫ q, χ' q * J.liftModel φ q ∂ν := by
    simp only [mul_sub]
    exact integral_sub (integrable_mul_of_isLocallyBoundedPshOn hh hν.2.1 hχ' hχ'c hχ'S)
      (integrable_mul_of_isLocallyBoundedPshOn hΦ hν.2.1 hχ' hχ'c hχ'S)
  change (∫ q, χ' q * (J.liftCurve q - J.liftModel φ q) ∂ν) = _
  rw [hsplit, e₁, e₂, ← sub_div, ← integral_sub hI₁ hI₂]
  congr 1
  exact integral_congr_ae (Eventually.of_forall hfib)

/-- Summed over a partition of unity and over `j`, the terms give `(n + 1) E(U_t)`. -/
theorem sum_sum_energyTerm
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφ : IsThetaPshPotential θ.val φ) (hφb : IsBoundedPotential φ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ.val (U t)) {m : ℕ} {χ : Fin m → M → ℝ}
    (hχs : ∀ a, ChartSmooth (n := n) (χ a)) (hχ0 : ∀ a x, 0 ≤ χ a x) (hχ1 : ∀ x, ∑ a, χ a x = 1)
    (t : ℝ) :
    ∑ j : Fin (n + 1), ∑ a, energyTerm θ φ U hφ hU (χ a) j t =
      ((n : ℝ) + 1) * energyCurve θ φ U hφ hU t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · simp only [energyTerm, energyCurve, dif_pos ht]
    have hUb : IsBoundedPotential (U t) := ⟨A, B, hbd t ht⟩
    have hmU := ThetaPlurisubharmonic.measurable_toReal (hU t ht).1
    have hmφ := ThetaPlurisubharmonic.measurable_toReal hφ.1
    obtain ⟨QU, hQU⟩ := IsBoundedPotential.exists_abs_toReal_le hUb
    obtain ⟨Qφ, hQφ⟩ := IsBoundedPotential.exists_abs_toReal_le hφb
    have hj : ∀ j : Fin (n + 1), ∑ a, ∫ x, χ a x * ((U t x).toReal - (φ x).toReal)
        ∂(endpointMixedMeasure θ φ (U t) hφ (hU t ht) j) =
        relativeEnergyTerm θ φ (U t) hφ (hU t ht) j := by
      intro j
      have : IsFiniteMeasure (endpointMixedMeasure θ φ (U t) hφ (hU t ht) j) :=
        globalMixedMeasure_isFiniteMeasure_of_bounded _
          (isBoundedPotential_endpointMixedPotential hbd hφb ht j)
      rw [← integral_finsetSum _ fun a _ => ?_]
      · rw [relativeEnergyTerm]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [← Finset.sum_mul, hχ1, one_mul, canonicalERealDiffToReal_of_bounded hUb hφb]
      · refine Integrable.of_bound
          ((ChartSmooth.continuous (hχs a)).measurable.mul (hmU.sub hmφ)).aestronglyMeasurable
          (QU + Qφ) (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |χ a x| ≤ 1 := by
          rw [abs_of_nonneg (hχ0 a x), ← hχ1 x]
          exact Finset.single_le_sum (fun b _ => hχ0 b x) (Finset.mem_univ a)
        calc |χ a x| * |(U t x).toReal - (φ x).toReal| ≤ 1 * (QU + Qφ) :=
              mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (hQU x) (hQφ x))) (abs_nonneg _)
                zero_le_one
          _ = QU + Qφ := one_mul _
    rw [Finset.sum_congr rfl fun j _ => hj j, relativeEnergyOfMinimalType]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · simp only [energyTerm, energyCurve, dif_neg ht, Finset.sum_const_zero, mul_zero]

/-- **The energy is weakly harmonic along a maximal bounded subgeodesic.** If every point of `X`
lies in a strip chart of `U`, then `∫ E(U_{Re τ}) Δψ(τ) dλ(τ) = 0` for every `ψ ∈ C_c^∞(strip)`. -/
theorem integral_energyCurve_mul_timeLaplacian_eq_zero
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφ : IsThetaPshPotential θ.val φ) (hφb : IsBoundedPotential φ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ.val (U t))
    (hcover : ∀ x : M, ∃ J : StripChart θ U, x ∈ J.region) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψS : tsupport ψ ⊆ complexTimeStrip) :
    ∫ τ : ℂ, energyCurve θ φ U hφ hU τ.re * timeLaplacian ψ τ = 0 := by
  classical
  obtain ⟨m, χ, J, hχs, hχ0, hχJ, hχc, hχ1⟩ := ChartPartition.exists_chartSmooth_partitionOfUnity
    (n := n) (fun J : StripChart θ U => J.region) hcover
  have hcut : ∀ a, (J a).IsCutoff (χ a) := fun a => ⟨hχs a, hχc a, hχJ a⟩
  obtain ⟨ζ, hζ1, -⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := (⟨complexTimeStrip, isOpen_complexTimeStrip⟩ : Opens ℂ)) hψc hψS
  obtain ⟨Nψ, hNo, hψN, hN1⟩ := mem_nhdsSet_iff_exists.mp hζ1
  have hζS : tsupport (ζ : ℂ → ℝ) ⊆ complexTimeStrip := ζ.tsupport_subset
  have hglue := sum_sum_defectPairing_eq_zero hbd hφ.1 hφb J hcut hχ1 hψ hψc hψS ζ.contDiff
    ζ.hasCompactSupport hζS hNo hψN fun τ hτ => hN1 hτ
  have hloc := fun a j => defectPairing_timeLift_eq hbd hφ hφb hU (J a) j (hcut a) hψ hψc hψS
    ζ.continuous ζ.hasCompactSupport hζS fun τ hτ => hN1 (hψN hτ)
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => (hloc a j).2] at hglue
  have hint : ∀ j a, Integrable fun τ : ℂ =>
      timeLaplacian ψ τ * energyTerm θ φ U hφ hU (χ a) j τ.re := fun j a => (hloc a j).1
  have hsum : (∫ τ : ℂ, ∑ j : Fin (n + 1), ∑ a,
      timeLaplacian ψ τ * energyTerm θ φ U hφ hU (χ a) j τ.re) =
      ∑ j : Fin (n + 1), ∑ a, ∫ τ : ℂ, timeLaplacian ψ τ * energyTerm θ φ U hφ hU (χ a) j τ.re := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun a _ => hint j a]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun a _ => hint j a
  have hpoint : ∀ τ : ℂ, ∑ j : Fin (n + 1), ∑ a,
      timeLaplacian ψ τ * energyTerm θ φ U hφ hU (χ a) j τ.re =
      ((n : ℝ) + 1) * (energyCurve θ φ U hφ hU τ.re * timeLaplacian ψ τ) := by
    intro τ
    simp_rw [← Finset.mul_sum]
    rw [sum_sum_energyTerm hbd hφ hφb hU hχs hχ0 hχ1]
    ring
  simp_rw [hpoint, integral_const_mul] at hsum
  have hzero : ∑ j : Fin (n + 1), ∑ a,
      (∫ τ : ℂ, timeLaplacian ψ τ * energyTerm θ φ U hφ hU (χ a) j τ.re) = 0 := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have h := hglue
    simp_rw [← Finset.sum_div] at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hπ
  rw [hzero] at hsum
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hsum).resolve_left hn

/-- **The energy is affine along a maximal bounded subgeodesic**, given its continuity. -/
theorem exists_affine_energyCurve
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ U t x ∧ U t x ≤ (B : EReal))
    (hφ : IsThetaPshPotential θ.val φ) (hφb : IsBoundedPotential φ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ.val (U t))
    (hcover : ∀ x : M, ∃ J : StripChart θ U, x ∈ J.region)
    (hcont : ContinuousOn (energyCurve θ φ U hφ hU) (Ioo 0 1)) :
    ∃ c₀ c₁ : ℝ, ∀ t (ht : t ∈ Ioo (0 : ℝ) 1),
      relativeEnergyOfMinimalType θ φ (U t) hφ (hU t ht) = c₀ + c₁ * t := by
  obtain ⟨c₀, c₁, hc⟩ := exists_affine_of_integral_timeLaplacian hcont
    fun ψ hψ hψc hψS => integral_energyCurve_mul_timeLaplacian_eq_zero hbd hφ hφb hU hcover hψ hψc hψS
  refine ⟨c₀, c₁, fun t ht => ?_⟩
  have := hc t ht
  rwa [energyCurve, dif_pos ht] at this

end Energy

/-! ### Bounded geodesics -/

section Geodesic

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Every point lies in a strip chart of a bounded Perron geodesic which is a subgeodesic. -/
theorem exists_stripChart_finiteGeodesic {θ : ClosedRealOneOneForm n M} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) (x : M) :
    ∃ J : StripChart θ (finiteGeodesic θ.val u₀ u₁), x ∈ J.region := by
  have hx := mem_complexChartAt_source (n := n) x
  obtain ⟨W, ρ, hρ, hzW, hpsh, hmax⟩ := exists_isBTLimit_eq_zero_finiteGeodesic_of_bounded hsub
    hb₀ hb₁ (complexChartAt (n := n) x) ((complexChartAt (n := n) x).val.map_source hx)
  exact ⟨{ chart := complexChartAt (n := n) x
           domain := ⟨W, hρ.1⟩
           potential := ρ
           localPotential := hρ
           psh := hpsh
           maximal := hmax }, hx, hzW⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

theorem le_zero_of_forall_le_mul_of_tendsto {a K : ℝ} {l : Filter ℝ} [l.NeBot] {g : ℝ → ℝ}
    (hg : Tendsto g l (𝓝 0)) (h : ∀ᶠ s in l, a ≤ K * g s) : a ≤ 0 := by
  have hK : Tendsto (fun s => K * g s) l (𝓝 0) := by simpa using hg.const_mul K
  exact ge_of_tendsto hK h

/-- **The energy is affine along bounded geodesics** (Xia, SGPT, Proposition 4.3.3, bounded case).
For a bounded model potential `φ` and bounded endpoints `u₀`, `u₁` whose Perron geodesic `U` is a
subgeodesic between them, `E(U_t) = (1 - t) E(u₀) + t E(u₁)` for `0 < t < 1`. -/
theorem relativeEnergyOfMinimalType_finiteGeodesic (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hφb : IsBoundedPotential φ)
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    (hb₀ : IsBoundedPotential u₀) (hb₁ : IsBoundedPotential u₁) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hUt : IsThetaPshPotential θ.val (finiteGeodesic θ.val u₀ u₁ t)) :
    relativeEnergyOfMinimalType θ φ _ hφ hUt =
      (1 - t) * relativeEnergyOfMinimalType θ φ u₀ hφ hsub.1 +
        t * relativeEnergyOfMinimalType θ φ u₁ hφ hsub.2.1 := by
  obtain ⟨A, B, hbd⟩ := finiteGeodesic_uniformly_bounded hsub hb₀ hb₁
  have hU : ∀ s ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ.val (finiteGeodesic θ.val u₀ u₁ s) :=
    fun s hs => hsub.2.2.1.thetaPshPotential hs
  obtain ⟨C, hC0, hC₁, hC₀⟩ := exists_nonneg_le_add_of_bounded hb₀ hb₁
  set V := (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set E := energyCurve θ φ (finiteGeodesic θ.val u₀ u₁) hφ hU with hE_def
  have hE : ∀ s (hs : s ∈ Ioo (0 : ℝ) 1),
      E s = relativeEnergyOfMinimalType θ φ _ hφ (hU s hs) := fun s hs => by
    rw [hE_def, energyCurve, dif_pos hs]
  -- continuity on `(0, 1)`: the energy is `C V`-Lipschitz
  have hcont : ContinuousOn E (Ioo 0 1) := by
    intro s hs
    refine Metric.continuousWithinAt_iff.mpr fun ε hε => ⟨ε / (C * V + 1), by positivity,
      fun r hr hrs => ?_⟩
    rw [Real.dist_eq, hE r hr, hE s hs]
    have hL := abs_energy_finiteGeodesic_sub_le omega θ hφ hφb hsub hb₀ hb₁ hC₁ hC₀ hs hr
      (hU s hs) (hU r hr)
    have hrs' : |r - s| < ε / (C * V + 1) := by rwa [Real.dist_eq] at hrs
    have hpos : 0 < C * V + 1 := by positivity
    calc _ ≤ C * |r - s| * V := hL
      _ = (C * V) * |r - s| := by ring
      _ ≤ (C * V + 1) * |r - s| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (C * V + 1) * (ε / (C * V + 1)) := mul_lt_mul_of_pos_left hrs' hpos
      _ = ε := by field_simp
  obtain ⟨c₀, c₁, hc⟩ := exists_affine_energyCurve hbd hφ hφb hU
    (exists_stripChart_finiteGeodesic hsub hb₀ hb₁) hcont
  set E₀ := relativeEnergyOfMinimalType θ φ u₀ hφ hsub.1
  set E₁ := relativeEnergyOfMinimalType θ φ u₁ hφ hsub.2.1
  -- the endpoint values
  have h0 : c₀ = E₀ := by
    have hle : |c₀ - E₀| ≤ 0 := by
      refine le_zero_of_forall_le_mul_of_tendsto (K := C * V + |c₁|) (l := 𝓝[>] (0 : ℝ))
        (g := id) (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
      have hL := abs_energy_finiteGeodesic_sub_left_le omega θ hφ hφb hsub hb₀ hb₁ hC₁ hC₀ hs
        (hU s hs)
      rw [hc s hs] at hL
      have hs0 : 0 ≤ s := hs.1.le
      calc |c₀ - E₀| = |(c₀ + c₁ * s - E₀) - c₁ * s| := by ring_nf
        _ ≤ |c₀ + c₁ * s - E₀| + |c₁ * s| := abs_sub _ _
        _ ≤ C * s * V + |c₁| * s := by rw [abs_mul, abs_of_nonneg hs0]; linarith
        _ = (C * V + |c₁|) * id s := by simp only [id]; ring
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)
  have h1 : c₀ + c₁ = E₁ := by
    have hle : |c₀ + c₁ - E₁| ≤ 0 := by
      refine le_zero_of_forall_le_mul_of_tendsto (K := C * V + |c₁|) (l := 𝓝[<] (1 : ℝ))
        (g := fun s => 1 - s) ?_ ?_
      · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) :=
          tendsto_const_nhds.sub tendsto_id
        simpa using tendsto_nhdsWithin_of_tendsto_nhds this
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
      have hL := abs_energy_finiteGeodesic_sub_right_le omega θ hφ hφb hsub hb₀ hb₁ hC₁ hC₀ hs
        (hU s hs)
      rw [hc s hs] at hL
      have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
      calc |c₀ + c₁ - E₁| = |(c₀ + c₁ * s - E₁) + c₁ * (1 - s)| := by ring_nf
        _ ≤ |c₀ + c₁ * s - E₁| + |c₁ * (1 - s)| := abs_add_le _ _
        _ ≤ C * (1 - s) * V + |c₁| * (1 - s) := by rw [abs_mul, abs_of_nonneg hs1]; linarith
        _ = (C * V + |c₁|) * (1 - s) := by ring
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)
  rw [hc t ht]
  rw [← h0, ← h1]
  ring

/-- **The energy is affine along geodesics between endpoints in `E^∞(X, θ; φ)`**, for a bounded
model potential `φ` (there the Perron geodesic is a subgeodesic between bounded endpoints,
`trace:finite-geodesic-einfinity`). -/
theorem relativeEnergyOfMinimalType_finiteGeodesic_of_relativeEInfinity [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal}
    (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ)
    (hu₀ : RelativeEInfinity θ φ u₀) (hu₁ : RelativeEInfinity θ φ u₁) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hUt : IsThetaPshPotential θ.val (finiteGeodesic θ.val u₀ u₁ t)) :
    relativeEnergyOfMinimalType θ φ _ hφ.plurisubharmonic hUt =
      (1 - t) * relativeEnergyOfMinimalType θ φ u₀ hφ.plurisubharmonic hu₀.1 +
        t * relativeEnergyOfMinimalType θ φ u₁ hφ.plurisubharmonic hu₁.1 := by
  have hsub := FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
    omega θ φ u₀ u₁ hφ hu₀ hu₁
  exact relativeEnergyOfMinimalType_finiteGeodesic omega θ hφ.plurisubharmonic hφb hsub
    (isBoundedPotential_of_sameSingularityType hφb hu₀.2)
    (isBoundedPotential_of_sameSingularityType hφb hu₁.2) ht hUt

end Geodesic

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyAffine

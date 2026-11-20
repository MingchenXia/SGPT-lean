import SGPT.Foundations.Analysis.Pending.SmoothLastSlotChartRegularizer
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyProductPartition
import SGPT.Foundations.Analysis.Pending.SingularSmoothTestChartStokes

set_option autoImplicit false

/-!
# The produced signed fibre defect is the actual compact Stokes chart defect

Independent identification supporting Xia SGPT PDF0171. Actual full-form
core local potentials produce the Stokes slot chart. The actual corrected
endpoint tuples agree on its whole domain, including poles. Genuine NP
congruence and actual product cutoff readers identify the ordinary signed
integrals; neither a measure identity nor energy affinity is an input.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreDefectIdentification

open scoped ProductComplexManifold
open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  GlobalSlotStokes ProductComplexManifold CompactAffineCurveCharts
  FiniteGeodesicMaximality BedfordTaylorStripCovariance FiniteGeodesicStripCharts
  BedfordTaylor BedfordTaylorTimeSlot MixedNonPluripolar
  NonPluripolarTimeSlotTruncationBalance SingularModelEnergyCoreChartData
  SingularModelEnergyCoreSignedChartData SingularModelEnergyFibrePairing
  SingularModelEnergySignedFibreIdentification
  SingularModelEnergyProductPartition SmoothLastSlotChartRegularizer
  SingularSmoothTestLastSlot SingularSmoothTestChartStokes DeepCoincidenceIntegrationByParts

noncomputable section

variable {n : ℕ} {M T : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]
  {θ : ClosedRealOneOneForm n M}

/-- The true product-core slot chart read with the Stokes auxiliary alpha background, retaining exactly the actual signed-regularizer chart and slot potentials. -/
def coreStokesSlotChart (J : SlotChart (fun _ : Fin n => θ) θ)
    (e : ComplexChart 1 T) (N : Opens T) (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T)) (ρΓ : ComplexModel (n + 1) → ℝ)
    (hρΓ : IsSmoothLocalPotential Γ.val (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ρΓ) :
    SlotChart (lastHybridForms (prodForm θ κ) Γ) (prodForm θ κ) where
  chart := productComplexChart J.chart e
  domain := stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen
  domain_le_target := hρΓ.2.1
  potential := Function.update (fun _ q => J.kahler (stripFst n q)) (Fin.last n) ρΓ
  localPotential i := by
    by_cases hi : i = Fin.last n
    · subst i
      simpa only [lastHybridForms, Function.update_self] using hρΓ
    · simpa only [lastHybridForms, Function.update_of_ne hi] using
        isSmoothLocalPotential_core J e N κ hκzero
  kahler := fun q => J.kahler (stripFst n q)
  kahlerLocal := isSmoothLocalPotential_core J e N κ hκzero

/-- On the actual whole core domain, the zero-extended corrected endpoint tuple with a genuine real last slot agrees with the true Stokes patch tuple, with finite corrections and pole values intact. -/
theorem core_endpoint_tuple_eq_corrected
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T)) (ρΓ : ComplexModel (n + 1) → ℝ)
    (hρΓ : IsSmoothLocalPotential Γ.val (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ρΓ)
    {W : M × T → EReal} {φ : M → EReal}
    (hW : IsThetaPshPotential (prodForm θ κ).val W)
    (hΦ : IsThetaPshPotential (prodForm θ κ).val (fun z : M × T => φ z.1))
    (r : M × T → ℝ) (hr : IsThetaPshPotential Γ.val (fun z => (r z : EReal)))
    (k : Fin (n + 1)) :
    let P := coreStokesSlotChart J e N κ hκzero Γ ρΓ hρΓ
    ∀ i, EqOn
      (Function.update
        (endpointTimeTuple (coreChartPotential J e N W)
          (coreChartPotential J e N (fun z : M × T => φ z.1)) k)
        (Fin.last n) (fun q => ((r (P.chart.val.symm q) + ρΓ q : ℝ) : EReal)) i)
      ((P.patch (lastHybridPotentials k W (fun z : M × T => φ z.1)
        (fun z => (r z : EReal))) (lastHybridThetaPlurisubharmonic hW hΦ hr k)).corrected i)
      P.domain := by
  classical
  intro P i q hq
  dsimp only [P, coreStokesSlotChart] at hq ⊢
  by_cases hi : i = Fin.last n
  · subst i
    simp only [Function.update_self, Patch.corrected, SlotChart.patch,
      lastHybridPotentials, chartFunction, ← EReal.coe_add]
  · simp only [Function.update_of_ne hi, endpointTimeTuple, if_neg hi,
      Patch.corrected, SlotChart.patch, lastHybridPotentials,
      prefixPotentialTuple]
    split_ifs <;> simp only [coreChartPotential, Set.indicator_of_mem hq]

private theorem raw_curve_cutoff (e : ComplexChart 1 T) (N : Opens T)
    {ξ : T → ℝ} (hξ : ChartSmooth (n := 1) ξ) (hξc : HasCompactSupport ξ)
    (hξe : tsupport ξ ⊆ e.val.source) (hξN : tsupport ξ ⊆ (N : Set T)) :
    let ζ := fun σ => chartRead e ξ (curveModelEquiv.symm σ)
    Continuous ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ (coreTimeDomain e N : Set ℂ) := by
  intro ζ
  have hc := continuous_chartRead hξ hξc hξe
  have hs := hasCompactSupport_chartRead hξc hξe
  refine ⟨hc.comp curveModelEquiv.symm.continuous,
    hs.comp_homeomorph curveModelEquiv.symm.toHomeomorph, ?_⟩
  intro σ hσ
  have hread : curveModelEquiv.symm σ ∈ tsupport (chartRead e ξ) :=
    tsupport_comp_subset_preimage (chartRead e ξ) curveModelEquiv.symm.continuous hσ
  obtain ⟨y, hy, heq⟩ := tsupport_chartRead_subset hξc hξe hread
  change curveModelEquiv.symm σ ∈ e.val.target ∧
    e.val.symm (curveModelEquiv.symm σ) ∈ N
  rw [← heq, e.val.left_inv (hξe hy)]
  exact ⟨e.val.map_source (hξe hy), hξN hy⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [MeasurableSpace T] [BorelSpace T] [CompactSpace T]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [MeasurableSpace T] [BorelSpace T] [CompactSpace T] in
private theorem integral_core_tuple_eq_chart
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T)) (ρΓ : ComplexModel (n + 1) → ℝ)
    (hρΓ : IsSmoothLocalPotential Γ.val (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ρΓ)
    {W : M × T → EReal} {φ : M → EReal}
    (hW : IsThetaPshPotential (prodForm θ κ).val W)
    (hΦ : IsThetaPshPotential (prodForm θ κ).val (fun z : M × T => φ z.1))
    (hH : PlurisubharmonicOn (coreChartPotential J e N W)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen))
    (hF : PlurisubharmonicOn (coreChartPotential J e N (fun z : M × T => φ z.1))
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen))
    {f : M → ℝ} (hfc : HasCompactSupport f) (hfJ : tsupport f ⊆ (J.source : Set M))
    {ξ : T → ℝ} (hξ : ChartSmooth (n := 1) ξ) (hξc : HasCompactSupport ξ)
    (hξe : tsupport ξ ⊆ e.val.source) (hξN : tsupport ξ ⊆ (N : Set T))
    (r : M × T → ℝ) (hr : IsThetaPshPotential Γ.val (fun z => (r z : EReal)))
    (p : ComplexModel (n + 1) → ℝ)
    (hp : IsSmoothPsdOn (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) p)
    (hloc : EqOn (fun q => r ((productComplexChart J.chart e).val.symm q) + ρΓ q) p
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen))
    (k : Fin (n + 1)) :
    let P := coreStokesSlotChart J e N κ hκzero Γ ρΓ hρΓ
    (∫ q, stripCutoff (chartRead J.chart f)
        (fun σ => chartRead e ξ (curveModelEquiv.symm σ)) q *
      canonicalERealDiffToReal (coreChartPotential J e N W q)
        (coreChartPotential J e N (fun z : M × T => φ z.1) q)
      ∂mixedTruncationLimitMeasure P.domain
        (Function.update (endpointTimeTuple (coreChartPotential J e N W)
          (coreChartPotential J e N (fun z : M × T => φ z.1)) k)
          (Fin.last n) (fun q => (p q : EReal)))
        (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hF k) hp)) =
    ∫ q, chartWeight P (productWeight f ξ) W (fun z : M × T => φ z.1) q
      ∂lastHybridChartMeasure hW hΦ hr P k := by
  classical
  intro P
  let A := stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen
  let χ := stripCutoff (chartRead J.chart f) (fun σ => chartRead e ξ (curveModelEquiv.symm σ))
  let Q := P.patch (lastHybridPotentials k W (fun z : M × T => φ z.1) (fun z => (r z : EReal)))
    (lastHybridThetaPlurisubharmonic hW hΦ hr k)
  have ht := core_endpoint_tuple_eq_corrected J e N κ hκzero Γ ρΓ hρΓ hW hΦ r hr k
  have htuples : ∀ i, EqOn
      (Function.update (endpointTimeTuple (coreChartPotential J e N W)
        (coreChartPotential J e N (fun z : M × T => φ z.1)) k)
        (Fin.last n) (fun q => (p q : EReal)) i) (Q.corrected i) A := by
    intro i q hq
    by_cases hi : i = Fin.last n
    · subst i
      rw [Function.update_self, ← hloc hq]
      simpa only [Function.update_self, Q, P, coreStokesSlotChart] using ht (Fin.last n) hq
    · simpa only [Function.update_of_ne hi] using ht i hq
  have hμ := mixedTruncationLimitMeasure_congr
    (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hF k) hp)
    Q.plurisubharmonic htuples
  change (∫ q, χ q * canonicalERealDiffToReal (coreChartPotential J e N W q)
      (coreChartPotential J e N (fun z : M × T => φ z.1) q)
      ∂mixedTruncationLimitMeasure A _ _) = _
  rw [hμ]
  have hfs : tsupport f ⊆ J.chart.val.source := fun _ hx => (hfJ hx).1
  have hreadD : tsupport (chartRead J.chart f) ⊆ (J.domain : Set (ComplexModel n)) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := tsupport_chartRead_subset hfc hfs hq
    exact (hfJ hx).2
  have hraw := raw_curve_cutoff e N hξ hξc hξe hξN
  have hχA : tsupport χ ⊆ (A : Set (ComplexModel (n + 1))) :=
    tsupport_stripCutoff_subset_stripLift (hasCompactSupport_chartRead hfc hfs)
      hraw.2.1 (coreTimeDomain e N).isOpen hreadD hraw.2.2
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  change χ q * canonicalERealDiffToReal (coreChartPotential J e N W q)
      (coreChartPotential J e N (fun z : M × T => φ z.1) q) =
    chartWeight P (productWeight f ξ) W (fun z : M × T => φ z.1) q
  dsimp only [chartWeight, P, coreStokesSlotChart]
  rw [chartRead_productWeight_eq]
  by_cases hq : q ∈ A
  · change q ∈ stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen at hq
    simp only [coreChartPotential, Set.indicator_of_mem hq]
    rfl
  · have hz : χ q = 0 := image_eq_zero_of_notMem_tsupport fun ht => hq (hχA ht)
    change χ q * _ = χ q * _
    rw [hz, zero_mul, zero_mul]

/-- The complete internally produced smooth compact-core signed chart data have exactly the actual compact Stokes chart defect, with no supplied tuple or measure identity. -/
theorem produced_defect_eq_stokes_chart_defect
    (omega : KahlerBackground (n + 1) (M × T))
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T)) (ρΓ : ComplexModel (n + 1) → ℝ)
    (hρΓ : IsSmoothLocalPotential Γ.val (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ρΓ)
    {W : M × T → EReal} {φ : M → EReal}
    (hW : IsThetaPshPotential (prodForm θ κ).val W)
    (hΦ : IsThetaPshPotential (prodForm θ κ).val (fun z : M × T => φ z.1))
    (hWΦ : SameSingularityTypeOn W (fun z : M × T => φ z.1) univ)
    (U : ℝ → M → EReal) (time : T → ℂ)
    (hcore : ∀ x y, y ∈ N → W (x, y) = U (time y).re x)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (hfc : HasCompactSupport f)
    (hfJ : tsupport f ⊆ (J.source : Set M))
    {ξ : T → ℝ} (hξ : ChartSmooth (n := 1) ξ) (hξc : HasCompactSupport ξ)
    (hξe : tsupport ξ ⊆ e.val.source) (hξN : tsupport ξ ⊆ (N : Set T))
    (a b : Fin (n + 1) → M × T → ℝ)
    (has : ∀ k, ChartSmooth (n := n + 1) (a k))
    (hbs : ∀ k, ChartSmooth (n := n + 1) (b k))
    (ha : ∀ k, IsThetaPshPotential Γ.val fun z => (a k z : EReal))
    (hb : ∀ k, IsThetaPshPotential Γ.val fun z => (b k z : EReal))
    (G : M × T → ℝ) (hab : ∀ k z, a k z = b k z + G z) {ψ : ℂ → ℝ}
    (hG : EqOn (fun z => G ((productComplexChart J.chart e).val.symm z))
      (timeLift n ψ) (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen))
    (k : Fin (n + 1)) :
    let hζ := raw_curve_cutoff e N hξ hξc hξe hξN
    let d := signedChartData_of_smooth_compact_host omega J e N κ hκzero Γ ρΓ hρΓ
      hW.1 hΦ.1 hWΦ U time hcore hf hfc hfJ hζ.1 hζ.2.1 hζ.2.2 a b has hbs
      (fun j => (ha j).1) (fun j => (hb j).1) G hab hG
    let P := coreStokesSlotChart J e N κ hκzero Γ ρΓ hρΓ
    d.defect k =
      (∫ q, chartWeight P (productWeight f ξ) W (fun z : M × T => φ z.1) q
        ∂lastHybridChartMeasure hW hΦ (ha k) P k) -
      (∫ q, chartWeight P (productWeight f ξ) W (fun z : M × T => φ z.1) q
        ∂lastHybridChartMeasure hW hΦ (hb k) P k) := by
  intro hζ d P
  have hreg := smooth_pair_regularizer (productComplexChart J.chart e) hρΓ
    (has k) (hbs k) (ha k).1 (hb k).1 (hab k) hG
  have hA := integral_core_tuple_eq_chart J e N κ hκzero Γ ρΓ hρΓ hW hΦ
    d.hH d.hΦ hfc hfJ hξ hξc hξe hξN (a k) (ha k)
    (fun q => timeLift n ψ q + (b k ((productComplexChart J.chart e).val.symm q) + ρΓ q))
    hreg.2.1 hreg.2.2.1 k
  have hB := integral_core_tuple_eq_chart J e N κ hκzero Γ ρΓ hρΓ hW hΦ
    d.hH d.hΦ hfc hfJ hξ hξc hξe hξN (b k) (hb k)
    (fun q => b k ((productComplexChart J.chart e).val.symm q) + ρΓ q)
    hreg.1 hreg.2.2.2 k
  exact congrArg₂ (fun x y : ℝ => x - y) hA hB

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreDefectIdentification

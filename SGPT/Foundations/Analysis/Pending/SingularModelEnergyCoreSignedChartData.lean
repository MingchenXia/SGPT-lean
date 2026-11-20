import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreChartData
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyFibrePairing
import SGPT.Foundations.Analysis.Pending.CompactNonPluripolarTimeSlotDefect

set_option autoImplicit false

/-!
# Genuine compact product-core geometry produces all signed fibre-chart fields

Independent assembler for Xia SGPT PDF0171. The inputs concern actual
compact-host potentials, actual zero core and genuine smooth last-slot
geometry. No joint PSH, fibre-coordinate identity, regularizer integral
or energy/current conclusion is a new premise.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreSignedChartData

open scoped ProductComplexManifold
open FirstPass FirstPass.PositiveClasses GlobalSlotStokes ProductComplexManifold
  CompactAffineCurveCharts FiniteGeodesicMaximality BedfordTaylorStripCovariance
  FiniteGeodesicStripCharts BedfordTaylor BedfordTaylorTimeSlot MixedDensityRankOneSlot MixedNonPluripolar
  NonPluripolarTimeSlotTruncationBalance SingularModelEnergyCoreChartData
  SingularModelEnergySignedFibreIdentification SingularModelEnergyFibrePairing
  CompactNonPluripolarTimeSlotDefect

noncomputable section

variable {n : ℕ} {M T : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]

/-- Actual singular product backgrounds in the first n slots, and the true global smooth regularizer background in the last slot. -/
def coreSlotForms (θ : ClosedRealOneOneForm n M) (κ : ClosedRealOneOneForm 1 T)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T)) :
    Fin (n + 1) → ClosedRealOneOneForm (n + 1) (M × T) :=
  Function.update (fun _ => prodForm θ κ) (Fin.last n) Γ

/-- The genuine common product atlas slot chart, internally producing every first-slot local potential from the actual zero core. -/
def coreSlotChart {θ : ClosedRealOneOneForm n M}
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T)) (ρΓ : ComplexModel (n + 1) → ℝ)
    (hρΓ : IsSmoothLocalPotential Γ.val (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ρΓ) :
    SlotChart (coreSlotForms θ κ Γ) Γ where
  chart := productComplexChart J.chart e
  domain := stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen
  domain_le_target := hρΓ.2.1
  potential := Function.update (fun _ q => J.kahler (stripFst n q)) (Fin.last n) ρΓ
  localPotential i := by
    by_cases hi : i = Fin.last n
    · subst i
      simpa only [coreSlotForms, Function.update_self] using hρΓ
    · simpa only [coreSlotForms, Function.update_of_ne hi] using
        isSmoothLocalPotential_core J e N κ hκzero
  kahler := ρΓ
  kahlerLocal := hρΓ

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [MeasurableSpace T] [BorelSpace T] [CompactSpace T]

/-- Actual compact-host, zero-core and smooth-slot geometric data produce all Borel joint PSH, fibre coordinates and genuine regularizer integrability fields of the signed chart package. -/
def signedChartData_of_compact_host {θ : ClosedRealOneOneForm n M}
    (omega : KahlerBackground (n + 1) (M × T))
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T)) (ρΓ : ComplexModel (n + 1) → ℝ)
    (hρΓ : IsSmoothLocalPotential Γ.val (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ρΓ)
    {W : M × T → EReal} {φ : M → EReal}
    (hW : ThetaPlurisubharmonic (prodForm θ κ).val W)
    (hΦ : ThetaPlurisubharmonic (prodForm θ κ).val (fun q : M × T => φ q.1))
    (hWΦ : SameSingularityTypeOn W (fun q : M × T => φ q.1) univ)
    (U : ℝ → M → EReal) (time : T → ℂ)
    (hcore : ∀ x y, y ∈ N → W (x, y) = U (time y).re x)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (hfc : HasCompactSupport f)
    (hfJ : tsupport f ⊆ (J.source : Set M))
    {ζ ψ : ℂ → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    (hζS : tsupport ζ ⊆ (coreTimeDomain e N : Set ℂ))
    (a b : Fin (n + 1) → M × T → ℝ)
    (ha : ∀ k, ThetaPlurisubharmonic Γ.val fun q => (a k q : EReal))
    (hb : ∀ k, ThetaPlurisubharmonic Γ.val fun q => (b k q : EReal))
    (p : Fin (n + 1) → ComplexModel (n + 1) → ℝ)
    (hp : ∀ k, IsSmoothPsdOn
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) (p k))
    (hψp : ∀ k, IsSmoothPsdOn
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen)
        fun q => timeLift n ψ q + p k q)
    (haLocal : ∀ k, EqOn
      (fun q => a k ((productComplexChart J.chart e).val.symm q) + ρΓ q)
      (fun q => timeLift n ψ q + p k q)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen))
    (hbLocal : ∀ k, EqOn
      (fun q => b k ((productComplexChart J.chart e).val.symm q) + ρΓ q) (p k)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen)) :
    SignedChartData θ φ
      (fun σ => U (time (e.val.symm (curveModelEquiv.symm σ))).re)
      (coreTimeDomain e N) (coreTimeDomain e N).isOpen J f ψ ζ := by
  classical
  let H := coreChartPotential J e N W
  let F := coreChartPotential J e N (fun q : M × T => φ q.1)
  let A := stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen
  let P := coreSlotChart J e N κ hκzero Γ ρΓ hρΓ
  have hdata := core_joint_chart_data J e N κ hκzero hW hΦ U time hcore
  have hH : PlurisubharmonicOn H A := hdata.2.2.1
  have hF : PlurisubharmonicOn F A := hdata.2.2.2.1
  let χ := stripCutoff (chartRead J.chart f) ζ
  have hfs : tsupport f ⊆ J.chart.val.source := fun _ hx => (hfJ hx).1
  have hreadc : HasCompactSupport (chartRead J.chart f) := hasCompactSupport_chartRead hfc hfs
  have hreadD : tsupport (chartRead J.chart f) ⊆ (J.domain : Set (ComplexModel n)) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := tsupport_chartRead_subset hfc hfs hq
    exact (hfJ hx).2
  have hχ : Continuous χ := continuous_stripCutoff (continuous_chartRead hf hfc hfs) hζ
  have hχc : HasCompactSupport χ := hasCompactSupport_stripCutoff hreadc hζc
  have hχA : tsupport χ ⊆ (A : Set (ComplexModel (n + 1))) :=
    tsupport_stripCutoff_subset_stripLift hreadc hζc (coreTimeDomain e N).isOpen hreadD hζS
  have hweights (q : ComplexModel (n + 1)) :
      χ q * canonicalERealDiffToReal
        (chartFunction W P.chart q + (J.kahler (stripFst n q) : EReal))
        (chartFunction (fun q : M × T => φ q.1) P.chart q + (J.kahler (stripFst n q) : EReal)) =
      χ q * canonicalERealDiffToReal (H q) (F q) := by
    by_cases hq : q ∈ A
    · change q ∈ stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen at hq
      simp only [H, F, coreChartPotential, Set.indicator_of_mem hq]
      rfl
    · have hχzero : χ q = 0 := image_eq_zero_of_notMem_tsupport fun ht => hq (hχA ht)
      simp only [hχzero, zero_mul]
  have hints (k : Fin (n + 1)) :
      Integrable (fun q => χ q * canonicalERealDiffToReal (H q) (F q))
        (mixedTruncationLimitMeasure A
          (Function.update (endpointTimeTuple H F k) (Fin.last n)
            fun q => ((timeLift n ψ q + p k q : ℝ) : EReal))
          (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hF k) (hψp k))) ∧
      Integrable (fun q => χ q * canonicalERealDiffToReal (H q) (F q))
        (mixedTruncationLimitMeasure A
          (Function.update (endpointTimeTuple H F k) (Fin.last n) fun q => (p k q : EReal))
          (plurisubharmonicOn_update_last (endpointTimeTuple_plurisubharmonicOn hH hF k) (hp k))) := by
    let v : Fin (n + 1) → M × T → EReal := fun i => if i.val < k.val then W else fun q => φ q.1
    have hv (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
        ThetaPlurisubharmonic (coreSlotForms θ κ Γ i).val (v i) := by
      simp only [coreSlotForms, Function.update_of_ne hi]
      dsimp only [v]
      split_ifs <;> assumption
    have hfirst (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
        EqOn (endpointTimeTuple H F k i)
          (fun q => chartFunction (v i) P.chart q + (P.potential i q : EReal)) P.domain := by
      intro q hq
      change q ∈ stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen at hq
      simp only [endpointTimeTuple, if_neg hi, P, coreSlotChart, Function.update_of_ne hi]
      dsimp only [v]
      split_ifs <;> simp only [H, F, coreChartPotential, Set.indicator_of_mem hq]
    have ha' : ThetaPlurisubharmonic (coreSlotForms θ κ Γ (Fin.last n)).val
        fun q => (a k q : EReal) := by
      simpa only [coreSlotForms, Function.update_self] using ha k
    have hb' : ThetaPlurisubharmonic (coreSlotForms θ κ Γ (Fin.last n)).val
        fun q => (b k q : EReal) := by
      simpa only [coreSlotForms, Function.update_self] using hb k
    have haL : EqOn (fun q => a k (P.chart.val.symm q) + P.potential (Fin.last n) q)
        (fun q => timeLift n ψ q + p k q) P.domain := by
      simpa only [P, coreSlotChart, Function.update_self] using haLocal k
    have hbL : EqOn (fun q => b k (P.chart.val.symm q) + P.potential (Fin.last n) q)
        (p k) P.domain := by
      simpa only [P, coreSlotChart, Function.update_self] using hbLocal k
    have hi := regularizer_weights_integrable omega hW hΦ hWΦ P hv ha' hb'
      (endpointTimeTuple_plurisubharmonicOn hH hF k) hfirst (hp k) (hψp k)
      haL hbL hχ hχc (fun q => J.kahler (stripFst n q))
    exact ⟨hi.1.congr (Eventually.of_forall hweights), hi.2.congr (Eventually.of_forall hweights)⟩
  exact {
    H := H
    Φ := F
    hH := hH
    hΦ := hF
    hHm := hdata.1
    hΦm := hdata.2.1
    c := fun _ => 0
    hHcoord := fun σ hσ y hy => (hdata.2.2.2.2 σ hσ y hy).1
    hΦcoord := fun σ hσ y hy => (hdata.2.2.2.2 σ hσ y hy).2
    p := p
    hp := hp
    hψp := hψp
    ha := fun k => (hints k).1
    hb := fun k => (hints k).2 }

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreSignedChartData

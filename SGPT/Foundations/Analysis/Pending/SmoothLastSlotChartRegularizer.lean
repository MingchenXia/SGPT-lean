import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreSignedChartData
import SGPT.Foundations.Analysis.Pending.GlobalWeightedDecreasingLimit

set_option autoImplicit false

/-!
# Actual global smooth PSH pairs produce their local regularizer slots

Independent smooth-slot assembler supporting Xia SGPT PDF0171. The actual
global pair and chart reading of its ordinary scalar difference internally
produce local PSD and both local smooth-slot identities. The compact-core
consumer also produces all signed fibre-chart data and ordinary integrability.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SmoothLastSlotChartRegularizer

open FirstPass FirstPass.PositiveClasses BedfordTaylor GlobalWeightedDecreasingLimit

noncomputable section

/-- Genuine global chart-smooth Gamma-PSH functions and the actual chart reading of their ordinary difference produce both local PSD facts and both scalar regularizer identities. -/
theorem smooth_pair_regularizer {m : ℕ} {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {Γ : ClosedRealOneOneForm m Y} (e : ComplexChart m Y)
    {D : Opens (ComplexModel m)} {ρΓ : ComplexModel m → ℝ}
    (hρΓ : IsSmoothLocalPotential Γ.val e D ρΓ) {a b G : Y → ℝ}
    (has : ChartSmooth (n := m) a) (hbs : ChartSmooth (n := m) b)
    (ha : ThetaPlurisubharmonic Γ.val fun y => (a y : EReal))
    (hb : ThetaPlurisubharmonic Γ.val fun y => (b y : EReal))
    (hab : ∀ y, a y = b y + G y) {q : ComplexModel m → ℝ}
    (hG : EqOn (fun z => G (e.val.symm z)) q D) :
    IsSmoothPsdOn D (fun z => b (e.val.symm z) + ρΓ z) ∧
    IsSmoothPsdOn D (fun z => q z + (b (e.val.symm z) + ρΓ z)) ∧
    EqOn (fun z => a (e.val.symm z) + ρΓ z)
      (fun z => q z + (b (e.val.symm z) + ρΓ z)) D ∧
    EqOn (fun z => b (e.val.symm z) + ρΓ z)
      (fun z => b (e.val.symm z) + ρΓ z) D := by
  have hp := isSmoothPsdOn_chart hbs hb e hρΓ (U := D) Subset.rfl
  have hpa := isSmoothPsdOn_chart has ha e hρΓ (U := D) Subset.rfl
  have heqa : EqOn (fun z => a (e.val.symm z) + ρΓ z)
      (fun z => q z + (b (e.val.symm z) + ρΓ z)) D := by
    intro z hz
    change a (e.val.symm z) + ρΓ z = q z + (b (e.val.symm z) + ρΓ z)
    have hGz : G (e.val.symm z) = q z := hG hz
    rw [hab, hGz]
    ring
  have hsm : ContDiffOn ℝ ∞ (fun z => q z + (b (e.val.symm z) + ρΓ z)) D :=
    hpa.1.congr (fun z hz => (heqa hz).symm)
  have hpsh : PlurisubharmonicOn
      (fun z => ((q z + (b (e.val.symm z) + ρΓ z) : ℝ) : EReal)) D := by
    intro z hz
    apply (hpa.plurisubharmonicOn z hz).congr
    filter_upwards [D.isOpen.mem_nhds hz] with w hw
    exact congrArg (fun r : ℝ => (r : EReal)) (heqa hw)
  exact ⟨hp, UniformBoundedGlobalMass.isSmoothPsdOn_of_plurisubharmonicOn hsm hpsh,
    heqa, fun _ _ => rfl⟩

open scoped ProductComplexManifold
open GlobalSlotStokes ProductComplexManifold CompactAffineCurveCharts
  FiniteGeodesicMaximality BedfordTaylorStripCovariance FiniteGeodesicStripCharts
  BedfordTaylorTimeSlot SingularModelEnergyCoreChartData
  SingularModelEnergyCoreSignedChartData SingularModelEnergyFibrePairing

variable {n : ℕ} {M T : Type*}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [MeasurableSpace T] [BorelSpace T] [CompactSpace T]

/-- Actual smooth global Gamma-PSH pairs and their scalar test reading produce the complete signed fibre-chart data without supplied PSD, local regularizer identities, joint PSH, fibre coordinates or integral-finiteness conclusions. -/
def signedChartData_of_smooth_compact_host {θ : ClosedRealOneOneForm n M}
    (omega : KahlerBackground (n + 1) (M × T))
    (J : SlotChart (fun _ : Fin n => θ) θ) (e : ComplexChart 1 T) (N : Opens T)
    (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T)) (ρΓ : ComplexModel (n + 1) → ℝ)
    (hρΓ : IsSmoothLocalPotential Γ.val (productComplexChart J.chart e)
      (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) ρΓ)
    {W : M × T → EReal} {φ : M → EReal}
    (hW : ThetaPlurisubharmonic (prodForm θ κ).val W)
    (hΦ : ThetaPlurisubharmonic (prodForm θ κ).val (fun z : M × T => φ z.1))
    (hWΦ : SameSingularityTypeOn W (fun z : M × T => φ z.1) univ)
    (U : ℝ → M → EReal) (time : T → ℂ)
    (hcore : ∀ x y, y ∈ N → W (x, y) = U (time y).re x)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (hfc : HasCompactSupport f)
    (hfJ : tsupport f ⊆ (J.source : Set M))
    {ζ ψ : ℂ → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    (hζS : tsupport ζ ⊆ (coreTimeDomain e N : Set ℂ))
    (a b : Fin (n + 1) → M × T → ℝ)
    (has : ∀ k, ChartSmooth (n := n + 1) (a k))
    (hbs : ∀ k, ChartSmooth (n := n + 1) (b k))
    (ha : ∀ k, ThetaPlurisubharmonic Γ.val fun z => (a k z : EReal))
    (hb : ∀ k, ThetaPlurisubharmonic Γ.val fun z => (b k z : EReal))
    (G : M × T → ℝ) (hab : ∀ k z, a k z = b k z + G z)
    (hG : EqOn (fun z => G ((productComplexChart J.chart e).val.symm z))
      (timeLift n ψ) (stripLift J.domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen)) :
    SignedChartData θ φ
      (fun σ => U (time (e.val.symm (curveModelEquiv.symm σ))).re)
      (coreTimeDomain e N) (coreTimeDomain e N).isOpen J f ψ ζ := by
  let p : Fin (n + 1) → ComplexModel (n + 1) → ℝ := fun k z =>
    b k ((productComplexChart J.chart e).val.symm z) + ρΓ z
  have hreg (k : Fin (n + 1)) := smooth_pair_regularizer (productComplexChart J.chart e)
    hρΓ (has k) (hbs k) (ha k) (hb k) (hab k) hG
  exact signedChartData_of_compact_host omega J e N κ hκzero Γ ρΓ hρΓ hW hΦ hWΦ U time hcore
    hf hfc hfJ hζ hζc hζS a b ha hb p
    (fun k => (hreg k).1) (fun k => (hreg k).2.1)
    (fun k => (hreg k).2.2.1) (fun k => (hreg k).2.2.2)

end

end SGPT.Foundations.Analysis.Pending.SmoothLastSlotChartRegularizer

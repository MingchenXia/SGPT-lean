import SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshHartogs
import SGPT.Foundations.Analysis.Pending.NaturalWeakDistributionOrder

/-!
# Original global theta-PSH order retained by genuine weak chart limits

The same actual local potential corrects the family, its weak limit and
its genuine original barrier. Only finite correction is canceled after
the original PSH weak-order producer recovers every point.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshOrder

open FirstPass NaturalWeakPotentialHartogs

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- An actual original eventual theta-PSH barrier survives a genuine native weak chart limit. -/
theorem le_of_chart_weak_limit_eventually_le
    {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → M → EReal} {v w : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hw : IsThetaPshPotential θ w)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    (hdom : ∀ᶠ i in l, u i ≤ w) : v ≤ w := by
  intro x
  let e : ComplexChart n M := complexChartAt (n := n) x
  let z : ComplexModel n := e.val x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : z ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpv⟩ := hv.1 e z hz
  obtain ⟨ε, hε, hlocal⟩ := Metric.mem_nhds_iff.mp (hρ.1.mem_nhds hzW)
  let Ω : Opens (ComplexModel n) := ⟨ball z ε, isOpen_ball⟩
  have hΩW : (Ω : Set (ComplexModel n)) ⊆ W := hlocal
  have hΩt : (Ω : Set (ComplexModel n)) ⊆ e.val.target := hΩW.trans hρ.2.1
  let corrected (f : M → EReal) : ComplexModel n → EReal :=
    fun y => chartFunction f e y + (ρ y : EReal)
  have hcpsh (f : M → EReal) (hf : IsThetaPshPotential θ f) :
      PlurisubharmonicOn (corrected f) Ω :=
    (ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
      hf.1 e hρ).mono hΩW
  have hne (f : M → EReal) (hf : IsThetaPshPotential θ f) :
      ∃ y ∈ Ω, corrected f y ≠ ⊥ := by
    obtain ⟨y, hyΩ, hy⟩ := hf.2.exists_chart_ne_bot e Ω.isOpen hΩt (mem_ball_self hε)
    exact ⟨y, hyΩ, EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot (ρ y)⟩⟩
  have hrawlim : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ y, φ y * (chartFunction (u i) e y).toReal ∂volume) l
        (𝓝 (∫ y, φ y * (chartFunction v e y).toReal ∂volume)) := by
    intro φ
    let ψ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ) := TestFunction.monoCLM ℝ φ
    have hψ : (ψ : ComplexModel n → ℝ) = φ := by
      have hinc : Ω ≤ ⟨e.val.target, e.val.open_target⟩ := hΩt
      simp only [ψ, TestFunction.monoCLM_apply, le_refl, hinc, and_self, ite_true]
    simpa only [hψ] using hlim e ψ
  have hcorrectedlim : ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => ∫ y, φ y * (corrected (u i) y).toReal ∂volume) l
        (𝓝 (∫ y, φ y * (corrected v y).toReal ∂volume)) :=
    weak_tests_tendsto_corrected_of_continuous_potential
      (hρ.2.2.1.continuousOn.mono hΩW) (fun i => hcpsh (u i) (hu i))
      (hcpsh v hv) volume (convex_ball z ε).isPreconnected
      (fun i => hne (u i) (hu i)) (hne v hv) hrawlim
  have hcorrectedDom : ∀ᶠ i in l, ∀ y ∈ Ω, corrected (u i) y ≤ corrected w y := by
    filter_upwards [hdom] with i hi
    intro y _
    exact add_le_add (hi (e.val.symm y)) le_rfl
  have hmodel := NaturalWeakDistributionOrder.le_of_weak_limit_eventually_le
    (fun i => hcpsh (u i) (hu i)) (hcpsh v hv) (hcpsh w hw) volume
    (convex_ball z ε).isPreconnected (fun i => hne (u i) (hu i)) (hne v hv) (hne w hw)
    hcorrectedlim hcorrectedDom
  have h := hmodel z (mem_ball_self hε)
  change v (e.val.symm (e.val x)) + (ρ z : EReal) ≤
    w (e.val.symm (e.val x)) + (ρ z : EReal) at h
  rw [e.val.left_inv hx] at h
  exact (EReal.addLECancellable_coe (ρ z)).add_le_add_iff_right.mp h

end SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshOrder

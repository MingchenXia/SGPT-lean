import SGPT.Foundations.Analysis.Pending.NaturalWeakPotentialHartogs
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord

/-!
# Genuine original theta-PSH neighborhood recovery from native weak chart tests

One actual local potential corrects the limit and every family member.
The original filter event is retained through native test inclusion, finite
potential transport, and recovery of every original value on a neighborhood.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshHartogs

open FirstPass NaturalWeakPotentialHartogs

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : SmoothRealForm n M 2}

/-- Actual weak chart reads yield one original upper event throughout an actual neighborhood. -/
theorem eventually_locally_le_of_chart_weak_tests
    {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hlim : ∀ (e : ComplexChart n M)
      (φ : 𝓓(⟨e.val.target, e.val.open_target⟩, ℝ)),
      Tendsto (fun i => ∫ z, φ z * (chartFunction (u i) e z).toReal ∂volume) l
        (𝓝 (∫ z, φ z * (chartFunction v e z).toReal ∂volume)))
    {C : ℝ} (hC : ∀ i y, u i y ≤ (C : EReal))
    (x : M) {a : ℝ} (ha : v x < (a : EReal)) :
    ∃ V : Set M, V ∈ 𝓝 x ∧ ∀ᶠ i in l, ∀ y ∈ V, u i y ≤ (a : EReal) := by
  obtain ⟨b, hvb, hba⟩ := EReal.exists_rat_btwn_of_lt ha
  have hbaR : (b : ℝ) < a := EReal.coe_lt_coe_iff.mp hba
  let δ : ℝ := (a - (b : ℝ)) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let e : ComplexChart n M := complexChartAt (n := n) x
  let z : ComplexModel n := e.val x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : z ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpv⟩ := hv.1 e z hz
  let corrected (f : M → EReal) : ComplexModel n → EReal :=
    fun y => chartFunction f e y + (ρ y : EReal)
  let A : ℝ := (b : ℝ) + ρ z
  have htest : corrected v z < (A : EReal) := by
    have hraw : chartFunction v e z < ((b : ℝ) : EReal) := by
      simpa only [chartFunction, z, e.val.left_inv hx] using hvb
    simpa only [corrected, A, EReal.coe_add] using EReal.add_lt_add_right_coe hraw (ρ z)
  have hρcont : ContinuousAt ρ z :=
    ((hρ.2.2.1 z hzW).contDiffAt (hρ.1.mem_nhds hzW)).continuousAt
  have hρlow : ∀ᶠ y in 𝓝 z, ρ z - δ < ρ y :=
    hρcont.eventually (lt_mem_nhds (sub_lt_self _ hδ))
  have hρupper : ∀ᶠ y in 𝓝 z, ρ y < ρ z + 1 :=
    hρcont.eventually (gt_mem_nhds (by linarith : ρ z < ρ z + 1))
  have hnhds : {y | y ∈ W ∧ ρ z - δ < ρ y ∧ ρ y < ρ z + 1} ∈ 𝓝 z := by
    filter_upwards [hρ.1.mem_nhds hzW, hρlow, hρupper] with y hyW hylo hyup
    exact ⟨hyW, hylo, hyup⟩
  obtain ⟨ε, hε, hlocal⟩ := Metric.mem_nhds_iff.mp hnhds
  let Ω : Opens (ComplexModel n) := ⟨ball z ε, isOpen_ball⟩
  have hΩW : (Ω : Set (ComplexModel n)) ⊆ W := fun y hy => (hlocal hy).1
  have hΩt : (Ω : Set (ComplexModel n)) ⊆ e.val.target := hΩW.trans hρ.2.1
  have hρΩ : ContinuousOn ρ Ω := hρ.2.2.1.continuousOn.mono hΩW
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
    weak_tests_tendsto_corrected_of_continuous_potential hρΩ
      (fun i => hcpsh (u i) (hu i)) (hcpsh v hv) volume (convex_ball z ε).isPreconnected
      (fun i => hne (u i) (hu i)) (hne v hv) hrawlim
  have hcorrectedC : ∀ i y, y ∈ Ω → corrected (u i) y ≤ ((C + ρ z + 1 : ℝ) : EReal) := by
    intro i y hy
    have hsum := add_le_add (hC i (e.val.symm y))
      (EReal.coe_le_coe_iff.mpr (hlocal hy).2.2.le)
    simpa only [corrected, chartFunction, ← EReal.coe_add, add_assoc] using hsum
  have htarget : corrected v z < ((A + δ : ℝ) : EReal) :=
    htest.trans (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hδ))
  obtain ⟨r, hr, hrΩ, hevent⟩ := eventually_locally_le_of_weak_tests
    (fun i => hcpsh (u i) (hu i)) (hcpsh v hv) volume (convex_ball z ε).isPreconnected
    (fun i => hne (u i) (hu i)) (hne v hv) hcorrectedlim hcorrectedC z
    (mem_ball_self hε) htarget
  let V : Set M := e.val.source ∩ e.val ⁻¹' ball z r
  have hVopen : IsOpen V := e.val.isOpen_inter_preimage isOpen_ball
  have hxV : x ∈ V := ⟨hx, mem_ball_self hr⟩
  refine ⟨V, hVopen.mem_nhds hxV, ?_⟩
  filter_upwards [hevent] with i hi
  intro y hy
  have hρy := (hlocal (hrΩ hy.2)).2.1
  have hbound := hi (e.val y) hy.2
  change u i (e.val.symm (e.val y)) + (ρ (e.val y) : EReal) ≤
    ((A + δ : ℝ) : EReal) at hbound
  rw [e.val.left_inv hy.1] at hbound
  have hboundTarget : ((A + δ : ℝ) : EReal) ≤ (a : EReal) + (ρ (e.val y) : EReal) := by
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    dsimp only [A, δ] at hρy ⊢
    linarith
  exact (EReal.addLECancellable_coe (ρ (e.val y))).add_le_add_iff_right.mp
    (hbound.trans hboundTarget)

end SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshHartogs

import SGPT.PSH.CartierLocalGeometricFactorization

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open InvertibleIdealQuotient RegularLocusComponent AnalyticGermDecomposition
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem centered_holomorphic (x : M) (b : M → ℂ) (hb : HolomorphicAt n b x) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ
      (fun z => b ((complexChartAt (n := n) x).val.symm
        (z + (complexChartAt (n := n) x).val x))) z := by
  let e := (complexChartAt (n := n) x).val
  have ht : Tendsto (fun z : ComplexModel n => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hcoord : ∀ᶠ w in 𝓝 (e x), DifferentiableAt ℂ (fun w : ComplexModel n => b (e.symm w)) w :=
    DerivativeIdeal.eventually_differentiableAt_comp_symm (complexChartAt (n := n) x)
      (mem_complexChartAt_source x) hb
  filter_upwards [ht.eventually hcoord] with z hz
  change DifferentiableAt ℂ
    ((fun w : ComplexModel n => b (e.symm w)) ∘ fun z => z + e x) z
  exact hz.comp z (differentiableAt_id.add_const (e x))

/-- Equality of the ACTUAL generated Cartier ideals produces a genuine
unit transition between original centered functions, including singular zeros. -/
theorem exists_centered_unit_transition_of_cartier_generators
    (D : EffectiveDivisor n M) (x : M) (g h : M → ℂ)
    (hg : HolomorphicAt n g x) (hh : HolomorphicAt n h x)
    (hgenG : ∀ b, D.ideal.mem x b ↔ IsInSpanAt (n := n) (· = g) x b)
    (hgenH : ∀ b, D.ideal.mem x b ↔ IsInSpanAt (n := n) (· = h) x b) :
    ∃ (U : ComplexModel n → ℂ)
      (_hU : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ U z),
      U 0 ≠ 0 ∧ (∀ᶠ z in 𝓝 0, U z ≠ 0) ∧
      (fun z => g ((complexChartAt (n := n) x).val.symm
        (z + (complexChartAt (n := n) x).val x))) =ᶠ[𝓝 0]
        fun z => h ((complexChartAt (n := n) x).val.symm
          (z + (complexChartAt (n := n) x).val x)) * U z := by
  have hgmem : D.ideal.mem x g := (hgenG g).mpr (isInSpanAt_self rfl hg)
  have hhmem : D.ideal.mem x h := (hgenH h).mpr (isInSpanAt_self rfl hh)
  obtain ⟨_, a, ha, hga⟩ := isInSpanAt_eq_iff.mp ((hgenH g).mp hgmem)
  obtain ⟨_, b, hb, hhb⟩ := isInSpanAt_eq_iff.mp ((hgenG h).mp hhmem)
  let e := (complexChartAt (n := n) x).val
  let center := fun k : M → ℂ => fun z : ComplexModel n => k (e.symm (z + e x))
  have hfg := centered_holomorphic x g hg
  have hfh := centered_holomorphic x h hh
  have hfa := centered_holomorphic x a ha
  have hfb := centered_holomorphic x b hb
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have ht : Tendsto (fun z : ComplexModel n => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hchart : Tendsto (fun z : ComplexModel n => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  have hga' : HolGerm.mk (center g) hfg = HolGerm.mk (center a) hfa * HolGerm.mk (center h) hfh := by
    rw [← HolGerm.mk_mul (center a) (center h) hfa hfh]
    exact HolGerm.mk_eq_mk_iff.mpr (hchart.eventually hga)
  have hhb' : HolGerm.mk (center h) hfh = HolGerm.mk (center b) hfb * HolGerm.mk (center g) hfg := by
    rw [← HolGerm.mk_mul (center b) (center g) hfb hfg]
    exact HolGerm.mk_eq_mk_iff.mpr (hchart.eventually hhb)
  have hdivGH : HolGerm.mk (center g) hfg ∣ HolGerm.mk (center h) hfh :=
    ⟨HolGerm.mk (center b) hfb, hhb'.trans (mul_comm _ _)⟩
  have hdivHG : HolGerm.mk (center h) hfh ∣ HolGerm.mk (center g) hfg :=
    ⟨HolGerm.mk (center a) hfa, hga'.trans (mul_comm _ _)⟩
  obtain ⟨unit, heq⟩ := (associated_of_dvd_dvd hdivGH hdivHG).symm
  obtain ⟨U, hU, hUrep⟩ := HolGerm.exists_eq_mk (unit : HolGerm (ComplexModel n))
  have hU0 : U 0 ≠ 0 := by
    have hv := (HolGerm.isUnit_iff_eval_ne_zero _).mp unit.isUnit
    rwa [hUrep, HolGerm.eval_mk] at hv
  have hfuneq : HolGerm.mk (center g) hfg = HolGerm.mk
      (fun z => center h z * U z) (eventually_differentiableAt_mul hfh hU) := by
    rw [HolGerm.mk_mul (center h) U hfh hU, ← hUrep]
    exact heq.symm
  exact ⟨U, hU, hU0, hU.self_of_nhds.continuousAt.eventually_ne hU0, HolGerm.mk_eq_mk_iff.mp hfuneq⟩

section Geometric

variable {m : ℕ} {Z : Type u} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]

/-- ANY original actual stalk generator has the SAME finite geometric
weighted product, with no supplied factorization and no zero-set-only transition. -/
theorem exists_geometric_factorization_of_cartier_stalk_generator
    (D : EffectiveDivisor (m + 1) Z) (x : Z) (g : Z → ℂ)
    (hg : HolomorphicAt (m + 1) g x)
    (hgen : ∀ b, D.ideal.mem x b ↔ IsInSpanAt (n := m + 1) (· = g) x b) :
    ∃ S : Finset (GlobalComponents.globalComponents (n := m + 1) D.support),
      ∃ (r : GlobalComponents.globalComponents (n := m + 1) D.support →
          ComplexModel (m + 1) → ℂ)
        (hr : ∀ B, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (r B) z),
        (∀ B, HolGerm.mk (r B) (hr B) ≠ 0 ∧ Squarefree (HolGerm.mk (r B) (hr B)) ∧
          vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1)
            (cartierPrimeComponent D B).carrier x) = Ideal.span {HolGerm.mk (r B) (hr B)} ∧
          AnalyticDescendingChain.chartGerm (n := m + 1)
            (cartierPrimeComponent D B).carrier x =ᶠ[𝓝 0] {z | r B z = 0}) ∧
        (∀ B ∈ S, 0 < regularComponentOrder D D.support B) ∧
        (∃ T ∈ 𝓝 x, ∀ y ∈ T, y ∈ D.support ↔
          ∃ B ∈ S, y ∈ (cartierPrimeComponent D B).carrier) ∧
        ∃ (U : ComplexModel (m + 1) → ℂ)
          (_hU : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ U z),
          U 0 ≠ 0 ∧ (∀ᶠ z in 𝓝 0, U z ≠ 0) ∧
          (fun z => g ((complexChartAt (n := m + 1) x).val.symm
            (z + (complexChartAt (n := m + 1) x).val x))) =ᶠ[𝓝 0]
              fun z => (∏ B : {B // B ∈ S}, r B.val z ^
                regularComponentOrder D D.support B.val) * U z := by
  obtain ⟨g0, _hf0, _hF0, hgen0, _hzero0, S, r, hr, hRdata, hpos, hcover,
    U0, hU0, hU00, _hU0near, hproduct⟩ := exists_cartier_local_geometric_factorization D x
  obtain ⟨V, hV, hV0, _hVnear, htransition⟩ :=
    exists_centered_unit_transition_of_cartier_generators D x g g0 hg hgen0.self_of_nhds.1
      hgen hgen0.self_of_nhds.2
  refine ⟨S, r, hr, hRdata, hpos, hcover, (fun z => U0 z * V z),
    eventually_differentiableAt_mul hU0 hV, mul_ne_zero hU00 hV0, ?_, ?_⟩
  · have hcont : ContinuousAt (fun z => U0 z * V z) 0 :=
      hU0.self_of_nhds.continuousAt.mul hV.self_of_nhds.continuousAt
    exact hcont.eventually_ne (mul_ne_zero hU00 hV0)
  · filter_upwards [htransition, hproduct] with z hz hzp
    rw [hz, hzp, mul_assoc]

end Geometric
end SGPT.PSH

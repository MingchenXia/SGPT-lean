import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open scoped Topology ContDiff Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The same actual scalar function is holomorphic on an original open set
exactly when it is holomorphic in every original native atlas chart. -/
theorem chartHolomorphicOn_iff_native {f : M → ℂ} {U : Set M} (hU : IsOpen U) :
    (ofFixedModel n M).ChartHolomorphicOn f U ↔
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f U := by
  constructor
  · intro hf x hx
    let e := complexChartAt (n := n) x
    have hxe : x ∈ e.val.source := mem_complexChartAt_source x
    have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
      e.val.isOpen_inter_preimage_symm hU
    have hxD : e.val x ∈ e.val.target ∩ e.val.symm ⁻¹' U := by
      refine ⟨e.val.map_source hxe, ?_⟩
      simpa only [mem_preimage, e.val.left_inv hxe] using hx
    have hc : DifferentiableAt ℂ (f ∘ e.val.symm) (e.val x) :=
      (hf e).differentiableAt (hD.mem_nhds hxD)
    have hh := hc.mdifferentiableAt.comp x (mdifferentiableAt_atlas e.property hxe)
    have heq : ((f ∘ e.val.symm) ∘ e.val) =ᶠ[𝓝 x] f := by
      filter_upwards [e.val.open_source.mem_nhds hxe] with y hy
      simp only [Function.comp_apply, e.val.left_inv hy]
    exact (hh.congr_of_eventuallyEq heq.symm).mdifferentiableWithinAt
  · intro hf
    change ∀ e : ComplexChart n M, DifferentiableOn ℂ (f ∘ e.val.symm)
      (e.val.target ∩ e.val.symm ⁻¹' U)
    intro e z hz
    have hc := (hf.mdifferentiableAt (hU.mem_nhds hz.2)).comp z
      (mdifferentiableAt_atlas_symm e.property hz.1)
    exact hc.differentiableAt.differentiableWithinAt

/-- Source type `(c,I)` on connected ORIGINAL neighborhoods, preserving
the same global rational coefficient and genuine all-point stalk ideal. -/
def HasCoherentRationalAnalyticType (A : VariableComplexAtlas M) (u : M → EReal)
    (c : ℚ) (I : GermIdeal n M) : Prop :=
  0 < c ∧ I.IsCoherent ∧
    ∀ x : M, ∃ (N : ℕ) (f : Fin N → M → ℂ) (b : M → ℝ) (C : ℝ) (U : Set M),
      0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
        (∀ j, A.ChartHolomorphicOn (f j) U) ∧
        (∀ y ∈ U, ∀ g, I.mem y g ↔ IsInSpanAt (n := n) (· ∈ range f) y g) ∧
        (∀ y ∈ U, |b y| ≤ C) ∧
        EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U

/-- Exact connected original readback of the existing coherent global type;
the global ideal, coefficient, original generators and remainder are retained. -/
theorem hasCoherentRationalAnalyticType_iff_native {u : M → EReal} {c : ℚ}
    {I : GermIdeal n M} :
    (ofFixedModel n M).HasCoherentRationalAnalyticType u c I ↔
      HasAnalyticSingularitiesOfType u c I := by
  constructor
  · rintro ⟨hc, hI, hp⟩
    refine ⟨hc, hI, ?_⟩
    intro x
    obtain ⟨N, f, b, C, U, _hC, hU, _hconn, hx, hf, hgen, hb, heq⟩ := hp x
    exact ⟨U, hU, hx, N, f,
      fun j => (chartHolomorphicOn_iff_native hU).mp (hf j), hgen, b, C, hb, heq⟩
  · rintro ⟨hc, hI, hp⟩
    refine ⟨hc, hI, ?_⟩
    intro x
    obtain ⟨U, hU, hx, N, f, hf, hgen, b, C, hb, heq⟩ := hp x
    let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel n) M
    obtain ⟨V, ⟨hV, hxV, hconn⟩, hVU⟩ :=
      (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp (hU.mem_nhds hx)
    refine ⟨N, f, b, max C 0, V, le_max_right _ _, hV, hconn, hxV,
      fun j => (chartHolomorphicOn_iff_native hV).mpr ((hf j).mono hVU),
      fun y hy => hgen y (hVU hy), fun y hy => (hb y (hVU hy)).trans (le_max_left _ _),
      fun y hy => heq y (hVU hy)⟩

omit [IsComplexManifold n M] in
/-- Forget only the genuine extra global ideal and generator equations. -/
theorem HasCoherentRationalAnalyticType.intrinsic {A : VariableComplexAtlas M}
    {u : M → EReal} {c : ℚ} {I : GermIdeal n M}
    (hu : A.HasCoherentRationalAnalyticType u c I) : A.HasRationalAnalyticType u := by
  obtain ⟨hc, _hI, hp⟩ := hu
  intro x
  obtain ⟨N, f, b, C, U, hC, hU, hconn, hx, hf, _hgen, hb, heq⟩ := hp x
  exact ⟨c, N, f, b, C, U, hc, hC, hU, hconn, hx, hf, hb, heq⟩

section Neat

universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Actual source neat rational singularities: at every original point,
CHOOSE one connected bounded presentation with smooth original remainder
in every actual chart, including independently dimensional charts. -/
def HasNeatRationalAnalyticType (A : VariableComplexAtlas X) (u : X → EReal) : Prop :=
  ∀ x : X, ∃ (c : ℚ) (N : ℕ) (f : Fin N → X → ℂ) (b : X → ℝ) (C : ℝ) (U : Set X),
    0 < c ∧ 0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
      (∀ j, A.ChartHolomorphicOn (f j) U) ∧ (∀ y ∈ U, |b y| ≤ C) ∧
      (∀ i, ContDiffOn ℝ ∞ (b ∘ (A.chart i).symm)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) ∧
      EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U

/-- Smoothness of the chosen actual bounded remainder can be forgotten. -/
theorem HasNeatRationalAnalyticType.intrinsic {u : X → EReal}
    (hu : A.HasNeatRationalAnalyticType u) : A.HasRationalAnalyticType u := by
  intro x
  obtain ⟨c, N, f, b, C, U, hc, hC, hU, hconn, hx, hf, hb, _hsmooth, heq⟩ := hu x
  exact ⟨c, N, f, b, C, U, hc, hC, hU, hconn, hx, hf, hb, heq⟩

end Neat

/-- The same original coherent generators are internally nonzero somewhere
in the same neighborhood, by genuine QPSH nondegeneracy and the existing pole law. -/
theorem IsQPSH.exists_coherent_intrinsic_presentation {u : M → EReal} {c : ℚ}
    {I : GermIdeal n M} (hu : (ofFixedModel n M).IsQPSH u)
    (ht : (ofFixedModel n M).HasCoherentRationalAnalyticType u c I) (x : M) :
    ∃ (N : ℕ) (f : Fin N → M → ℂ) (b : M → ℝ) (C : ℝ) (U : Set M),
      0 < c ∧ 0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
        (∀ j, (ofFixedModel n M).ChartHolomorphicOn (f j) U) ∧
        (∀ y ∈ U, ∀ g, I.mem y g ↔ IsInSpanAt (n := n) (· ∈ range f) y g) ∧
        (∀ y ∈ U, |b y| ≤ C) ∧
        EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U ∧
        ∃ y ∈ U, ∃ j, f j y ≠ 0 := by
  obtain ⟨hc, _hI, hp⟩ := ht
  obtain ⟨N, f, b, C, U, hC, hU, hconn, hx, hf, hgen, hb, heq⟩ := hp x
  obtain ⟨θ, hθ⟩ := hu
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hθ
  obtain ⟨y, hy, hfin⟩ := hn.2 x U hU hx
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnonzero : ¬ ∀ j, f j y = 0 := by
    intro hz
    exact hfin ((heq hy).trans ((scaled_generatorLog_add_eq_bot_iff f y hcR (b y)).mpr hz))
  push Not at hnonzero
  exact ⟨N, f, b, C, U, hc, hC, hU, hconn, hx, hf, hgen, hb, heq, y, hy, hnonzero⟩

end SGPT.PSH.VariableComplexAtlas

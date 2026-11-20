import SGPT.PSH.AtlasQPSHAddition

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Genuine holomorphicity of an original scalar function in EVERY original chart. -/
def ChartHolomorphicOn (A : VariableComplexAtlas X) (f : X → ℂ) (U : Set X) : Prop :=
  ∀ i, DifferentiableOn ℂ (f ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)

/-- Lift an actual coordinate holomorphic function through genuine overlap derivatives. -/
theorem coordinate_holomorphic_chartHolomorphicOn (i : A.Index)
    {V : Set (ComplexModel (A.dimension i))} {f : ComplexModel (A.dimension i) → ℂ}
    (hf : DifferentiableOn ℂ f V) :
    A.ChartHolomorphicOn (f ∘ (A.chart i))
      ((A.chart i).source ∩ (A.chart i) ⁻¹' V) := by
  intro j
  let U := (A.chart i).source ∩ (A.chart i) ⁻¹' V
  let D := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U
  let F := (A.chart j).symm.trans (A.chart i)
  have hDF : D ⊆ F.source := fun _ hz => ⟨hz.1, hz.2.1⟩
  exact hf.comp ((A.holomorphic j i).mono hDF) (fun _ hz => hz.2.2)

/-- The source bounded-remainder rational presentation on ONE original connected open set. -/
def HasRationalAnalyticPresentationAt (A : VariableComplexAtlas X)
    (u : X → EReal) (x : X) : Prop :=
  ∃ (c : ℚ) (N : ℕ) (f : Fin N → X → ℂ) (b : X → ℝ) (C : ℝ) (U : Set X),
    0 < c ∧ 0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
      (∀ j, A.ChartHolomorphicOn (f j) U) ∧ (∀ y ∈ U, |b y| ≤ C) ∧
      EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U

/-- Original connected rational analytic presentations at every original point. -/
def HasRationalAnalyticType (A : VariableComplexAtlas X) (u : X → EReal) : Prop :=
  ∀ x, A.HasRationalAnalyticPresentationAt u x

private theorem lift_connected_presentation {u : X → EReal} (i : A.Index)
    {x : X} (hx : x ∈ (A.chart i).source)
    {c : ℚ} {N : ℕ} {f : Fin N → ComplexModel (A.dimension i) → ℂ}
    {b : ComplexModel (A.dimension i) → ℝ} {C : ℝ}
    {V : Set (ComplexModel (A.dimension i))}
    (hV : IsOpen V) (hconn : IsConnected V) (hxV : A.chart i x ∈ V)
    (hVe : V ⊆ (A.chart i).target) (hf : ∀ j, DifferentiableOn ℂ (f j) V)
    (hb : ∀ y ∈ V, |b y| ≤ C)
    (heq : EqOn (A.coordinate u i)
      (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) V) :
    let U := (A.chart i).source ∩ (A.chart i) ⁻¹' V
    IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
      (∀ j, A.ChartHolomorphicOn (f j ∘ (A.chart i)) U) ∧
      (∀ y ∈ U, |(b ∘ (A.chart i)) y| ≤ C) ∧
      EqOn u (fun y => ((c : ℝ) : EReal) *
        generatorLog (fun j => f j ∘ (A.chart i)) y + ((b ∘ (A.chart i)) y : EReal)) U := by
  let U := (A.chart i).source ∩ (A.chart i) ⁻¹' V
  have hU : IsOpen U := (A.chart i).isOpen_inter_preimage hV
  have himage : (A.chart i).symm '' V = U := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(A.chart i).map_target (hVe hz), ?_⟩
      change (A.chart i) ((A.chart i).symm z) ∈ V
      simpa only [(A.chart i).right_inv (hVe hz)] using hz
    · rintro ⟨hyS, hyV⟩
      exact ⟨(A.chart i) y, hyV, (A.chart i).left_inv hyS⟩
  have hconnected : IsConnected U := by
    rw [← himage]
    exact hconn.image _ ((A.chart i).continuousOn_symm.mono hVe)
  refine ⟨hU, hconnected, ⟨hx, hxV⟩,
    fun j => coordinate_holomorphic_chartHolomorphicOn i (hf j),
    fun y hy => hb _ hy.2, ?_⟩
  intro y hy
  have h := heq hy.2
  simpa only [coordinate, generatorLog, generatorVector, Function.comp_apply, (A.chart i).left_inv hy.1] using h

/-- An actual original presentation has native rational type in EVERY chart containing its point. -/
theorem HasRationalAnalyticPresentationAt.chartType {u : X → EReal} {x : X}
    (hu : A.HasRationalAnalyticPresentationAt u x) (i : A.Index)
    (hx : x ∈ (A.chart i).source) :
    HasAnalyticSingularityTypeAt (A.coordinate u i) (A.chart i x) := by
  obtain ⟨c, N, f, b, C, U, hc, hC, hU, _hconn, hxU, hf, hb, heq⟩ := hu
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hU
  have hxD : A.chart i x ∈ D := by
    refine ⟨(A.chart i).map_source hx, ?_⟩
    simpa only [mem_preimage, (A.chart i).left_inv hx] using hxU
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨c, N, fun j => f j ∘ (A.chart i).symm, hcR,
    ⟨D, hD, hxD, fun j => hf j i⟩, b ∘ (A.chart i).symm,
    ⟨C, hC, eventually_of_mem (hD.mem_nhds hxD) (fun y hy => hb _ hy.2)⟩, ?_⟩
  exact eventually_of_mem (hD.mem_nhds hxD) (fun y hy => heq hy.2)

/-- A genuine germ in any covering chart manufactures the original connected presentation. -/
theorem hasRationalAnalyticPresentationAt_of_chartType {u : X → EReal} {x : X}
    (i : A.Index) (hx : x ∈ (A.chart i).source)
    (hu : HasAnalyticSingularityTypeAt (A.coordinate u i) (A.chart i x)) :
    A.HasRationalAnalyticPresentationAt u x := by
  obtain ⟨c, N, f, b, C, V, hc, hC, hV, hconn, hxV, hVe, hf, hb, heq⟩ :=
    (connectedRationalPresentation_iff_germ (A.chart i).open_target
      ((A.chart i).map_source hx)).mp hu
  exact ⟨c, N, fun j => f j ∘ (A.chart i), b ∘ (A.chart i), C,
    (A.chart i).source ∩ (A.chart i) ⁻¹' V, hc, hC,
    lift_connected_presentation i hx hV hconn hxV hVe hf hb heq⟩

/-- Exact original-manifold connected analytic type and actual all-chart type agree. -/
theorem hasRationalAnalyticType_iff_chartType {u : X → EReal} :
    A.HasRationalAnalyticType u ↔ A.HasRationalAnalyticChartType u := by
  constructor
  · intro hu i z hz
    have h := (hu ((A.chart i).symm z)).chartType i ((A.chart i).map_target hz)
    simpa only [(A.chart i).right_inv hz] using h
  · intro hu x
    obtain ⟨i, hx⟩ := A.cover x
    exact hasRationalAnalyticPresentationAt_of_chartType i hx
      (hu i _ ((A.chart i).map_source hx))

/-- Original global QPSH internally gives a proper common zero locus in the SAME presentation. -/
theorem IsQPSH.exists_intrinsic_analytic_presentation {u : X → EReal}
    (hu : A.IsQPSH u) (han : A.HasRationalAnalyticType u) (x : X) :
    ∃ (c : ℚ) (N : ℕ) (f : Fin N → X → ℂ) (b : X → ℝ) (C : ℝ) (U : Set X),
      0 < c ∧ 0 ≤ C ∧ IsOpen U ∧ IsConnected U ∧ x ∈ U ∧
        (∀ j, A.ChartHolomorphicOn (f j) U) ∧ (∀ y ∈ U, |b y| ≤ C) ∧
        EqOn u (fun y => ((c : ℝ) : EReal) * generatorLog f y + (b y : EReal)) U ∧
        ∃ y ∈ U, ∃ j, f j y ≠ 0 := by
  obtain ⟨i, hx⟩ := A.cover x
  obtain ⟨c, N, f, b, C, V, hc, hC, hV, hconn, hxV, hVe, hf, hb, heq,
      y, hy, j, hnonzero⟩ :=
    hu.exists_connected_analytic_presentation (hasRationalAnalyticType_iff_chartType.mp han)
      i ((A.chart i).map_source hx)
  obtain ⟨hU, hcU, hxU, hfU, hbU, heqU⟩ :=
    lift_connected_presentation i hx hV hconn hxV hVe hf hb heq
  refine ⟨c, N, fun j => f j ∘ (A.chart i), b ∘ (A.chart i), C,
    (A.chart i).source ∩ (A.chart i) ⁻¹' V, hc, hC, hU, hcU, hxU, hfU, hbU, heqU,
    (A.chart i).symm y, ⟨(A.chart i).map_target (hVe hy), ?_⟩, j, ?_⟩
  · simpa only [mem_preimage, (A.chart i).right_inv (hVe hy)] using hy
  · simpa only [Function.comp_apply, (A.chart i).right_inv (hVe hy)] using hnonzero

/-- Thin intrinsic readback of the already proved rational scaling producer. -/
theorem HasRationalAnalyticType.pos_rat_smul {u : X → EReal}
    (hu : A.HasRationalAnalyticType u) {r : ℚ} (hr : 0 < r) :
    A.HasRationalAnalyticType (fun x => ((r : ℝ) : EReal) * u x) :=
  hasRationalAnalyticType_iff_chartType.mpr
    ((hasRationalAnalyticType_iff_chartType.mp hu).pos_rat_smul hr)

/-- Thin intrinsic readback of the genuine synchronized rational addition producer. -/
theorem HasRationalAnalyticType.add {u w : X → EReal}
    (hu : A.HasRationalAnalyticType u) (hw : A.HasRationalAnalyticType w) :
    A.HasRationalAnalyticType (fun x => u x + w x) :=
  hasRationalAnalyticType_iff_chartType.mpr
    ((hasRationalAnalyticType_iff_chartType.mp hu).add
      (hasRationalAnalyticType_iff_chartType.mp hw))

/-- Thin intrinsic readback of the existing maximum producer, including every pole branch. -/
theorem HasRationalAnalyticType.max {u w : X → EReal}
    (hu : A.HasRationalAnalyticType u) (hw : A.HasRationalAnalyticType w) :
    A.HasRationalAnalyticType (fun x => max (u x) (w x)) :=
  hasRationalAnalyticType_iff_chartType.mpr
    ((hasRationalAnalyticType_iff_chartType.mp hu).max
      (hasRationalAnalyticType_iff_chartType.mp hw))

/-- The original global QPSH rational scaling and intrinsic analytic predicates hold together. -/
theorem IsQPSH.pos_rat_smul_intrinsic {u : X → EReal} (hu : A.IsQPSH u)
    (han : A.HasRationalAnalyticType u) {r : ℚ} (hr : 0 < r) :
    A.IsQPSH (fun x => ((r : ℝ) : EReal) * u x) ∧
      A.HasRationalAnalyticType (fun x => ((r : ℝ) : EReal) * u x) := by
  obtain ⟨hQ, hA⟩ := hu.pos_rat_smul_analytic
    (hasRationalAnalyticType_iff_chartType.mp han) hr
  exact ⟨hQ, hasRationalAnalyticType_iff_chartType.mpr hA⟩

/-- Independently original global QPSH inputs give their SAME intrinsic analytic sum. -/
theorem IsQPSH.add_intrinsic {u w : X → EReal} (hu : A.IsQPSH u) (hw : A.IsQPSH w)
    (hanU : A.HasRationalAnalyticType u) (hanW : A.HasRationalAnalyticType w) :
    A.IsQPSH (fun x => u x + w x) ∧ A.HasRationalAnalyticType (fun x => u x + w x) := by
  obtain ⟨hQ, hA⟩ := hu.add_analytic hw (hasRationalAnalyticType_iff_chartType.mp hanU)
    (hasRationalAnalyticType_iff_chartType.mp hanW)
  exact ⟨hQ, hasRationalAnalyticType_iff_chartType.mpr hA⟩

end SGPT.PSH.VariableComplexAtlas

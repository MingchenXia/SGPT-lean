import SGPT.Toric.BigToric2Orbits
import SGPT.Toric.TropicalProductVolume
import SGPT.Foundations.Analysis.Pending.ChartWeightedL2Transfer
import SGPT.Foundations.Analysis.Pending.MultiplierIdeals
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBasics
import SGPT.PSH.GlobalQPSH

/-!
# Sections of `L ⊗ 𝓘(φ)` on a smooth projective toric manifold

Source `chapter_toric_ample.tex`, statement and proof of `thm:Yao`, and
`chapter_toric_big.tex` (the same objects for `L = O(D)`): for a toric potential `φ`, the
space `H⁰(X, L ⊗ 𝓘(φ))` of holomorphic sections of `L` whose local coefficients lie in the
multiplier ideal sheaf `𝓘(φ)`.

## The model

`X = PolytopeToricVariety γ hs` with its vertex charts `U_v ≅ ℂ^n` and `L = O(D)` with the
frames `e_v = χ^{m_v} s_D` on `U_v` (see `BigToric2Sections`): a section `g = s / s_D ∈
H⁰(X, O(D))` is `g = f_v(z_v) χ^{m_v}` on the torus, with `f_v` entire, and `f_v ∘ z_v` is
the coefficient of `s` in the frame `e_v` on `U_v`.  The section `s` is a section of the
subsheaf `O(D) ⊗ 𝓘(cφ)` iff at every point `x ∈ U_v` the germ of its coefficient lies in the
stalk `𝓘(cφ)_x` of the existing multiplier ideal sheaf
`SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.multiplierIdeal c φ`
(holomorphic germs `g` with `|g|² e^{-cφ}` locally integrable, tested in the preferred chart;
the source works with `c = 1`, and with `c = k` for `L^k ⊗ 𝓘(kφ)`).  Since the frames differ
by nowhere vanishing holomorphic functions and the coefficient is unique, this does not
depend on choices.

## Main definitions

* `IsToricMultiplierCoefficient D c φ g`: every coefficient of `g` lies in `𝓘(cφ)` on its
  chart;
* `toricMultiplierSections D hc hφ`: the complex vector space `H⁰(X, O(D) ⊗ 𝓘(cφ))` (for a
  quasi-psh `φ` and `c > 0`), a subspace of `toricSections D = H⁰(X, O(D))`.

## Main results

* `mem_multiplierIdeal_vertexChart_iff`: the stalk condition at `x ∈ U_v` can be tested in the
  vertex chart `U_v` itself (chart independence of local `L²` integrability);
* `mem_toricMultiplierSections_iff`: `g ∈ H⁰(X, O(D) ⊗ 𝓘(cφ))` iff `g` is a section and its
  vertex coefficients are locally `e^{-cφ}`-square integrable at every point of `ℂ^n`;
* `volume_compl_complexTorus`: the complement of the torus in a vertex chart is Lebesgue null;
* `BigToricMetric.chartFunction_vertexChart_embedding`, `BigToricMetric.multiplierDensity_toricMonomial`:
  on the torus, `|χ^{m - k m_v}|² e^{-kφ} = exp(⟨m, ν⟩ - k F_φ(ν) + k ψ_v)`, `ν = Trop`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology ContDiff BigOperators Manifold ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### Vertex charts as atlas charts -/

theorem vertexChart_val (v : latticePolytopeVertices γ) :
    (polytopeToricVertexChart γ hs v).val = originalPolytopeNativeModelChart γ hs v := rfl

theorem vertexChart_target (v : latticePolytopeVertices γ) :
    (originalPolytopeNativeModelChart γ hs v).target = univ :=
  originalPolytopeNativeModelChart_target γ hs v

theorem vertexChart_right_inv (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    originalPolytopeNativeModelChart γ hs v ((originalPolytopeNativeModelChart γ hs v).symm z) = z :=
  (originalPolytopeNativeModelChart γ hs v).right_inv (by rw [vertexChart_target]; exact mem_univ z)

theorem vertexChart_symm_mem_source (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    (originalPolytopeNativeModelChart γ hs v).symm z ∈
      (originalPolytopeNativeModelChart γ hs v).source :=
  (originalPolytopeNativeModelChart γ hs v).map_target (by rw [vertexChart_target]; exact mem_univ z)

theorem embedding_mem_vertexChart_source (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    polytopeToricEmbedding γ hs a ∈ (originalPolytopeNativeModelChart γ hs v).source := by
  rw [originalPolytopeNativeModelChart_source]
  exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs v a

/-- Every torus point of a vertex chart is the vertex coordinate of a torus point of `X`. -/
theorem exists_embedding_eq_of_mem_complexTorus (v : latticePolytopeVertices γ)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    ∃ a, originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) = z := by
  obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs v hz
  exact ⟨a, by rw [ha, vertexChart_right_inv]⟩

/-- Quasi-psh functions have quasi-psh chart functions in every chart. -/
theorem IsQPSH.chartFunction {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (e : ComplexChart n (PolytopeToricVariety γ hs)) :
    QuasiPlurisubharmonicOn (chartFunction φ e) e.val.target := by
  obtain ⟨θ, hθ⟩ := hφ
  exact hθ.chart_quasiPSH e

/-! ### The multiplier ideal stalks in a vertex chart -/

/-- The stalk condition `F ∘ z_v ∈ 𝓘(cφ)_x` at a point `x ∈ U_v` is local `L²` integrability of
`|F|² e^{-cφ}` near `z_v(x)` in the vertex chart itself. -/
theorem mem_multiplierIdeal_vertexChart_iff {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) {c : ℝ} (hc : c ≠ 0)
    (v : latticePolytopeVertices γ) {x : PolytopeToricVariety γ hs}
    (hx : x ∈ (polytopeToricVertexChart γ hs v).val.source) (F : ComplexModel n → ℂ) :
    (multiplierIdeal (n := n) c φ).mem x (fun p => F ((polytopeToricVertexChart γ hs v).val p)) ↔
      MultiplierIntegrableAt (chartFunction φ (polytopeToricVertexChart γ hs v)) c F
        ((polytopeToricVertexChart γ hs v).val x) volume := by
  set e := polytopeToricVertexChart γ hs v
  set f := complexChartAt (n := n) x
  have hFeq : (fun z => F (e.val (e.val.symm z))) = F := by
    funext z
    exact congrArg F (vertexChart_right_inv v z)
  constructor
  · rintro ⟨-, hint⟩
    have husc : UpperSemicontinuousOn (chartFunction φ e)
        (Pending.ChartWeightedL2.overlapDomain e f) :=
      ((IsQPSH.chartFunction hφ e).upperSemicontinuousOn).mono fun z hz => hz.1
    have h := Pending.ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      (g := fun p => F (e.val p)) e f hx (mem_complexChartAt_source x) husc hc hint
    rwa [hFeq] at h
  · intro hint
    obtain ⟨hcpos, U, hU, hxU, hdiff, hL2⟩ := hint
    refine ⟨?_, ?_⟩
    · -- holomorphy of `F ∘ z_v` near `x`
      have hcont : ContinuousAt e.val x := e.val.continuousAt hx
      have hnhds : e.val.source ∩ e.val ⁻¹' U ∈ 𝓝 x :=
        inter_mem (e.val.open_source.mem_nhds hx) (hcont.preimage_mem_nhds (hU.mem_nhds hxU))
      filter_upwards [hnhds] with y hy
      have hF : DifferentiableAt ℂ F (e.val y) :=
        (hdiff _ hy.2).differentiableAt (hU.mem_nhds hy.2)
      have hchart : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.val y :=
        mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.property hy.1
      exact hF.mdifferentiableAt.comp y hchart
    · have husc : UpperSemicontinuousOn (chartFunction φ f)
          (Pending.ChartWeightedL2.overlapDomain f e) :=
        ((IsQPSH.chartFunction hφ f).upperSemicontinuousOn).mono fun z hz => hz.1
      have hint' : MultiplierIntegrableAt (chartFunction φ e) c
          (fun z => F (e.val (e.val.symm z))) (e.val x) volume := by
        rw [hFeq]; exact ⟨hcpos, U, hU, hxU, hdiff, hL2⟩
      exact Pending.ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
        (g := fun p => F (e.val p)) f e (mem_complexChartAt_source x) hx husc hc hint'

/-! ### Sections of `O(D) ⊗ 𝓘(cφ)` -/

variable (D : ToricDivisor γ hs)

/-- Source `thm:Yao` (the space `H⁰(X, L ⊗ 𝓘(φ))`): every local coefficient `f_v ∘ z_v` of
the section `g` of `O(D)` in the frame `e_v` lies in the multiplier ideal `𝓘(cφ)` at every
point of `U_v`. -/
def IsToricMultiplierCoefficient (c : ℝ) (φ : PolytopeToricVariety γ hs → EReal)
    (g : (Fin n → ℂˣ) → ℂ) : Prop :=
  ∀ (v : latticePolytopeVertices γ) (f : ComplexModel n → ℂ), Continuous f →
    (∀ a, g a = f (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
      latticeCharacter (toricCartierDatum D v) a) →
    ∀ x ∈ (originalPolytopeNativeModelChart γ hs v).source,
      (multiplierIdeal (n := n) c φ).mem x (fun p => f (originalPolytopeNativeModelChart γ hs v p))

variable {D}

/-- The coefficient condition in vertex coordinates. -/
theorem isToricMultiplierCoefficient_iff {c : ℝ} (hc : c ≠ 0)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) (g : (Fin n → ℂˣ) → ℂ) :
    IsToricMultiplierCoefficient D c φ g ↔
      ∀ (v : latticePolytopeVertices γ) (f : ComplexModel n → ℂ), Continuous f →
        (∀ a, g a = f (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
          latticeCharacter (toricCartierDatum D v) a) →
        ∀ z : ComplexModel n,
          MultiplierIntegrableAt (chartFunction φ (polytopeToricVertexChart γ hs v)) c f z volume := by
  constructor
  · intro h v f hf hgf z
    have hx := vertexChart_symm_mem_source (hs := hs) v z
    have := (mem_multiplierIdeal_vertexChart_iff hφ hc v hx f).mp (h v f hf hgf _ hx)
    rwa [show (polytopeToricVertexChart γ hs v).val
      ((originalPolytopeNativeModelChart γ hs v).symm z) = z from vertexChart_right_inv v z] at this
  · intro h v f hf hgf x hx
    exact (mem_multiplierIdeal_vertexChart_iff hφ hc v hx f).mpr (h v f hf hgf _)

/-- The coefficient of the zero section is zero. -/
private theorem coeff_eq_zero_of_zero {v : latticePolytopeVertices γ} {f : ComplexModel n → ℂ}
    (hf : Continuous f)
    (hgf : ∀ a, (0 : (Fin n → ℂˣ) → ℂ) a =
      f (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
        latticeCharacter (toricCartierDatum D v) a) : f = 0 :=
  toricSectionCoeff_unique (D := D) v hf continuous_const hgf (fun a => by simp)

variable (D)

/-- Source `thm:Yao`: the space `H⁰(X, O(D) ⊗ 𝓘(cφ))` of holomorphic sections of `O(D)` whose
local coefficients lie in the multiplier ideal sheaf `𝓘(cφ)`, for a quasi-psh `φ` and
`c > 0`; it is a subspace of `H⁰(X, O(D)) = toricSections D`.  The source's
`H⁰(X, L ⊗ 𝓘(φ))` is `c = 1`, and `H⁰(X, L^k ⊗ 𝓘(kφ))` is `D ↦ k • D`, `c = k`. -/
def toricMultiplierSections {c : ℝ} (hc : 0 < c) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) :
    Submodule ℂ ((Fin n → ℂˣ) → ℂ) where
  carrier := {g | g ∈ toricSections D ∧ IsToricMultiplierCoefficient D c φ g}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_⟩
    rw [isToricMultiplierCoefficient_iff hc.ne' hφ]
    intro v f hf hgf z
    rw [coeff_eq_zero_of_zero hf hgf]
    refine ⟨hc, univ, isOpen_univ, mem_univ z, differentiableOn_const 0, ?_⟩
    have h0 : multiplierDensity (chartFunction φ (polytopeToricVertexChart γ hs v)) c
        (0 : ComplexModel n → ℂ) = 0 := by
      funext y; exact multiplierDensity_zero _ _ y
    refine ⟨?_, ?_⟩
    · rw [h0]; exact aemeasurable_const
    · rw [h0]; simp
  add_mem' := by
    rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
    refine ⟨Submodule.add_mem _ hg₁ hg₂, ?_⟩
    rw [isToricMultiplierCoefficient_iff hc.ne' hφ] at h₁ h₂ ⊢
    intro v f hf hgf z
    obtain ⟨f₁, hf₁, hgf₁⟩ := hg₁ v
    obtain ⟨f₂, hf₂, hgf₂⟩ := hg₂ v
    have hsum : f = fun w => f₁ w + f₂ w := by
      apply toricSectionCoeff_unique (D := D) v hf (hf₁.continuous.add hf₂.continuous) hgf
      intro a
      simp only [Pi.add_apply, hgf₁ a, hgf₂ a, add_mul]
    rw [hsum]
    exact Pending.multiplierIntegrableAt_add
      (IsQPSH.chartFunction hφ _ z (by rw [vertexChart_val, vertexChart_target]; exact mem_univ z))
      (h₁ v f₁ hf₁.continuous hgf₁ z) (h₂ v f₂ hf₂.continuous hgf₂ z)
  smul_mem' := by
    rintro r g ⟨hg, h⟩
    refine ⟨Submodule.smul_mem _ r hg, ?_⟩
    rw [isToricMultiplierCoefficient_iff hc.ne' hφ] at h ⊢
    intro v f hf hgf z
    obtain ⟨f₁, hf₁, hgf₁⟩ := hg v
    have hsc : f = fun w => r * f₁ w := by
      apply toricSectionCoeff_unique (D := D) v hf (continuous_const.mul hf₁.continuous) hgf
      intro a
      change r * g a = r * f₁ _ * _
      rw [hgf₁ a, mul_assoc]
    rw [hsc]
    exact Pending.multiplierIntegrableAt_holomorphic_mul
      (IsQPSH.chartFunction hφ _ z (by rw [vertexChart_val, vertexChart_target]; exact mem_univ z))
      (h v f₁ hf₁.continuous hgf₁ z) analyticAt_const

variable {D}

theorem mem_toricMultiplierSections {c : ℝ} (hc : 0 < c) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) (g : (Fin n → ℂˣ) → ℂ) :
    g ∈ toricMultiplierSections D hc hφ ↔
      g ∈ toricSections D ∧ IsToricMultiplierCoefficient D c φ g := Iff.rfl

/-- `g ∈ H⁰(X, O(D) ⊗ 𝓘(cφ))` iff `g ∈ H⁰(X, O(D))` and its vertex coefficients are locally
`e^{-cφ}`-square integrable at every point of every vertex chart. -/
theorem mem_toricMultiplierSections_iff {c : ℝ} (hc : 0 < c)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) (g : (Fin n → ℂˣ) → ℂ) :
    g ∈ toricMultiplierSections D hc hφ ↔
      g ∈ toricSections D ∧
        ∀ (v : latticePolytopeVertices γ) (f : ComplexModel n → ℂ), Continuous f →
          (∀ a, g a = f (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
            latticeCharacter (toricCartierDatum D v) a) →
          ∀ z : ComplexModel n,
            MultiplierIntegrableAt (chartFunction φ (polytopeToricVertexChart γ hs v)) c f z volume := by
  rw [mem_toricMultiplierSections, isToricMultiplierCoefficient_iff hc.ne' hφ]

/-- The space depends only on `D`, `c` and `φ`. -/
theorem toricMultiplierSections_congr {D' : ToricDivisor γ hs} (hD : D = D') {c c' : ℝ}
    (hcc : c = c') (hc : 0 < c) (hc' : 0 < c') {φ : PolytopeToricVariety γ hs → EReal}
    (hφ hφ' : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) :
    toricMultiplierSections D hc hφ = toricMultiplierSections D' hc' hφ' := by
  subst hD; subst hcc; rfl

/-- `H⁰(X, O(D) ⊗ 𝓘(cφ)) ⊆ H⁰(X, O(D))`. -/
theorem toricMultiplierSections_le {c : ℝ} (hc : 0 < c) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) :
    toricMultiplierSections D hc hφ ≤ toricSections D := fun _ hg => hg.1

/-- A character is a section of `O(D)` only for lattice points of `P_D`. -/
theorem mem_toricLatticePoints_of_latticeCharacter_mem {m : Fin n → ℤ}
    (hm : (fun a => (latticeCharacter m a : ℂ)) ∈ toricSections D) : m ∈ toricLatticePoints D := by
  rw [toricSections_eq_span] at hm
  have hrange : (Set.range fun m' : toricLatticePoints D =>
      fun a => (latticeCharacter m'.val a : ℂ)) =
      (fun m' : Fin n → ℤ => fun a : Fin n → ℂˣ => (latticeCharacter m' a : ℂ)) ''
        toricLatticePoints D := by
    ext g; simp
  rw [hrange] at hm
  by_contra hmS
  exact (linearIndependent_latticeCharacter (n := n)).notMem_span_image hmS hm

/-! ### The complement of the torus is null -/

/-- The coordinate hyperplanes of `ℂ^n` are Lebesgue null. -/
theorem volume_compl_complexTorus : volume (complexTorus n)ᶜ = 0 := by
  have hcompl : (complexTorus n)ᶜ = ⋃ j : Fin n, {z : ComplexModel n | z j = 0} := by
    ext z; simp [complexTorus]
  rw [hcompl]
  apply measure_iUnion_null
  intro j
  have hmp := volume_preserving_complexModel_coordinates n
  have hpre : {z : ComplexModel n | z j = 0} =
      (fun z : ComplexModel n => (fun i => z i)) ⁻¹' {x : Fin n → ℂ | x j = 0} := rfl
  rw [hpre, hmp.measure_preimage (measurableSet_eq_fun (measurable_pi_apply j)
    measurable_const).nullMeasurableSet]
  exact Measure.pi_hyperplane _ j 0

theorem ae_mem_complexTorus : ∀ᵐ z : ComplexModel n, z ∈ complexTorus n :=
  measure_eq_zero_iff_ae_notMem.mp volume_compl_complexTorus |>.mono fun _ hz => by
    simpa using hz

/-! ### The weighted density of a character on the torus -/

namespace BigToricMetric

variable (h : BigToricMetric D)

/-- Toric `θ`-psh functions are quasi-psh. -/
theorem isQPSH_of_mem {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH u :=
  ⟨h.atlasForm, hu.1⟩

/-- On the torus, the vertex-chart function of a toric potential is `F_φ - F_θ` at `Trop`. -/
theorem chartFunction_vertexChart_embedding {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    chartFunction u (polytopeToricVertexChart γ hs v)
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) =
      ((h.realProfile u (unitTorusLog a) - h.potential (unitTorusLog a) : ℝ) : EReal) := by
  change u ((originalPolytopeNativeModelChart γ hs v).symm
    (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a))) = _
  rw [(originalPolytopeNativeModelChart γ hs v).left_inv (embedding_mem_vertexChart_source v a),
    hu.2.embedding_eq γ hs a]
  have hx := congrFun (h.realProfile_mem hu).2 (unitTorusLog a)
  rw [profile] at hx
  rw [EReal.coe_sub, ← hx, EReal.add_sub_cancel_right]

/-- `|z_j(v)|² = exp ⟨b_j(v), Trop⟩` on the torus. -/
theorem norm_sq_vertexChart_embedding (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ)
    (i : Fin n) :
    ‖originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) i‖ ^ 2 =
      Real.exp (latticeFunctional (originalPolytopeNativeBasis γ hs v i) (unitTorusLog a)) := by
  rw [vertexChart_embedding hs v, modelPoint_apply]
  have hpos : 0 < ‖(latticeCharacter (originalPolytopeNativeBasis γ hs v i) a : ℂ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2
  rw [← Real.exp_log hpos, latticeCharacter_log_norm_sq]
  rfl

/-- `|χ^m|² = exp ⟨m, Trop⟩`. -/
theorem norm_sq_latticeCharacter (m : Fin n → ℤ) (a : Fin n → ℂˣ) :
    ‖(latticeCharacter m a : ℂ)‖ ^ 2 = Real.exp (latticeFunctional m (unitTorusLog a)) := by
  have hpos : 0 < ‖(latticeCharacter m a : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) 2
  rw [← Real.exp_log hpos, latticeCharacter_log_norm_sq]
  rfl

/-- Source proof of `thm:Yao`: on the torus, in the vertex chart at `v`, the weighted density
of the coefficient `χ^{m - k m_v}` of `χ^m ∈ H⁰(X, O(kD))` is
`|χ^{m - k m_v}|² e^{-kφ} = exp(⟨m, ν⟩ - k F_φ(ν) + k ψ_v)` with `ν = Trop`. -/
theorem multiplierDensity_toricMonomial {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) {k : ℕ} {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints ((k : ℤ) • D))
    (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    multiplierDensity (chartFunction u (polytopeToricVertexChart γ hs v)) k
        (toricMonomial ((k : ℤ) • D) v m)
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) =
      ENNReal.ofReal (Real.exp (latticeFunctional m (unitTorusLog a) -
        k * h.realProfile u (unitTorusLog a) +
        k * h.weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)))) := by
  set z := originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)
  set ν := unitTorusLog a
  have hchar := latticeCharacter_eq_toricMonomial (hs := hs) ((k : ℤ) • D) hm v a
  have hne : (latticeCharacter (toricCartierDatum ((k : ℤ) • D) v) a : ℂ) ≠ 0 := Units.ne_zero _
  have hmono : ‖toricMonomial ((k : ℤ) • D) v m z‖ ^ 2 =
      Real.exp (latticeFunctional m ν - k * latticeFunctional (toricCartierDatum D v) ν) := by
    have h1 : toricMonomial ((k : ℤ) • D) v m z =
        (latticeCharacter m a : ℂ) / latticeCharacter (toricCartierDatum ((k : ℤ) • D) v) a := by
      rw [hchar, mul_div_cancel_right₀ _ hne]
    rw [h1, norm_div, div_pow, norm_sq_latticeCharacter, norm_sq_latticeCharacter,
      ← Real.exp_sub, toricCartierDatum_smul]
    congr 1
    have : latticeFunctional ((k : ℤ) • toricCartierDatum D v) ν =
        k * latticeFunctional (toricCartierDatum D v) ν := by
      simp only [latticeFunctional_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
        Int.cast_natCast, Finset.mul_sum, mul_assoc]
    rw [this]
  have hw := h.weight_chart_embedding v a
  unfold multiplierDensity
  rw [h.chartFunction_vertexChart_embedding hu v a, multiplierWeight_coe, hmono,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [hw]
  ring

end BigToricMetric

end SGPT.Toric

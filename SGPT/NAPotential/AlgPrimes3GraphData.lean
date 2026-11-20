import SGPT.NAPotential.AlgPrimes3Graph
import SGPT.GAGA.AlgPrimes3Immersion
import SGPT.Foundations.Analysis.Pending.ClosureDifferenceAnalytic

/-!
# Graph data: the graph model from an analytic set containing the graph


`SGPT.NAPotential.AlgPrimes3.GraphModel` asks for the graph closure `Γ` itself, smooth along the
graph and at the points of the local model.  This file derives these properties from data closer
to the algebraic construction (`GraphData`):

* an analytic set `Γ₀ ⊆ M` (for the intended model, the zero set in `X(ℂ) × ℙ^s(ℂ)` of the
  bihomogeneous relations of the graph map) containing the graph and meeting `pr⁻¹(X(ℂ) \ B)`
  only along the graph;
* a holomorphic immersion `ι : N → M` into `Γ₀`, open onto `Γ₀` (every neighbourhood of a point of
  `N` is mapped onto a neighbourhood in `Γ₀`), whose points over `B` have empty interior in `N`.

`GraphData.toGraphModel` takes `Γ = closure (Γ₀ \ pr⁻¹ B)`, analytic by
`ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff`; it is smooth of dimension
`dim X` along the graph (`SGPT.GAGA.AlgPrimes3.regularAtDim_of_section`) and at the points of
`ι(N)` (`SGPT.GAGA.AlgPrimes3.regularAtDim_of_immersion`).  Hence `HighCodimGraphData` (graph
data for every prime divisor centred in codimension `≥ 2`) implies `AlgebraicPrimesRealized`
(`algebraicPrimesRealized_of_highCodimGraphData`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3

open Set Filter
open scoped Topology Manifold ContDiff
open AlgebraicGeometry CategoryTheory
open SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.NAPotential.Berkovich SGPT.NAPotential.FSPos
open SGPT.GAGA.H0S SGPT.NAPotential.TowerAlg SGPT.NAPotential.AlgPrimes
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder
open FirstPass.BlowupSequences BlowupTowers AnalyticModificationLocalDiscrepancy
open HolomorphicIdealSheaves

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance algPrimes3DataPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPrimes3DataPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algPrimes3DataPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [IsIntegral X]

variable (f m) in
/-- **Graph data of an algebraic prime divisor `D` over `X`**: an analytic set `Γ₀` containing
the graph of a holomorphic section `φ` of `pr : M → X(ℂ)` over `X(ℂ) \ B` and meeting
`pr⁻¹(X(ℂ) \ B)` only along it; a holomorphic immersion `ι : N → M` from a complex manifold of
dimension `dim X` into `Γ₀`, open onto `Γ₀`, with `ι⁻¹ pr⁻¹ B` of empty interior; the analytic set
`Δ` and the order comparison at `n₀` as in `GraphModel`. -/
structure GraphData (D : PrimeDivisorOver X) where
  /-- The dimension of the ambient manifold. -/
  K : ℕ
  /-- The ambient compact complex manifold. -/
  M : CMfd.{0} K
  [compactSpace : CompactSpace M]
  /-- The projection to `X(ℂ)`. -/
  pr : M → SchemeComplexPoint f
  contMDiff_pr : ContMDiff 𝓘(ℂ, ComplexModel K) 𝓘(ℂ, ComplexModel (m + 1)) ∞ pr
  /-- An analytic set containing the graph. -/
  Γ₀ : Set M
  isAnalytic_Γ₀ : IsComplexAnalyticSubset (n := K) Γ₀
  /-- The locus over which the graph map is not defined. -/
  B : Set (SchemeComplexPoint f)
  isClosed_B : IsClosed B
  isAnalytic_B : IsComplexAnalyticSubset (n := m + 1) B
  interior_B : interior B = ∅
  /-- The graph map. -/
  φ : SchemeComplexPoint f → M
  contMDiffOn_φ : ContMDiffOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ∞ φ Bᶜ
  pr_φ : ∀ x ∉ B, pr (φ x) = x
  φ_mem : ∀ x ∉ B, φ x ∈ Γ₀
  eq_φ : ∀ z ∈ Γ₀, pr z ∉ B → φ (pr z) = z
  /-- The local smooth model. -/
  N : CMfd.{0} (m + 1)
  ι : N → M
  contMDiff_ι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ∞ ι
  ι_mem : ∀ p, ι p ∈ Γ₀
  injective_mfderiv_ι :
    ∀ p, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel K) ι p)
  ι_local : ∀ p, ∀ U ∈ 𝓝 p, ∃ V ∈ 𝓝 (ι p), Γ₀ ∩ V ⊆ ι '' U
  interior_ι_B : interior (ι ⁻¹' (pr ⁻¹' B)) = ∅
  /-- The point of `N` over the centre of `ord_D`. -/
  n₀ : N
  /-- The analytic set of the centre of `ord_D` on the model. -/
  Δ : Set M
  isAnalytic_Δ : IsComplexAnalyticSubset (n := K) Δ
  flattening : DivisorFlattening (m := m) (ι ⁻¹' Δ) n₀
  ord_eq : ∀ g : X.presheaf.stalk (schemeComplexPointImage f (pr (ι n₀))), g ≠ 0 →
    (D.ord ((BerkovichPoint.specializationMap
      (ordVal_support_specializes f D (schemeComplexPointImage f (pr (ι n₀))))).hom g) : ℤ) =
      ((functionNormalOrder flattening (stalkRep m (pr (ι n₀)) g ∘ (pr ∘ ι))
        (HolomorphicIdealSheaves.HolomorphicAt.comp_contMDiff (f := pr ∘ ι) (y := n₀)
          (stalkRep_holomorphicAt (pr (ι n₀)) g)
          (Eventually.of_forall fun _ => (contMDiff_pr.comp contMDiff_ι).contMDiffAt))).toNat : ℤ)

attribute [instance] GraphData.compactSpace

namespace GraphData

variable {D : PrimeDivisorOver X} (G : GraphData f m D)

/-- The graph closure `Γ = closure (Γ₀ \ pr⁻¹ B)`. -/
def Γ : Set G.M := closure (G.Γ₀ \ G.pr ⁻¹' G.B)

theorem Γ_subset : G.Γ ⊆ G.Γ₀ :=
  closure_minimal sdiff_subset G.isAnalytic_Γ₀.isClosed

theorem isAnalytic_Γ : IsComplexAnalyticSubset (n := G.K) G.Γ :=
  ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff G.isAnalytic_Γ₀
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage G.contMDiff_pr G.isAnalytic_B)

theorem φ_mem_Γ {x : SchemeComplexPoint f} (hx : x ∉ G.B) : G.φ x ∈ G.Γ :=
  subset_closure ⟨G.φ_mem x hx, by
    change G.pr (G.φ x) ∉ G.B
    rw [G.pr_φ x hx]
    exact hx⟩

theorem eq_φ_of_mem_Γ {z : G.M} (hz : z ∈ G.Γ) (hzB : G.pr z ∉ G.B) : G.φ (G.pr z) = z :=
  G.eq_φ z (G.Γ_subset hz) hzB

theorem Γ_subset_closure : G.Γ ⊆ closure (G.φ '' G.Bᶜ) := by
  refine closure_mono ?_
  rintro z ⟨hz, hzB⟩
  exact ⟨G.pr z, hzB, G.eq_φ z hz hzB⟩

theorem ι_mem_Γ (p : G.N) : G.ι p ∈ G.Γ := by
  rw [Γ, mem_closure_iff_nhds]
  intro V hV
  have hU : G.ι ⁻¹' V ∈ 𝓝 p := G.contMDiff_ι.continuous.continuousAt.preimage_mem_nhds hV
  by_contra hne
  have hsub : G.ι ⁻¹' V ⊆ G.ι ⁻¹' (G.pr ⁻¹' G.B) := by
    intro q hq
    by_contra hqB
    exact hne ⟨G.ι q, hq, G.ι_mem q, hqB⟩
  have hp : p ∈ interior (G.ι ⁻¹' (G.pr ⁻¹' G.B)) :=
    interior_mono hsub (mem_interior_iff_mem_nhds.mpr hU)
  rw [G.interior_ι_B] at hp
  exact hp

theorem regularAtDim_φ {x : SchemeComplexPoint f} (hx : x ∉ G.B) :
    RegularAtDim (n := G.K) G.Γ (G.φ x) (m + 1) :=
  SGPT.GAGA.AlgPrimes3.regularAtDim_of_section G.contMDiff_pr G.isClosed_B.isOpen_compl
    G.contMDiffOn_φ G.pr_φ (fun _ hx => G.φ_mem_Γ hx) (fun _ hz hzB => G.eq_φ_of_mem_Γ hz hzB) hx

theorem regularAtDim_ι (p : G.N) : RegularAtDim (n := G.K) G.Γ (G.ι p) (m + 1) := by
  refine SGPT.GAGA.AlgPrimes3.regularAtDim_of_immersion
    (Eventually.of_forall fun q => G.contMDiff_ι.contMDiffAt) (G.injective_mfderiv_ι p)
    (Eventually.of_forall fun q => G.ι_mem_Γ q) fun U hU => ?_
  obtain ⟨V, hV, hVU⟩ := G.ι_local p U hU
  exact ⟨V, hV, fun z hz => hVU ⟨G.Γ_subset hz.1, hz.2⟩⟩

/-- **Graph data give a graph model**, with `Γ = closure (Γ₀ \ pr⁻¹ B)`. -/
def toGraphModel : GraphModel f m D where
  K := G.K
  M := G.M
  pr := G.pr
  contMDiff_pr := G.contMDiff_pr
  Γ := G.Γ
  isAnalytic_Γ := G.isAnalytic_Γ
  B := G.B
  isClosed_B := G.isClosed_B
  isAnalytic_B := G.isAnalytic_B
  interior_B := G.interior_B
  φ := G.φ
  contMDiffOn_φ := G.contMDiffOn_φ
  pr_φ := G.pr_φ
  φ_mem := fun _ hx => G.φ_mem_Γ hx
  eq_φ := fun _ hz hzB => G.eq_φ_of_mem_Γ hz hzB
  regularAtDim_φ := fun _ hx => G.regularAtDim_φ hx
  subset_closure := G.Γ_subset_closure
  N := G.N
  ι := G.ι
  contMDiff_ι := G.contMDiff_ι
  regularAtDim_ι := G.regularAtDim_ι
  n₀ := G.n₀
  injective_mfderiv_ι := G.injective_mfderiv_ι G.n₀
  Δ := G.Δ
  isAnalytic_Δ := G.isAnalytic_Δ
  flattening := G.flattening
  ord_eq := G.ord_eq

end GraphData

variable (f m) in
/-- **Every algebraic prime divisor centred in codimension at least two has graph data.**  (A
statement, not proved here.) -/
def HighCodimGraphData : Prop :=
  ∀ D : PrimeDivisorOver X, Order.coheight (D.ordVal f 1 one_pos).center ≠ 1 →
    Nonempty (GraphData f m D)

theorem highCodimGraphModels_of_highCodimGraphData (h : HighCodimGraphData f m) :
    HighCodimGraphModels f m :=
  fun D hD => (h D hD).map GraphData.toGraphModel

/-- **Graph data give `AlgebraicPrimesRealized`.** -/
theorem algebraicPrimesRealized_of_highCodimGraphData (E : ClosedProjectiveEmbedding f)
    (h : HighCodimGraphData f m) : AlgebraicPrimesRealized (f := f) m E :=
  algebraicPrimesRealized_of_highCodimGraphModels E (highCodimGraphModels_of_highCodimGraphData h)

end SGPT.NAPotential.AlgPrimes3

end

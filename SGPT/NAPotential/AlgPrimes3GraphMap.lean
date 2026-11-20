import SGPT.NAPotential.AlgPrimes3GraphData
import SGPT.Projective.Maps
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold

/-!
# The holomorphic graph map of finitely many rational functions

Lane ALG-PRIMES3, blueprint `claude-alg-primes3:graph-map`.

Part of step (b) of the plan of `claude-alg-primes:remaining`: the ambient manifold and the graph
map of graph data (`GraphData`).  For regular functions `r₁, …, r_s` on a nonempty open `V ⊆ X`
(e.g. the rational functions `bᵢ` of `PrimeDivisorOver'.exists_affine_generators`, regular on a
basic open of an affine chart):

* `graphAmbient f m s`: the compact complex manifold `X(ℂ) × ℙ^s(ℂ)` of dimension `dim X + s`
  (`SGPT.Foundations.Analysis.Pending.ProductComplexManifold`), with the holomorphic first projection;
* `graphBase V`: the complex points outside `V`, a closed analytic subset of `X(ℂ)` with empty
  interior (`isClosed_graphBase`, `isAnalytic_graphBase`, `interior_graphBase`);
* `graphMap E r : X(ℂ) → X(ℂ) × ℙ^s(ℂ)`, `x ↦ (x, [1 : r₁(x) : … : r_s(x)])`, holomorphic off
  `graphBase V` (`contMDiffOn_graphMap`), a section of the projection (`fst_graphMap`);
* `ProductGraphData`: graph data on `X(ℂ) × ℙ^s(ℂ)` with this graph map
  (`ProductGraphData.toGraphData`), and `algebraicPrimesRealized_of_highCodimProductGraphData`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3

open Set Filter
open scoped Topology Manifold ContDiff
open AlgebraicGeometry CategoryTheory
open SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.NAPotential.Berkovich
open SGPT.Projective HolomorphicIdealSheaves BlowupTowers
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance algPrimes3MapPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPrimes3MapPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algPrimes3MapPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (f m) in
/-- The ambient manifold `X(ℂ) × ℙ^s(ℂ)` of the graph of `s` rational functions. -/
def graphAmbient (s : ℕ) : CMfd.{0} ((m + 1) + s) :=
  CMfd.of (SchemeComplexPoint f × ComplexProjectiveSpace s)

/-- `X(ℂ) × ℙ^s(ℂ)` is compact. -/
theorem compactSpace_graphAmbient (E : ClosedProjectiveEmbedding f) (s : ℕ) :
    CompactSpace (graphAmbient f m s) := by
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  change CompactSpace (SchemeComplexPoint f × ComplexProjectiveSpace s)
  infer_instance

/-- The first projection `X(ℂ) × ℙ^s(ℂ) → X(ℂ)` is holomorphic. -/
theorem contMDiff_fst_graphAmbient (s : ℕ) :
    ContMDiff 𝓘(ℂ, ComplexModel ((m + 1) + s)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      (Prod.fst : graphAmbient f m s → SchemeComplexPoint f) :=
  ProductComplexManifold.contMDiff_fst

variable (f) in
/-- The complex points outside the open set `V`. -/
def graphBase (V : X.Opens) : Set (SchemeComplexPoint f) :=
  schemeNativeAlgebraicTrace f ((V : Set X)ᶜ)

omit [IsProper f] in
theorem mem_graphBase {V : X.Opens} {x : SchemeComplexPoint f} :
    x ∈ graphBase f V ↔ schemeComplexPointImage f x ∉ V := Iff.rfl

omit [IsProper f] in
theorem isClosed_graphBase (V : X.Opens) : IsClosed (graphBase f V) :=
  V.isOpen.isClosed_compl.preimage (schemeComplexPointImage_continuous f)

theorem isAnalytic_graphBase (E : ClosedProjectiveEmbedding f) (V : X.Opens) :
    IsComplexAnalyticSubset (n := m + 1) (graphBase f V) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact schemeNativeAlgebraicTrace_isComplexAnalyticSubset f (m + 1) _ V.isOpen.isClosed_compl

variable (m) in
include m in
omit [IsProper f] in
theorem interior_graphBase [IsIntegral X] (E : ClosedProjectiveEmbedding f) {V : X.Opens}
    (hV : (V : Set X).Nonempty) : interior (graphBase f V) = ∅ := by
  let := E.isSeparated
  let := E.quasiCompact
  refine schemeNativeAlgebraicTrace_interior_eq_empty f (m + 1) _ V.isOpen.isClosed_compl ?_
  intro h
  obtain ⟨y, hy⟩ := hV
  have : y ∈ ((V : Set X)ᶜ) := by rw [h]; trivial
  exact this hy

variable (E : ClosedProjectiveEmbedding f) {V : X.Opens} {s : ℕ}

/-- The homogeneous lift `(1, r₁(x), …, r_s(x))` of the graph map. -/
def graphLift (r : Fin s → Γ(X, V)) (x : SchemeComplexPoint f) : Fin (s + 1) → ℂ :=
  Fin.cons 1 fun i => schemeOpenRegularFunction f (m + 1) E V (r i) x

omit [IsProper f] in
theorem graphLift_ne_zero (r : Fin s → Γ(X, V)) (x : SchemeComplexPoint f) :
    graphLift (m := m) E r x ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [graphLift] at this

/-- **The graph map** `x ↦ (x, [1 : r₁(x) : … : r_s(x)])`. -/
def graphMap (r : Fin s → Γ(X, V)) (x : SchemeComplexPoint f) : graphAmbient f m s :=
  ((x, ComplexProjectiveSpace.mk (graphLift (m := m) E r x) (graphLift_ne_zero E r x)) :
    SchemeComplexPoint f × ComplexProjectiveSpace s)

@[simp]
theorem fst_graphMap (r : Fin s → Γ(X, V)) (x : SchemeComplexPoint f) :
    (graphMap (m := m) E r x).1 = x := rfl

/-- The lift is holomorphic at the complex points of `V`. -/
theorem contMDiffAt_graphLift (r : Fin s → Γ(X, V)) {x : SchemeComplexPoint f}
    (hx : schemeComplexPointImage f x ∈ V) :
    ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, Fin (s + 1) → ℂ) ∞
      (graphLift (m := m) E r) x := by
  rw [contMDiffAt_pi_space]
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa [graphLift] using contMDiffAt_const
  · have hhol := schemeOpenRegularFunction_holomorphicAt f (m + 1) E V (r i) x hx
    have h := contMDiffAt_of_eventually_mdifferentiableAt
      (m := m + 1) (F := schemeOpenRegularFunction f (m + 1) E V (r i)) hhol
    simpa [graphLift] using h

/-- The `ℙ^s`-component of the graph map is holomorphic at the complex points of `V`. -/
theorem contMDiffAt_graphMap_snd (r : Fin s → Γ(X, V)) {x : SchemeComplexPoint f}
    (hx : schemeComplexPointImage f x ∈ V) :
    ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel s) ∞
      (fun y => ComplexProjectiveSpace.mk (graphLift (m := m) E r y) (graphLift_ne_zero E r y)) x :=
  ComplexProjectiveSpace.contMDiffAt_of_lift (contMDiffAt_graphLift E r hx)
    (graphLift_ne_zero E r x) (Eventually.of_forall fun y => ⟨graphLift_ne_zero E r y, rfl⟩)

/-- **The graph map is holomorphic off `graphBase V`.** -/
theorem contMDiffOn_graphMap (r : Fin s → Γ(X, V)) :
    ContMDiffOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel ((m + 1) + s)) ∞
      (graphMap (m := m) E r) (graphBase f V)ᶜ := by
  set O : TopologicalSpace.Opens (SchemeComplexPoint f) :=
    ⟨(graphBase f V)ᶜ, (isClosed_graphBase V).isOpen_compl⟩ with hO
  have hsnd : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel s) ∞
      (fun z : O => ComplexProjectiveSpace.mk (graphLift (m := m) E r z.1)
        (graphLift_ne_zero E r z.1)) := by
    intro z
    have hz : schemeComplexPointImage f z.1 ∈ V := by
      have h : z.1 ∉ graphBase f V := z.2
      rw [mem_graphBase, not_not] at h
      exact h
    exact (contMDiffAt_graphMap_snd E r hz).comp z contMDiff_subtype_val.contMDiffAt
  have hpair : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel ((m + 1) + s)) ∞
      (fun z : O => graphMap (m := m) E r z.1) :=
    ProductComplexManifold.contMDiff_prodMk contMDiff_subtype_val hsnd
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (hpair ⟨x, hx⟩)).contMDiffWithinAt

section ProductGraphData

open SGPT.NAPotential.AlgPrimes SGPT.NAPotential.TowerAlg DemaillyApproximantDivisorialLelong
open FixedGermNormalOrder

variable [IsIntegral X]

variable (m) in
/-- **Product graph data** of an algebraic prime divisor `D` over `X`: graph data
(`GraphData`) on the ambient manifold `X(ℂ) × ℙ^s(ℂ)` with the graph map `graphMap E r` of
regular functions `r₁, …, r_s` on a nonempty open `V ⊆ X` (off `graphBase V`).  What remains to
be supplied: an analytic set `Γ₀ ⊆ X(ℂ) × ℙ^s(ℂ)` meeting `pr⁻¹(V(ℂ))` exactly along the graph,
and the local model (`ι`, `n₀`, `Δ`, the order comparison). -/
structure ProductGraphData (D : PrimeDivisorOver X) where
  /-- The open set on which the functions are regular. -/
  V : X.Opens
  nonempty_V : (V : Set X).Nonempty
  /-- The number of functions. -/
  s : ℕ
  /-- The regular functions. -/
  r : Fin s → Γ(X, V)
  /-- An analytic set containing the graph. -/
  Γ₀ : Set (graphAmbient f m s)
  isAnalytic_Γ₀ : IsComplexAnalyticSubset (n := (m + 1) + s) Γ₀
  graphMap_mem : ∀ x ∉ graphBase f V, graphMap (m := m) E r x ∈ Γ₀
  eq_graphMap : ∀ z ∈ Γ₀, z.1 ∉ graphBase f V → graphMap (m := m) E r z.1 = z
  /-- The local smooth model. -/
  N : CMfd.{0} (m + 1)
  ι : N → graphAmbient f m s
  contMDiff_ι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel ((m + 1) + s)) ∞ ι
  ι_mem : ∀ p, ι p ∈ Γ₀
  injective_mfderiv_ι :
    ∀ p, Function.Injective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel ((m + 1) + s)) ι p)
  ι_local : ∀ p, ∀ U ∈ 𝓝 p, ∃ W ∈ 𝓝 (ι p), Γ₀ ∩ W ⊆ ι '' U
  interior_ι_B : interior (ι ⁻¹' (Prod.fst ⁻¹' graphBase f V)) = ∅
  /-- The point of `N` over the centre of `ord_D`. -/
  n₀ : N
  /-- The analytic set of the centre of `ord_D` on the model. -/
  Δ : Set (graphAmbient f m s)
  isAnalytic_Δ : IsComplexAnalyticSubset (n := (m + 1) + s) Δ
  flattening : DivisorFlattening (m := m) (ι ⁻¹' Δ) n₀
  ord_eq : ∀ g : X.presheaf.stalk (schemeComplexPointImage f (ι n₀).1), g ≠ 0 →
    (D.ord ((BerkovichPoint.specializationMap
      (ordVal_support_specializes f D (schemeComplexPointImage f (ι n₀).1))).hom g) : ℤ) =
      ((functionNormalOrder flattening (stalkRep m (ι n₀).1 g ∘ (Prod.fst ∘ ι))
        (HolomorphicIdealSheaves.HolomorphicAt.comp_contMDiff (f := Prod.fst ∘ ι) (y := n₀)
          (stalkRep_holomorphicAt (ι n₀).1 g)
          (Eventually.of_forall fun _ =>
            ((contMDiff_fst_graphAmbient s).comp contMDiff_ι).contMDiffAt))).toNat : ℤ)

namespace ProductGraphData

variable {E} {D : PrimeDivisorOver X}

/-- Product graph data are graph data. -/
def toGraphData (G : ProductGraphData m E D) : GraphData f m D where
  K := (m + 1) + G.s
  M := graphAmbient f m G.s
  compactSpace := compactSpace_graphAmbient E G.s
  pr := Prod.fst
  contMDiff_pr := contMDiff_fst_graphAmbient G.s
  Γ₀ := G.Γ₀
  isAnalytic_Γ₀ := G.isAnalytic_Γ₀
  B := graphBase f G.V
  isClosed_B := isClosed_graphBase G.V
  isAnalytic_B := isAnalytic_graphBase E G.V
  interior_B := interior_graphBase m E G.nonempty_V
  φ := graphMap (m := m) E G.r
  contMDiffOn_φ := contMDiffOn_graphMap E G.r
  pr_φ := fun _ _ => rfl
  φ_mem := G.graphMap_mem
  eq_φ := G.eq_graphMap
  N := G.N
  ι := G.ι
  contMDiff_ι := G.contMDiff_ι
  ι_mem := G.ι_mem
  injective_mfderiv_ι := G.injective_mfderiv_ι
  ι_local := G.ι_local
  interior_ι_B := G.interior_ι_B
  n₀ := G.n₀
  Δ := G.Δ
  isAnalytic_Δ := G.isAnalytic_Δ
  flattening := G.flattening
  ord_eq := G.ord_eq

end ProductGraphData

variable (m) in
/-- **Every algebraic prime divisor centred in codimension at least two has product graph
data.**  (A statement, not proved here.) -/
def HighCodimProductGraphData : Prop :=
  ∀ D : PrimeDivisorOver X, Order.coheight (D.ordVal f 1 one_pos).center ≠ 1 →
    Nonempty (ProductGraphData m E D)

/-- **Product graph data give `AlgebraicPrimesRealized`.** -/
theorem algebraicPrimesRealized_of_highCodimProductGraphData
    (h : HighCodimProductGraphData m E) : AlgebraicPrimesRealized (f := f) m E :=
  algebraicPrimesRealized_of_highCodimGraphData E
    fun D hD => (h D hD).map ProductGraphData.toGraphData

end ProductGraphData

end SGPT.NAPotential.AlgPrimes3

end

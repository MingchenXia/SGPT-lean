import SGPT.BDivisor.CartierBDivisor
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The Euclidean topology on `H^{1,1}`, convergence of b-divisors and nef b-divisors

Source: `chap:bdiv`, `def:nefb` and the convergence notion stated after `lma:volbdivnet`:
"`(𝔻_i)_i` converges to `𝔻` if for any modification `π : Y → X`, `𝔻_{i,Y} → 𝔻_Y` with respect to
the Euclidean topology"; a Weil b-divisor is **nef** if it is the limit of a net of nef Cartier
b-divisors. The book adds: "Our definition amounts to defining the set of [nef] Weil b-divisors
as the closure of the set of [nef] Cartier b-divisors in `lim← H^{1,1}(Y, ℝ)` with respect to the
projective limit topology. In particular, the limit of a converging net of nef b-divisors is
still nef."

**The Euclidean topology.** `H^{1,1}(Y, ℝ)` is a finite-dimensional real vector space (Hodge
theory, not formalized here). The Euclidean topology of a finite-dimensional real vector space
`V` is intrinsic: it is the coarsest topology making every linear functional `V → ℝ` continuous
(`euclideanTopology`), and it coincides with **every** Hausdorff topological vector space topology
on `V` as soon as `V` is finite-dimensional (`eq_euclideanTopology`). We use this intrinsic
description on `RealBottChern n Y`; convergence is coordinatewise convergence
(`tendsto_euclideanTopology_iff`: `α_i → α` iff `f(α_i) → f(α)` for every linear `f`).

Main declarations:

* `SGPT.BDivisor.euclideanTopology`, `SGPT.BDivisor.eq_euclideanTopology`;
* `SGPT.BDivisor.WeilBDivisor.Converges` — convergence of a family of b-divisors on every model,
  and `SGPT.BDivisor.WeilBDivisor.modelwiseTopology` — the projective limit topology
  (`converges_iff_tendsto`);
* `SGPT.BDivisor.WeilBDivisor.IsNef` (`def:nefb`), with `isNef_iff_mem_closure` (the closure
  description), `IsNefCartier.isNef`, and `IsNef.of_converges` (limits of nets of nef b-divisors
  are nef).
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace SGPT.BDivisor

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

/-! ### The Euclidean topology of a real vector space -/

section EuclideanTopology

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- The **Euclidean topology** of a real vector space, described intrinsically: the coarsest
topology for which every linear functional is continuous. On a finite-dimensional space it is
the usual Euclidean topology (`eq_euclideanTopology`). -/
@[instance_reducible] def euclideanTopology : TopologicalSpace V :=
  ⨅ f : Module.Dual ℝ V, TopologicalSpace.induced f inferInstance

variable {V}

/-- Convergence in the Euclidean topology is convergence of all linear coordinates. -/
theorem tendsto_euclideanTopology_iff {ι : Type*} {l : Filter ι} {x : ι → V} {y : V} :
    Tendsto x l (@nhds V (euclideanTopology V) y) ↔
      ∀ f : Module.Dual ℝ V, Tendsto (fun i => f (x i)) l (𝓝 (f y)) := by
  rw [euclideanTopology, nhds_iInf, tendsto_iInf]
  refine forall_congr' fun f => ?_
  rw [nhds_induced, tendsto_comap_iff]
  rfl

/-- Every linear functional is continuous for the Euclidean topology. -/
theorem continuous_euclideanTopology (f : Module.Dual ℝ V) :
    Continuous[euclideanTopology V, inferInstance] f :=
  continuous_iInf_dom continuous_induced_dom

/-- Finitely many linear coordinates are jointly continuous for the Euclidean topology. -/
theorem continuous_euclideanTopology_pi {ι : Type*} (F : ι → Module.Dual ℝ V) :
    Continuous[euclideanTopology V, inferInstance] (fun v i => F i v) := by
  let _ := euclideanTopology V
  exact continuous_pi fun i => continuous_euclideanTopology (F i)

/-- **On a finite-dimensional real vector space, every Hausdorff topological vector space
topology is the Euclidean topology.** -/
theorem eq_euclideanTopology [τ : TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] :
    τ = euclideanTopology V := by
  apply le_antisymm
  · exact le_iInf fun f => continuous_iff_le_induced.mp (LinearMap.continuous_of_finiteDimensional f)
  · let b := Module.finBasis ℝ V
    have hτ : τ = TopologicalSpace.induced (fun v i => b.coord i v) inferInstance :=
      b.equivFunL.toHomeomorph.isInducing.eq_induced
    rw [hτ]
    exact continuous_iff_le_induced.mp (continuous_euclideanTopology_pi fun i => b.coord i)

end EuclideanTopology

/-! ### Convergence of b-divisors and nef b-divisors -/

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace WeilBDivisor

variable {hn : 0 < n}

variable (n X hn) in
/-- The projective limit topology on Weil b-divisors: the coarsest topology for which every
class map `𝔻 ↦ 𝔻_π ∈ H^{1,1}(Y_π, ℝ)` is continuous for the Euclidean topology. -/
@[instance_reducible] def modelwiseTopology : TopologicalSpace (WeilBDivisor n X hn) :=
  ⨅ π : Modification n X,
    TopologicalSpace.induced (fun D : WeilBDivisor n X hn => D.onModel π)
      (euclideanTopology (RealBottChern n π.carrier))

/-- A family `(𝔻_i)` **converges** to `𝔻` along `l` if `𝔻_{i,π} → 𝔻_π` in the Euclidean topology
of `H^{1,1}(Y_π, ℝ)` for every modification `π`. -/
def Converges {ι : Type*} (l : Filter ι) (D : ι → WeilBDivisor n X hn)
    (𝔻 : WeilBDivisor n X hn) : Prop :=
  ∀ π : Modification n X, Tendsto (fun i => (D i).onModel π) l
    (@nhds _ (euclideanTopology (RealBottChern n π.carrier)) (𝔻.onModel π))

/-- Convergence on every model is convergence in the projective limit topology. -/
theorem converges_iff_tendsto {ι : Type*} {l : Filter ι} {D : ι → WeilBDivisor n X hn}
    {𝔻 : WeilBDivisor n X hn} :
    Converges l D 𝔻 ↔ Tendsto D l (@nhds _ (modelwiseTopology n X hn) 𝔻) := by
  rw [modelwiseTopology, nhds_iInf, tendsto_iInf]
  refine forall_congr' fun π => ?_
  rw [nhds_induced (T := euclideanTopology (RealBottChern n π.carrier)), tendsto_comap_iff]
  rfl

/-- Coordinatewise description: `𝔻_i → 𝔻` iff `f(𝔻_{i,π}) → f(𝔻_π)` for every model `π` and every
linear functional `f` on `H^{1,1}(Y_π, ℝ)`. -/
theorem converges_iff_forall_dual {ι : Type*} {l : Filter ι} {D : ι → WeilBDivisor n X hn}
    {𝔻 : WeilBDivisor n X hn} :
    Converges l D 𝔻 ↔ ∀ (π : Modification n X) (f : Module.Dual ℝ (RealBottChern n π.carrier)),
      Tendsto (fun i => f ((D i).onModel π)) l (𝓝 (f (𝔻.onModel π))) :=
  forall_congr' fun _ => tendsto_euclideanTopology_iff

/-- **Nef b-divisors** (`def:nefb`): `𝔻` is nef if it is the limit of a net of nef Cartier
b-divisors, i.e. there are a nonempty directed preorder `ι` and nef Cartier b-divisors `𝔻_i`
with `𝔻_{i,π} → 𝔻_π` along `ι` for every model `π`. (Nets are indexed by types of the universe of
the b-divisors themselves; by `isNef_iff_mem_closure` this is no restriction.) -/
def IsNef (𝔻 : WeilBDivisor n X hn) : Prop :=
  ∃ (ι : Type (u + 1)) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (D : ι → WeilBDivisor n X hn), (∀ i, (D i).IsNefCartier) ∧ Converges atTop D 𝔻

/-- A limit of a net (indexed by any directed type, in any universe) of b-divisors in a set `S`
lies in the closure of `S` for the projective limit topology. -/
theorem mem_closure_of_converges {S : Set (WeilBDivisor n X hn)} {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {D : ι → WeilBDivisor n X hn}
    {𝔻 : WeilBDivisor n X hn} (hD : ∀ i, D i ∈ S) (h : Converges atTop D 𝔻) :
    𝔻 ∈ @closure _ (modelwiseTopology n X hn) S := by
  let _ : TopologicalSpace (WeilBDivisor n X hn) := modelwiseTopology n X hn
  exact mem_closure_of_tendsto (converges_iff_tendsto.mp h) (Eventually.of_forall hD)

/-- Every point of the closure of `S` is the limit of a net of elements of `S` indexed by the
neighbourhoods of the point. -/
theorem exists_net_of_mem_closure {S : Set (WeilBDivisor n X hn)} {𝔻 : WeilBDivisor n X hn}
    (h : 𝔻 ∈ @closure _ (modelwiseTopology n X hn) S) :
    ∃ (ι : Type (u + 1)) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (D : ι → WeilBDivisor n X hn), (∀ i, D i ∈ S) ∧ Converges atTop D 𝔻 := by
  let _ : TopologicalSpace (WeilBDivisor n X hn) := modelwiseTopology n X hn
  -- the neighbourhoods of `𝔻`, ordered by reverse inclusion
  let ι := {U : (Set (WeilBDivisor n X hn))ᵒᵈ // OrderDual.ofDual U ∈ 𝓝 𝔻}
  have hdir : IsDirected ι (· ≤ ·) := ⟨fun U V =>
    ⟨⟨OrderDual.toDual (OrderDual.ofDual U.1 ∩ OrderDual.ofDual V.1), inter_mem U.2 V.2⟩,
      inter_subset_left, inter_subset_right⟩⟩
  have hne : Nonempty ι := ⟨⟨OrderDual.toDual univ, univ_mem⟩⟩
  have hpt : ∀ U : ι, (OrderDual.ofDual U.1 ∩ S).Nonempty := fun U =>
    mem_closure_iff_nhds.mp h _ U.2
  choose D hD using hpt
  refine ⟨ι, inferInstance, hdir, hne, D, fun U => (hD U).2, converges_iff_tendsto.mpr ?_⟩
  intro W hW
  rw [mem_map, mem_atTop_sets]
  refine ⟨⟨OrderDual.toDual W, hW⟩, fun U hU => ?_⟩
  exact hU (hD U).1

/-- **The closure description of nef b-divisors**: `𝔻` is nef iff it lies in the closure of the
nef Cartier b-divisors for the projective limit topology. -/
theorem isNef_iff_mem_closure (𝔻 : WeilBDivisor n X hn) :
    𝔻.IsNef ↔ 𝔻 ∈ @closure _ (modelwiseTopology n X hn) {D | D.IsNefCartier} := by
  constructor
  · rintro ⟨ι, _, _, _, D, hD, hconv⟩
    exact mem_closure_of_converges hD hconv
  · intro h
    obtain ⟨ι, i1, i2, i3, D, hD, hconv⟩ := exists_net_of_mem_closure h
    exact ⟨ι, i1, i2, i3, D, hD, hconv⟩

/-- A nef Cartier b-divisor is nef (constant net). -/
theorem IsNefCartier.isNef {𝔻 : WeilBDivisor n X hn} (h : 𝔻.IsNefCartier) : 𝔻.IsNef := by
  let _ : TopologicalSpace (WeilBDivisor n X hn) := modelwiseTopology n X hn
  exact (isNef_iff_mem_closure 𝔻).mpr (subset_closure h)

/-- **The limit of a converging net of nef b-divisors is nef** (the net may be indexed by a
directed type of any universe). -/
theorem IsNef.of_converges {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {D : ι → WeilBDivisor n X hn} {𝔻 : WeilBDivisor n X hn} (hD : ∀ i, (D i).IsNef)
    (h : Converges atTop D 𝔻) : 𝔻.IsNef := by
  rw [isNef_iff_mem_closure]
  have hD' : ∀ i, D i ∈ @closure _ (modelwiseTopology n X hn) {D | D.IsNefCartier} :=
    fun i => (isNef_iff_mem_closure (D i)).mp (hD i)
  have hcl := mem_closure_of_converges hD' h
  let _ : TopologicalSpace (WeilBDivisor n X hn) := modelwiseTopology n X hn
  rwa [closure_closure] at hcl

/-- The set of nef b-divisors is closed in the projective limit topology. -/
theorem isClosed_setOf_isNef :
    IsClosed[modelwiseTopology n X hn] {𝔻 : WeilBDivisor n X hn | 𝔻.IsNef} := by
  have h : {𝔻 : WeilBDivisor n X hn | 𝔻.IsNef} =
      @closure _ (modelwiseTopology n X hn) {D | D.IsNefCartier} := by
    ext 𝔻
    exact isNef_iff_mem_closure 𝔻
  rw [h]
  let _ : TopologicalSpace (WeilBDivisor n X hn) := modelwiseTopology n X hn
  exact isClosed_closure

end WeilBDivisor

end SGPT.BDivisor

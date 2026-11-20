import SGPT.BDivisor.BlowupModelWeil
import SGPT.BDivisor.NefBDivisor

/-!
# Convergence of b-divisors and nef b-divisors over a model system

Source: `chap:bdiv`, `def:nefb` and the convergence notion after `lma:volbdivnet`: "`(𝔻_i)_i`
converges to `𝔻` if for any modification `π : Y → X`, `𝔻_{i,Y} → 𝔻_Y` with respect to the
Euclidean topology"; a Weil b-divisor is **nef** if it is the limit of a net of nef Cartier
b-divisors; "our definition amounts to defining [nef b-divisors as] the closure of the set of
[nef] Cartier b-divisors in `lim← H^{1,1}(Y, ℝ)` with respect to the projective limit topology. In
particular, the limit of a converging net of nef b-divisors is still nef." `cor:nefbCequiv`, the
easy implication: a nef Cartier b-divisor (`def:nefCar`) is nef (`def:nefb`).

The Euclidean topology on `H^{1,1}(Y, ℝ)` is the intrinsic one of `SGPT.BDivisor.euclideanTopology`
(the coarsest topology making every linear functional continuous), which is the Euclidean topology
as soon as `H^{1,1}(Y, ℝ)` is finite-dimensional (`SGPT.BDivisor.eq_euclideanTopology`).

Everything is stated for an arbitrary model system `S`; the book's nef b-divisors are the case
`S = ModelSystem.blowup n X`.

Main declarations (namespace `SGPT.BDivisor.WeilBDivisorOn`): `modelwiseTopology`, `Converges`,
`converges_iff_tendsto`, `IsNef`, `isNef_iff_mem_closure`, `IsNefCartier.isNef`,
`IsNef.of_converges`, `isClosed_setOf_isNef`; and `SGPT.BDivisor.tendsto_euclideanTopology_map`
(linear maps are continuous for the intrinsic topologies).
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace SGPT.BDivisor

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

/-- Linear maps are continuous for the intrinsic Euclidean topologies: if `x_i → y`, then
`f x_i → f y`. -/
theorem tendsto_euclideanTopology_map {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) {ι : Type*} {l : Filter ι} {x : ι → V} {y : V}
    (h : Tendsto x l (@nhds V (euclideanTopology V) y)) :
    Tendsto (fun i => f (x i)) l (@nhds W (euclideanTopology W) (f y)) := by
  rw [tendsto_euclideanTopology_iff] at h ⊢
  intro g
  exact h (g ∘ₗ f)

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace WeilBDivisorOn

variable {S : ModelSystem n X} {hn : 0 < n}

variable (S hn) in
/-- The projective limit topology: the coarsest topology for which every class map
`𝔻 ↦ 𝔻_π ∈ H^{1,1}(Y_π, ℝ)`, `π ∈ S`, is continuous for the Euclidean topology. -/
@[instance_reducible] def modelwiseTopology : TopologicalSpace (WeilBDivisorOn S hn) :=
  ⨅ π : S.Model,
    TopologicalSpace.induced (fun D : WeilBDivisorOn S hn => D.onModel π)
      (euclideanTopology (RealBottChern n π.1.carrier))

/-- A family `(𝔻_i)` **converges** to `𝔻` along `l` if `𝔻_{i,π} → 𝔻_π` in the Euclidean topology
of `H^{1,1}(Y_π, ℝ)` for every model `π`. -/
def Converges {ι : Type*} (l : Filter ι) (D : ι → WeilBDivisorOn S hn)
    (𝔻 : WeilBDivisorOn S hn) : Prop :=
  ∀ π : S.Model, Tendsto (fun i => (D i).onModel π) l
    (@nhds _ (euclideanTopology (RealBottChern n π.1.carrier)) (𝔻.onModel π))

theorem converges_iff_tendsto {ι : Type*} {l : Filter ι} {D : ι → WeilBDivisorOn S hn}
    {𝔻 : WeilBDivisorOn S hn} :
    Converges l D 𝔻 ↔ Tendsto D l (@nhds _ (modelwiseTopology S hn) 𝔻) := by
  rw [modelwiseTopology, nhds_iInf, tendsto_iInf]
  refine forall_congr' fun π => ?_
  rw [nhds_induced (T := euclideanTopology (RealBottChern n π.1.carrier)), tendsto_comap_iff]
  rfl

theorem converges_iff_forall_dual {ι : Type*} {l : Filter ι} {D : ι → WeilBDivisorOn S hn}
    {𝔻 : WeilBDivisorOn S hn} :
    Converges l D 𝔻 ↔ ∀ (π : S.Model) (f : Module.Dual ℝ (RealBottChern n π.1.carrier)),
      Tendsto (fun i => f ((D i).onModel π)) l (𝓝 (f (𝔻.onModel π))) :=
  forall_congr' fun _ => tendsto_euclideanTopology_iff

/-- **Nef b-divisors** (`def:nefb`): `𝔻` is nef if it is the limit of a net (a nonempty directed
preorder `ι`) of nef Cartier b-divisors. -/
def IsNef (𝔻 : WeilBDivisorOn S hn) : Prop :=
  ∃ (ι : Type (u + 1)) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (D : ι → WeilBDivisorOn S hn), (∀ i, (D i).IsNefCartier) ∧ Converges atTop D 𝔻

theorem mem_closure_of_converges {T : Set (WeilBDivisorOn S hn)} {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {D : ι → WeilBDivisorOn S hn}
    {𝔻 : WeilBDivisorOn S hn} (hD : ∀ i, D i ∈ T) (h : Converges atTop D 𝔻) :
    𝔻 ∈ @closure _ (modelwiseTopology S hn) T := by
  let _ : TopologicalSpace (WeilBDivisorOn S hn) := modelwiseTopology S hn
  exact mem_closure_of_tendsto (converges_iff_tendsto.mp h) (Eventually.of_forall hD)

theorem exists_net_of_mem_closure {T : Set (WeilBDivisorOn S hn)} {𝔻 : WeilBDivisorOn S hn}
    (h : 𝔻 ∈ @closure _ (modelwiseTopology S hn) T) :
    ∃ (ι : Type (u + 1)) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (D : ι → WeilBDivisorOn S hn), (∀ i, D i ∈ T) ∧ Converges atTop D 𝔻 := by
  let _ : TopologicalSpace (WeilBDivisorOn S hn) := modelwiseTopology S hn
  let ι := {U : (Set (WeilBDivisorOn S hn))ᵒᵈ // OrderDual.ofDual U ∈ 𝓝 𝔻}
  have hdir : IsDirected ι (· ≤ ·) := ⟨fun U V =>
    ⟨⟨OrderDual.toDual (OrderDual.ofDual U.1 ∩ OrderDual.ofDual V.1), inter_mem U.2 V.2⟩,
      inter_subset_left, inter_subset_right⟩⟩
  have hne : Nonempty ι := ⟨⟨OrderDual.toDual univ, univ_mem⟩⟩
  have hpt : ∀ U : ι, (OrderDual.ofDual U.1 ∩ T).Nonempty := fun U =>
    mem_closure_iff_nhds.mp h _ U.2
  choose D hD using hpt
  refine ⟨ι, inferInstance, hdir, hne, D, fun U => (hD U).2, converges_iff_tendsto.mpr ?_⟩
  intro W hW
  rw [mem_map, mem_atTop_sets]
  refine ⟨⟨OrderDual.toDual W, hW⟩, fun U hU => ?_⟩
  exact hU (hD U).1

/-- **The closure description of nef b-divisors.** -/
theorem isNef_iff_mem_closure (𝔻 : WeilBDivisorOn S hn) :
    𝔻.IsNef ↔ 𝔻 ∈ @closure _ (modelwiseTopology S hn) {D | D.IsNefCartier} := by
  constructor
  · rintro ⟨ι, _, _, _, D, hD, hconv⟩
    exact mem_closure_of_converges hD hconv
  · intro h
    obtain ⟨ι, i1, i2, i3, D, hD, hconv⟩ := exists_net_of_mem_closure h
    exact ⟨ι, i1, i2, i3, D, hD, hconv⟩

/-- **`cor:nefbCequiv`, easy direction**: a nef Cartier b-divisor (`def:nefCar`) is nef in the
sense of `def:nefb` (constant net). -/
theorem IsNefCartier.isNef {𝔻 : WeilBDivisorOn S hn} (h : 𝔻.IsNefCartier) : 𝔻.IsNef := by
  let _ : TopologicalSpace (WeilBDivisorOn S hn) := modelwiseTopology S hn
  exact (isNef_iff_mem_closure 𝔻).mpr (subset_closure h)

/-- **The limit of a converging net of nef b-divisors is nef.** -/
theorem IsNef.of_converges {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {D : ι → WeilBDivisorOn S hn} {𝔻 : WeilBDivisorOn S hn} (hD : ∀ i, (D i).IsNef)
    (h : Converges atTop D 𝔻) : 𝔻.IsNef := by
  rw [isNef_iff_mem_closure]
  have hD' : ∀ i, D i ∈ @closure _ (modelwiseTopology S hn) {D | D.IsNefCartier} :=
    fun i => (isNef_iff_mem_closure (D i)).mp (hD i)
  have hcl := mem_closure_of_converges hD' h
  let _ : TopologicalSpace (WeilBDivisorOn S hn) := modelwiseTopology S hn
  rwa [closure_closure] at hcl

theorem isClosed_setOf_isNef :
    IsClosed[modelwiseTopology S hn] {𝔻 : WeilBDivisorOn S hn | 𝔻.IsNef} := by
  have h : {𝔻 : WeilBDivisorOn S hn | 𝔻.IsNef} =
      @closure _ (modelwiseTopology S hn) {D | D.IsNefCartier} := by
    ext 𝔻
    exact isNef_iff_mem_closure 𝔻
  rw [h]
  let _ : TopologicalSpace (WeilBDivisorOn S hn) := modelwiseTopology S hn
  exact isClosed_closure

end WeilBDivisorOn

end SGPT.BDivisor

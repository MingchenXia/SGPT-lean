import SGPT.Toric.BigToric2Orbits
import SGPT.Toric.Toric3AdaptedFlag
import SGPT.Toric.Toric3CoordinateDivision
import SGPT.Okounkov.OriginalFlagGeometry

/-!
# Toric flags of a smooth projective toric manifold

Source `chapter_toric_big.tex`, Subsection `subsec:pobtorgeneral`: "Since `X` is smooth and
projective, we can choose a full-dimensional cone `σ` in `Σ` with rays `ρ_1, …, ρ_n` such that
`u_{ρ_1}, …, u_{ρ_n}` form a basis of `N`. Define `Y_i = D_{ρ_1} ∩ ⋯ ∩ D_{ρ_i}`. Then `Y•` is a
smooth flag on `X`."

In the model `X = PolytopeToricVariety γ hs` (see `BigToricDivisor`) the maximal cones are the
cones `σ_v` of the vertices `v` of the Delzant polytope `P`, with rays `u_j(v)`; an ordering of
the rays is a permutation `e` of `Fin n` (`ρ_{l+1} = u_{e(l)}(v)`).

## Main results

* `toricFlag hs v e`: the flag `Y_i = V(⟨ρ_1, …, ρ_i⟩) = D_{ρ_1} ∩ ⋯ ∩ D_{ρ_i}`;
* `mem_toricFlag_iff_chart`, `mem_toricFlag_iff_vertexChart`: `Y_i` in the vertex charts;
* `isSmoothFlag_toricFlag`: `Y•` is a smooth flag (source `def:Okounkov:L170`): each `Y_i` is a
  closed connected complex submanifold of dimension `n - i`;
* `toricFlagGeometry`: `X` with the Kähler form `ω` and the flag `Y•`, as an
  `OriginalFlagGeometry`, and its point `Y_n = {x_v}` (`toricFlagPoint`, the torus fixed point
  `z_v = 0` of `U_v`);
* `isAdaptedFlagCoordinates_toricFlag`: the vertex coordinates `z_{e(0)}, …, z_{e(n-1)}` of
  `U_v` are adapted to the flag at `x_v`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open scoped Topology BigOperators Manifold ContDiff

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### Preliminaries -/

variable (hs) in
/-- The rays of a maximal cone are distinct. -/
theorem polytopeToricRayGenerator_injective (v : latticePolytopeVertices γ) :
    Function.Injective (polytopeToricRayGenerator γ hs v) := by
  intro j j' h
  have h1 := intPairing_basis_rayGenerator γ hs v j j
  rw [h, intPairing_basis_rayGenerator γ hs v j j'] at h1
  by_contra hne
  rw [if_neg hne] at h1
  simp at h1

/-- A set cut out, in the chart at `x` (with target `ℂ^n`), by the vanishing of the
coordinates in `S` is regular of dimension `n - #S` at `x`. -/
theorem regularAtDim_of_chart_coordinates {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {A : Set M} {x : M} (hx : x ∈ A)
    (htarget : (complexChartAt (n := n) x).val.target = univ) (S : Finset (Fin n))
    (hA : ∀ y ∈ (complexChartAt (n := n) x).val.source,
      y ∈ A ↔ ∀ k ∈ S, (complexChartAt (n := n) x).val y k = 0) :
    RegularAtDim (n := n) A x (n - S.card) := by
  classical
  set E := (complexChartAt (n := n) x).val
  set c := E x
  have hc : ∀ k ∈ S, c k = 0 := (hA x (mem_complexChartAt_source x)).mp hx
  set s := S.card
  have hs : s ≤ n := by simpa using Finset.card_le_univ S
  have hcard : Fintype.card {k // k ∈ S} = Fintype.card {j : Fin n // n - s ≤ (j : ℕ)} := by
    rw [Fintype.card_coe, Fintype.card_subtype]
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j : Fin n => (j : ℕ) < n - s)
    have h2 : (Finset.univ.filter fun j : Fin n => (j : ℕ) < n - s).card = n - s := by
      rw [Fin.card_filter_val_lt]; omega
    simp only [Finset.card_univ, Fintype.card_fin, not_lt] at h1
    omega
  let e0 := Fintype.equivOfCardEq hcard
  let τ : Equiv.Perm (Fin n) := e0.extendSubtype
  have hτ : ∀ k, k ∈ S ↔ n - s ≤ (τ k : ℕ) := fun k =>
    ⟨fun hk => e0.extendSubtype_mem k hk, fun h => by
      by_contra hk
      exact e0.extendSubtype_not_mem k hk h⟩
  let Φ : LocalHolomorphicEquivAt (n := n) c :=
    { source := univ
      target := univ
      isOpen_source := isOpen_univ
      isOpen_target := isOpen_univ
      center_mem_source := mem_univ _
      toFun := fun z => coordPerm τ.symm (z - c)
      invFun := fun w => coordPerm τ w + c
      toFun_holomorphic :=
        ((coordPerm τ.symm).differentiable.comp (differentiable_id.sub_const c)).differentiableOn
      invFun_holomorphic := ((coordPerm τ).differentiable.add_const c).differentiableOn
      mapsTo_toFun := fun _ _ => mem_univ _
      mapsTo_invFun := fun _ _ => mem_univ _
      left_inv := fun z _ => by ext k; simp
      right_inv := fun w _ => by ext j; simp }
  refine ⟨Nat.sub_le n s, hx, Φ, by rw [htarget], ?_, ?_⟩
  · change coordPerm τ.symm (c - c) = 0
    rw [sub_self, map_zero]
  · intro y hy _
    rw [hA y hy]
    change (∀ k ∈ S, E y k = 0) ↔ ∀ j : Fin n, n - s ≤ j.1 → (coordPerm τ.symm (E y - c)) j = 0
    constructor
    · intro h j hj
      have hjS : τ.symm j ∈ S := (hτ _).mpr (by simpa using hj)
      simp [h _ hjS, hc _ hjS]
    · intro h k hk
      have := h (τ k) ((hτ k).mp hk)
      simp only [coordPerm_apply, Equiv.symm_apply_apply, PiLp.sub_apply] at this
      rw [hc k hk, sub_zero] at this
      exact this

/-! ### The toric flag -/

variable (hs) in
/-- The rays `ρ_1, …, ρ_i` (`ρ_{l+1} = u_{e(l)}(v)`) of the flag. -/
def toricFlagRays (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) (i : ℕ) :
    Set (PolytopeToricRays γ hs) :=
  (fun l => polytopeToricRay γ hs v (e l)) '' {l | (l : ℕ) < i}

variable (hs) in
/-- Source `subsec:pobtorgeneral`: the toric flag `Y_i = D_{ρ_1} ∩ ⋯ ∩ D_{ρ_i}` of the maximal
cone `σ_v` with the ordering `ρ_{l+1} = u_{e(l)}(v)` of its rays. -/
def toricFlag (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    Set (PolytopeToricVariety γ hs) :=
  toricOrbitClosure (toricFlagRays hs v e i)

variable (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)

/-- `Y_i ∩ U_w`: the rays `ρ_1, …, ρ_i` are rays `u_k(w)` of `σ_w` with vanishing coordinate. -/
theorem mem_toricFlag_iff_chart {w : latticePolytopeVertices γ} {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs w).source) (i : Fin (n + 1)) :
    p ∈ toricFlag hs v e i ↔ ∀ l : Fin n, (l : ℕ) < i → ∃ k,
      polytopeToricRayGenerator γ hs w k = polytopeToricRayGenerator γ hs v (e l) ∧
        originalPolytopeNativeModelChart γ hs w p k = 0 := by
  rw [toricFlag, mem_toricOrbitClosure_iff_chart hp, toricFlagRays, forall_mem_image]
  rfl

/-- `Y_i ∩ U_v = {z_{e(0)} = ⋯ = z_{e(i-1)} = 0}`. -/
theorem mem_toricFlag_iff_vertexChart {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) (i : Fin (n + 1)) :
    p ∈ toricFlag hs v e i ↔ ∀ l : Fin n, (l : ℕ) < i →
      originalPolytopeNativeModelChart γ hs v p (e l) = 0 := by
  rw [mem_toricFlag_iff_chart v e hp]
  refine forall₂_congr fun l _ => ⟨?_, fun h => ⟨e l, rfl, h⟩⟩
  rintro ⟨k, hk, hz⟩
  rwa [polytopeToricRayGenerator_injective hs v hk] at hz

theorem toricFlag_zero : toricFlag hs v e 0 = univ := by
  ext p
  simp [toricFlag, toricOrbitClosure, toricFlagRays]

theorem antitone_toricFlag : Antitone (toricFlag hs v e) := by
  intro i j hij
  apply biInter_subset_biInter_left
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨l, lt_of_lt_of_le hl (Fin.le_def.mp hij), rfl⟩

theorem isClosed_toricFlag (i : Fin (n + 1)) : IsClosed (toricFlag hs v e i) :=
  isClosed_toricOrbitClosure _

/-- The flag rays `ρ_1, …, ρ_i` are rays of `σ_w`. -/
def FlagRaysIn (w : latticePolytopeVertices γ) (i : ℕ) : Prop :=
  ∀ l : Fin n, (l : ℕ) < i → ∃ k,
    polytopeToricRayGenerator γ hs w k = polytopeToricRayGenerator γ hs v (e l)

open Classical in
/-- The coordinates of `U_w` of the flag rays. -/
def flagChartIndices (w : latticePolytopeVertices γ) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun k => ∃ l : Fin n, (l : ℕ) < i ∧
    polytopeToricRayGenerator γ hs w k = polytopeToricRayGenerator γ hs v (e l)

theorem mem_flagChartIndices {w : latticePolytopeVertices γ} {i : ℕ} {k : Fin n} :
    k ∈ flagChartIndices (hs := hs) v e w i ↔ ∃ l : Fin n, (l : ℕ) < i ∧
      polytopeToricRayGenerator γ hs w k = polytopeToricRayGenerator γ hs v (e l) := by
  classical
  simp [flagChartIndices]

theorem flagRaysIn_of_mem {w : latticePolytopeVertices γ} {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs w).source) {i : Fin (n + 1)}
    (hpY : p ∈ toricFlag hs v e i) : FlagRaysIn (hs := hs) v e w i := by
  intro l hl
  obtain ⟨k, hk, -⟩ := (mem_toricFlag_iff_chart v e hp i).mp hpY l hl
  exact ⟨k, hk⟩

theorem mem_toricFlag_iff_flagChartIndices {w : latticePolytopeVertices γ}
    {p : PolytopeToricVariety γ hs} (hp : p ∈ (originalPolytopeNativeModelChart γ hs w).source)
    {i : Fin (n + 1)} (hw : FlagRaysIn (hs := hs) v e w i) :
    p ∈ toricFlag hs v e i ↔ ∀ k ∈ flagChartIndices (hs := hs) v e w i,
      originalPolytopeNativeModelChart γ hs w p k = 0 := by
  rw [mem_toricFlag_iff_chart v e hp]
  constructor
  · intro h k hk
    obtain ⟨l, hl, hkl⟩ := (mem_flagChartIndices v e).mp hk
    obtain ⟨k', hk', hz⟩ := h l hl
    rwa [polytopeToricRayGenerator_injective hs w (hk'.trans hkl.symm)] at hz
  · intro h l hl
    obtain ⟨k, hk⟩ := hw l hl
    exact ⟨k, hk, h k ((mem_flagChartIndices v e).mpr ⟨l, hl, hk⟩)⟩

theorem card_flagChartIndices {w : latticePolytopeVertices γ} {i : Fin (n + 1)}
    (hw : FlagRaysIn (hs := hs) v e w i) :
    (flagChartIndices (hs := hs) v e w i).card = i := by
  classical
  have hcard : (Finset.univ.filter fun l : Fin n => (l : ℕ) < i).card = i := by
    rw [Fin.card_filter_val_lt]; omega
  suffices h : (Finset.univ.filter fun l : Fin n => (l : ℕ) < i).card =
      (flagChartIndices (hs := hs) v e w i).card by rw [← h, hcard]
  refine Finset.card_bij (fun l hl => (hw l (Finset.mem_filter.mp hl).2).choose) ?_ ?_ ?_
  · intro l hl
    exact (mem_flagChartIndices v e).mpr
      ⟨l, (Finset.mem_filter.mp hl).2, (hw l (Finset.mem_filter.mp hl).2).choose_spec⟩
  · intro l hl l' hl' h
    have h1 := (hw l (Finset.mem_filter.mp hl).2).choose_spec
    have h2 := (hw l' (Finset.mem_filter.mp hl').2).choose_spec
    rw [h] at h1
    exact e.injective (polytopeToricRayGenerator_injective hs v (h1.symm.trans h2))
  · intro k hk
    obtain ⟨l, hl, hkl⟩ := (mem_flagChartIndices v e).mp hk
    refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, ?_⟩
    exact polytopeToricRayGenerator_injective hs w
      ((hw l hl).choose_spec.trans hkl.symm)

/-! ### The distinguished point of the orbit `O(τ_i)` -/

variable (hs) in
/-- The point of the vertex chart `U_w` with coordinates `z`. -/
def vertexPoint (w : latticePolytopeVertices γ) (z : ComplexModel n) : PolytopeToricVariety γ hs :=
  (originalPolytopeNativeModelChart γ hs w).symm z

theorem vertexPoint_mem_source (w : latticePolytopeVertices γ) (z : ComplexModel n) :
    vertexPoint hs w z ∈ (originalPolytopeNativeModelChart γ hs w).source :=
  (originalPolytopeNativeModelChart γ hs w).map_target
    (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ _)

theorem chart_vertexPoint (w : latticePolytopeVertices γ) (z : ComplexModel n) :
    originalPolytopeNativeModelChart γ hs w (vertexPoint hs w z) = z :=
  (originalPolytopeNativeModelChart γ hs w).right_inv
    (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ _)

theorem vertexPoint_chart (w : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    vertexPoint hs w (originalPolytopeNativeModelChart γ hs w p) = p :=
  (originalPolytopeNativeModelChart γ hs w).left_inv hp

theorem continuous_vertexPoint (w : latticePolytopeVertices γ) :
    Continuous (vertexPoint hs w) := by
  rw [← continuousOn_univ, ← originalPolytopeNativeModelChart_target γ hs w]
  exact (originalPolytopeNativeModelChart γ hs w).continuousOn_symm


/-- Zeroing the coordinates in `S`. -/
def zeroCoords (S : Finset (Fin n)) (z : ComplexModel n) : ComplexModel n :=
  modelPoint fun k => if k ∈ S then 0 else z k

theorem continuous_zeroCoords (S : Finset (Fin n)) : Continuous (zeroCoords S) := by
  apply continuous_modelPoint.comp
  refine continuous_pi fun k => ?_
  split_ifs
  · exact continuous_const
  · exact (EuclideanSpace.proj (𝕜 := ℂ) k).continuous

/-- The point with coordinates `0` on `S` and `1` elsewhere. -/
def flagModelPoint (S : Finset (Fin n)) : ComplexModel n := zeroCoords S (modelPoint fun _ => 1)

/-- The torus points `λ_u(s)`, `u = u_{ρ_1} + ⋯ + u_{ρ_i}`, converge as `s → 0` to the point
of `U_w` with coordinates `0` on the flag rays and `1` elsewhere, for every `w` containing the
flag rays: these points of the charts are therefore all equal. -/
theorem vertexPoint_flagModelPoint {w : latticePolytopeVertices γ} {i : ℕ}
    (hw : FlagRaysIn (hs := hs) v e w i) :
    vertexPoint hs w (flagModelPoint (flagChartIndices (hs := hs) v e w i)) =
      vertexPoint hs v (flagModelPoint (flagChartIndices (hs := hs) v e v i)) := by
  classical
  let u : Fin n → ℤ := ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < i),
    polytopeToricRayGenerator γ hs v (e l)
  let s : ℕ → ℂˣ := fun N => Units.mk0 ((N + 1 : ℂ)⁻¹) (by
    apply inv_ne_zero; exact_mod_cast Nat.succ_ne_zero N)
  have hs0 : Tendsto (fun N => (s N : ℂ)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
    refine h.congr fun N => ?_
    simp [s, one_div]
  -- the pairing `⟨b_k(w), u⟩`
  have hpair : ∀ (w : latticePolytopeVertices γ), FlagRaysIn (hs := hs) v e w i → ∀ k,
      intPairing (originalPolytopeNativeBasis γ hs w k) u =
        if k ∈ flagChartIndices (hs := hs) v e w i then 1 else 0 := by
    intro w hw k
    simp only [u, intPairing_sum_right]
    have hterm : ∀ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < i),
        intPairing (originalPolytopeNativeBasis γ hs w k) (polytopeToricRayGenerator γ hs v (e l)) =
          if polytopeToricRayGenerator γ hs w k = polytopeToricRayGenerator γ hs v (e l)
          then 1 else 0 := by
      intro l hl
      obtain ⟨k', hk'⟩ := hw l (Finset.mem_filter.mp hl).2
      rw [← hk', intPairing_basis_rayGenerator]
      by_cases hkk : k = k'
      · simp [hkk]
      · rw [if_neg hkk, if_neg ((polytopeToricRayGenerator_injective hs w).ne hkk)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    by_cases hk : k ∈ flagChartIndices (hs := hs) v e w i
    · rw [if_pos hk]
      obtain ⟨l, hl, hkl⟩ := (mem_flagChartIndices v e).mp hk
      have : (Finset.filter (fun l' => polytopeToricRayGenerator γ hs w k =
          polytopeToricRayGenerator γ hs v (e l'))
          (Finset.univ.filter fun l : Fin n => (l : ℕ) < i)) = {l} := by
        ext l'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h'⟩
          exact e.injective (polytopeToricRayGenerator_injective hs v (h'.symm.trans hkl))
        · rintro rfl
          exact ⟨hl, hkl⟩
      rw [this, Finset.card_singleton, Nat.cast_one]
    · rw [if_neg hk]
      have : (Finset.filter (fun l' => polytopeToricRayGenerator γ hs w k =
          polytopeToricRayGenerator γ hs v (e l'))
          (Finset.univ.filter fun l : Fin n => (l : ℕ) < i)) = ∅ := by
        ext l'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and]
        intro hl' h'
        exact hk ((mem_flagChartIndices v e).mpr ⟨l', hl', h'⟩)
      rw [this, Finset.card_empty, Nat.cast_zero]
  have hlim : ∀ (w : latticePolytopeVertices γ), FlagRaysIn (hs := hs) v e w i →
      Tendsto (fun N => polytopeToricEmbedding γ hs (1 * torusCocharacter u (s N))) atTop
        (𝓝 (vertexPoint hs w (flagModelPoint (flagChartIndices (hs := hs) v e w i)))) := by
    intro w hw
    set c := originalPolytopeNativeModelChart γ hs w
    have heq : ∀ N, polytopeToricEmbedding γ hs (1 * torusCocharacter u (s N)) =
        vertexPoint hs w
          (modelPoint fun k => if k ∈ flagChartIndices (hs := hs) v e w i then (s N : ℂ) else 1) := by
      intro N
      have hsrc : polytopeToricEmbedding γ hs (1 * torusCocharacter u (s N)) ∈ c.source := by
        rw [originalPolytopeNativeModelChart_source]
        exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs w _
      rw [← vertexPoint_chart w hsrc, vertexChart_embedding_mul_torusCocharacter hs w]
      congr 1
      ext k
      simp only [modelPoint_apply]
      rw [vertexChart_embedding hs w, modelPoint_apply, map_one, Units.val_one, one_mul, hpair w hw k]
      split_ifs <;> simp
    simp only [heq]
    apply ((continuous_vertexPoint w).tendsto _).comp
    apply (continuous_modelPoint.tendsto _).comp
    rw [tendsto_pi_nhds]
    intro k
    by_cases hk : k ∈ flagChartIndices (hs := hs) v e w i
    · simp only [hk, if_true]; exact hs0
    · simp only [hk, if_false]; exact tendsto_const_nhds
  have hv : FlagRaysIn (hs := hs) v e v i := fun l _ => ⟨e l, rfl⟩
  exact tendsto_nhds_unique (hlim w hw) (hlim v hv)

/-! ### Smoothness of the flag -/

/-- `Y_i` is the union, over the vertices `w` whose cone contains the flag rays, of the
coordinate subspaces `{z_k = 0 : k ∈ S_w}` of the charts `U_w`. -/
theorem toricFlag_eq_iUnion (i : Fin (n + 1)) :
    toricFlag hs v e i = ⋃ w : {w : latticePolytopeVertices γ // FlagRaysIn (hs := hs) v e w i},
      range (fun z => vertexPoint hs w.1 (zeroCoords (flagChartIndices (hs := hs) v e w.1 i) z)) := by
  ext p
  simp only [mem_iUnion, mem_range]
  constructor
  · intro hp
    obtain ⟨w, hw⟩ := originalPolytopeNativeModelChart_cover γ hs p
    have hfl := flagRaysIn_of_mem v e hw hp
    refine ⟨⟨w, hfl⟩, originalPolytopeNativeModelChart γ hs w p, ?_⟩
    have hz := (mem_toricFlag_iff_flagChartIndices v e hw hfl).mp hp
    have hzc : zeroCoords (flagChartIndices (hs := hs) v e w i)
        (originalPolytopeNativeModelChart γ hs w p) = originalPolytopeNativeModelChart γ hs w p := by
      ext k
      simp only [zeroCoords, modelPoint_apply]
      split_ifs with hk
      · exact (hz k hk).symm
      · rfl
    rw [hzc, vertexPoint_chart w hw]
  · rintro ⟨⟨w, hfl⟩, z, rfl⟩
    rw [mem_toricFlag_iff_flagChartIndices v e (vertexPoint_mem_source w _) hfl]
    intro k hk
    rw [chart_vertexPoint]
    change (modelPoint fun k => if k ∈ flagChartIndices (hs := hs) v e w i then 0 else z k) k = 0
    rw [modelPoint_apply, if_pos hk]

/-- `Y_i` is connected: its pieces in the charts `U_w` are connected and all contain the
distinguished point of the orbit `O(τ_i)`. -/
theorem isConnected_toricFlag (i : Fin (n + 1)) : IsConnected (toricFlag hs v e i) := by
  have hv : FlagRaysIn (hs := hs) v e v i := fun l _ => ⟨e l, rfl⟩
  set x0 := vertexPoint hs v (flagModelPoint (flagChartIndices (hs := hs) v e v i))
  rw [toricFlag_eq_iUnion]
  refine ⟨⟨x0, mem_iUnion.mpr ⟨⟨v, hv⟩, modelPoint fun _ => 1, rfl⟩⟩,
    isPreconnected_iUnion ⟨x0, mem_iInter.mpr fun w => ⟨modelPoint fun _ => 1, ?_⟩⟩
      fun w => isPreconnected_range ?_⟩
  · exact vertexPoint_flagModelPoint v e w.2
  · exact (continuous_vertexPoint w.1).comp (continuous_zeroCoords _)

/-- `Y_i` is a complex submanifold of dimension `n - i` at each of its points. -/
theorem regularAtDim_toricFlag (i : Fin (n + 1)) {x : PolytopeToricVariety γ hs}
    (hx : x ∈ toricFlag hs v e i) :
    RegularAtDim (n := n) (toricFlag hs v e i) x (n - i) := by
  set w := (originalPolytopeNativeModelChart_cover γ hs x).choose
  have hw : x ∈ (originalPolytopeNativeModelChart γ hs w).source :=
    (originalPolytopeNativeModelChart_cover γ hs x).choose_spec
  have hfl := flagRaysIn_of_mem v e hw hx
  have h := regularAtDim_of_chart_coordinates (n := n) hx
    (originalPolytopeNativeModelChart_target γ hs w) (flagChartIndices (hs := hs) v e w i)
    (fun y hy => mem_toricFlag_iff_flagChartIndices v e hy hfl)
  rwa [card_flagChartIndices v e hfl] at h

/-- Source `subsec:pobtorgeneral`: `Y•` is a smooth flag (`def:Okounkov:L170`). -/
theorem isSmoothFlag_toricFlag : IsSmoothFlag (toricFlag hs v e) :=
  ⟨toricFlag_zero v e, antitone_toricFlag v e, fun i =>
    ⟨isClosed_toricFlag v e i, isConnected_toricFlag v e i,
      fun _ hx => regularAtDim_toricFlag v e i hx⟩⟩

/-! ### The flag geometry and adapted coordinates -/

/-- The compact connected Kähler manifold `(X, ω)` with the toric flag `Y•`. -/
def toricFlagGeometry : OriginalFlagGeometry n :=
  OriginalFlagGeometry.ofOriginal (polytopeToricKahlerBackground γ hs) (toricFlag hs v e)
    (isSmoothFlag_toricFlag v e)

theorem toricFlagGeometry_flag : (toricFlagGeometry (hs := hs) v e).flag = toricFlag hs v e := rfl

/-- The torus fixed point `x_v` (`z_v = 0`) lies on `Y_n`. -/
theorem vertexPoint_zero_mem_toricFlag (i : Fin (n + 1)) :
    vertexPoint hs v 0 ∈ toricFlag hs v e i := by
  rw [mem_toricFlag_iff_vertexChart v e (vertexPoint_mem_source v 0), chart_vertexPoint]
  intro l _
  rfl

/-- The point `Y_n = {x_v}` of the flag (the torus fixed point `z_v = 0` of `U_v`). -/
def toricFlagPoint : OriginalFlagGermPoint (toricFlagGeometry (hs := hs) v e) :=
  ⟨vertexPoint hs v 0, vertexPoint_zero_mem_toricFlag v e (Fin.last n)⟩

theorem toricFlagPoint_val :
    ((toricFlagPoint (hs := hs) v e).1 : PolytopeToricVariety γ hs) = vertexPoint hs v 0 := rfl

theorem vertexChart_mem_atlas (w : latticePolytopeVertices γ) :
    originalPolytopeNativeModelChart γ hs w ∈ atlas (ComplexModel n) (PolytopeToricVariety γ hs) :=
  ⟨w, rfl⟩

/-- A function holomorphic near `z_w(p)` composed with the chart `z_w` is holomorphic at `p`. -/
theorem holomorphicAt_comp_vertexChart (w : latticePolytopeVertices γ)
    {f : ComplexModel n → ℂ} {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs w).source)
    (hf : ∀ᶠ z in 𝓝 (originalPolytopeNativeModelChart γ hs w p), DifferentiableAt ℂ f z) :
    HolomorphicAt n (fun q : PolytopeToricVariety γ hs => f (originalPolytopeNativeModelChart γ hs w q))
      p := by
  set c := originalPolytopeNativeModelChart γ hs w
  have hT : Tendsto c (𝓝 p) (𝓝 (c p)) := (c.continuousAt hp).tendsto
  filter_upwards [c.open_source.mem_nhds hp, hT.eventually hf] with q hq hfq
  exact (mdifferentiableAt_iff_differentiableAt.mpr hfq).comp q
    (mdifferentiableAt_atlas (vertexChart_mem_atlas w) hq)

/-- Source `prop:toricusualOko` (proof): the vertex coordinates `z_{e(0)}, …, z_{e(n-1)}` of
`U_v` are adapted to the toric flag at `x_v`. -/
theorem isAdaptedFlagCoordinates_toricFlag :
    IsAdaptedFlagCoordinates (toricFlagGeometry (hs := hs) v e) (toricFlagPoint (hs := hs) v e).1
      (fun k p => originalPolytopeNativeModelChart γ hs v p (e k)) := by
  set c := originalPolytopeNativeModelChart γ hs v
  set x0 : PolytopeToricVariety γ hs := vertexPoint hs v 0
  have hx0 : x0 ∈ c.source := vertexPoint_mem_source v 0
  have hcx0 : c x0 = 0 := chart_vertexPoint v 0
  have hTc : Tendsto c (𝓝 x0) (𝓝 0) := by
    have := (c.continuousAt hx0).tendsto
    rwa [hcx0] at this
  have hT : Tendsto (vertexPoint hs v) (𝓝 0) (𝓝 x0) :=
    (continuous_vertexPoint v).tendsto 0
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · change HolomorphicAt n (fun p : PolytopeToricVariety γ hs =>
      (EuclideanSpace.proj (𝕜 := ℂ) (e k)) (c p)) x0
    exact holomorphicAt_comp_vertexChart v hx0
      (Eventually.of_forall fun z => (EuclideanSpace.proj (𝕜 := ℂ) (e k)).differentiableAt)
  · change ∀ᶠ p in 𝓝 x0, p ∈ toricFlag hs v e k.succ → c p (e k) = 0
    filter_upwards [c.open_source.mem_nhds hx0] with p hp hpY
    exact (mem_toricFlag_iff_vertexChart v e hp k.succ).mp hpY k (by simp)
  · intro i h hh hvan
    change ∀ᶠ p in 𝓝 x0, p ∈ toricFlag hs v e i.succ → h p = 0 at hvan
    set S := Finset.univ.filter fun k : Fin n => k ≤ i
    have hG : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => h (vertexPoint hs v z)) z := by
      filter_upwards [hT.eventually hh] with z hz
      have htz : z ∈ c.target := by
        rw [originalPolytopeNativeModelChart_target]; exact mem_univ _
      exact mdifferentiableAt_iff_differentiableAt.mp
        (hz.comp z (mdifferentiableAt_atlas_symm (vertexChart_mem_atlas v) htz))
    have h0 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), (∀ s ∈ S, z (e s) = 0) →
        h (vertexPoint hs v z) = 0 := by
      filter_upwards [hT.eventually hvan] with z hz hzS
      apply hz
      rw [mem_toricFlag_iff_vertexChart v e (vertexPoint_mem_source v z) i.succ, chart_vertexPoint]
      intro l hl
      apply hzS l
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
      simp only [Fin.val_succ] at hl
      omega
    obtain ⟨A, hA, heq⟩ := exists_eq_sum_coord_mul S e hG h0
    refine ⟨fun k p => A k (c p), fun k => ?_, ?_⟩
    · change HolomorphicAt n (fun p : PolytopeToricVariety γ hs => A k (c p)) x0
      apply holomorphicAt_comp_vertexChart v hx0
      rw [hcx0]
      exact hA k
    · change h =ᶠ[𝓝 x0] fun p => ∑ k, if k ≤ i then c p (e k) * A k (c p) else 0
      filter_upwards [c.open_source.mem_nhds hx0, hTc.eventually heq] with p hp hpe
      have h1 : h p = h (vertexPoint hs v (c p)) := by rw [vertexPoint_chart v hp]
      rw [h1, hpe, Finset.sum_filter]

end SGPT.Toric

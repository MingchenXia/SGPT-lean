import SGPT.Foundations.Analysis.Pending.BlowupExistence
import SGPT.Foundations.Analysis.Pending.BlowupKahler
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.RegularAtDimChart
import SGPT.Foundations.Analysis.Pending.LocalDecompositionChart
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents
import SGPT.Okounkov.OriginalFlagGeometry
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The blow-up of a complex manifold at a point and its linear flags

Let `X` be a complex manifold of dimension `n ≥ 1` and `x ∈ X`.  The blow-up
`π : Bl_x X → X` is Demailly's concrete blow-up
`SGPT.Foundations.Analysis.Pending.BlowupConstruction.BlowupSpace n {x}` (it satisfies the
universal property `IsBlowupAlong`, is compact Kähler when `X` is, and connected when `X` is).
A point of `Bl_x X` over `x` is a pair `(x, L)` with `L ⊆ T_xX = ℂⁿ` a complex line (the
tangent space of the centre `{x}` is `0`, `tangentSpace_singleton`), so the exceptional divisor
`E = π⁻¹(x)` is the projective space `ℙ(T_xX)`.

The charts are Demailly's monomial charts `τ̃_j` over a *centred flattening* `Φ` at `x`
(`CentredFlattening`: a local biholomorphic change of the coordinates of the chart at `x` with
`Φ(x) = 0`); a point `(x, ℂξ)` of `E` lies in `τ̃_j` iff `(dΦ ξ)_j ≠ 0`, with coordinates
`w_k = (dΦ ξ)_k / (dΦ ξ)_j`, `w_j = 0`.

For `1 ≤ i ≤ n` let `V_i ⊆ ℂⁿ` be the coordinate subspace `{v | v_0 = ⋯ = v_{i-2} = 0}` (of
dimension `n - i + 1`; `V_1 = ℂⁿ`).  The levels

`Y_i = ℙ(dΦ⁻¹ V_i) = {(x, L) | dΦ(L) ⊆ V_i}`  (`CentredFlattening.level`)

are compact connected complex submanifolds of dimension `n - i`
(`CentredFlattening.isClosedConnectedSubmanifold_level`): in the chart `τ̃_j` (`i ≤ j + 1`) the
level is the coordinate plane `w_j = 0 = w_k (k + 1 < i)`, and it is the image of the unit sphere
of `V_i` under the continuous map `v ↦ (x, ℂ dΦ⁻¹v)`.  For the translated chart at `x`
(`centredFlattening`, `dΦ = id`) this gives the **linear flag**

`Y_0 = Bl_x X ⊇ Y_1 = E ⊇ Y_2 ⊇ ⋯ ⊇ Y_n`,  `Y_i = {(x, L) | L ⊆ V_i} = ℙ(V_i)` (`i ≥ 1`),

a smooth flag (`isSmoothFlag_pointBlowupFlag`).

Main results:

* `pointBlowupFlag`, `isSmoothFlag_pointBlowupFlag`, `pointBlowupFlag_one`
  (`Y_1 = π⁻¹(x)` is the exceptional divisor);
* `pointBlowupFlagGeometry`: for a compact connected Kähler `X` of dimension `m + 1`, the
  blow-up of a point with a Kähler form and the linear flag, as an `OriginalFlagGeometry`;
  `isAnalyticModification_pointBlowupFlagGeometry`: its projection is an analytic modification;
* `exists_flagBearingModification`: **every compact connected Kähler manifold (of any dimension)
  has an analytic modification carrying a Kähler form and a smooth flag** (the geometric input of
  source `eq:DHmgeneral` / `prop:contDH`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace SGPT.Blowup

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.BlowupConstruction
  SGPT.Foundations.Analysis.Pending.BlowupConstruction.BlowupSpace
  SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
  SGPT.Foundations.Analysis.Pending.BlowupSpaceTangent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Okounkov

/-! ### Coordinate subspaces of the model space -/

section Model

variable {n : ℕ}

/-- The coordinate subspace of `ℂⁿ` on which the coordinates indexed by `S` vanish. -/
def coordZeroSet (S : Finset (Fin n)) : Set (ComplexModel n) := {w | ∀ k ∈ S, w k = 0}

/-- A coordinate subspace is a complex submanifold of dimension `n - #S` at each of its
points. -/
theorem regularAtDim_coordZeroSet (S : Finset (Fin n)) {z : ComplexModel n}
    (hz : z ∈ coordZeroSet S) :
    RegularAtDim (n := n) (M := ComplexModel n) (coordZeroSet S) z (n - S.card) := by
  classical
  set s := S.card with hs_def
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
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ τ
  have hL : ∀ (w : ComplexModel n) (i : Fin n), L w i = w (τ.symm i) := fun w i => rfl
  have hLs : ∀ (w : ComplexModel n) (k : Fin n), L.symm w k = w (τ k) := by
    intro w k
    rw [LinearIsometryEquiv.piLpCongrLeft_symm]
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  let Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) z).val z) :=
    { source := univ
      target := univ
      isOpen_source := isOpen_univ
      isOpen_target := isOpen_univ
      center_mem_source := mem_univ _
      toFun := fun w => L (w - z)
      invFun := fun u => L.symm u + z
      toFun_holomorphic :=
        (L.toContinuousLinearEquiv.differentiable.comp
          (differentiable_id.sub_const z)).differentiableOn
      invFun_holomorphic :=
        (L.symm.toContinuousLinearEquiv.differentiable.add_const z).differentiableOn
      mapsTo_toFun := fun _ _ => mem_univ _
      mapsTo_invFun := fun _ _ => mem_univ _
      left_inv := fun w _ => by simp
      right_inv := fun u _ => by simp }
  refine ⟨Nat.sub_le n s, hz, Φ, subset_univ _, ?_, ?_⟩
  · change L (z - z) = 0
    rw [sub_self, map_zero]
  · intro y _ _
    change y ∈ coordZeroSet S ↔ L (y - z) ∈ complexCoordinatePlane n (n - s)
    simp only [coordZeroSet, complexCoordinatePlane, mem_ofPred_eq, hL, PiLp.sub_apply]
    constructor
    · intro h i hi
      have hk : τ.symm i ∈ S := (hτ _).mpr (by simpa using hi)
      rw [h _ hk, hz _ hk, sub_zero]
    · intro h k hk
      have h' := h (τ k) ((hτ k).mp hk)
      rw [Equiv.symm_apply_apply, hz k hk, sub_zero] at h'
      exact h'

end Model

/-! ### The centre `{x}` and Demailly's charts at `x` -/

section Point

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A point is a closed complex submanifold (of dimension `0`). -/
instance factIsClosedSubmanifold_singleton (x : X) :
    Fact (IsClosedSubmanifold n ({x} : Set X)) :=
  ⟨⟨isClosed_singleton, fun y hy =>
    ⟨0, (DominationLogResolution.isClosedConnectedSubmanifold_singleton x).2.2 y hy⟩⟩⟩

/-- In positive dimension a point is nowhere dense. -/
theorem interior_singleton_eq_empty [NeZero n] (x : X) : interior ({x} : Set X) = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  have hyx : y = x := mem_singleton_iff.mp (interior_subset hy)
  subst hyx
  have hopen : IsOpen ({y} : Set X) := by
    have h : interior ({y} : Set X) = {y} :=
      Subset.antisymm interior_subset (singleton_subset_iff.mpr hy)
    exact h ▸ isOpen_interior
  have him := (chartAt (ComplexModel n) y).isOpen_image_of_subset_source hopen
    (singleton_subset_iff.mpr (mem_chart_source _ y))
  rw [image_singleton] at him
  exact not_isOpen_singleton _ him

variable (n) in
/-- The blow-up of `X` at the point `x` (Demailly's construction). -/
abbrev PointBlowup (x : X) : Type u := BlowupSpace n ({x} : Set X)

/-- The blow-up of a point of a positive-dimensional manifold satisfies the universal property
of the blow-up. -/
theorem isBlowupAlong_pointBlowup [NeZero n] (x : X) :
    IsBlowupAlong n ({x} : Set X) (blowupProj n ({x} : Set X)) :=
  isBlowupAlong_blowupProj (interior_singleton_eq_empty (n := n) x)

/-- The preferred chart at `x`, translated so that `x` sits at the origin. -/
def centredChart (x : X) : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) where
  source := (chartAt (ComplexModel n) x).target
  target := (fun w => w + chartAt (ComplexModel n) x x) ⁻¹' (chartAt (ComplexModel n) x).target
  isOpen_source := (chartAt (ComplexModel n) x).open_target
  isOpen_target :=
    (chartAt (ComplexModel n) x).open_target.preimage (continuous_id.add continuous_const)
  center_mem_source := (chartAt (ComplexModel n) x).map_source (mem_chart_source _ x)
  toFun z := z - chartAt (ComplexModel n) x x
  invFun w := w + chartAt (ComplexModel n) x x
  toFun_holomorphic := (differentiable_id.sub_const _).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const _).differentiableOn
  mapsTo_toFun z hz := by simpa only [mem_preimage, sub_add_cancel] using hz
  mapsTo_invFun _ hw := hw
  left_inv z _ := sub_add_cancel z _
  right_inv w _ := add_sub_cancel_right w _

/-! ### Centred flattenings and their monomial charts -/

variable (n) in
/-- A local biholomorphic change `Φ` of the coordinates of the preferred chart at `x` with
`Φ(e_x(x)) = 0`. -/
structure CentredFlattening (x : X) where
  Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)
  source_subset : Φ.source ⊆ (chartAt (ComplexModel n) x).target
  map_centre : Φ.toFun (chartAt (ComplexModel n) x x) = 0

namespace CentredFlattening

variable {x : X} (P : CentredFlattening n x)

/-- A centred flattening flattens the point `x` to the origin. -/
theorem flat {y : X} (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hyΦ : chartAt (ComplexModel n) x y ∈ P.Φ.source) :
    (y ∈ ({x} : Set X) ↔ P.Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n 0) := by
  have hplane : ∀ w : ComplexModel n, w ∈ complexCoordinatePlane n 0 ↔ w = 0 := by
    intro w
    simp only [complexCoordinatePlane, mem_ofPred_eq, zero_le, true_implies]
    constructor
    · intro h
      ext i
      exact h i
    · rintro rfl i
      rfl
  rw [hplane, mem_singleton_iff]
  constructor
  · rintro rfl
    exact P.map_centre
  · intro h
    have he : chartAt (ComplexModel n) x y = chartAt (ComplexModel n) x x := by
      rw [← P.Φ.left_inv _ hyΦ, h, ← P.map_centre, P.Φ.left_inv _ P.Φ.center_mem_source]
    exact (chartAt (ComplexModel n) x).injOn hy (mem_chart_source _ x) he

/-- Demailly's `j`-th monomial chart of the point blow-up over the centred flattening `P`. -/
def chart (j : Fin n) : FlatChart n ({x} : Set X) where
  y₀ := x
  k := 0
  Φ := P.Φ
  hsrc := P.source_subset
  hflat := fun hy hyΦ => P.flat hy hyΦ
  j := j
  hj := Nat.zero_le _

@[simp] theorem chart_j (j : Fin n) : (P.chart j).j = j := rfl
@[simp] theorem chart_k (j : Fin n) : (P.chart j).k = 0 := rfl

theorem chart_τ (j i : Fin n) (y : X) :
    (P.chart j).τ i y = P.Φ.toFun (chartAt (ComplexModel n) x y) i := rfl

theorem chart_τ_self (j i : Fin n) : (P.chart j).τ i x = 0 := by
  rw [chart_τ, P.map_centre]
  rfl

theorem mem_dom (j : Fin n) : x ∈ (P.chart j).dom := mem_flatDomain_self _

/-- The differential `dΦ` at `x`, read in the preferred chart at `x`. -/
def deriv : ComplexModel n →L[ℂ] ComplexModel n :=
  fderiv ℂ (flatMap P.Φ x) (chartAt (ComplexModel n) x x)

theorem germDiff_coord (j i : Fin n) (ξ : ComplexModel n) :
    germDiff n ((P.chart j).τ i) x ξ = P.deriv ξ i := by
  have h := germDiff_flatCoord (Φ := P.Φ) P.source_subset (mem_flatDomain_self P.Φ) i
  change germDiff n (flatCoord P.Φ i) x ξ = _
  rw [h]
  rfl

theorem deriv_surjective : Function.Surjective P.deriv := fun v =>
  ⟨flatVec P.Φ x v, fderiv_flatMap_flatVec P.source_subset (mem_flatDomain_self P.Φ) v⟩

theorem deriv_injective : Function.Injective P.deriv := by
  have h := LinearMap.injective_iff_surjective (f := (P.deriv : ComplexModel n →ₗ[ℂ] ComplexModel n))
  exact h.mpr P.deriv_surjective

/-- `dΦ` as a continuous linear equivalence. -/
def derivEquiv : ComplexModel n ≃L[ℂ] ComplexModel n :=
  (LinearEquiv.ofBijective (P.deriv : ComplexModel n →ₗ[ℂ] ComplexModel n)
    ⟨P.deriv_injective, P.deriv_surjective⟩).toContinuousLinearEquiv

@[simp] theorem derivEquiv_apply (ξ : ComplexModel n) : P.derivEquiv ξ = P.deriv ξ := rfl

end CentredFlattening

/-- The translated chart at `x` as a centred flattening. -/
def centredFlattening (x : X) : CentredFlattening n x where
  Φ := centredChart x
  source_subset := subset_rfl
  map_centre := sub_self _

/-- In the translated chart `dΦ` is the identity. -/
theorem deriv_centredFlattening (x : X) :
    (centredFlattening (n := n) x).deriv = ContinuousLinearMap.id ℂ (ComplexModel n) := by
  unfold CentredFlattening.deriv
  have hev : flatMap (centredFlattening (n := n) x).Φ x
      =ᶠ[𝓝 (chartAt (ComplexModel n) x x)] fun z => z - chartAt (ComplexModel n) x x := by
    filter_upwards [(chartAt (ComplexModel n) x).open_target.mem_nhds
      ((chartAt (ComplexModel n) x).map_source (mem_chart_source _ x))] with z hz
    show chartAt (ComplexModel n) x ((chartAt (ComplexModel n) x).symm z) -
      chartAt (ComplexModel n) x x = _
    rw [(chartAt (ComplexModel n) x).right_inv hz]
  rw [hev.fderiv_eq]
  exact ((hasFDerivAt_id (chartAt (ComplexModel n) x x)).sub_const _).fderiv

/-- **The tangent space of a point is zero.** -/
theorem tangentSpace_singleton (x : X) : tangentSpace n ({x} : Set X) x = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun ξ hξ => ?_
  set P := centredFlattening (n := n) x
  rw [mem_tangentSpace_iff (Φ := P.Φ) P.source_subset (fun hy hyΦ => P.flat hy hyΦ)
    (mem_flatDomain_self _) (mem_singleton x)] at hξ
  apply P.deriv_injective
  rw [map_zero]
  ext i
  have hi := hξ i (Nat.zero_le _)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact i.elim0
  have j : Fin n := ⟨0, hn⟩
  have h' := P.germDiff_coord j i ξ
  change germDiff n ((P.chart j).τ i) x ξ = 0 at hi
  rw [h'] at hi
  exact hi

/-! ### Points over `x` -/

variable {x : X}

theorem mem_singleton_of_base_eq {p : PointBlowup n x} (hp : p.base = x) :
    p.base ∈ ({x} : Set X) := hp

/-- Over `x` the direction is the line spanned by the chosen generator. -/
theorem dir_eq_span {p : PointBlowup n x} (hp : p.base = x) : p.dir = ℂ ∙ p.dirVec := by
  rw [dir_eq_sup_dirVec (mem_singleton_of_base_eq hp), hp, tangentSpace_singleton, bot_sup_eq]

theorem dirVec_ne_zero {p : PointBlowup n x} (hp : p.base = x) : p.dirVec ≠ 0 := by
  have h := dirVec_not_mem (mem_singleton_of_base_eq hp)
  rw [hp, tangentSpace_singleton] at h
  simpa using h

theorem dirVec_mem_dir {p : PointBlowup n x} (hp : p.base = x) : p.dirVec ∈ p.dir := by
  rw [dir_eq_span hp]
  exact Submodule.mem_span_singleton_self _

theorem dir_le_iff {p : PointBlowup n x} (hp : p.base = x) (V : Submodule ℂ (ComplexModel n)) :
    p.dir ≤ V ↔ p.dirVec ∈ V := by
  rw [dir_eq_span hp, Submodule.span_singleton_le_iff_mem]

namespace CentredFlattening

variable (P : CentredFlattening n x)

/-! #### Points over `x` -/

theorem extVal_coord (j k : Fin n) {p : PointBlowup n x} (hp : p.base = x) :
    extVal ((P.chart j).τ k) p = P.deriv p.dirVec k := by
  rw [extVal_of_mem (mem_singleton_of_base_eq hp), hp, P.germDiff_coord]

theorem mem_source_iff (j : Fin n) {p : PointBlowup n x} (hp : p.base = x) :
    p ∈ (P.chart j).source ↔ P.deriv p.dirVec j ≠ 0 := by
  constructor
  · intro h
    have h2 : extVal ((P.chart j).τ j) p ≠ 0 := h.2
    rwa [P.extVal_coord j j hp] at h2
  · intro h
    refine ⟨by rw [hp]; exact P.mem_dom j, ?_⟩
    show extVal ((P.chart j).τ j) p ≠ 0
    rw [P.extVal_coord j j hp]
    exact h

theorem toFun_self (j : Fin n) (p : PointBlowup n x) (hp : p.base = x) :
    (P.chart j).toFun p j = 0 := by
  have h := FlatChart.toFun_apply_j (P.chart j) p
  simp only [chart_j] at h
  rw [h, hp]
  exact P.chart_τ_self j j

theorem toFun_ne (j : Fin n) {k : Fin n} (hkj : k ≠ j) (p : PointBlowup n x) (hp : p.base = x) :
    (P.chart j).toFun p k = P.deriv p.dirVec k / P.deriv p.dirVec j := by
  have h := FlatChart.toFun_apply_normal (P.chart j) p (i := k) (Nat.zero_le _) hkj
  simp only [chart_j] at h
  rw [h, P.extVal_coord j k hp, P.extVal_coord j j hp]

/-- Off `x`, the chart is the monomial relation `σ_j(w) = Φ(e_x(π q))`: in particular
`Φ(e_x(π q))_k = w_k w_j` for `k ≠ j`. -/
theorem flat_base_ne (j : Fin n) {k : Fin n} (hkj : k ≠ j) {q : PointBlowup n x}
    (hq : q ∈ (P.chart j).source) :
    P.Φ.toFun (chartAt (ComplexModel n) x q.base) k =
      (P.chart j).toFun q k * (P.chart j).toFun q j := by
  have h := congrArg (fun w : ComplexModel n => w k) ((P.chart j).monomial_toFun hq)
  simp only [BlowupMonomialCharts.monomial_apply, chart_k, chart_j, zero_le, ne_eq, hkj,
    not_false_eq_true, and_self, if_true] at h
  exact h.symm

theorem chartComplex_mem (j : Fin n) :
    (P.chart j).homeo ∈ atlas (ComplexModel n) (PointBlowup n x) :=
  atlasHomeo_mem_atlas _ _

/-- The monomial chart as a chart of the atlas. -/
def complexChart (j : Fin n) : ComplexChart n (PointBlowup n x) :=
  ⟨(P.chart j).homeo, P.chartComplex_mem j⟩

end CentredFlattening

end Point

/-! ### The linear flag in the exceptional divisor -/

section Levels

variable {n : ℕ}

/-- The coordinate subspace `V_i = {v | v_k = 0 for k + 1 < i}` of `ℂⁿ` (`V_0 = V_1 = ℂⁿ`). -/
def flagSubspace (n i : ℕ) : Submodule ℂ (ComplexModel n) where
  carrier := {v | ∀ k : Fin n, k.1 + 1 < i → v k = 0}
  add_mem' {v w} hv hw k hk := by
    simp only [PiLp.add_apply, hv k hk, hw k hk, add_zero]
  zero_mem' k _ := rfl
  smul_mem' c v hv k hk := by
    simp only [PiLp.smul_apply, hv k hk, smul_zero]

theorem mem_flagSubspace {i : ℕ} {v : ComplexModel n} :
    v ∈ flagSubspace n i ↔ ∀ k : Fin n, k.1 + 1 < i → v k = 0 := Iff.rfl

theorem flagSubspace_antitone {i i' : ℕ} (h : i ≤ i') : flagSubspace n i' ≤ flagSubspace n i :=
  fun _ hv k hk => hv k (lt_of_lt_of_le hk h)

theorem flagSubspace_one : flagSubspace n 1 = ⊤ := by
  refine eq_top_iff.mpr fun v _ k hk => ?_
  omega

/-- The zero pattern of `Y_i` in the `j`-th monomial chart: `w_j = 0` and `w_k = 0` for
`k + 1 < i`. -/
def levelZeroSet (i : ℕ) (j : Fin n) : Finset (Fin n) :=
  insert j (Finset.univ.filter fun k : Fin n => k.1 + 1 < i)

theorem card_levelZeroSet {i : ℕ} (hi0 : i ≠ 0) (hin : i ≤ n) {j : Fin n} (hj : i ≤ j.1 + 1) :
    (levelZeroSet i j).card = i := by
  classical
  have hnot : j ∉ Finset.univ.filter fun k : Fin n => k.1 + 1 < i := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact hj
  rw [levelZeroSet, Finset.card_insert_of_notMem hnot]
  have hfilter : (Finset.univ.filter fun k : Fin n => k.1 + 1 < i) =
      Finset.univ.filter fun k : Fin n => k.1 < i - 1 := by
    apply Finset.filter_congr
    intro k _
    omega
  rw [hfilter, Fin.card_filter_val_lt]
  omega

end Levels

section Flag

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {x : X}

namespace CentredFlattening

variable (P : CentredFlattening n x)

/-- The level `ℙ(dΦ⁻¹ V_i) = {(x, L) | dΦ(L) ⊆ V_i}` of the exceptional divisor. -/
def level (i : ℕ) : Set (PointBlowup n x) :=
  {q | q.base = x ∧ q.dir ≤ (flagSubspace n i).comap (P.deriv : ComplexModel n →ₗ[ℂ] ComplexModel n)}

theorem mem_level_iff {i : ℕ} {q : PointBlowup n x} :
    q ∈ P.level i ↔ q.base = x ∧ P.deriv q.dirVec ∈ flagSubspace n i := by
  constructor
  · rintro ⟨hb, hd⟩
    exact ⟨hb, (dir_le_iff hb _).mp hd⟩
  · rintro ⟨hb, hd⟩
    exact ⟨hb, (dir_le_iff hb _).mpr hd⟩

theorem level_antitone {i i' : ℕ} (h : i ≤ i') : P.level i' ⊆ P.level i := fun _ hq =>
  ⟨hq.1, hq.2.trans (Submodule.comap_mono (flagSubspace_antitone h))⟩

/-- `ℙ(dΦ⁻¹ V_i)` in the chart `τ̃_j` (`i ≤ j + 1`): the coordinates `w_j` and `w_k` (`k + 1 < i`)
vanish. -/
theorem mem_level_iff_chart {i : ℕ} {j : Fin n} (hj : i ≤ j.1 + 1) {q : PointBlowup n x}
    (hq : q ∈ (P.chart j).source) :
    q ∈ P.level i ↔ (P.chart j).toFun q ∈ coordZeroSet (levelZeroSet i j) := by
  rw [P.mem_level_iff]
  constructor
  · rintro ⟨hb, hd⟩ k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact P.toFun_self k q hb
    · have hk' : k.1 + 1 < i := (Finset.mem_filter.mp hk).2
      have hkj : k ≠ j := by
        rintro rfl
        omega
      rw [P.toFun_ne j hkj q hb, (mem_flagSubspace.mp hd) k hk', zero_div]
  · intro h
    have hj0 : (P.chart j).toFun q j = 0 := h j (Finset.mem_insert_self _ _)
    have hbC : q.base ∈ ({x} : Set X) := by
      have h' := FlatChart.toFun_j_eq_zero_iff (P.chart j) hq
      simp only [chart_j] at h'
      exact h'.mp hj0
    have hb : q.base = x := hbC
    refine ⟨hb, mem_flagSubspace.mpr fun k hk => ?_⟩
    have hkj : k ≠ j := by
      rintro rfl
      omega
    have hk0 := h k (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩))
    rw [P.toFun_ne j hkj q hb] at hk0
    have hjne : P.deriv q.dirVec j ≠ 0 := (P.mem_source_iff j hb).mp hq
    exact (div_eq_zero_iff.mp hk0).resolve_right hjne

/-- `ℙ(dΦ⁻¹ V_i)` is a complex submanifold of dimension `n - i` at each of its points. -/
theorem regularAtDim_level {i : ℕ} (hi0 : i ≠ 0) (hin : i ≤ n) {p : PointBlowup n x}
    (hp : p ∈ P.level i) : RegularAtDim (n := n) (P.level i) p (n - i) := by
  obtain ⟨hb, hd⟩ := P.mem_level_iff.mp hp
  have hne : P.deriv p.dirVec ≠ 0 := fun h =>
    dirVec_ne_zero hb (P.deriv_injective (by rw [h, map_zero]))
  obtain ⟨j, hj⟩ : ∃ j : Fin n, P.deriv p.dirVec j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by ext k; exact h k)
  have hji : i ≤ j.1 + 1 := by
    by_contra h
    exact hj ((mem_flagSubspace.mp hd) j (by omega))
  have hpc : p ∈ (P.chart j).source := (P.mem_source_iff j hb).mpr hj
  set e := P.complexChart j with he
  have hep : ∀ q, e.val q = (P.chart j).toFun q := fun _ => rfl
  have hpe : p ∈ e.val.source := hpc
  have hcard := card_levelZeroSet hi0 hin hji
  have h1 : RegularAtDim (n := n) (M := ComplexModel n)
      (coordZeroSet (levelZeroSet i j) ∩ e.val.target) (e.val p) (n - i) := by
    refine (AnalyticLocalStatement.LocalDecomposition.regularAtDim_inter_open_iff
      e.val.open_target (e.val.map_source hpe)).mpr ?_
    have h0 := regularAtDim_coordZeroSet _ ((P.mem_level_iff_chart hji hpc).mp hp)
    rw [hcard] at h0
    exact h0
  have h2 := (RegularAtDimChart.regularAtDim_chart_iff e (coordZeroSet (levelZeroSet i j))
    hpe).mpr h1
  refine RegularPointDimension.regularAtDim_of_inter_eq e.val.open_source hpe ?_ h2
  ext q
  constructor
  · rintro ⟨⟨hqs, hqS⟩, -⟩
    refine ⟨(P.mem_level_iff_chart hji hqs).mpr ?_, hqs⟩
    rw [← hep]
    exact hqS
  · rintro ⟨hqY, hqs⟩
    refine ⟨⟨hqs, ?_⟩, hqs⟩
    show e.val q ∈ coordZeroSet (levelZeroSet i j)
    rw [hep]
    exact (P.mem_level_iff_chart hji hqs).mp hqY

end CentredFlattening

end Flag

/-! ### The levels are compact and connected -/

section Lines

variable {n : ℕ} [NeZero n] {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {x : X}

omit [NeZero n] in
theorem not_mem_tangentSpace_of_ne_zero {v : ComplexModel n} (hv : v ≠ 0) :
    v ∉ tangentSpace n ({x} : Set X) x := by
  rw [tangentSpace_singleton]
  simpa using hv

variable (x) in
/-- The point `(x, ℂv)` of the exceptional divisor (a fixed point for `v = 0`). -/
def linePoint (v : ComplexModel n) : PointBlowup n x :=
  if hv : v = 0 then ((centredFlattening (n := n) x).chart ⟨0, NeZero.pos n⟩).junk
  else excPoint x (mem_singleton x) v (not_mem_tangentSpace_of_ne_zero hv)

theorem linePoint_of_ne_zero {v : ComplexModel n} (hv : v ≠ 0) :
    linePoint x v = excPoint x (mem_singleton x) v (not_mem_tangentSpace_of_ne_zero hv) :=
  dif_neg hv

theorem base_linePoint {v : ComplexModel n} (hv : v ≠ 0) : (linePoint x v).base = x := by
  rw [linePoint_of_ne_zero hv]
  rfl

theorem dir_linePoint {v : ComplexModel n} (hv : v ≠ 0) : (linePoint x v).dir = ℂ ∙ v := by
  rw [linePoint_of_ne_zero hv]
  show tangentSpace n ({x} : Set X) x ⊔ ℂ ∙ v = ℂ ∙ v
  rw [tangentSpace_singleton, bot_sup_eq]

/-- The direction vector of `(x, ℂv)` is a nonzero multiple of `v`. -/
theorem exists_dirVec_linePoint {v : ComplexModel n} (hv : v ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ (linePoint x v).dirVec = a • v := by
  have hmem := dirVec_mem_dir (base_linePoint (x := x) hv)
  rw [dir_linePoint hv, Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, ?_, ha.symm⟩
  rintro rfl
  exact dirVec_ne_zero (base_linePoint (x := x) hv) (by rw [← ha, zero_smul])

omit [NeZero n] in
/-- The coordinates `u(v) = v_j⁻¹ (v - v_j e_j)` of `(x, ℂv)` in the chart `τ̃_j`. -/
def lineCoord (j : Fin n) (v : ComplexModel n) : ComplexModel n :=
  (v j)⁻¹ • (v - v j • EuclideanSpace.single j (1 : ℂ))

omit [NeZero n] in
theorem lineCoord_apply_self (j : Fin n) (v : ComplexModel n) : lineCoord j v j = 0 := by
  simp [lineCoord]

omit [NeZero n] in
theorem lineCoord_apply_ne {j k : Fin n} (hkj : k ≠ j) (v : ComplexModel n) :
    lineCoord j v k = v k / v j := by
  simp [lineCoord, hkj, div_eq_inv_mul]

omit [NeZero n] in
theorem continuousAt_lineCoord {j : Fin n} {v : ComplexModel n} (hvj : v j ≠ 0) :
    ContinuousAt (lineCoord j) v := by
  have hp : Continuous fun w : ComplexModel n => w j :=
    (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous
  unfold lineCoord
  exact ((hp.continuousAt).inv₀ hvj).smul
    (continuousAt_id.sub (hp.continuousAt.smul continuousAt_const))

namespace CentredFlattening

variable (P : CentredFlattening n x)

theorem linePoint_mem_source {j : Fin n} {v : ComplexModel n} (hvj : P.deriv v j ≠ 0) :
    linePoint x v ∈ (P.chart j).source := by
  have hv : v ≠ 0 := fun h => hvj (by rw [h, map_zero]; rfl)
  obtain ⟨a, ha, hav⟩ := exists_dirVec_linePoint (x := x) hv
  rw [P.mem_source_iff j (base_linePoint hv), hav, map_smul]
  simpa using And.intro ha hvj

theorem toFun_linePoint {j : Fin n} {v : ComplexModel n} (hvj : P.deriv v j ≠ 0) :
    (P.chart j).toFun (linePoint x v) = lineCoord j (P.deriv v) := by
  have hv : v ≠ 0 := fun h => hvj (by rw [h, map_zero]; rfl)
  obtain ⟨a, ha, hav⟩ := exists_dirVec_linePoint (x := x) hv
  ext k
  by_cases hkj : k = j
  · subst hkj
    rw [P.toFun_self k _ (base_linePoint hv), lineCoord_apply_self]
  · rw [P.toFun_ne j hkj _ (base_linePoint hv), lineCoord_apply_ne hkj, hav, map_smul]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ ha]

theorem linePoint_eq_symm {j : Fin n} {v : ComplexModel n} (hvj : P.deriv v j ≠ 0) :
    linePoint x v = (P.chart j).homeo.symm (lineCoord j (P.deriv v)) := by
  rw [← P.toFun_linePoint hvj]
  exact ((P.chart j).left_inv (P.linePoint_mem_source hvj)).symm

end CentredFlattening

/-- `v ↦ (x, ℂv)` is continuous on `ℂⁿ \ {0}`. -/
theorem continuousOn_linePoint : ContinuousOn (linePoint x) {v : ComplexModel n | v ≠ 0} := by
  intro v₀ hv₀
  set P := centredFlattening (n := n) x
  have hD₀ : P.deriv v₀ ≠ 0 := fun h => hv₀ (P.deriv_injective (by rw [h, map_zero]))
  obtain ⟨j, hj⟩ : ∃ j : Fin n, P.deriv v₀ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hD₀ (by ext k; exact h k)
  refine ContinuousAt.continuousWithinAt ?_
  have hcD : Continuous fun v : ComplexModel n => P.deriv v j :=
    (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.comp P.deriv.continuous
  have hopen : IsOpen {v : ComplexModel n | P.deriv v j ≠ 0} :=
    isOpen_ne_fun hcD continuous_const
  have hev : (P.chart j).homeo.symm ∘ (lineCoord j ∘ P.deriv) =ᶠ[𝓝 v₀] linePoint x := by
    filter_upwards [hopen.mem_nhds hj] with v hv
    exact (P.linePoint_eq_symm hv).symm
  have htarget : lineCoord j (P.deriv v₀) ∈ (P.chart j).homeo.target := by
    rw [← P.toFun_linePoint hj]
    exact (P.chart j).map_source (P.linePoint_mem_source hj)
  have hcomp : ContinuousAt (lineCoord j ∘ P.deriv) v₀ :=
    ContinuousAt.comp (g := lineCoord j) (continuousAt_lineCoord hj)
      P.deriv.continuous.continuousAt
  have hfin : ContinuousAt ((P.chart j).homeo.symm ∘ (lineCoord j ∘ P.deriv)) v₀ :=
    ContinuousAt.comp (f := lineCoord j ∘ P.deriv) (x := v₀)
      ((P.chart j).homeo.continuousAt_symm htarget) hcomp
  exact hfin.congr hev

omit [NeZero n] in
/-- The space `V_i` has real dimension `> 1` (`i ≤ n`, `n ≥ 1`). -/
theorem one_lt_rank_flagSubspace [NeZero n] {i : ℕ} (hin : i ≤ n) :
    1 < Module.rank ℝ (flagSubspace n i) := by
  have hl : n - 1 < n := Nat.sub_lt (NeZero.pos n) one_pos
  set l : Fin n := ⟨n - 1, hl⟩
  have hmem : EuclideanSpace.single l (1 : ℂ) ∈ flagSubspace n i := by
    intro k hk
    have hkl : k ≠ l := by
      intro h
      have : k.1 = n - 1 := congrArg Fin.val h
      omega
    simp [hkl]
  have : Nontrivial (flagSubspace n i) :=
    ⟨⟨⟨_, hmem⟩, 0, fun h => by
      have h' := congrArg (fun w : flagSubspace n i => (w : ComplexModel n) l) h
      simp at h'⟩⟩
  rw [rank_real_of_complex]
  have h1 : 1 ≤ Module.rank ℂ (flagSubspace n i) := Cardinal.one_le_iff_pos.mpr rank_pos
  calc (1 : Cardinal) < 2 := Cardinal.one_lt_two
    _ = 2 * 1 := (mul_one 2).symm
    _ ≤ 2 * Module.rank ℂ (flagSubspace n i) := mul_le_mul' le_rfl h1

omit [NeZero n] in
theorem isConnected_flagSubspace_sphere [NeZero n] {i : ℕ} (hin : i ≤ n) :
    IsConnected ((flagSubspace n i : Set (ComplexModel n)) ∩ sphere 0 1) := by
  have hc := isConnected_sphere (one_lt_rank_flagSubspace hin) (0 : flagSubspace n i) zero_le_one
  have himg : ((flagSubspace n i : Set (ComplexModel n)) ∩ sphere 0 1) =
      (Subtype.val : flagSubspace n i → ComplexModel n) '' sphere 0 1 := by
    ext v
    constructor
    · rintro ⟨hv, hvs⟩
      refine ⟨⟨v, hv⟩, ?_, rfl⟩
      simpa [mem_sphere_zero_iff_norm] using hvs
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      simpa [mem_sphere_zero_iff_norm] using hw
  rw [himg]
  exact hc.image _ continuous_subtype_val.continuousOn

omit [NeZero n] in
theorem isCompact_flagSubspace_sphere (i : ℕ) :
    IsCompact ((flagSubspace n i : Set (ComplexModel n)) ∩ sphere 0 1) :=
  (isCompact_sphere 0 1).inter_left (Submodule.closed_of_finiteDimensional _)

theorem ne_zero_of_mem_flagSubspace_sphere {i : ℕ} {v : ComplexModel n}
    (hv : v ∈ (flagSubspace n i : Set (ComplexModel n)) ∩ sphere 0 1) : v ≠ 0 := by
  rintro rfl
  simp at hv

namespace CentredFlattening

variable (P : CentredFlattening n x)

/-- `ℙ(dΦ⁻¹ V_i)` is the image of the unit sphere of `V_i` under `v ↦ (x, ℂ dΦ⁻¹v)`. -/
theorem level_eq_image (i : ℕ) :
    P.level i = (linePoint x ∘ P.derivEquiv.symm) ''
      ((flagSubspace n i : Set (ComplexModel n)) ∩ sphere 0 1) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hb, hd⟩ := P.mem_level_iff.mp hp
    set ξ := P.deriv p.dirVec with hξ
    have hne : ξ ≠ 0 := fun h =>
      dirVec_ne_zero hb (P.deriv_injective (by rw [← hξ, h, map_zero]))
    have hnorm : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    set c : ℂ := ((‖ξ‖⁻¹ : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact_mod_cast inv_ne_zero hnorm
    have hsymm : P.derivEquiv.symm (c • ξ) = c • p.dirVec := by
      rw [map_smul, hξ, ← P.derivEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
    have hcv : c • p.dirVec ≠ 0 := smul_ne_zero hc0 (dirVec_ne_zero hb)
    refine ⟨c • ξ, ⟨(flagSubspace n i).smul_mem c hd, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hnorm]
    · rw [Function.comp_apply, hsymm]
      refine BlowupSpace.ext (base_linePoint hcv |>.trans hb.symm) ?_
      rw [dir_linePoint hcv, dir_eq_span hb, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0)]
  · rintro ⟨v, ⟨hvV, hvs⟩, rfl⟩
    have hv : v ≠ 0 := ne_zero_of_mem_flagSubspace_sphere (i := i) ⟨hvV, hvs⟩
    have hv' : P.derivEquiv.symm v ≠ 0 := by
      intro h
      apply hv
      rw [← P.derivEquiv.apply_symm_apply v, h, map_zero]
    refine ⟨base_linePoint hv', ?_⟩
    rw [Function.comp_apply, dir_linePoint hv', Submodule.span_singleton_le_iff_mem,
      Submodule.mem_comap]
    have : P.deriv (P.derivEquiv.symm v) = v := by
      rw [← P.derivEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
    simpa [this] using hvV

theorem continuousOn_linePoint_comp :
    ContinuousOn (linePoint x ∘ P.derivEquiv.symm) {v : ComplexModel n | v ≠ 0} := by
  refine continuousOn_linePoint.comp P.derivEquiv.symm.continuous.continuousOn fun v hv => ?_
  intro h
  apply hv
  rw [← P.derivEquiv.apply_symm_apply v, h, map_zero]

theorem isCompact_level (i : ℕ) : IsCompact (P.level i) := by
  rw [P.level_eq_image]
  exact (isCompact_flagSubspace_sphere i).image_of_continuousOn
    (P.continuousOn_linePoint_comp.mono fun _ hv => ne_zero_of_mem_flagSubspace_sphere hv)

theorem isConnected_level {i : ℕ} (hin : i ≤ n) : IsConnected (P.level i) := by
  rw [P.level_eq_image]
  exact (isConnected_flagSubspace_sphere hin).image _
    (P.continuousOn_linePoint_comp.mono fun _ hv => ne_zero_of_mem_flagSubspace_sphere hv)

/-- `ℙ(dΦ⁻¹ V_i)` is a compact connected complex submanifold of dimension `n - i`. -/
theorem isClosedConnectedSubmanifold_level {i : ℕ} (hi0 : i ≠ 0) (hin : i ≤ n) :
    IsClosedConnectedSubmanifold n (P.level i) (n - i) :=
  ⟨(P.isCompact_level i).isClosed, P.isConnected_level hin,
    fun _ hp => P.regularAtDim_level hi0 hin hp⟩

end CentredFlattening

end Lines

/-! ### The flag and the flag-bearing modification -/

section FlagGeometry

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The blow-up of a compact manifold at a point is compact. -/
instance compactSpace_pointBlowup [NeZero n] [CompactSpace X] (x : X) :
    CompactSpace (PointBlowup n x) :=
  BlowupCompact.compactSpace_of_isBlowupAlong (isBlowupAlong_pointBlowup x)

/-- The blow-up of a connected manifold at a point is connected. -/
instance connectedSpace_pointBlowup [NeZero n] [ConnectedSpace X] (x : X) :
    ConnectedSpace (PointBlowup n x) :=
  BlowupConnected.connectedSpace_of_isBlowupAlong (isBlowupAlong_pointBlowup x)

/-- **Blanchard.** For a Kähler form `ω` on `X`, `π^*ω + εΘ` is a Kähler form on the point
blow-up for some `ε > 0`, where `Θ` is the closed `(1,1)`-form `ddᶜ log` of the Blanchard weight
of `{x}` (a smooth representative of `-{E}` up to a positive factor). -/
theorem exists_isKahler_pullback_add_pointBlowup [NeZero n] [CompactSpace X]
    (omega : KahlerBackground n X) (x : X) (D : BlanchardWeight.BlanchardData n ({x} : Set X)) :
    ∃ F : FactorizedWeightForm.WeightFactorization n
        (fun p : PointBlowup n x => D.weight (blowupProj n ({x} : Set X) p)),
      ∃ ε : ℝ, 0 < ε ∧
        (ClosedRealOneOneForm.pullback (isBlowupAlong_pointBlowup (n := n) x).contMDiff
          omega.form + ε • F.closedForm).val.IsKahler :=
  BlowupKahler.exists_isKahler_pullback_add omega (isBlowupAlong_pointBlowup x) D

/-- The point blow-up of a compact Kähler manifold carries a Kähler form. -/
theorem nonempty_kahlerBackground_pointBlowup [NeZero n] [CompactSpace X]
    (omega : KahlerBackground n X) (x : X) : Nonempty (KahlerBackground n (PointBlowup n x)) :=
  (BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong ⟨omega⟩
    (isBlowupAlong_pointBlowup x)).2

/-- The point blow-up is an analytic modification. -/
theorem isAnalyticModification_pointBlowup [NeZero n] (x : X) :
    IsAnalyticModification (n := n) (blowupProj n ({x} : Set X)) :=
  PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong
    (isBlowupAlong_pointBlowup x)

variable (n) in
/-- **The linear flag of the point blow-up**: `Y_0 = Bl_x X` and `Y_i = ℙ(V_i)` for
`1 ≤ i ≤ n` (levels of the translated chart at `x`); `Y_1` is the exceptional divisor and `Y_n`
is a point. -/
def pointBlowupFlag (x : X) (i : Fin (n + 1)) : Set (PointBlowup n x) :=
  if (i : ℕ) = 0 then univ else (centredFlattening (n := n) x).level i

/-- The levels of the translated chart are the coordinate projective subspaces `ℙ(V_i)`. -/
theorem centredFlattening_level (x : X) (i : ℕ) :
    (centredFlattening (n := n) x).level i =
      {q : PointBlowup n x | q.base = x ∧ q.dir ≤ flagSubspace n i} := by
  simp only [CentredFlattening.level, deriv_centredFlattening, ContinuousLinearMap.coe_id,
    Submodule.comap_id]

theorem pointBlowupFlag_zero (x : X) : pointBlowupFlag n x 0 = univ := if_pos rfl

theorem pointBlowupFlag_of_ne_zero (x : X) {i : Fin (n + 1)} (hi : (i : ℕ) ≠ 0) :
    pointBlowupFlag n x i = (centredFlattening (n := n) x).level i := if_neg hi

/-- The first member of the linear flag is the exceptional divisor `π⁻¹(x)`. -/
theorem pointBlowupFlag_one [NeZero n] (x : X) :
    pointBlowupFlag n x 1 = blowupProj n ({x} : Set X) ⁻¹' {x} := by
  have h1 : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (Nat.succ_lt_succ (NeZero.pos n))]
  rw [pointBlowupFlag_of_ne_zero x (by omega), h1, centredFlattening_level]
  ext p
  simp only [flagSubspace_one, le_top, and_true, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  rfl

/-- **The linear flag of the point blow-up is a smooth flag.** -/
theorem isSmoothFlag_pointBlowupFlag [NeZero n] [ConnectedSpace X] (x : X) :
    IsSmoothFlag (pointBlowupFlag n x) := by
  refine ⟨pointBlowupFlag_zero x, ?_, fun i => ?_⟩
  · intro i i' hii'
    by_cases hi : (i : ℕ) = 0
    · show pointBlowupFlag n x i' ⊆ pointBlowupFlag n x i
      have h0 : pointBlowupFlag n x i = univ := if_pos hi
      rw [h0]
      exact subset_univ _
    · have hi' : (i' : ℕ) ≠ 0 := fun h => hi (by have : (i : ℕ) ≤ i' := hii'; omega)
      rw [pointBlowupFlag_of_ne_zero x hi, pointBlowupFlag_of_ne_zero x hi']
      exact (centredFlattening x).level_antitone hii'
  · by_cases hi : (i : ℕ) = 0
    · rw [pointBlowupFlag, if_pos hi, hi, Nat.sub_zero]
      exact ⟨isClosed_univ, isConnected_univ,
        fun z _ => AnalyticIrreducibleComponents.regularAtDim_univ z⟩
    · rw [pointBlowupFlag_of_ne_zero x hi]
      exact (centredFlattening x).isClosedConnectedSubmanifold_level hi (Nat.lt_succ_iff.mp i.2)

end FlagGeometry

section Existence

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- **The flag-bearing point blow-up.** The blow-up of a compact connected Kähler manifold `X`
of dimension `m + 1` at `x`, with a Kähler form (`π^*ω + εΘ`) and its linear flag, as an
`OriginalFlagGeometry`. -/
def pointBlowupFlagGeometry (omega : KahlerBackground (m + 1) X) (x : X) :
    OriginalFlagGeometry.{u} (m + 1) :=
  OriginalFlagGeometry.ofOriginal
    (Classical.choice (nonempty_kahlerBackground_pointBlowup omega x))
    (pointBlowupFlag (m + 1) x) (isSmoothFlag_pointBlowupFlag x)

theorem pointBlowupFlagGeometry_carrier (omega : KahlerBackground (m + 1) X) (x : X) :
    (pointBlowupFlagGeometry omega x).carrier = PointBlowup (m + 1) x := rfl

theorem pointBlowupFlagGeometry_flag (omega : KahlerBackground (m + 1) X) (x : X) :
    (pointBlowupFlagGeometry omega x).flag = pointBlowupFlag (m + 1) x := rfl

/-- The projection of the flag-bearing point blow-up. -/
def pointBlowupFlagGeometryProj (omega : KahlerBackground (m + 1) X) (x : X) :
    (pointBlowupFlagGeometry omega x).carrier → X :=
  blowupProj (m + 1) ({x} : Set X)

/-- The first flag member of the flag-bearing point blow-up is its exceptional divisor. -/
theorem pointBlowupFlagGeometry_flag_one (omega : KahlerBackground (m + 1) X) (x : X) :
    (pointBlowupFlagGeometry omega x).flag 1 = pointBlowupFlagGeometryProj omega x ⁻¹' {x} :=
  pointBlowupFlag_one x

theorem isBlowupAlong_pointBlowupFlagGeometryProj (omega : KahlerBackground (m + 1) X) (x : X) :
    IsBlowupAlong (m + 1) ({x} : Set X) (pointBlowupFlagGeometryProj omega x) :=
  isBlowupAlong_pointBlowup x

theorem isAnalyticModification_pointBlowupFlagGeometry (omega : KahlerBackground (m + 1) X)
    (x : X) : IsAnalyticModification (n := m + 1) (pointBlowupFlagGeometryProj omega x) :=
  isAnalyticModification_pointBlowup x

end Existence

/-- The identity is an analytic modification. -/
private theorem isAnalyticModification_id' {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] :
    IsAnalyticModification (n := n) (id : X → X) :=
  ⟨contMDiff_id, isProperMap_id, ∅, ∅, id, isClosed_empty, isComplexAnalyticSubset_empty,
    interior_empty, isClosed_empty, isComplexAnalyticSubset_empty, interior_empty, rfl,
    contMDiff_id.contMDiffOn, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Every compact connected Kähler manifold has a flag-bearing modification**: an analytic
modification `π : Y → X` with `Y` compact connected Kähler carrying a smooth flag.  In positive
dimension `Y` is the blow-up of a point with its linear flag (`pointBlowupFlagGeometry`); in
dimension zero `Y = X` with the flag `Y_0 = X`. -/
theorem exists_flagBearingModification {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X) :
    ∃ (F : OriginalFlagGeometry.{u} n) (π : F.carrier → X), IsAnalyticModification (n := n) π := by
  cases n with
  | zero =>
      have hflag : IsSmoothFlag (fun _ : Fin (0 + 1) => (univ : Set X)) :=
        ⟨rfl, fun _ _ _ => Subset.rfl, fun i => ⟨isClosed_univ, isConnected_univ,
          fun z _ => by
            simpa only [Nat.zero_sub] using AnalyticIrreducibleComponents.regularAtDim_univ z⟩⟩
      exact ⟨OriginalFlagGeometry.ofOriginal omega _ hflag, id, isAnalyticModification_id'⟩
  | succ m =>
      obtain ⟨x⟩ := (inferInstance : Nonempty X)
      exact ⟨pointBlowupFlagGeometry omega x, pointBlowupFlagGeometryProj omega x,
        isAnalyticModification_pointBlowupFlagGeometry omega x⟩

end SGPT.Blowup

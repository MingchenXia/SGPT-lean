import SGPT.Okounkov.TailFlag
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

/-!
# Submanifolds of submanifolds, and connected components of submanifolds


Let `X` be a complex manifold of dimension `n` (the `SGPT.Foundations.Analysis` charts) and `W ⊆ X`
a submanifold of dimension `d`, regular of dimension `d` at each of its points
(`RegularAtDim`); `↥W` carries the flattening atlas of
`SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace` (charts `p ↦ π_d (Φ (e p))`, `e` the
preferred chart of `X`, `Φ` the flattening of `W`).

* `prodIdEquiv`: a local biholomorphism `Ψ` of `ℂᵈ` acting on the first `d` coordinates of `ℂⁿ`,
  `(a, b) ↦ (Ψ a, b)`, as a local holomorphic equivalence of `ℂⁿ`.
* **`regularAtDim_image_val`**: a point of `C ⊆ ↥W` at which `C` is regular of dimension `j`
  *in the charts of `↥W`* is a point at which `C ⊆ X` is regular of dimension `j` in the charts
  of `X`: the flattening is `(Ψ × id) ∘ Φ`, read in the preferred chart of `X`.
* **`isClosedConnectedSubmanifold_image_val`**: for `W` closed, a closed connected submanifold of
  `↥W` is a closed connected submanifold of `X` (of the same dimension).
* **`isClosedConnectedSubmanifold_connectedComponentIn`**: every connected component of a closed
  submanifold `A ⊆ X` of pure dimension `k` is a closed connected submanifold of dimension `k`
  (`↥A` is a manifold, hence locally connected, so its components are open in `A`).
* `exists_ne_of_one_le`: a nonempty manifold of positive dimension has two distinct points.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.SmoothFlags

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending

/-! ### A local biholomorphism of `ℂᵈ` acting on the first coordinates of `ℂⁿ` -/

section Product

variable {n d : ℕ}

/-- `(a, b) ↦ (Ψ a, b)` on `ℂⁿ = ℂᵈ × ℂⁿ⁻ᵈ`: `z ↦ z - ι(π z) + ι(Ψ(π z))`. -/
def prodIdMap (Ψf : ComplexModel d → ComplexModel d) (z : ComplexModel n) : ComplexModel n :=
  z - coordinateInclusion n d (coordinateProjection n d z) +
    coordinateInclusion n d (Ψf (coordinateProjection n d z))

theorem coordinateProjection_prodIdMap (hd : d ≤ n) (Ψf : ComplexModel d → ComplexModel d)
    (z : ComplexModel n) :
    coordinateProjection n d (prodIdMap Ψf z) = Ψf (coordinateProjection n d z) := by
  simp only [prodIdMap, map_add, map_sub, coordinateProjection_coordinateInclusion hd, sub_self,
    zero_add]

/-- The last `n - d` coordinates are unchanged. -/
theorem prodIdMap_apply_of_le (Ψf : ComplexModel d → ComplexModel d) (z : ComplexModel n)
    {i : Fin n} (hi : d ≤ i.1) : prodIdMap Ψf z i = z i := by
  have h1 := NestedFlattening.sub_inclusion_projection_apply (m := d) z i
  rw [if_neg (not_lt.mpr hi)] at h1
  rw [prodIdMap, PiLp.add_apply, h1, coordinateInclusion_apply, dif_neg (not_lt.mpr hi), add_zero]

theorem prodIdMap_mem_plane_iff (Ψf : ComplexModel d → ComplexModel d) (z : ComplexModel n) :
    prodIdMap Ψf z ∈ complexCoordinatePlane n d ↔ z ∈ complexCoordinatePlane n d := by
  constructor
  · intro h i hi
    rw [← prodIdMap_apply_of_le Ψf z hi]
    exact h i hi
  · intro h i hi
    rw [prodIdMap_apply_of_le Ψf z hi]
    exact h i hi

theorem prodIdMap_prodIdMap (hd : d ≤ n) {Ψf Ψg : ComplexModel d → ComplexModel d}
    {z : ComplexModel n} (h : Ψg (Ψf (coordinateProjection n d z)) = coordinateProjection n d z) :
    prodIdMap Ψg (prodIdMap Ψf z) = z := by
  rw [prodIdMap, coordinateProjection_prodIdMap hd, h]
  unfold prodIdMap
  abel

theorem differentiableOn_prodIdMap {Ψf : ComplexModel d → ComplexModel d} {S : Set (ComplexModel d)}
    (hΨ : DifferentiableOn ℂ Ψf S) :
    DifferentiableOn ℂ (prodIdMap (n := n) Ψf) (coordinateProjection n d ⁻¹' S) := by
  have h1 : Differentiable ℂ fun z : ComplexModel n =>
      z - coordinateInclusion n d (coordinateProjection n d z) :=
    differentiable_id.sub
      ((coordinateInclusion n d).differentiable.comp (coordinateProjection n d).differentiable)
  have h2 : DifferentiableOn ℂ
      (fun z : ComplexModel n => coordinateInclusion n d (Ψf (coordinateProjection n d z)))
      (coordinateProjection n d ⁻¹' S) :=
    (coordinateInclusion n d).differentiable.comp_differentiableOn
      (hΨ.comp (coordinateProjection n d).differentiable.differentiableOn fun _ hz => hz)
  exact h1.differentiableOn.add h2

/-- The local holomorphic equivalence `Ψ × id` of `ℂⁿ`, centred at `p`, for `Ψ` centred at the
first `d` coordinates of `p`. -/
def prodIdEquiv (hd : d ≤ n) {p : ComplexModel n}
    (Ψ : LocalHolomorphicEquivAt (n := d) (coordinateProjection n d p)) :
    LocalHolomorphicEquivAt (n := n) p where
  source := coordinateProjection n d ⁻¹' Ψ.source
  target := coordinateProjection n d ⁻¹' Ψ.target
  isOpen_source := Ψ.isOpen_source.preimage (coordinateProjection n d).continuous
  isOpen_target := Ψ.isOpen_target.preimage (coordinateProjection n d).continuous
  center_mem_source := Ψ.center_mem_source
  toFun := prodIdMap Ψ.toFun
  invFun := prodIdMap Ψ.invFun
  toFun_holomorphic := differentiableOn_prodIdMap Ψ.toFun_holomorphic
  invFun_holomorphic := differentiableOn_prodIdMap Ψ.invFun_holomorphic
  mapsTo_toFun := fun z hz => by
    show coordinateProjection n d (prodIdMap Ψ.toFun z) ∈ Ψ.target
    rw [coordinateProjection_prodIdMap hd]
    exact Ψ.mapsTo_toFun hz
  mapsTo_invFun := fun w hw => by
    show coordinateProjection n d (prodIdMap Ψ.invFun w) ∈ Ψ.source
    rw [coordinateProjection_prodIdMap hd]
    exact Ψ.mapsTo_invFun hw
  left_inv := fun z hz => prodIdMap_prodIdMap hd (Ψ.left_inv _ hz)
  right_inv := fun w hw => prodIdMap_prodIdMap hd (Ψ.right_inv _ hw)

theorem complexCoordinatePlane_mono {j d : ℕ} (hjd : j ≤ d) :
    complexCoordinatePlane n j ⊆ complexCoordinatePlane n d :=
  fun _ h i hi => h i (hjd.trans hi)

/-- `(Ψ a, b) ∈ ℂʲ × 0 ⟺ b = 0 ∧ Ψ a ∈ ℂʲ × 0` (for `j ≤ d ≤ n`). -/
theorem prodIdMap_mem_plane_iff_of_le {j : ℕ} (hjd : j ≤ d) (hd : d ≤ n)
    (Ψf : ComplexModel d → ComplexModel d) (z : ComplexModel n) :
    prodIdMap Ψf z ∈ complexCoordinatePlane n j ↔
      z ∈ complexCoordinatePlane n d ∧
        Ψf (coordinateProjection n d z) ∈ complexCoordinatePlane d j := by
  constructor
  · intro h
    have hd' : prodIdMap Ψf z ∈ complexCoordinatePlane n d := complexCoordinatePlane_mono hjd h
    refine ⟨(prodIdMap_mem_plane_iff Ψf z).mp hd', ?_⟩
    rw [← coordinateProjection_prodIdMap hd Ψf z]
    exact (SGPT.Okounkov.coordinateProjection_mem_plane_iff hd hd').mpr h
  · rintro ⟨h1, h2⟩
    have hd' : prodIdMap Ψf z ∈ complexCoordinatePlane n d := (prodIdMap_mem_plane_iff Ψf z).mpr h1
    refine (SGPT.Okounkov.coordinateProjection_mem_plane_iff hd hd').mp ?_
    rw [coordinateProjection_prodIdMap hd]
    exact h2

end Product

/-! ### Submanifolds of a submanifold -/

section Transfer

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Regularity transfers from a submanifold to the ambient manifold.** If `C ⊆ ↥W` is regular
of dimension `j` at `q` in the flattening charts of `↥W`, then `C`, viewed in `X`, is regular of
dimension `j` at `q` in the charts of `X`. The ambient flattening is `(Ψ × id) ∘ Φ`, with `Φ` the
flattening of `W` and `Ψ` that of `C` in the chart of `↥W` at `q`. -/
theorem regularAtDim_image_val {W : Set X} {d : ℕ} (hd : d ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x d) {C : Set W} {q : W} {j : ℕ}
    (hC : letI := SubmanifoldChartedSpace.chartedSpace hd hW
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hW
      RegularAtDim (n := d) C q j) :
    RegularAtDim (n := n) (Subtype.val '' C) (q : X) j := by
  let := SubmanifoldChartedSpace.chartedSpace hd hW
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hW
  obtain ⟨hjd, hqC, Ψ, -, hΨ0, hΨC⟩ := hC
  set e := complexChartAt (n := n) (q : X) with he
  set Φ := (hW q.1 q.2).2.2.choose with hΦ
  obtain ⟨hΦt, hΦ0, hΦW⟩ := (hW q.1 q.2).2.2.choose_spec
  let Ψ' : LocalHolomorphicEquivAt (n := d) (coordinateProjection n d (Φ.toFun (e.val q))) := Ψ
  let Θ : LocalHolomorphicEquivAt (n := n) (e.val q) :=
    RegularAtDimTransport.LocalHolomorphicEquivAt.comp Φ (prodIdEquiv hd Ψ') rfl
  refine ⟨hjd.trans hd, ⟨q, hqC, rfl⟩, Θ, fun u hu => hΦt hu.1, ?_, ?_⟩
  · have h1 : Ψ'.toFun (coordinateProjection n d (Φ.toFun (e.val q))) = 0 := hΨ0
    show prodIdMap Ψ'.toFun (Φ.toFun (e.val q)) = 0
    rw [prodIdMap, h1, hΦ0]
    simp
  · intro y hy hyΘ
    have hyΦ : e.val y ∈ Φ.source := hyΘ.1
    have hyΨ : coordinateProjection n d (Φ.toFun (e.val y)) ∈ Ψ'.source := hyΘ.2
    show y ∈ Subtype.val '' C ↔ prodIdMap Ψ'.toFun (Φ.toFun (e.val y)) ∈ complexCoordinatePlane n j
    rw [prodIdMap_mem_plane_iff_of_le hjd hd, ← hΦW hy hyΦ]
    constructor
    · rintro ⟨p, hpC, rfl⟩
      exact ⟨p.2, (hΨC (y := p) ⟨hy, hyΦ⟩ hyΨ).mp hpC⟩
    · rintro ⟨hyW, h⟩
      exact ⟨⟨y, hyW⟩, (hΨC (y := ⟨y, hyW⟩) ⟨hy, hyΦ⟩ hyΨ).mpr h, rfl⟩

/-- **A closed connected submanifold of a closed submanifold `W` is a closed connected
submanifold of `X`** of the same dimension. -/
theorem isClosedConnectedSubmanifold_image_val {W : Set X} {d : ℕ} (hd : d ≤ n)
    (hWc : IsClosed W) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x d) {C : Set W} {j : ℕ}
    (hC : letI := SubmanifoldChartedSpace.chartedSpace hd hW
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hW
      IsClosedConnectedSubmanifold d C j) :
    IsClosedConnectedSubmanifold n (Subtype.val '' C) j := by
  let := SubmanifoldChartedSpace.chartedSpace hd hW
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hW
  refine ⟨hWc.isClosedEmbedding_subtypeVal.isClosedMap C hC.1,
    hC.2.1.image _ continuous_subtype_val.continuousOn, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact regularAtDim_image_val hd hW (hC.2.2 q hq)

end Transfer

/-! ### Connected components of a submanifold -/

section Component

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Connected components of a closed submanifold.** If `A ⊆ X` is closed and regular of
dimension `k` at each of its points, the connected component of `A` through `x ∈ A` is a closed
connected submanifold of dimension `k`. -/
theorem isClosedConnectedSubmanifold_connectedComponentIn {A : Set X} (hAc : IsClosed A) {k : ℕ}
    (hA : ∀ x ∈ A, RegularAtDim (n := n) A x k) {x : X} (hx : x ∈ A) :
    IsClosedConnectedSubmanifold n (connectedComponentIn A x) k := by
  have hk : k ≤ n := (hA x hx).1
  let := SubmanifoldChartedSpace.chartedSpace hk hA
  have : LocallyConnectedSpace A := ChartedSpace.locallyConnectedSpace (ComplexModel k) A
  have hopen : IsOpen (connectedComponent (⟨x, hx⟩ : A)) := isOpen_connectedComponent
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hopen
  have himg : connectedComponentIn A x = Subtype.val '' connectedComponent (⟨x, hx⟩ : A) :=
    connectedComponentIn_eq_image hx
  refine ⟨?_, isConnected_connectedComponentIn_iff.mpr hx, fun y hy => ?_⟩
  · rw [himg]
    exact hAc.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  · have hyA : y ∈ A := connectedComponentIn_subset A x hy
    have hAU : A ∩ U = connectedComponentIn A x ∩ U := by
      ext z
      constructor
      · rintro ⟨hzA, hzU⟩
        refine ⟨?_, hzU⟩
        rw [himg]
        refine ⟨⟨z, hzA⟩, ?_, rfl⟩
        rw [← hUeq]
        exact hzU
      · rintro ⟨hz, hzU⟩
        exact ⟨connectedComponentIn_subset A x hz, hzU⟩
    have hyU : y ∈ U := by
      rw [himg] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      rw [← hUeq] at hw
      exact hw
    exact RegularPointDimension.regularAtDim_of_inter_eq hU hyU hAU (hA y hyA)

end Component

/-! ### Manifolds of positive dimension -/

/-- A nonempty manifold modelled on `ℂᵏ`, `k ≥ 1`, has two distinct points. -/
theorem exists_ne_of_one_le {k : ℕ} (hk : 1 ≤ k) {W : Type*} [TopologicalSpace W]
    [ChartedSpace (ComplexModel k) W] [Nonempty W] : ∃ a b : W, a ≠ b := by
  obtain ⟨w⟩ := ‹Nonempty W›
  set c := chartAt (ComplexModel k) w with hc
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : (𝓝[≠] (c w)).NeBot := Module.punctured_nhds_neBot ℂ (ComplexModel k) (c w)
  have hmem : c.target ∈ 𝓝[≠] (c w) :=
    mem_nhdsWithin_of_mem_nhds (c.open_target.mem_nhds (mem_chart_target (ComplexModel k) w))
  have hmem' : c.target ∩ {c w}ᶜ ∈ 𝓝[≠] (c w) := inter_mem hmem self_mem_nhdsWithin
  obtain ⟨ζ, hζt, hζw⟩ := Filter.nonempty_of_mem hmem'
  refine ⟨c.symm ζ, w, fun h => hζw ?_⟩
  rw [mem_singleton_iff, ← h, c.right_inv hζt]

end SGPT.GAGA.SmoothFlags

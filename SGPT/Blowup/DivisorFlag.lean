import SGPT.Blowup.PointBlowupFlag
import SGPT.Blowup.SubmanifoldBlowupExceptional
import SGPT.Foundations.Analysis.Pending.AnalyticComplementConnected
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

/-!
# Smooth flags whose first member is a given smooth divisor

Let `Y` be a connected complex manifold of dimension `n ≥ 2`, `E ⊆ Y` a closed connected smooth
hypersurface and `x ∈ E`.  In the blow-up `π : Bl_x Y → Y` the strict transform of `E` is

`Ẽ = π⁻¹(E \ {x}) ∪ ℙ(T_xE)`  (`strictDivisor`, equal to `closure (π⁻¹E \ Exc π)`),

a closed connected smooth hypersurface, and `Ẽ ∩ π⁻¹(x) = ℙ(T_xE)`.  Choosing a flattening
`(z_0, …, z_{n-1})` of `E` at `x` with `E = {z_0 = 0}` near `x`, the linear subspaces
`ℙ(V_i) ⊆ ℙ(T_xE)`, `V_i = {dz_0 = ⋯ = dz_{i-2} = 0}` (`2 ≤ i ≤ n`), complete `Ẽ` to a smooth
flag

`Bl_x Y ⊇ Ẽ ⊇ ℙ(T_xE) ⊇ ℙ(V_3) ⊇ ⋯ ⊇ ℙ(V_n) = pt`  (`isSmoothFlag_divisorFlag`).

This is the geometric input "a smooth flag whose first member is (the strict transform of) a given
prime divisor, on a further blow-up" used for `cor:Deltacontimplyvarphi` / `thm:nuOk`-type
arguments.

The charts are Demailly's monomial charts of the point blow-up over the centred flattening
`ofRegular` adapted to `E` (`SGPT.Blowup.CentredFlattening`): in these coordinates a point
`(x, ℂξ)` of the exceptional divisor has coordinates `w_k = (dΦ ξ)_k / (dΦ ξ)_j`, `w_j = 0`, and
`Ẽ` is the coordinate hyperplane `w_0 = 0` (`mem_strictDivisor_iff_chart`).
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

/-! ### A centred flattening adapted to a smooth hypersurface -/

section Adapted

variable {n : ℕ} [NeZero n] {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The last coordinate index `n - 1`. -/
def lastIndex (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) one_pos⟩

/-- The coordinate swap `0 ↔ n - 1`. -/
def swapLast (n : ℕ) [NeZero n] : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap (0 : Fin n) (lastIndex n))

theorem swapLast_apply_zero (w : ComplexModel n) : swapLast n w 0 = w (lastIndex n) := by
  simp [swapLast, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- Compose a local biholomorphism with a linear isometry of the target. -/
def linearCompose {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    (L : ComplexModel n ≃ₗᵢ[ℂ] ComplexModel n) : LocalHolomorphicEquivAt (n := n) p where
  source := Φ.source
  target := L.symm ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source
  isOpen_target := Φ.isOpen_target.preimage L.symm.continuous
  center_mem_source := Φ.center_mem_source
  toFun z := L (Φ.toFun z)
  invFun w := Φ.invFun (L.symm w)
  toFun_holomorphic :=
    L.toContinuousLinearEquiv.differentiable.comp_differentiableOn Φ.toFun_holomorphic
  invFun_holomorphic :=
    Φ.invFun_holomorphic.comp L.symm.toContinuousLinearEquiv.differentiable.differentiableOn
      (fun _ hw => hw)
  mapsTo_toFun z hz := by
    show L.symm (L (Φ.toFun z)) ∈ Φ.target
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact Φ.mapsTo_toFun hz
  mapsTo_invFun _ hw := Φ.mapsTo_invFun hw
  left_inv z hz := by
    show Φ.invFun (L.symm (L (Φ.toFun z))) = z
    rw [LinearIsometryEquiv.symm_apply_apply, Φ.left_inv z hz]
  right_inv w hw := by
    show L (Φ.toFun (Φ.invFun (L.symm w))) = w
    rw [Φ.right_inv _ hw, LinearIsometryEquiv.apply_symm_apply]

theorem mem_complexCoordinatePlane_pred_iff (w : ComplexModel n) :
    w ∈ complexCoordinatePlane n (n - 1) ↔ w (lastIndex n) = 0 := by
  have hn := NeZero.pos n
  simp only [complexCoordinatePlane, mem_ofPred_eq]
  constructor
  · intro h
    exact h _ (by simp [lastIndex])
  · intro h i hi
    have : i = lastIndex n := Fin.ext (by simp [lastIndex]; omega)
    rw [this]
    exact h

variable {E : Set X} {x : X}

/-- The flattening of a smooth hypersurface at `x`, with coordinates swapped so that the
hypersurface is `{z_0 = 0}`. -/
def ofRegular (h : RegularAtDim (n := n) E x (n - 1)) : CentredFlattening n x where
  Φ := linearCompose (Classical.choose h.2.2) (swapLast n)
  source_subset := (Classical.choose_spec h.2.2).1
  map_centre := by
    show swapLast n ((Classical.choose h.2.2).toFun (chartAt (ComplexModel n) x x)) = 0
    rw [show (Classical.choose h.2.2).toFun (chartAt (ComplexModel n) x x) = 0 from
      (Classical.choose_spec h.2.2).2.1, map_zero]

theorem ofRegular_flat (h : RegularAtDim (n := n) E x (n - 1)) {y : X}
    (hy : y ∈ (chartAt (ComplexModel n) x).source)
    (hyΦ : chartAt (ComplexModel n) x y ∈ (ofRegular h).Φ.source) :
    (y ∈ E ↔ (ofRegular h).Φ.toFun (chartAt (ComplexModel n) x y) 0 = 0) := by
  have hf := (Classical.choose_spec h.2.2).2.2 (y := y) hy hyΦ
  rw [hf, mem_complexCoordinatePlane_pred_iff]
  show _ ↔ swapLast n _ 0 = 0
  rw [swapLast_apply_zero]
  exact Iff.rfl

/-- **The tangent space of the hypersurface in the adapted frame**: `T_xE = {ξ | (dΦ ξ)_0 = 0}`. -/
theorem tangentSpace_eq_comap (h : RegularAtDim (n := n) E x (n - 1)) :
    tangentSpace n E x = (flagSubspace n 2).comap
      ((ofRegular h).deriv : ComplexModel n →ₗ[ℂ] ComplexModel n) := by
  obtain ⟨hsrc, -, hflat⟩ := Classical.choose_spec h.2.2
  set Ψ := Classical.choose h.2.2 with hΨ
  have hderiv : (ofRegular h).deriv = (swapLast n : ComplexModel n →L[ℂ] ComplexModel n).comp
      (fderiv ℂ (flatMap Ψ x) (chartAt (ComplexModel n) x x)) := by
    have hfun : flatMap (ofRegular h).Φ x = swapLast n ∘ flatMap Ψ x := rfl
    rw [CentredFlattening.deriv, hfun, LinearIsometryEquiv.comp_fderiv]
  have hd0 : ∀ ξ : ComplexModel n, (ofRegular h).deriv ξ 0 =
      (fderiv ℂ (flatMap Ψ x) (chartAt (ComplexModel n) x x) ξ) (lastIndex n) := by
    intro ξ
    rw [hderiv]
    exact swapLast_apply_zero _
  have hcoord : ∀ (ξ : ComplexModel n) (i : Fin n), germDiff n (flatCoord Ψ i) x ξ =
      (fderiv ℂ (flatMap Ψ x) (chartAt (ComplexModel n) x x) ξ) i := by
    intro ξ i
    rw [germDiff_flatCoord hsrc (mem_flatDomain_self Ψ)]
    rfl
  ext ξ
  rw [mem_tangentSpace_iff (Φ := Ψ) hsrc (fun hy hyΦ => hflat hy hyΦ) (mem_flatDomain_self Ψ)
    h.2.1, Submodule.mem_comap, mem_flagSubspace]
  have hn := NeZero.pos n
  constructor
  · intro hξ k hk
    have hk0 : k = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    rw [hk0]
    show (ofRegular h).deriv ξ 0 = 0
    rw [hd0, ← hcoord]
    exact hξ (lastIndex n) (by simp [lastIndex])
  · intro hξ i hi
    have hi' : i = lastIndex n := Fin.ext (by simp [lastIndex]; omega)
    have h0 : (ofRegular h).deriv ξ 0 = 0 := hξ 0 (by rw [Fin.val_zero]; omega)
    rw [hd0, ← hcoord] at h0
    rw [hi']
    exact h0

end Adapted

/-! ### The strict transform of a smooth hypersurface through the centre -/

section Strict

variable {n : ℕ} [NeZero n] {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {E : Set X} {x : X}

variable (n x) in
/-- The strict transform `Ẽ = π⁻¹(E \ {x}) ∪ ℙ(T_xE)` of `E ∋ x` in the point blow-up. -/
def strictDivisor (E : Set X) : Set (PointBlowup n x) :=
  {q | (q.base ≠ x ∧ q.base ∈ E) ∨ (q.base = x ∧ q.dir ≤ tangentSpace n E x)}

theorem strictDivisor_subset (hx : x ∈ E) :
    strictDivisor n x E ⊆ blowupProj n ({x} : Set X) ⁻¹' E := by
  rintro q (⟨_, h⟩ | ⟨h, _⟩)
  · exact h
  · show q.base ∈ E
    rw [h]
    exact hx

theorem mem_strictDivisor_iff_deriv (h : RegularAtDim (n := n) E x (n - 1)) {q : PointBlowup n x}
    (hb : q.base = x) :
    q ∈ strictDivisor n x E ↔ (ofRegular h).deriv q.dirVec 0 = 0 := by
  have hT : q.dir ≤ tangentSpace n E x ↔ (ofRegular h).deriv q.dirVec 0 = 0 := by
    rw [dir_le_iff hb, tangentSpace_eq_comap h, Submodule.mem_comap, mem_flagSubspace]
    constructor
    · intro hk
      exact hk 0 (by simp)
    · intro h0 k hk
      have hk0 : k = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [hk0]
      exact h0
  constructor
  · rintro (⟨hne, _⟩ | ⟨_, hd⟩)
    · exact absurd hb hne
    · exact hT.mp hd
  · intro h0
    exact Or.inr ⟨hb, hT.mpr h0⟩

/-- **`Ẽ` in the chart `τ̃_j`, `j ≠ 0`**: a point of the chart lies on `Ẽ` iff `w_0 = 0`. -/
theorem mem_strictDivisor_iff_chart (h : RegularAtDim (n := n) E x (n - 1)) {j : Fin n}
    (hj : j ≠ 0) {q : PointBlowup n x} (hq : q ∈ ((ofRegular h).chart j).source) :
    q ∈ strictDivisor n x E ↔ ((ofRegular h).chart j).toFun q ∈ coordZeroSet {0} := by
  set P := ofRegular h
  have hz : ((ofRegular h).chart j).toFun q ∈ coordZeroSet {0} ↔
      (P.chart j).toFun q 0 = 0 := by
    simp [coordZeroSet, P]
  rw [hz]
  by_cases hb : q.base = x
  · rw [mem_strictDivisor_iff_deriv h hb, P.toFun_ne j (Ne.symm hj) q hb]
    have hjne : P.deriv q.dirVec j ≠ 0 := (P.mem_source_iff j hb).mp hq
    rw [div_eq_zero_iff, or_iff_left hjne]
  · have hwj : (P.chart j).toFun q j ≠ 0 := by
      intro h0
      have h' := FlatChart.toFun_j_eq_zero_iff (P.chart j) hq
      simp only [CentredFlattening.chart_j] at h'
      exact hb (h'.mp h0)
    have hmem : q ∈ strictDivisor n x E ↔ q.base ∈ E := by
      constructor
      · rintro (⟨_, hE⟩ | ⟨hb', _⟩)
        · exact hE
        · exact absurd hb' hb
      · intro hE
        exact Or.inl ⟨hb, hE⟩
    rw [hmem, ofRegular_flat h hq.1.1 hq.1.2, P.flat_base_ne j (Ne.symm hj) hq,
      mul_eq_zero, or_iff_left hwj]

/-- `Ẽ` does not meet the chart `τ̃_0`. -/
theorem strictDivisor_disjoint_chart_zero (h : RegularAtDim (n := n) E x (n - 1))
    {q : PointBlowup n x} (hq : q ∈ ((ofRegular h).chart 0).source) : q ∉ strictDivisor n x E := by
  set P := ofRegular h
  by_cases hb : q.base = x
  · rw [mem_strictDivisor_iff_deriv h hb]
    exact (P.mem_source_iff 0 hb).mp hq
  · rintro (⟨_, hE⟩ | ⟨hb', _⟩)
    · rw [ofRegular_flat h hq.1.1 hq.1.2] at hE
      have hmono := (P.chart 0).monomial_toFun hq
      have h0 := congrArg (fun w : ComplexModel n => w 0) hmono
      simp only [BlowupMonomialCharts.monomial_apply, CentredFlattening.chart_k,
        CentredFlattening.chart_j, ne_eq, not_true_eq_false, and_false, if_false] at h0
      have hwj : (P.chart 0).toFun q 0 ≠ 0 := by
        intro h00
        have h' := FlatChart.toFun_j_eq_zero_iff (P.chart 0) hq
        simp only [CentredFlattening.chart_j] at h'
        exact hb (h'.mp h00)
      exact hwj (h0.trans hE)
    · exact hb hb'

end Strict

/-! ### `Ẽ` is a closed connected smooth hypersurface -/

section StrictGeometry

variable {n : ℕ} [NeZero n] {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {E : Set X} {x : X}

/-- `Ẽ` is smooth of dimension `n - 1` at its points over `x`. -/
theorem regularAtDim_strictDivisor_of_base_eq (h : RegularAtDim (n := n) E x (n - 1))
    {q : PointBlowup n x} (hq : q ∈ strictDivisor n x E) (hb : q.base = x) :
    RegularAtDim (n := n) (strictDivisor n x E) q (n - 1) := by
  set P := ofRegular h
  have h0 : P.deriv q.dirVec 0 = 0 := (mem_strictDivisor_iff_deriv h hb).mp hq
  have hne : P.deriv q.dirVec ≠ 0 := fun h' =>
    dirVec_ne_zero hb (P.deriv_injective (by rw [h', map_zero]))
  obtain ⟨j, hj⟩ : ∃ j : Fin n, P.deriv q.dirVec j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hne (by ext k; exact h' k)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj h0
  have hqc : q ∈ (P.chart j).source := (P.mem_source_iff j hb).mpr hj
  set e := P.complexChart j with he
  have hep : ∀ p, e.val p = (P.chart j).toFun p := fun _ => rfl
  have hqe : q ∈ e.val.source := hqc
  have h1 : RegularAtDim (n := n) (M := ComplexModel n)
      (coordZeroSet ({0} : Finset (Fin n)) ∩ e.val.target) (e.val q) (n - 1) := by
    refine (AnalyticLocalStatement.LocalDecomposition.regularAtDim_inter_open_iff
      e.val.open_target (e.val.map_source hqe)).mpr ?_
    have h0' := regularAtDim_coordZeroSet ({0} : Finset (Fin n))
      ((mem_strictDivisor_iff_chart h hj0 hqc).mp hq)
    rwa [Finset.card_singleton] at h0'
  have h2 := (RegularAtDimChart.regularAtDim_chart_iff e (coordZeroSet ({0} : Finset (Fin n)))
    hqe).mpr h1
  refine RegularPointDimension.regularAtDim_of_inter_eq e.val.open_source hqe ?_ h2
  ext p
  constructor
  · rintro ⟨⟨hps, hpS⟩, -⟩
    refine ⟨(mem_strictDivisor_iff_chart h hj0 hps).mpr ?_, hps⟩
    rw [← hep]
    exact hpS
  · rintro ⟨hpY, hps⟩
    refine ⟨⟨hps, ?_⟩, hps⟩
    show e.val p ∈ coordZeroSet ({0} : Finset (Fin n))
    rw [hep]
    exact (mem_strictDivisor_iff_chart h hj0 hps).mp hpY

/-- Off `x`, `Ẽ = π⁻¹(E)` is smooth of dimension `n - 1` wherever `E` is. -/
theorem regularAtDim_strictDivisor_of_base_ne {q : PointBlowup n x} (hb : q.base ≠ x)
    (hreg : RegularAtDim (n := n) E q.base (n - 1)) :
    RegularAtDim (n := n) (strictDivisor n x E) q (n - 1) := by
  let o : OffChart n ({x} : Set X) := ⟨q.base, hb⟩
  let oc : ComplexChart n (PointBlowup n x) :=
    ⟨atlasHomeo o.toPartialEquiv (Or.inr ⟨o, rfl⟩), atlasHomeo_mem_atlas _ _⟩
  set e := complexChartAt (n := n) q.base with he
  have hes : q.base ∈ e.val.source := mem_complexChartAt_source _
  set B : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' E with hB
  have hoc : ∀ p, oc.val p = e.val p.base := fun _ => rfl
  have hqo : q ∈ oc.val.source := ⟨hes, hb⟩
  have hX : RegularAtDim (n := n) (e.val.source ∩ e.val ⁻¹' B) q.base (n - 1) := by
    refine RegularPointDimension.regularAtDim_of_inter_eq e.val.open_source hes ?_ hreg
    ext y
    constructor
    · rintro ⟨hyE, hys⟩
      refine ⟨⟨hys, e.val.map_source hys, ?_⟩, hys⟩
      show e.val.symm (e.val y) ∈ E
      rw [e.val.left_inv hys]
      exact hyE
    · rintro ⟨⟨hys, -, hyB⟩, -⟩
      have hyB' : e.val.symm (e.val y) ∈ E := hyB
      rw [e.val.left_inv hys] at hyB'
      exact ⟨hyB', hys⟩
  have hX' := (RegularAtDimChart.regularAtDim_chart_iff e B hes).mp hX
  have htgt : oc.val.target ⊆ e.val.target := fun z hz => hz.1
  have hqt : oc.val q ∈ oc.val.target := oc.val.map_source hqo
  have hB' : RegularAtDim (n := n) (M := ComplexModel n) (B ∩ oc.val.target) (oc.val q)
      (n - 1) := by
    have h3 := (AnalyticLocalStatement.LocalDecomposition.regularAtDim_inter_open_iff
      oc.val.open_target hqt (B := B ∩ e.val.target)).mpr (by rw [hoc]; exact hX')
    have hset : B ∩ e.val.target ∩ oc.val.target = B ∩ oc.val.target := by
      ext z
      constructor
      · rintro ⟨⟨hzB, -⟩, hz⟩
        exact ⟨hzB, hz⟩
      · rintro ⟨hzB, hz⟩
        exact ⟨⟨hzB, htgt hz⟩, hz⟩
    rwa [hset] at h3
  have h2 := (RegularAtDimChart.regularAtDim_chart_iff oc B hqo).mpr hB'
  refine RegularPointDimension.regularAtDim_of_inter_eq oc.val.open_source hqo ?_ h2
  ext p
  constructor
  · rintro ⟨⟨hps, hpB⟩, -⟩
    refine ⟨Or.inl ⟨hps.2, ?_⟩, hps⟩
    have hpB' : e.val.symm (e.val p.base) ∈ E := hpB.2
    rwa [e.val.left_inv hps.1] at hpB'
  · rintro ⟨hpY, hps⟩
    have hpE : p.base ∈ E := by
      rcases hpY with ⟨_, hE⟩ | ⟨hb', _⟩
      · exact hE
      · exact absurd hb' hps.2
    refine ⟨⟨hps, ?_⟩, hps⟩
    show e.val p.base ∈ B
    refine ⟨e.val.map_source hps.1, ?_⟩
    show e.val.symm (e.val p.base) ∈ E
    rw [e.val.left_inv hps.1]
    exact hpE

/-- `Ẽ` is closed. -/
theorem isClosed_strictDivisor (h : RegularAtDim (n := n) E x (n - 1)) (hEc : IsClosed E) :
    IsClosed (strictDivisor n x E) := by
  have hx : x ∈ E := h.2.1
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro q hq
  by_cases hqE : q.base ∈ E
  · have hb : q.base = x := by
      by_contra hb
      exact hq (Or.inl ⟨hb, hqE⟩)
    set P := ofRegular h
    have h0 : P.deriv q.dirVec 0 ≠ 0 := fun h0 => hq ((mem_strictDivisor_iff_deriv h hb).mpr h0)
    refine ⟨(P.chart 0).source, fun p hp => strictDivisor_disjoint_chart_zero h hp,
      FlatChart.isOpen_source _, (P.mem_source_iff 0 hb).mpr h0⟩
  · refine ⟨blowupProj n ({x} : Set X) ⁻¹' Eᶜ, fun p hp hpY => hp (strictDivisor_subset hx hpY),
      hEc.isOpen_compl.preimage continuous_blowupProj, hqE⟩

/-- In positive dimension a connected submanifold stays connected after removing a point. -/
theorem isPreconnected_diff_singleton [NeZero (n - 1)]
    (hE : IsClosedConnectedSubmanifold n E (n - 1)) (x : X) : IsPreconnected (E \ {x}) := by
  by_cases hx : x ∈ E
  · let _ := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le n 1) hE.2.2
    have _ := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.sub_le n 1) hE.2.2
    have : ConnectedSpace E := isConnected_iff_connectedSpace.mp hE.2.1
    let pt : E := ⟨x, hx⟩
    have hT : IsComplexAnalyticSubset (n := n - 1) ({pt} : Set E) :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        (factIsClosedSubmanifold_singleton (n := n - 1) pt).out
    have hne : ({pt} : Set E) ≠ univ := by
      intro h'
      have hi := interior_singleton_eq_empty (n := n - 1) pt
      rw [h', interior_univ] at hi
      exact univ_nonempty.ne_empty hi
    have hpre := AnalyticComplementConnected.isPreconnected_compl hT hne
    have himg : E \ {x} = Subtype.val '' ({pt}ᶜ : Set E) := by
      ext y
      constructor
      · rintro ⟨hyE, hyx⟩
        refine ⟨⟨y, hyE⟩, ?_, rfl⟩
        intro h'
        exact hyx (congrArg Subtype.val (mem_singleton_iff.mp h'))
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z.2, fun h' => hz (mem_singleton_iff.mpr (Subtype.ext h'))⟩
    rw [himg]
    exact hpre.image _ continuous_subtype_val.continuousOn
  · rw [sdiff_singleton_eq_self hx]
    exact hE.2.1.isPreconnected

/-- `Ẽ` is the closure of `π⁻¹(E \ {x})`. -/
theorem strictDivisor_eq_closure (h : RegularAtDim (n := n) E x (n - 1)) (hEc : IsClosed E) :
    strictDivisor n x E = closure (blowupProj n ({x} : Set X) ⁻¹' (E \ {x})) := by
  have hSsub : blowupProj n ({x} : Set X) ⁻¹' (E \ {x}) ⊆ strictDivisor n x E :=
    fun q hq => Or.inl ⟨hq.2, hq.1⟩
  refine Subset.antisymm ?_ ((isClosed_strictDivisor h hEc).closure_subset_iff.mpr hSsub)
  intro q hq
  by_cases hb : q.base = x
  · set P := ofRegular h
    have h0 : P.deriv q.dirVec 0 = 0 := (mem_strictDivisor_iff_deriv h hb).mp hq
    have hne : P.deriv q.dirVec ≠ 0 := fun h' =>
      dirVec_ne_zero hb (P.deriv_injective (by rw [h', map_zero]))
    obtain ⟨j, hj⟩ : ∃ j : Fin n, P.deriv q.dirVec j ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hne (by ext k; exact h' k)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hj h0
    set c := P.chart j with hc
    have hqc : q ∈ c.source := (P.mem_source_iff j hb).mpr hj
    set w := c.toFun q with hw
    have hwt : w ∈ c.target := c.map_source hqc
    have hw0 : w 0 = 0 := by
      have := (mem_strictDivisor_iff_chart h hj0 hqc).mp hq
      exact this 0 (Finset.mem_singleton_self _)
    have hwj : w j = 0 := P.toFun_self j q hb
    set v : ComplexModel n := EuclideanSpace.single j (1 : ℂ) with hv
    let f : ℂ → PointBlowup n x := fun t => c.homeo.symm (w + t • v)
    have hcont : ContinuousAt (fun t : ℂ => w + t • v) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    have hlim : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 q) := by
      have h1 : Tendsto (fun t : ℂ => w + t • v) (𝓝 0) (𝓝 w) := by
        simpa using hcont.tendsto
      have h2 := (c.homeo.continuousAt_symm hwt).tendsto.comp h1
      have hq' : c.homeo.symm w = q := c.left_inv hqc
      rw [hq'] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    have hopen : ∀ᶠ t in 𝓝 (0 : ℂ), w + t • v ∈ c.target := by
      have h1 : Tendsto (fun t : ℂ => w + t • v) (𝓝 0) (𝓝 w) := by
        simpa using hcont.tendsto
      exact h1.eventually (c.isOpen_target.mem_nhds hwt)
    filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with t ht htne
    have hft : f t ∈ c.source := c.map_target ht
    have hcf : c.toFun (f t) = w + t • v := c.right_inv ht
    have hfj : c.toFun (f t) j ≠ 0 := by
      rw [hcf]
      simpa [hv, hwj] using htne
    have hfb : (f t).base ≠ x := by
      intro hfb
      exact hfj (P.toFun_self j (f t) hfb)
    have hf0 : c.toFun (f t) ∈ coordZeroSet ({0} : Finset (Fin n)) := by
      intro k hk
      rw [Finset.mem_singleton.mp hk, hcf]
      simp [hv, hw0, Ne.symm hj0]
    have hfY := (mem_strictDivisor_iff_chart h hj0 hft).mpr hf0
    rcases hfY with ⟨_, hfE⟩ | ⟨hfb', _⟩
    · exact ⟨hfE, hfb⟩
    · exact absurd hfb' hfb
  · rcases hq with ⟨_, hqE⟩ | ⟨hb', _⟩
    · exact subset_closure ⟨hqE, hb⟩
    · exact absurd hb' hb

/-- `π⁻¹(E \ {x})` is connected. -/
theorem isPreconnected_preimage_diff [NeZero (n - 1)]
    (hE : IsClosedConnectedSubmanifold n E (n - 1)) :
    IsPreconnected (blowupProj n ({x} : Set X) ⁻¹' (E \ {x})) := by
  obtain ⟨s, hs, hsπ, hsec⟩ :=
    BlowupIsomorphismOff.exists_section_compl (isBlowupAlong_pointBlowup (n := n) x)
  have hpre := isPreconnected_diff_singleton hE x
  have hsub : IsPreconnected ((Subtype.val : ({x}ᶜ : Set X) → X) ⁻¹' (E \ {x})) :=
    hpre.preimage_of_isOpenMap Subtype.val_injective
      isClosed_singleton.isOpen_compl.isOpenMap_subtype_val
      (fun y hy => ⟨⟨y, hy.2⟩, rfl⟩)
  have himg : blowupProj n ({x} : Set X) ⁻¹' (E \ {x}) =
      s '' ((Subtype.val : ({x}ᶜ : Set X) → X) ⁻¹' (E \ {x})) := by
    ext q
    constructor
    · intro hq
      exact ⟨⟨blowupProj n ({x} : Set X) q, hq.2⟩, hq, hsec q hq.2⟩
    · rintro ⟨y, hy, rfl⟩
      show blowupProj n ({x} : Set X) (s y) ∈ E \ {x}
      rw [show blowupProj n ({x} : Set X) (s y) = y.1 from congrFun hsπ y]
      exact hy
  rw [himg]
  exact hsub.image _ hs.continuous.continuousOn

/-- **The strict transform `Ẽ` is a closed connected smooth hypersurface of the point
blow-up** (`dim E = n - 1 ≥ 1`). -/
theorem isClosedConnectedSubmanifold_strictDivisor [NeZero (n - 1)]
    (hE : IsClosedConnectedSubmanifold n E (n - 1)) (hx : x ∈ E) :
    IsClosedConnectedSubmanifold n (strictDivisor n x E) (n - 1) := by
  have h := hE.2.2 x hx
  refine ⟨isClosed_strictDivisor h hE.1, ?_, fun q hq => ?_⟩
  · rw [strictDivisor_eq_closure h hE.1]
    refine ⟨?_, (isPreconnected_preimage_diff hE).closure⟩
    -- `E \ {x}` is nonempty since `E` has positive dimension
    have hne : (E \ {x}).Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hcon
      have hEx : E = {x} := Subset.antisymm hcon (singleton_subset_iff.mpr hx)
      let _ := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le n 1) hE.2.2
      have _ := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.sub_le n 1) hE.2.2
      let pt : E := ⟨x, hx⟩
      have : Nonempty E := ⟨pt⟩
      have hi := interior_singleton_eq_empty (n := n - 1) pt
      have huniv : ({pt} : Set E) = univ := by
        ext z
        simp only [mem_singleton_iff, mem_univ, iff_true]
        have hz : (z : X) ∈ ({x} : Set X) := by
          rw [← hEx]
          exact z.2
        exact Subtype.ext hz
      rw [huniv, interior_univ] at hi
      exact univ_nonempty.ne_empty hi
    obtain ⟨y, hy⟩ := hne
    obtain ⟨q, hq⟩ := (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong
      (isBlowupAlong_pointBlowup (n := n) x)).2.1.isClosedMap.isQuotientMap
        (isBlowupAlong_pointBlowup (n := n) x).contMDiff.continuous
        (fun z => (AnalyticModificationConnectedFibres.isConnected_fibre
          (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong
            (isBlowupAlong_pointBlowup (n := n) x)) z).1.nonempty) |>.surjective y
    exact ⟨q, subset_closure (show blowupProj n ({x} : Set X) q ∈ E \ {x} by rw [hq]; exact hy)⟩
  · by_cases hb : q.base = x
    · exact regularAtDim_strictDivisor_of_base_eq h hq hb
    · have hqE : q.base ∈ E := strictDivisor_subset hx hq
      exact regularAtDim_strictDivisor_of_base_ne hb (hE.2.2 _ hqE)

end StrictGeometry

/-! ### The divisor-first flag -/

section DivisorFlag

variable {n : ℕ} [NeZero n] {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {E : Set X} {x : X}

/-- The linear levels `ℙ(dΦ⁻¹ V_i)`, `i ≥ 2`, lie on `Ẽ`. -/
theorem level_subset_strictDivisor (h : RegularAtDim (n := n) E x (n - 1)) {i : ℕ} (hi : 2 ≤ i) :
    (ofRegular h).level i ⊆ strictDivisor n x E := by
  intro q hq
  obtain ⟨hb, hd⟩ := (ofRegular h).mem_level_iff.mp hq
  rw [mem_strictDivisor_iff_deriv h hb]
  exact (mem_flagSubspace.mp hd) 0 (by rw [Fin.val_zero]; omega)

/-- `ℙ(dΦ⁻¹ V_2) = ℙ(T_xE) = Ẽ ∩ π⁻¹(x)`. -/
theorem level_two_eq (h : RegularAtDim (n := n) E x (n - 1)) :
    (ofRegular h).level 2 = strictDivisor n x E ∩ blowupProj n ({x} : Set X) ⁻¹' {x} := by
  ext q
  constructor
  · intro hq
    exact ⟨level_subset_strictDivisor h le_rfl hq, ((ofRegular h).mem_level_iff.mp hq).1⟩
  · rintro ⟨hq, hb⟩
    have hb' : q.base = x := hb
    refine (ofRegular h).mem_level_iff.mpr ⟨hb', mem_flagSubspace.mpr fun k hk => ?_⟩
    have hk0 : k = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    rw [hk0]
    exact (mem_strictDivisor_iff_deriv h hb').mp hq

variable (n x) in
/-- **The divisor-first flag** of the point blow-up at `x ∈ E`:
`Y_0 = Bl_x X`, `Y_1 = Ẽ`, `Y_i = ℙ(dΦ⁻¹ V_i) ⊆ ℙ(T_xE)` for `i ≥ 2`. -/
def divisorFlag (h : RegularAtDim (n := n) E x (n - 1)) (i : Fin (n + 1)) :
    Set (PointBlowup n x) :=
  if (i : ℕ) = 0 then univ else if (i : ℕ) = 1 then strictDivisor n x E else (ofRegular h).level i

theorem divisorFlag_one (h : RegularAtDim (n := n) E x (n - 1)) :
    divisorFlag n x h 1 = strictDivisor n x E := by
  have h1 : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (Nat.succ_lt_succ (NeZero.pos n))]
  unfold divisorFlag
  rw [if_neg (by omega), if_pos h1]

/-- **The divisor-first flag is a smooth flag** (`dim X ≥ 2`, `X` connected, `E` a closed
connected smooth hypersurface through `x`). -/
theorem isSmoothFlag_divisorFlag [NeZero (n - 1)] [ConnectedSpace X]
    (hE : IsClosedConnectedSubmanifold n E (n - 1)) (hx : x ∈ E) :
    IsSmoothFlag (divisorFlag n x (hE.2.2 x hx)) := by
  set h := hE.2.2 x hx
  refine ⟨if_pos rfl, ?_, fun i => ?_⟩
  · intro i i' hii'
    have hle : (i : ℕ) ≤ i' := hii'
    show divisorFlag n x h i' ⊆ divisorFlag n x h i
    by_cases hi0 : (i : ℕ) = 0
    · have h0 : divisorFlag n x h i = univ := if_pos hi0
      rw [h0]
      exact subset_univ _
    by_cases hi1 : (i : ℕ) = 1
    · have h1 : divisorFlag n x h i = strictDivisor n x E := by
        unfold divisorFlag
        rw [if_neg hi0, if_pos hi1]
      rw [h1]
      unfold divisorFlag
      rw [if_neg (by omega)]
      split_ifs with hi'1
      · exact Subset.rfl
      · exact level_subset_strictDivisor h (by omega)
    · have h2 : divisorFlag n x h i = (ofRegular h).level i := by
        unfold divisorFlag
        rw [if_neg hi0, if_neg hi1]
      have h2' : divisorFlag n x h i' = (ofRegular h).level i' := by
        unfold divisorFlag
        rw [if_neg (by omega), if_neg (by omega)]
      rw [h2, h2']
      exact (ofRegular h).level_antitone hle
  · have hin : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.2
    by_cases hi0 : (i : ℕ) = 0
    · have h0 : divisorFlag n x h i = univ := if_pos hi0
      rw [h0, hi0, Nat.sub_zero]
      exact ⟨isClosed_univ, isConnected_univ,
        fun z _ => AnalyticIrreducibleComponents.regularAtDim_univ z⟩
    by_cases hi1 : (i : ℕ) = 1
    · have h1 : divisorFlag n x h i = strictDivisor n x E := by
        unfold divisorFlag
        rw [if_neg hi0, if_pos hi1]
      rw [h1, hi1]
      exact isClosedConnectedSubmanifold_strictDivisor hE hx
    · have h2 : divisorFlag n x h i = (ofRegular h).level i := by
        unfold divisorFlag
        rw [if_neg hi0, if_neg hi1]
      rw [h2]
      exact (ofRegular h).isClosedConnectedSubmanifold_level hi0 hin

/-- **`Ẽ` is the strict transform** `closure (π⁻¹E \ Exc π)` of `E` (`dim X ≥ 2`). -/
theorem strictDivisor_eq_strictTransform [NeZero (n - 1)]
    (h : RegularAtDim (n := n) E x (n - 1)) (hEc : IsClosed E) :
    strictDivisor n x E = strictTransform n (blowupProj n ({x} : Set X)) E := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  have hm : 1 ≤ m := by
    have := NeZero.pos (m + 1 - 1)
    omega
  have hexc := exceptionalLocus_eq_preimage (isBlowupAlong_pointBlowup (n := m + 1) x)
    (k := 0) (fun y hy => (DominationLogResolution.isClosedConnectedSubmanifold_singleton x).2.2
      y hy) (by omega)
  rw [strictTransform, hexc, ← preimage_sdiff]
  exact strictDivisor_eq_closure h hEc

end DivisorFlag

/-! ### The flag-bearing blow-up of a point of a divisor -/

section DivisorGeometry

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 2)) X]
  [IsComplexManifold (m + 2) X] [CompactSpace X] [ConnectedSpace X]

instance neZero_succ_succ_sub_one : NeZero (m + 2 - 1) := ⟨by omega⟩

/-- **A smooth flag whose first member is a given smooth divisor.** For a compact connected
Kähler manifold `X` of dimension `m + 2`, a closed connected smooth hypersurface `E` and `x ∈ E`:
the blow-up of `x` with a Kähler form and the flag `Ẽ ⊇ ℙ(T_xE) ⊇ ⋯`, as an
`OriginalFlagGeometry`. -/
def divisorFlagGeometry (omega : KahlerBackground (m + 2) X) {E : Set X}
    (hE : IsClosedConnectedSubmanifold (m + 2) E (m + 1)) {x : X} (hx : x ∈ E) :
    OriginalFlagGeometry.{u} (m + 2) :=
  OriginalFlagGeometry.ofOriginal
    (Classical.choice (nonempty_kahlerBackground_pointBlowup omega x))
    (divisorFlag (m + 2) x (hE.2.2 x hx)) (isSmoothFlag_divisorFlag hE hx)

/-- The projection of the divisor-first flag-bearing blow-up. -/
def divisorFlagGeometryProj (omega : KahlerBackground (m + 2) X) {E : Set X}
    (hE : IsClosedConnectedSubmanifold (m + 2) E (m + 1)) {x : X} (hx : x ∈ E) :
    (divisorFlagGeometry omega hE hx).carrier → X :=
  blowupProj (m + 2) ({x} : Set X)

theorem isAnalyticModification_divisorFlagGeometry (omega : KahlerBackground (m + 2) X)
    {E : Set X} (hE : IsClosedConnectedSubmanifold (m + 2) E (m + 1)) {x : X} (hx : x ∈ E) :
    IsAnalyticModification (n := m + 2) (divisorFlagGeometryProj omega hE hx) :=
  isAnalyticModification_pointBlowup x

theorem isBlowupAlong_divisorFlagGeometryProj (omega : KahlerBackground (m + 2) X)
    {E : Set X} (hE : IsClosedConnectedSubmanifold (m + 2) E (m + 1)) {x : X} (hx : x ∈ E) :
    IsBlowupAlong (m + 2) ({x} : Set X) (divisorFlagGeometryProj omega hE hx) :=
  isBlowupAlong_pointBlowup x

/-- **The first flag member is the strict transform of `E`.** -/
theorem divisorFlagGeometry_flag_one (omega : KahlerBackground (m + 2) X) {E : Set X}
    (hE : IsClosedConnectedSubmanifold (m + 2) E (m + 1)) {x : X} (hx : x ∈ E) :
    (divisorFlagGeometry omega hE hx).flag 1 =
      strictTransform (m + 2) (divisorFlagGeometryProj omega hE hx) E :=
  (divisorFlag_one (hE.2.2 x hx)).trans (strictDivisor_eq_strictTransform (hE.2.2 x hx) hE.1)

/-- Off the exceptional divisor the first flag member is `π⁻¹(E)`. -/
theorem divisorFlagGeometry_flag_one_diff (omega : KahlerBackground (m + 2) X) {E : Set X}
    (hE : IsClosedConnectedSubmanifold (m + 2) E (m + 1)) {x : X} (hx : x ∈ E) :
    (divisorFlagGeometry omega hE hx).flag 1 \ divisorFlagGeometryProj omega hE hx ⁻¹' {x} =
      divisorFlagGeometryProj omega hE hx ⁻¹' (E \ {x}) := by
  show divisorFlag (m + 2) x (hE.2.2 x hx) 1 \ _ = _
  rw [divisorFlag_one]
  ext q
  constructor
  · rintro ⟨hq, hqx⟩
    have hqx' : q.base ≠ x := hqx
    rcases hq with ⟨_, hqE⟩ | ⟨hb, _⟩
    · exact ⟨hqE, hqx'⟩
    · exact absurd hb hqx'
  · rintro ⟨hqE, hqx⟩
    exact ⟨Or.inl ⟨hqx, hqE⟩, hqx⟩

end DivisorGeometry

end SGPT.Blowup

import SGPT.Hodge.ConePositive
import SGPT.Foundations.Analysis.Pending.MovingBottChernClassCurrentCompactness

/-!
# Weak continuity of the class map on closed positive currents

Blueprint `claude-hodge` (lane HODGE-TOP, package `HodgeTopology`), node
`claude-hodge:prop-class-weak-continuity` (positive currents, sequences); Xia, *Foundations of
pluripotential theory*, q07, after `def:real-one-one-cohomology` ("the map `T ↦ {T}` on closed
currents is continuous for weak convergence").  Used in Xia, *Singularities in global
pluripotential theory*, `thm:DT` (Step 3, the finite-tail estimate `∑_{i>N} a_i{E_i} ≤ ε{ω}`),
`prop:dscontbdiv` and `cor:Iequiv_curr_b_div`.

Let `X` be a compact connected Kähler manifold.  Weak convergence `T_k → T` of currents is
convergence on every chart test form (the convergence of TN's compactness theorems).

* `bottChernClass_eq_of_tendsto` (**closed graph**): if closed positive `(1,1)`-currents `T_k`
  converge weakly to `T` and their classes converge to `β` (Euclidean topology), then `{T} = β`.
  By TN's compactness of positive currents with converging classes
  (`MovingBottChernClassCurrentCompactness.exists_tendsto_moving_class_originalClosedPositiveCurrent`)
  some ultrafilter limit `S` of `(T_k)` has class `β`; weak limits are unique, so `S = T`.
* `tendsto_bottChernClass_of_tendsto` (**weak continuity**): if closed positive
  `(1,1)`-currents `T_k` converge weakly to `T`, then `{T_k} → {T}`.  In coordinates of a basis,
  every subsequence of classes has a convergent sub-subsequence, whose limit is `{T}` by the closed
  graph property: if the classes were unbounded along a subsequence, the currents
  `T_k / ‖{T_k}‖` would converge weakly to `0` with classes of norm `1`, and a limit class of
  norm `1` would be the class of `0`.
* `eventually_classPseudoeffective_smul_sub` (**finite-tail estimate**, the form used in the proof
  of `thm:DT`): if closed positive currents `R_k` converge weakly to `0`, then for every `ε > 0`,
  eventually `{R_k} ≤ ε{ω}` (indeed `ε{ω} - {R_k}` contains a smooth semipositive form).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped Topology

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  SGPT.Foundations.Analysis.Pending.XiaoPureSmoothTopology
  SGPT.Foundations.Analysis.Pending.XiaoPureSmoothBottChernClosure

/-! ### Coordinates on a finite-dimensional space with the Euclidean topology -/

section Coordinates

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]

/-- Convergence in the Euclidean topology is convergence of the coordinates in a finite basis. -/
theorem tendsto_euclideanTopology_iff_equivFun (b : Module.Basis ι ℝ V) {κ : Type*}
    {l : Filter κ} {x : κ → V} {y : V} :
    Tendsto x l (@nhds V (SGPT.BDivisor.euclideanTopology V) y) ↔
      Tendsto (fun k => b.equivFun (x k)) l (𝓝 (b.equivFun y)) := by
  rw [SGPT.BDivisor.tendsto_euclideanTopology_iff, tendsto_pi_nhds]
  constructor
  · intro h j
    exact h (b.coord j)
  · intro h f
    have hf : ∀ v, f v = ∑ j, f (b j) * b.equivFun v j := by
      intro v
      calc f v = f (∑ j, b.equivFun v j • b j) := by rw [b.sum_equivFun v]
        _ = ∑ j, f (b j) * b.equivFun v j := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, smul_eq_mul, mul_comm]
    have hfx : (fun k => f (x k)) = fun k => ∑ j, f (b j) * b.equivFun (x k) j :=
      funext fun k => hf (x k)
    rw [hfx, hf y]
    exact tendsto_finsetSum _ fun j _ => (h j).const_mul _

end Coordinates

/-! ### The Euclidean topology is finer than TN's smooth class topology -/

section PureSmooth

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

/-- On a finite-dimensional `H^{1,1}`, the identity is continuous from the Euclidean topology to
TN's quotient topology of the smooth (all coefficient jets) topology of forms: a linear section
`α ↦ ∑ⱼ αⱼ θⱼ` is continuous into the smooth topology of forms. -/
theorem continuous_id_euclidean_classPureSmooth (w : KahlerBackground n M) {ι : Type*}
    [Fintype ι] (b : Module.Basis ι ℝ (RealBottChern n M)) :
    Continuous[SGPT.BDivisor.euclideanTopology (RealBottChern n M), classPureSmoothTopology]
      (id : RealBottChern n M → RealBottChern n M) := by
  classical
  let : TopologicalSpace (ClosedRealOneOneForm n M) := formPureSmoothTopology
  have : IsTopologicalAddGroup (ClosedRealOneOneForm n M) :=
    formPureSmoothTopology_isTopologicalAddGroup
  have : ContinuousSMul ℝ (ClosedRealOneOneForm n M) := formPureSmoothTopology_continuousSMul
  let B : ι → ClosedRealOneOneForm n M := fun j => Quotient.out (b j)
  have hB (j) : RealBottChern.ofRepresentative (B j) = b j := Quotient.out_eq _
  have hid : (id : RealBottChern n M → RealBottChern n M) =
      RealBottChern.ofRepresentative ∘ fun α => ∑ j, b.coord j α • B j := by
    funext α
    change α = RealBottChern.ofRepresentativeLinearMap (∑ j, b.coord j α • B j)
    rw [map_sum]
    conv_lhs => rw [← b.sum_repr α]
    refine Finset.sum_congr rfl fun j _ => ?_
    change b.repr α j • b j = RealBottChern.ofRepresentative (b.coord j α • B j)
    rw [RealBottChern.ofRepresentative_smul, hB, Module.Basis.coord_apply]
  rw [hid]
  have h1 : @Continuous _ _ (SGPT.BDivisor.euclideanTopology (RealBottChern n M))
      formPureSmoothTopology (fun α => ∑ j, b.coord j α • B j) := by
    let := SGPT.BDivisor.euclideanTopology (RealBottChern n M)
    exact continuous_finsetSum _ fun j _ =>
      (SGPT.BDivisor.continuous_euclideanTopology (b.coord j)).smul continuous_const
  exact @Continuous.comp _ _ _ (SGPT.BDivisor.euclideanTopology _) formPureSmoothTopology
    classPureSmoothTopology _ _
    (@IsOpenQuotientMap.continuous _ _ formPureSmoothTopology classPureSmoothTopology _
      (isOpenQuotientMap_ofRepresentative (n := n) (M := M) w)) h1

end PureSmooth

/-! ### The closed graph property and weak continuity -/

section Weak

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

local notation "Cur" => ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)

local notation "cls" => bottChernClass (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)

/-- Weak convergence of currents: convergence on every chart test form. -/
def WeakTendsto (T : ℕ → Cur) (S : Cur) : Prop :=
  ∀ (e : ComplexChart (m + 1) X)
    (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
      (Module.finrank ℝ (ComplexModel (m + 1)) - 2)),
    Tendsto (fun k => (T k).val.inChart e η) atTop (𝓝 (S.val.inChart e η))

omit [CompactSpace X] in
theorem WeakTendsto.comp {T : ℕ → Cur} {S : Cur} (h : WeakTendsto T S) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) : WeakTendsto (T ∘ φ) S :=
  fun e η => (h e η).comp hφ

variable [ConnectedSpace X]

/-- **Closed graph property of the class map**: if closed positive `(1,1)`-currents `T_k`
converge weakly to `T` and their classes converge to `β` in the Euclidean topology, then
`{T} = β`. -/
theorem bottChernClass_eq_of_tendsto (w : KahlerBackground (m + 1) X) {T : ℕ → Cur} {S : Cur}
    (hT : ∀ k, IsFullPositive (T k).val) (hTS : WeakTendsto T S)
    {β : RealBottChern (m + 1) X}
    (hβ : Tendsto (fun k => cls (T k)) atTop
      (@nhds _ (SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) X)) β)) :
    cls S = β := by
  have := finiteDimensional_realBottChern w
  have hpure : Tendsto (fun k => cls (T k)) atTop
      (@nhds _ classPureSmoothTopology β) :=
    (@Continuous.tendsto _ _ (SGPT.BDivisor.euclideanTopology _) classPureSmoothTopology _
      (continuous_id_euclidean_classPureSmooth w
        (Module.finBasis ℝ (RealBottChern (m + 1) X))) β).comp hβ
  set U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨S', -, hS'β, hS'lim⟩ :=
    MovingBottChernClassCurrentCompactness.exists_tendsto_moving_class_originalClosedPositiveCurrent
      w U hU β T hT hpure
  have hSS' : S' = S := by
    apply Subtype.ext
    apply GlobalCurrent.ext
    intro e η
    exact tendsto_nhds_unique (hS'lim e η) ((hTS e η).mono_left hU)
  rw [← hSS', hS'β]

/-- **Weak continuity of the class map on closed positive currents**
(`claude-hodge:prop-class-weak-continuity`, for positive currents and sequences): if closed
positive `(1,1)`-currents `T_k` converge weakly to `T`, then `{T_k} → {T}` in the Euclidean
topology of `H^{1,1}(X, ℝ)`. -/
theorem tendsto_bottChernClass_of_tendsto (w : KahlerBackground (m + 1) X) {T : ℕ → Cur}
    {S : Cur} (hT : ∀ k, IsFullPositive (T k).val) (hTS : WeakTendsto T S) :
    Tendsto (fun k => cls (T k)) atTop
      (@nhds _ (SGPT.BDivisor.euclideanTopology (RealBottChern (m + 1) X)) (cls S)) := by
  have := finiteDimensional_realBottChern w
  set b := Module.finBasis ℝ (RealBottChern (m + 1) X)
  -- the closed graph property in coordinates
  have hgraph : ∀ (T' : ℕ → Cur) (S' : Cur), (∀ k, IsFullPositive (T' k).val) →
      WeakTendsto T' S' → ∀ v, Tendsto (fun k => b.equivFun (cls (T' k))) atTop (𝓝 v) →
        b.equivFun (cls S') = v := by
    intro T' S' hT' hTS' v hv
    have hβ : Tendsto (fun k => cls (T' k)) atTop
        (@nhds _ (SGPT.BDivisor.euclideanTopology _) (b.equivFun.symm v)) := by
      rw [tendsto_euclideanTopology_iff_equivFun b, LinearEquiv.apply_symm_apply]
      exact hv
    rw [bottChernClass_eq_of_tendsto w hT' hTS' hβ, LinearEquiv.apply_symm_apply]
  rw [tendsto_euclideanTopology_iff_equivFun b]
  apply tendsto_of_subseq_tendsto
  intro ns hns
  set a : ℕ → (Fin (Module.finrank ℝ (RealBottChern (m + 1) X)) → ℝ) :=
    fun k => b.equivFun (cls (T (ns k))) with ha
  by_cases hbdd : ∃ C : ℝ, ∃ᶠ k in atTop, a k ∈ Metric.closedBall 0 C
  · obtain ⟨C, hC⟩ := hbdd
    obtain ⟨v, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Fin _ → ℝ) C).tendsto_subseq' hC
    refine ⟨φ, ?_⟩
    have hv := hgraph (T ∘ ns ∘ φ) S (fun k => hT _)
      (hTS.comp (hns.comp hφ.tendsto_atTop)) v hlim
    rw [hv]
    exact hlim
  · exfalso
    push Not at hbdd
    -- the norms of the coordinates tend to infinity
    have hnorm : Tendsto (fun k => ‖a k‖) atTop atTop := by
      rw [tendsto_atTop]
      intro C
      filter_upwards [hbdd C] with k hk
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hk
      exact hk.le
    set c : ℕ → ℝ := fun k => ‖a k‖⁻¹ with hc
    have hc0 : ∀ k, 0 ≤ c k := fun k => inv_nonneg.mpr (norm_nonneg _)
    have hclim : Tendsto c atTop (𝓝 0) := hnorm.inv_tendsto_atTop
    have hpos : ∀ᶠ k in atTop, 0 < ‖a k‖ := hnorm.eventually_gt_atTop 0
    set T' : ℕ → Cur := fun k => c k • T (ns k) with hT'def
    have hT' : ∀ k, IsFullPositive (T' k).val := by
      intro k e α hα
      change 0 ≤ (c k • (T (ns k)).val).inChart e _
      rw [GlobalCurrent.inChart_smul]
      change 0 ≤ c k * _
      exact mul_nonneg (hc0 k) (hT (ns k) e α hα)
    have hTS' : WeakTendsto T' ((0 : ℝ) • S) := by
      intro e η
      change Tendsto (fun k => (c k • (T (ns k)).val).inChart e η) atTop
        (𝓝 (((0 : ℝ) • S.val).inChart e η))
      simp only [GlobalCurrent.inChart_smul]
      change Tendsto (fun k => c k * (T (ns k)).val.inChart e η) atTop
        (𝓝 ((0 : ℝ) * S.val.inChart e η))
      exact hclim.mul ((hTS e η).comp hns)
    have hcls : ∀ k, b.equivFun (cls (T' k)) = c k • a k := by
      intro k
      have h := (bottChernClassLinearMap (M := X) (canonicalBasis (m + 1))
        (Nat.succ_pos m)).map_smul (c k) (T (ns k))
      change b.equivFun (bottChernClassLinearMap (M := X) (canonicalBasis (m + 1))
        (Nat.succ_pos m) (c k • T (ns k))) = c k • a k
      rw [h, map_smul]
      rfl
    have hunit : ∀ᶠ k in atTop, ‖b.equivFun (cls (T' k))‖ = 1 := by
      filter_upwards [hpos] with k hk
      rw [hcls, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 k), hc, inv_mul_cancel₀ hk.ne']
    obtain ⟨v, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Fin _ → ℝ) 1).tendsto_subseq'
      (hunit.mono fun k hk => by
        rw [Metric.mem_closedBall, dist_zero_right, hk]).frequently
    have hv := hgraph (T' ∘ φ) ((0 : ℝ) • S) (fun k => hT' _)
      (hTS'.comp hφ.tendsto_atTop) v hlim
    have h0 : cls ((0 : ℝ) • S) = 0 := by
      change bottChernClassLinearMap (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)
        ((0 : ℝ) • S) = 0
      rw [map_smul, zero_smul]
    rw [h0, map_zero] at hv
    have hnv : ‖v‖ = 1 := by
      have h1 : Tendsto (fun k => ‖b.equivFun (cls (T' (φ k)))‖) atTop (𝓝 ‖v‖) :=
        hlim.norm
      have h2 : Tendsto (fun k => ‖b.equivFun (cls (T' (φ k)))‖) atTop (𝓝 1) :=
        tendsto_const_nhds.congr' ((hφ.tendsto_atTop.eventually hunit).mono fun k hk => hk.symm)
      exact tendsto_nhds_unique h1 h2
    rw [← hv, norm_zero] at hnv
    exact zero_ne_one hnv

/-- **The finite-tail estimate**: if closed positive `(1,1)`-currents `R_k` converge weakly to
`0`, then for every `ε > 0`, eventually `ε{ω} - {R_k}` contains a smooth semipositive form; in
particular `{R_k} ≤ ε{ω}` in the pseudo-effective order. -/
theorem eventually_classPseudoeffective_smul_sub (w : KahlerBackground (m + 1) X)
    {R : ℕ → Cur} (hR : ∀ k, IsFullPositive (R k).val) (hR0 : WeakTendsto R 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (∃ σ : ClosedRealOneOneForm (m + 1) X, σ.val.IsSemipositive ∧
        RealBottChern.ofRepresentative σ = ε • RealBottChern.ofRepresentative w.form - cls (R k)) ∧
      ClassPseudoeffectiveViaPotentials
        (ε • RealBottChern.ofRepresentative w.form - cls (R k)) := by
  have hlim := tendsto_bottChernClass_of_tendsto w hR hR0
  have h0 : cls (0 : Cur) = 0 :=
    (bottChernClassLinearMap (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_zero
  rw [h0] at hlim
  filter_upwards [eventually_exists_semipositive_of_tendsto w hlim hε] with k hk
  obtain ⟨⟨σ, hσ, hσc⟩, -⟩ := hk
  rw [zero_add] at hσc
  refine ⟨⟨σ, hσ, hσc⟩, ?_⟩
  rw [← hσc]
  exact ⟨fun _ => 0, (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ⟩

end Weak

end SGPT.Hodge

import SGPT.Unibranch.FNLWSP

/-!
# FN80 Lemma 5.2: restricting a branched covering to a small polydisc

Source: `[FN80]` Lemma 5.2, proof: "if we replace `X` by `X' = X ∩ Δ'ⁿ` with a small polydisc
`Δ'ⁿ (= Δ'ᵏ × Δ'ⁿ⁻ᵏ)` centred at `p₀` [...] then `π|X'` is a branched covering of `Δ'ᵏ` with
sheet number `< λ`".

`IsBranchedCovering.exists_restrict_pdisc`: for the coordinate projection `π : ℂⁿ → ℂᵏ`
(first `k` coordinates) and `p₀ ∈ X`, every neighbourhood of `p₀` contains a polydisc `Δ'`
centred at `p₀` such that `X ∩ Δ' → π(Δ')` is a branched covering whose number of sheets is
the sheet number of `p₀`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense

variable {n k : ℕ}

theorem convex_pdisc (c : ComplexModel n) (r : Fin n → ℝ) : Convex ℝ (pdisc c r) := by
  have h : pdisc c r = ⋂ i, ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ
      ).toLinearMap ⁻¹' ball (c i) (r i) := by
    ext z
    simp [dist_eq_norm]
  rw [h]
  exact convex_iInter fun i => (convex_ball _ _).linear_preimage _

theorem coordinateProjection_apply_of_le (hk : k ≤ n) (z : ComplexModel n) (j : Fin k) :
    coordinateProjection n k z j = z ⟨j.1, lt_of_lt_of_le j.2 hk⟩ := by
  rw [coordinateProjection_apply, dif_pos (lt_of_lt_of_le j.2 hk)]

/-- Two points with the same projection differ in a fibre coordinate. -/
theorem exists_fibre_coord_ne (hk : k ≤ n) {p q : ComplexModel n}
    (hπ : coordinateProjection n k p = coordinateProjection n k q) (hpq : p ≠ q) :
    ∃ i : Fin n, k ≤ i.1 ∧ p i ≠ q i := by
  by_contra h
  push Not at h
  apply hpq
  ext i
  by_cases hi : i.1 < k
  · have := congrArg (fun z : ComplexModel k => z ⟨i.1, hi⟩) hπ
    simpa [coordinateProjection_apply_of_le hk] using this
  · exact h i (not_lt.mp hi)

variable {X : Set (ComplexModel n)} {D : Set (ComplexModel k)} {deg : ℕ} {δ : ComplexModel k → ℂ}

namespace IsBranchedCovering

/-- **Restriction to a small polydisc** around a point `p₀ ∈ X`, inside a given neighbourhood:
a branched covering whose number of sheets is the sheet number of `p₀`. -/
theorem exists_restrict_pdisc (hX : IsBranchedCovering X (coordinateProjection n k) D deg δ)
    (hk : k ≤ n) {p₀ : ComplexModel n} (hp₀ : p₀ ∈ X) {O : Set (ComplexModel n)} (hO : IsOpen O)
    (hp₀O : p₀ ∈ O) :
    ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧ pdisc p₀ r ⊆ O ∧ ∃ D' : Set (ComplexModel k),
      MapsTo (coordinateProjection n k) (pdisc p₀ r) D' ∧
      IsBranchedCovering (X ∩ pdisc p₀ r) (coordinateProjection n k) D'
        (sheetNumber X (coordinateProjection n k) δ p₀) δ := by
  classical
  set π := coordinateProjection n k with hπdef
  set z₀ := π p₀ with hz₀def
  have hz₀ : z₀ ∈ D := hX.mem_base hp₀
  set F₀ := fibre X π z₀ with hF₀def
  have hF₀ : F₀.Finite := hX.finite_fibre z₀ hz₀
  obtain ⟨ρ₀, hρ₀, hρ₀O⟩ := Metric.isOpen_iff.mp hO p₀ hp₀O
  -- the fibre radius `s`
  have hfar : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ p ∈ F₀, p ≠ p₀ →
      ∃ i : Fin n, k ≤ i.1 ∧ 3 * s < ‖p i - p₀ i‖ := by
    refine (hF₀.eventually_all).mpr fun p hp => ?_
    by_cases hpp : p = p₀
    · exact Eventually.of_forall fun _ h => absurd hpp h
    · obtain ⟨i, hik, hi⟩ := exists_fibre_coord_ne hk hp.2 hpp
      have hpos : 0 < ‖p i - p₀ i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hi)
      filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < ‖p i - p₀ i‖ / 3)] with s hs _
      exact ⟨i, hik, by linarith [hs.2]⟩
  obtain ⟨s, ⟨hsfar, hsρ⟩, hspos⟩ := ((hfar.and (Ioo_mem_nhdsGT
    (by positivity : (0 : ℝ) < ρ₀ / (n + 1)))).and self_mem_nhdsWithin).exists
  have hs : (0 : ℝ) < s := hspos
  -- the base radius `t`
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (Filter.Eventually.and
    (hX.isOpen_base.mem_nhds hz₀ : ∀ᶠ z in 𝓝 z₀, z ∈ D) (hX.eventually_fibre_subset hz₀ hs))
  set t := min s (η / (k + 1)) with htdef
  have ht : 0 < t := lt_min hs (by positivity)
  set r : Fin n → ℝ := fun i => if i.1 < k then t else s with hrdef
  have hr : ∀ i, 0 < r i := fun i => by simp only [hrdef]; split_ifs <;> assumption
  have hrs : ∀ i, r i ≤ s := fun i => by
    simp only [hrdef]; split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  set V : Set (ComplexModel n) := {x | ∀ i : Fin n, k ≤ i.1 → ‖x i - p₀ i‖ < s} with hVdef
  set D' : Set (ComplexModel k) := pdisc z₀ (fun _ => t) with hD'def
  have hVo : IsOpen V := by
    have : V = ⋂ i : Fin n, ⋂ (_ : k ≤ i.1), {x : ComplexModel n | ‖x i - p₀ i‖ < s} := by
      ext x; simp [hVdef]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun _ => isOpen_lt
      (continuous_norm.comp (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).sub
        continuous_const)) continuous_const
  have hD'ball : D' ⊆ ball z₀ η := pdisc_subset_ball z₀ hη (min_le_right _ _) fun _ => le_rfl
  have hD'D : D' ⊆ D := fun z hz => (hηsub (hD'ball hz)).1
  have hset : X ∩ V ∩ π ⁻¹' D' = X ∩ pdisc p₀ r := by
    ext x
    simp only [mem_inter_iff, mem_preimage, hVdef, hD'def, pdisc, mem_ofPred_eq, hrdef]
    constructor
    · rintro ⟨⟨hx, hxV⟩, hxD'⟩
      refine ⟨hx, fun i => ?_⟩
      split_ifs with hi
      · have := hxD' ⟨i.1, hi⟩
        rwa [hπdef, hz₀def, coordinateProjection_apply_of_le hk,
          coordinateProjection_apply_of_le hk] at this
      · exact hxV i (not_lt.mp hi)
    · rintro ⟨hx, hxr⟩
      refine ⟨⟨hx, fun i hi => ?_⟩, fun j => ?_⟩
      · have := hxr i
        rwa [if_neg (not_lt.mpr hi)] at this
      · have := hxr ⟨j.1, lt_of_lt_of_le j.2 hk⟩
        rw [if_pos j.2] at this
        rw [hπdef, hz₀def, coordinateProjection_apply_of_le hk, coordinateProjection_apply_of_le hk]
        exact this
  -- points near another point of `F₀` are far from `V`
  have hfarV : ∀ ε : ℝ, ε ≤ s → ∀ p ∈ F₀, p ≠ p₀ → ∀ x ∈ ball p ε,
      ∃ i : Fin n, k ≤ i.1 ∧ s < ‖x i - p₀ i‖ := by
    intro ε hε p hp hpp x hx
    obtain ⟨i, hik, hi⟩ := hsfar p hp hpp
    refine ⟨i, hik, ?_⟩
    have h1 : ‖x i - p i‖ < ε := by
      calc ‖x i - p i‖ = ‖(x - p) i‖ := by simp
        _ ≤ ‖x - p‖ := norm_apply_le _ i
        _ < ε := by rw [← dist_eq_norm]; exact hx
    have h2 : ‖p i - p₀ i‖ ≤ ‖x i - p₀ i‖ + ‖x i - p i‖ := by
      calc ‖p i - p₀ i‖ = ‖(x i - p₀ i) - (x i - p i)‖ := by ring_nf
        _ ≤ ‖x i - p₀ i‖ + ‖x i - p i‖ := norm_sub_le _ _
    linarith
  have hnearV : ∀ ε : ℝ, ε ≤ s → ∀ x ∈ ball p₀ ε, x ∈ V := by
    intro ε hε x hx i _
    calc ‖x i - p₀ i‖ = ‖(x - p₀) i‖ := by simp
      _ ≤ ‖x - p₀‖ := norm_apply_le _ i
      _ < s := by rw [← dist_eq_norm]; linarith [mem_ball.mp hx]
  have hclosed : IsClosed {x : ComplexModel n | ∀ i : Fin n, k ≤ i.1 → ‖x i - p₀ i‖ ≤ s} := by
    have : {x : ComplexModel n | ∀ i : Fin n, k ≤ i.1 → ‖x i - p₀ i‖ ≤ s} =
        ⋂ i : Fin n, ⋂ (_ : k ≤ i.1), {x : ComplexModel n | ‖x i - p₀ i‖ ≤ s} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_le
      (continuous_norm.comp (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).sub
        continuous_const)) continuous_const
  have hclV : closure V ⊆ {x : ComplexModel n | ∀ i : Fin n, k ≤ i.1 → ‖x i - p₀ i‖ ≤ s} :=
    closure_minimal (fun x hx i hi => (hx i hi).le) hclosed
  have hfront : ∀ z ∈ D', ∀ x ∈ fibre X π z, x ∉ frontier V := by
    intro z hz x hx hxf
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp ((hηsub (hD'ball hz)).2 hx)
    by_cases hpp : p = p₀
    · rw [hpp] at hxp
      have hxV := hnearV s le_rfl x hxp
      exact hxf.2 (by rw [hVo.interior_eq]; exact hxV)
    · obtain ⟨i, hik, hi⟩ := hfarV s le_rfl p hp hpp x hxp
      have := hclV hxf.1 i hik
      linarith
  have hm : ∃ z ∈ D', δ z ≠ 0 ∧ (fibre X π z ∩ V).ncard = sheetNumber X π δ p₀ := by
    obtain ⟨m, hm⟩ := hX.exists_isSheetNumber hp₀
    rw [sheetNumber_eq (hX.neBot_generic hz₀) hm]
    obtain ⟨ε, ⟨hεm, hεs⟩, hεpos⟩ := ((hm.and (Ioo_mem_nhdsGT hs)).and self_mem_nhdsWithin).exists
    have hε : (0 : ℝ) < ε := hεpos
    have := hX.neBot_generic hz₀
    have hD'z : D' ∈ 𝓝 z₀ := (isOpen_pdisc z₀ _).mem_nhds (fun _ => by simpa using ht)
    obtain ⟨z, ⟨hzm, hzA, hzD'⟩, hzδ⟩ := ((hεm.and (Filter.Eventually.and
      (nhdsWithin_le_nhds (hX.eventually_fibre_subset hz₀ hε))
      (nhdsWithin_le_nhds hD'z : ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀, z ∈ D'))).and
      self_mem_nhdsWithin).exists
    refine ⟨z, hzD', hzδ, ?_⟩
    rw [← hzm]
    congr 1
    ext x
    constructor
    · rintro ⟨hx, hxV⟩
      refine ⟨hx, ?_⟩
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hzA hx)
      by_cases hpp : p = p₀
      · rwa [hpp] at hxp
      · obtain ⟨i, hik, hi⟩ := hfarV ε hεs.2.le p hp hpp x hxp
        linarith [hxV i hik]
    · rintro ⟨hx, hxb⟩
      exact ⟨hx, hnearV ε hεs.2.le x hxb⟩
  have hR := hX.restrict hVo (isOpen_pdisc z₀ _) (convex_pdisc z₀ _).isPreconnected hD'D hfront hm
  rw [hset] at hR
  refine ⟨r, hr, ?_, D', ?_, hR⟩
  · exact (pdisc_subset_ball p₀ hρ₀ hsρ.2.le hrs).trans hρ₀O
  · intro x hx
    have : x ∈ X ∩ V ∩ π ⁻¹' D' ∨ x ∉ X := by
      by_cases hxX : x ∈ X
      · left; rw [hset]; exact ⟨hxX, hx⟩
      · right; exact hxX
    intro j
    have := hx ⟨j.1, lt_of_lt_of_le j.2 hk⟩
    simp only [hrdef, if_pos j.2] at this
    rw [hπdef, hz₀def, coordinateProjection_apply_of_le hk, coordinateProjection_apply_of_le hk]
    exact this

end IsBranchedCovering

end SGPT.Unibranch.FNL

import SGPT.Foundations.Analysis.Pending.BoundedIntegrationByParts
import SGPT.Foundations.Analysis.Pending.RelativeEnergy
import SGPT.Foundations.Analysis.Pending.GlobalSlotComparison
import SGPT.Foundations.Analysis.Pending.GlobalSlotPerm

set_option autoImplicit false

/-!
# The Monge–Ampère energy of bounded potentials

Let `(M, ω)` be a compact Kähler manifold of dimension `n`, `θ` a smooth closed real
`(1,1)`-form and `φ`, `u`, `v` bounded `θ`-PSH functions. Xia's energy (SGPT, Definition 3.1.6,
`RelativeEnergy.relativeEnergyOfMinimalType`) is

  `E^φ(u) = (1/(n+1)) Σ_{j=0}^n ∫ (u - φ) θ_u^j ∧ θ_φ^{n-j}`.

This module proves, for bounded potentials:

* the **cocycle formula** (Xia (3.32)): `E^φ(u) - E^φ(v) = E^v(u)`
  (`relativeEnergyOfMinimalType_sub`);
* the **comparison inequalities** (Xia (3.33)):
  `∫ (u - v) θ_u^n ≤ E^φ(u) - E^φ(v) ≤ ∫ (u - v) θ_v^n`;
* **monotonicity** (Xia, Lemma 3.1.3) and **concavity** (Xia, Lemma 3.1.5);
* the **translation formula** (Xia (3.31)): `E^φ(u + c) = E^φ(u) + c ∫ θ_φ^n`.

## The proof of the cocycle

Write `μ(x^j y^{k-j} S)` for the global mixed measure of the tuple carrying `x` in the slots
`< j`, `y` in the slots `j ≤ i < k` and a fixed bounded tuple `S` in the slots `≥ k` (`lay`).
By induction on `k` (`sum_lay_cocycle`):

  `Σ_{j ≤ k} ∫ (a - c) dμ(a^j c^{k-j} S) - Σ_{j ≤ k} ∫ (b - c) dμ(b^j c^{k-j} S)
     = Σ_{j ≤ k} ∫ (a - b) dμ(a^j b^{k-j} S)`.

The step `k → k + 1` puts `c` into slot `k` of the background, applies the induction
hypothesis, and then integration by parts in slot `k`
(`BoundedIntegrationByParts.integral_sub_symm`) with slot symmetry
(`GlobalSlotPerm.globalMixedMeasure_perm`) makes the remaining sum telescope. For `k = n` this is
the cocycle formula.

The comparison inequalities follow from `∫ (u - v) d(μ[u] - μ[v]) ≤ 0` in one slot
(`integral_sub_le_of_update`), which is the comparison principle in one slot
(`GlobalSlotComparison.globalMixedMeasure_comparison`) integrated over the levels (layer-cake
formula).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.BoundedMongeAmpereEnergy

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar BoundedGlobalProduct
open RelativeEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Layout tuples -/

/-- The tuple with `x` in the slots `< j`, `y` in the slots `j ≤ i < k`, and `S i` in the
slots `i ≥ k`. -/
def lay (k j : ℕ) (x y : M → EReal) (S : Fin n → M → EReal) : Fin n → M → EReal :=
  fun i => if i.val < j then x else if i.val < k then y else S i

theorem lay_psh {θ : SmoothRealForm n M 2} {k j : ℕ} {x y : M → EReal}
    {S : Fin n → M → EReal} (hx : ThetaPlurisubharmonic θ x) (hy : ThetaPlurisubharmonic θ y)
    (hS : ∀ i, ThetaPlurisubharmonic θ (S i)) (i : Fin n) :
    ThetaPlurisubharmonic θ (lay k j x y S i) := by
  unfold lay
  split_ifs
  · exact hx
  · exact hy
  · exact hS i

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem lay_bounded {k j : ℕ} {x y : M → EReal} {S : Fin n → M → EReal}
    (hx : IsBoundedPotential x) (hy : IsBoundedPotential y)
    (hS : ∀ i, IsBoundedPotential (S i)) (i : Fin n) : IsBoundedPotential (lay k j x y S i) := by
  unfold lay
  split_ifs
  · exact hx
  · exact hy
  · exact hS i

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- With no `y`-slot below `k`, the background is untouched. -/
theorem lay_zero_zero (x y : M → EReal) (S : Fin n → M → EReal) : lay 0 0 x y S = S := by
  funext i
  simp [lay]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Moving the slot `k` from the background to the `y`-block. -/
theorem lay_succ_eq {k j : ℕ} (hk : k < n) (x y : M → EReal)
    (S : Fin n → M → EReal) :
    lay (k + 1) j x y S = lay k j x y (Function.update S ⟨k, hk⟩ y) := by
  funext i
  unfold lay
  by_cases h1 : i.val < j
  · simp [h1]
  · by_cases h2 : i.val < k
    · have : i.val < k + 1 := by omega
      simp [h1, h2, this]
    · by_cases h3 : i.val = k
      · have hi : i = ⟨k, hk⟩ := Fin.ext h3
        simp [hi]
      · have h4 : ¬ i.val < k + 1 := by omega
        have hi : i ≠ ⟨k, hk⟩ := fun h => h3 (by rw [h])
        simp [h1, h2, h4, Function.update_of_ne hi]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Putting any `z` in slot `k` of `lay k j` is `lay k j` with background updated at `k`. -/
theorem update_lay_eq_lay_update {k j : ℕ} (hk : k < n) (hj : j ≤ k) (x y z : M → EReal)
    (S : Fin n → M → EReal) :
    Function.update (lay k j x y S) ⟨k, hk⟩ z = lay k j x y (Function.update S ⟨k, hk⟩ z) := by
  funext i
  by_cases hi : i = ⟨k, hk⟩
  · subst hi
    have h1 : ¬ k < j := not_lt.mpr hj
    simp [lay, h1]
  · rw [Function.update_of_ne hi]
    unfold lay
    split_ifs <;> simp_all

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Putting `y` in slot `k` of `lay k j` gives `lay (k + 1) j`. -/
theorem update_lay_eq {k j : ℕ} (hk : k < n) (hj : j ≤ k) (x y : M → EReal)
    (S : Fin n → M → EReal) :
    Function.update (lay k j x y S) ⟨k, hk⟩ y = lay (k + 1) j x y S := by
  rw [update_lay_eq_lay_update hk hj, lay_succ_eq hk]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Putting `x` in slot `k` of `lay k j` is `lay (k + 1) (j + 1)` after swapping slots `j` and
`k`. -/
theorem update_lay_swap {k j : ℕ} (hk : k < n) (hj : j ≤ k) (x y : M → EReal)
    (S : Fin n → M → EReal) :
    (fun i => Function.update (lay k j x y S) ⟨k, hk⟩ x
        (Equiv.swap (⟨j, by omega⟩ : Fin n) ⟨k, hk⟩ i)) = lay (k + 1) (j + 1) x y S := by
  funext i
  by_cases hij : i = ⟨j, by omega⟩
  · subst hij
    rw [Equiv.swap_apply_left]
    simp [lay]
  · by_cases hik : i = ⟨k, hk⟩
    · subst hik
      rw [Equiv.swap_apply_right]
      by_cases hjk : j = k
      · subst hjk
        simp [lay]
      · have hne : (⟨j, by omega⟩ : Fin n) ≠ ⟨k, hk⟩ := fun h => hjk (Fin.mk.inj h)
        rw [Function.update_of_ne hne]
        have h2 : j < k := lt_of_le_of_ne hj hjk
        have h3 : ¬ k < j + 1 := by omega
        simp [lay, h2, h3]
    · rw [Equiv.swap_apply_of_ne_of_ne hij hik, Function.update_of_ne hik]
      have h1 : i.val ≠ j := fun h => hij (Fin.ext h)
      have h2 : i.val ≠ k := fun h => hik (Fin.ext h)
      unfold lay
      by_cases a1 : i.val < j
      · have : i.val < j + 1 := by omega
        simp [a1, this]
      · by_cases a2 : i.val < k
        · have b1 : ¬ i.val < j + 1 := by omega
          have b2 : i.val < k + 1 := by omega
          simp [a1, a2, b1, b2]
        · have b1 : ¬ i.val < j + 1 := by omega
          have b2 : ¬ i.val < k + 1 := by omega
          simp [a1, a2, b1, b2]

/-! ### The cocycle of the layout sums -/

section Cocycle

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The global mixed measure of `lay k j x y S`, all forms equal to `θ`. -/
def layMeasure (θ : ClosedRealOneOneForm n M) (k j : ℕ) (x y : M → EReal)
    (S : Fin n → M → EReal) (hx : ThetaPlurisubharmonic θ.val x)
    (hy : ThetaPlurisubharmonic θ.val y) (hS : ∀ i, ThetaPlurisubharmonic θ.val (S i)) :
    Measure M :=
  globalMixedMeasure (fun _ => θ) (lay k j x y S) (lay_psh hx hy hS)

theorem layMeasure_isFiniteMeasure (θ : ClosedRealOneOneForm n M) (k j : ℕ) {x y : M → EReal}
    {S : Fin n → M → EReal} (hx : ThetaPlurisubharmonic θ.val x)
    (hy : ThetaPlurisubharmonic θ.val y) (hS : ∀ i, ThetaPlurisubharmonic θ.val (S i))
    (hxb : IsBoundedPotential x) (hyb : IsBoundedPotential y)
    (hSb : ∀ i, IsBoundedPotential (S i)) : IsFiniteMeasure (layMeasure θ k j x y S hx hy hS) :=
  globalMixedMeasure_isFiniteMeasure_of_bounded _ (lay_bounded hxb hyb hSb)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] in
/-- The integral of a difference of two bounded measurable potentials. -/
theorem integral_toReal_sub {μ : Measure M} [IsFiniteMeasure μ] {f g : M → EReal}
    (hf : Measurable fun x => (f x).toReal) (hg : Measurable fun x => (g x).toReal)
    (hfb : IsBoundedPotential f) (hgb : IsBoundedPotential g) :
    ∫ x, ((f x).toReal - (g x).toReal) ∂μ = (∫ x, (f x).toReal ∂μ) - ∫ x, (g x).toReal ∂μ :=
  BoundedIntegrationByParts.integral_sub_of_bounded hf hg
    (GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hfb)
    (GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hgb)

/-- **The cocycle of the layout sums.** For bounded `θ`-PSH `a, b, c`, every `k ≤ n` and every
bounded `θ`-PSH background `S`:
`Σ_{j ≤ k} ∫ (a - c) dμ(a^j c^{k-j} S) - Σ_{j ≤ k} ∫ (b - c) dμ(b^j c^{k-j} S)
  = Σ_{j ≤ k} ∫ (a - b) dμ(a^j b^{k-j} S)`. -/
theorem sum_lay_cocycle (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {a b c : M → EReal} (ha : ThetaPlurisubharmonic θ.val a) (hb : ThetaPlurisubharmonic θ.val b)
    (hc : ThetaPlurisubharmonic θ.val c) (hab : IsBoundedPotential a)
    (hbb : IsBoundedPotential b) (hcb : IsBoundedPotential c) :
    ∀ k, k ≤ n → ∀ (S : Fin n → M → EReal) (hS : ∀ i, ThetaPlurisubharmonic θ.val (S i)),
      (∀ i, IsBoundedPotential (S i)) →
      (∑ j ∈ Finset.range (k + 1),
          ∫ x, ((a x).toReal - (c x).toReal) ∂(layMeasure θ k j a c S ha hc hS)) -
        ∑ j ∈ Finset.range (k + 1),
          ∫ x, ((b x).toReal - (c x).toReal) ∂(layMeasure θ k j b c S hb hc hS) =
      ∑ j ∈ Finset.range (k + 1),
          ∫ x, ((a x).toReal - (b x).toReal) ∂(layMeasure θ k j a b S ha hb hS) := by
  classical
  have hma : Measurable fun x => (a x).toReal := GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal ha
  have hmb : Measurable fun x => (b x).toReal := GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hb
  have hmc : Measurable fun x => (c x).toReal := GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hc
  -- integrals of differences split into differences of integrals
  have hsplit : ∀ (μ : Measure M) [IsFiniteMeasure μ] {f g : M → EReal},
      ThetaPlurisubharmonic θ.val f → ThetaPlurisubharmonic θ.val g →
      IsBoundedPotential f → IsBoundedPotential g →
      ∫ x, ((f x).toReal - (g x).toReal) ∂μ = (∫ x, (f x).toReal ∂μ) - ∫ x, (g x).toReal ∂μ :=
    fun μ _ f g hf hg hfb hgb => integral_toReal_sub
      (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hf)
      (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hg) hfb hgb
  intro k
  induction k with
  | zero =>
    intro _ S hS hSb
    simp only [zero_add, Finset.sum_range_one]
    have e : ∀ (x y : M → EReal) (hx : ThetaPlurisubharmonic θ.val x)
        (hy : ThetaPlurisubharmonic θ.val y),
        layMeasure θ 0 0 x y S hx hy hS = globalMixedMeasure (fun _ => θ) S hS := fun x y hx hy =>
      BoundedIntegrationByParts.globalMixedMeasure_congr' rfl (lay_zero_zero x y S) _ _
    rw [e, e, e]
    have := globalMixedMeasure_isFiniteMeasure_of_bounded (θ := fun _ => θ) hS hSb
    rw [hsplit _ ha hc hab hcb, hsplit _ hb hc hbb hcb, hsplit _ ha hb hab hbb]
    ring
  | succ k ih =>
    intro hk S hS hSb
    have hkn : k < n := by omega
    set i₀ : Fin n := ⟨k, hkn⟩ with hi₀
    -- the backgrounds with `c`, `b` in slot `k`
    have hSc : ∀ i, ThetaPlurisubharmonic θ.val (Function.update S i₀ c i) := by
      intro i; by_cases h : i = i₀
      · subst h; simpa using hc
      · simpa [Function.update_of_ne h] using hS i
    have hScb : ∀ i, IsBoundedPotential (Function.update S i₀ c i) := by
      intro i; by_cases h : i = i₀
      · subst h; simpa using hcb
      · simpa [Function.update_of_ne h] using hSb i
    have hSbb : ∀ i, ThetaPlurisubharmonic θ.val (Function.update S i₀ b i) := by
      intro i; by_cases h : i = i₀
      · subst h; simpa using hb
      · simpa [Function.update_of_ne h] using hS i
    have hIH := ih (by omega) (Function.update S i₀ c) hSc hScb
    -- finiteness of all layout measures
    have hfin : ∀ (k' j : ℕ) {x y : M → EReal} {T : Fin n → M → EReal}
        (hx : ThetaPlurisubharmonic θ.val x) (hy : ThetaPlurisubharmonic θ.val y)
        (hT : ∀ i, ThetaPlurisubharmonic θ.val (T i)), IsBoundedPotential x →
        IsBoundedPotential y → (∀ i, IsBoundedPotential (T i)) →
        IsFiniteMeasure (layMeasure θ k' j x y T hx hy hT) :=
      fun k' j _ _ _ hx hy hT hxb hyb hTb =>
        layMeasure_isFiniteMeasure θ k' j hx hy hT hxb hyb hTb
    -- low terms: `lay (k + 1) j x c S = lay k j x c S'`
    have hlow : ∀ (x : M → EReal) (hx : ThetaPlurisubharmonic θ.val x) (j : ℕ),
        layMeasure θ (k + 1) j x c S hx hc hS =
          layMeasure θ k j x c (Function.update S i₀ c) hx hc hSc := fun x hx j =>
      BoundedIntegrationByParts.globalMixedMeasure_congr' rfl (lay_succ_eq hkn x c S) _ _
    -- the top terms
    have htopA : layMeasure θ (k + 1) (k + 1) a c S ha hc hS =
        layMeasure θ (k + 1) (k + 1) a b S ha hb hS :=
      BoundedIntegrationByParts.globalMixedMeasure_congr' rfl (by
        funext i; simp only [lay]; split_ifs <;> rfl) _ _
    have htopB : layMeasure θ (k + 1) (k + 1) b c S hb hc hS =
        layMeasure θ (k + 1) 0 a b S ha hb hS :=
      BoundedIntegrationByParts.globalMixedMeasure_congr' rfl (by
        funext i; simp only [lay]; split_ifs <;> first | rfl | omega) _ _
    -- the sums of the statement, split at the top index
    have hsA : (∑ j ∈ Finset.range (k + 1 + 1),
        ∫ x, ((a x).toReal - (c x).toReal) ∂(layMeasure θ (k + 1) j a c S ha hc hS)) =
        (∑ j ∈ Finset.range (k + 1), ∫ x, ((a x).toReal - (c x).toReal) ∂(layMeasure θ k j a c
          (Function.update S i₀ c) ha hc hSc)) +
        ∫ x, ((a x).toReal - (c x).toReal) ∂(layMeasure θ (k + 1) (k + 1) a b S ha hb hS) := by
      rw [Finset.sum_range_succ, htopA]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hlow]
    have hsB : (∑ j ∈ Finset.range (k + 1 + 1),
        ∫ x, ((b x).toReal - (c x).toReal) ∂(layMeasure θ (k + 1) j b c S hb hc hS)) =
        (∑ j ∈ Finset.range (k + 1), ∫ x, ((b x).toReal - (c x).toReal) ∂(layMeasure θ k j b c
          (Function.update S i₀ c) hb hc hSc)) +
        ∫ x, ((b x).toReal - (c x).toReal) ∂(layMeasure θ (k + 1) 0 a b S ha hb hS) := by
      rw [Finset.sum_range_succ, htopB]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hlow]
    rw [hsA, hsB, Finset.sum_range_succ (fun j =>
      ∫ x, ((a x).toReal - (b x).toReal) ∂(layMeasure θ (k + 1) j a b S ha hb hS)) (k + 1)]
    -- integration by parts in slot `k`, for each `j ≤ k`
    set L : ℕ → Measure M := fun j => layMeasure θ (k + 1) j a b S ha hb hS with hL
    set Lc : ℕ → Measure M := fun j => layMeasure θ k j a b (Function.update S i₀ c) ha hb hSc
      with hLc
    have hibp : ∀ j ∈ Finset.range (k + 1),
        (∫ x, ((a x).toReal - (b x).toReal) ∂(Lc j)) =
          (∫ x, ((a x).toReal - (b x).toReal) ∂(L j)) -
            ((∫ x, ((b x).toReal - (c x).toReal) ∂(L (j + 1))) -
              ∫ x, ((b x).toReal - (c x).toReal) ∂(L j)) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      set w := lay k j a b S with hw
      have hwb : ∀ i, IsBoundedPotential (w i) := lay_bounded hab hbb hSb
      have hconst : Function.update (fun _ : Fin n => θ) i₀ θ = fun _ => θ :=
        Function.update_eq_self i₀ _
      have hwx : ∀ (x : M → EReal), ThetaPlurisubharmonic θ.val x →
          ∀ i, ThetaPlurisubharmonic ((fun _ : Fin n => θ) i).val (Function.update w i₀ x i) := by
        intro x hx i
        by_cases h : i = i₀
        · subst h; simpa using hx
        · simpa [Function.update_of_ne h] using lay_psh ha hb hS i
      have hwx' : ∀ (x : M → EReal), ThetaPlurisubharmonic θ.val x →
          ∀ i, ThetaPlurisubharmonic (Function.update (fun _ : Fin n => θ) i₀ θ i).val
            (Function.update w i₀ x i) := by
        intro x hx; rw [hconst]; exact hwx x hx
      have h := BoundedIntegrationByParts.integral_sub_symm omega hwb i₀ hab hbb hbb hcb
        (hwx a ha) (hwx b hb) (hwx' b hb) (hwx' c hc)
      -- identify the four measures
      have eb' : globalMixedMeasure (Function.update (fun _ : Fin n => θ) i₀ θ)
          (Function.update w i₀ b) (hwx' b hb) = L j :=
        BoundedIntegrationByParts.globalMixedMeasure_congr' hconst (update_lay_eq hkn hjk a b S) _ _
      have ec' : globalMixedMeasure (Function.update (fun _ : Fin n => θ) i₀ θ)
          (Function.update w i₀ c) (hwx' c hc) = Lc j :=
        BoundedIntegrationByParts.globalMixedMeasure_congr' hconst
          (update_lay_eq_lay_update hkn hjk a b c S) _ _
      have eb : globalMixedMeasure (fun _ : Fin n => θ) (Function.update w i₀ b) (hwx b hb) = L j :=
        BoundedIntegrationByParts.globalMixedMeasure_congr' rfl (update_lay_eq hkn hjk a b S) _ _
      have ea : globalMixedMeasure (fun _ : Fin n => θ) (Function.update w i₀ a) (hwx a ha) =
          L (j + 1) := by
        have hperm := GlobalSlotPerm.globalMixedMeasure_perm (hwx a ha)
          (Equiv.swap (⟨j, by omega⟩ : Fin n) i₀)
        rw [← hperm]
        exact BoundedIntegrationByParts.globalMixedMeasure_congr' rfl
          (update_lay_swap hkn hjk a b S) _ _
      rw [eb', ec', eb, ea] at h
      linarith
    rw [Finset.sum_congr rfl hibp] at hIH
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub
      (fun j => ∫ x, ((b x).toReal - (c x).toReal) ∂(L j))] at hIH
    -- the top-index terms are linear in the integrand
    have := layMeasure_isFiniteMeasure θ (k + 1) (k + 1) ha hb hS hab hbb hSb
    have := layMeasure_isFiniteMeasure θ (k + 1) 0 ha hb hS hab hbb hSb
    have e1 := hsplit (L (k + 1)) ha hc hab hcb
    have e2 := hsplit (L (k + 1)) hb hc hbb hcb
    have e3 := hsplit (L (k + 1)) ha hb hab hbb
    have e4 := hsplit (L 0) hb hc hbb hcb
    simp only [hL] at e1 e2 e3 e4 hIH ⊢
    linarith

end Cocycle

/-! ### The energy of bounded potentials -/

section Energy

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The canonical difference of two finite values is the difference of the reals. -/
theorem canonicalERealDiffToReal_of_bounded {u v : M → EReal} (hu : IsBoundedPotential u)
    (hv : IsBoundedPotential v) (x : M) :
    canonicalERealDiffToReal (u x) (v x) = (u x).toReal - (v x).toReal := by
  rw [← EReal.coe_toReal (hu.ne_top x) (hu.ne_bot x), ← EReal.coe_toReal (hv.ne_top x) (hv.ne_bot x),
    canonicalERealDiffToReal_coe_coe, EReal.toReal_coe, EReal.toReal_coe]

/-- The endpoint mixed measure `θ_u^j ∧ θ_φ^{n-j}` is a layout measure. -/
theorem endpointMixedMeasure_eq_layMeasure (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u) (j : Fin (n + 1)) :
    endpointMixedMeasure θ φ u hφ hu j =
      layMeasure θ n j.val u φ (fun _ => φ) hu.1 hφ.1 (fun _ => hφ.1) := by
  refine BoundedIntegrationByParts.globalMixedMeasure_congr' rfl ?_ _ _
  funext i
  simp [endpointMixedPotential, lay, i.isLt]

/-- `(n + 1) E^φ(u)` as a sum over the layout measures. -/
theorem relativeEnergyOfMinimalType_mul (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) :
    ((n : ℝ) + 1) * relativeEnergyOfMinimalType θ φ u hφ hu =
      ∑ j ∈ Finset.range (n + 1), ∫ x, ((u x).toReal - (φ x).toReal) ∂(layMeasure θ n j u φ
        (fun _ => φ) hu.1 hφ.1 (fun _ => hφ.1)) := by
  rw [relativeEnergyOfMinimalType, mul_div_cancel₀ _ (by positivity)]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∫ x, ((u x).toReal - (φ x).toReal) ∂(layMeasure θ n j u
    φ (fun _ => φ) hu.1 hφ.1 (fun _ => hφ.1)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [relativeEnergyTerm, endpointMixedMeasure_eq_layMeasure]
  exact integral_congr_ae (Eventually.of_forall fun x =>
    canonicalERealDiffToReal_of_bounded hub hφb x)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- In `lay n j`, the background is invisible. -/
theorem lay_n_eq (j : ℕ) (x y : M → EReal) (S T : Fin n → M → EReal) :
    lay n j x y S = lay n j x y T := by
  funext i
  simp [lay, i.isLt]

/-- **The cocycle formula** (Xia, SGPT (3.32)): for bounded `θ`-PSH `φ`, `u`, `v` on a compact
Kähler manifold, `E^φ(u) - E^φ(v) = E^v(u)`, that is
`E^φ(u) - E^φ(v) = (1/(n+1)) Σ_j ∫ (u - v) θ_u^j ∧ θ_v^{n-j}`. -/
theorem relativeEnergyOfMinimalType_sub (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v) :
    relativeEnergyOfMinimalType θ φ u hφ hu - relativeEnergyOfMinimalType θ φ v hφ hv =
      relativeEnergyOfMinimalType θ v u hv hu := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := sum_lay_cocycle omega θ hu.1 hv.1 hφ.1 hub hvb hφb n le_rfl (fun _ => φ)
    (fun _ => hφ.1) (fun _ => hφb)
  rw [← relativeEnergyOfMinimalType_mul θ hφ hu hφb hub,
    ← relativeEnergyOfMinimalType_mul θ hφ hv hφb hvb] at h
  have h2 := relativeEnergyOfMinimalType_mul θ hv hu hvb hub
  have e : ∀ j, layMeasure θ n j u v (fun _ => φ) hu.1 hv.1 (fun _ => hφ.1) =
      layMeasure θ n j u v (fun _ => v) hu.1 hv.1 (fun _ => hv.1) := fun j =>
    BoundedIntegrationByParts.globalMixedMeasure_congr' rfl (lay_n_eq j u v _ _) _ _
  simp only [e] at h
  rw [← h2] at h
  have h3 : ((n : ℝ) + 1) * (relativeEnergyOfMinimalType θ φ u hφ hu -
      relativeEnergyOfMinimalType θ φ v hφ hv) =
      ((n : ℝ) + 1) * relativeEnergyOfMinimalType θ v u hv hu := by
    rw [mul_sub, h]
  exact mul_left_cancel₀ hpos.ne' h3

end Energy

/-! ### One-slot negativity -/

section Negativity

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Subtracting a constant in one slot does not change the global mixed measure. -/
theorem globalMixedMeasure_update_sub_const {η : Fin n → ClosedRealOneOneForm n M}
    {w : Fin n → M → EReal} (i₀ : Fin n) {x : M → EReal} (s : ℝ)
    (hx : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ x i))
    (hxs : ∀ i, ThetaPlurisubharmonic (η i).val
      (Function.update w i₀ (fun p => x p - (s : EReal)) i)) :
    globalMixedMeasure η (Function.update w i₀ (fun p => x p - (s : EReal))) hxs =
      globalMixedMeasure η (Function.update w i₀ x) hx := by
  classical
  have h := GlobalMeasureInvariance.globalMixedMeasure_sub_const hx
    (fun i => if i = i₀ then s else 0)
  rw [← h]
  refine BoundedIntegrationByParts.globalMixedMeasure_congr' rfl ?_ _ _
  funext i p
  by_cases hi : i = i₀
  · subst hi; simp
  · simp [Function.update_of_ne hi, if_neg hi]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Shifted strict comparison of finite extended reals. -/
theorem sub_coe_neg_lt_iff {x y : EReal} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) (hy : y ≠ ⊥)
    (hy' : y ≠ ⊤) (t : ℝ) : x - ((-t : ℝ) : EReal) < y ↔ t < y.toReal - x.toReal := by
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, x = a := ⟨x.toReal, (EReal.coe_toReal hx' hx).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℝ, y = b := ⟨y.toReal, (EReal.coe_toReal hy' hy).symm⟩
  rw [← EReal.coe_sub, EReal.coe_lt_coe_iff, EReal.toReal_coe, EReal.toReal_coe]
  constructor <;> intro h <;> linarith

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Shifted weak comparison of finite extended reals. -/
theorem sub_coe_neg_le_iff {x y : EReal} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) (hy : y ≠ ⊥)
    (hy' : y ≠ ⊤) (t : ℝ) : x - ((-t : ℝ) : EReal) ≤ y ↔ t ≤ y.toReal - x.toReal := by
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, x = a := ⟨x.toReal, (EReal.coe_toReal hx' hx).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℝ, y = b := ⟨y.toReal, (EReal.coe_toReal hy' hy).symm⟩
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.toReal_coe, EReal.toReal_coe]
  constructor <;> intro h <;> linarith

/-- **The comparison principle in one slot, at a level.** For bounded `x`, `y` in slot `i₀` of
a bounded tuple on a compact Kähler manifold and every real `t`,
`μ[y] {t < y - x} ≤ μ[x] {t ≤ y - x}`. -/
theorem measure_lt_le_measure_le (omega : KahlerBackground n M)
    {η : Fin n → ClosedRealOneOneForm n M} {w : Fin n → M → EReal}
    (hwb : ∀ i, IsBoundedPotential (w i)) (i₀ : Fin n) {x y : M → EReal}
    (hxb : IsBoundedPotential x) (hyb : IsBoundedPotential y)
    (hx : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ x i))
    (hy : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ y i)) (t : ℝ) :
    globalMixedMeasure η (Function.update w i₀ y) hy {p | t < (y p).toReal - (x p).toReal} ≤
      globalMixedMeasure η (Function.update w i₀ x) hx {p | t ≤ (y p).toReal - (x p).toReal} := by
  classical
  set c : M → EReal := fun p => x p - ((-t : ℝ) : EReal) with hc_def
  have hxi : ThetaPlurisubharmonic (η i₀).val x := by simpa using hx i₀
  have hyi : ThetaPlurisubharmonic (η i₀).val y := by simpa using hy i₀
  have hci : ThetaPlurisubharmonic (η i₀).val c :=
    GlobalPotentialTransforms.thetaPlurisubharmonic_sub_const hxi (-t)
  have hc : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ c i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa using hci
    · simpa [Function.update_of_ne h] using hx i
  have hm : ∀ i, ThetaPlurisubharmonic (η i).val
      (Function.update w i₀ (fun p => max (c p) (y p)) i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa using BoundedGlobalProduct.ThetaPlurisubharmonic.max hci hyi
    · simpa [Function.update_of_ne h] using hx i
  have hcb : IsBoundedPotential c := by
    obtain ⟨a, b, hab⟩ := id hxb
    refine ⟨a + t, b + t, fun p => ?_⟩
    have h1 := (hab p).1
    have h2 := (hab p).2
    obtain ⟨r, hr⟩ : ∃ r : ℝ, x p = r :=
      ⟨(x p).toReal, (EReal.coe_toReal (hxb.ne_top p) (hxb.ne_bot p)).symm⟩
    simp only [hc_def, hr, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1 h2 ⊢
    constructor <;> linarith
  have hmb : IsBoundedPotential fun p => max (c p) (y p) := by
    obtain ⟨a, b, hab⟩ := id hcb
    obtain ⟨a', b', hab'⟩ := id hyb
    exact ⟨a, max b b', fun p => ⟨(hab p).1.trans (le_max_left _ _),
      max_le ((hab p).2.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
        ((hab' p).2.trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _)))⟩⟩
  have hwc : ∀ i, IsBoundedPotential (Function.update w i₀ c i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa using hcb
    · simpa [Function.update_of_ne h] using hwb i
  have hmass : globalMixedMeasure η (Function.update w i₀ (fun p => max (c p) (y p))) hm univ =
      globalMixedMeasure η (Function.update w i₀ c) hc univ := by
    have hva : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update (Function.update w i₀ c) i₀
        (fun p => max (c p) (y p)) i) := by
      rw [Function.update_idem]; exact hm
    have h := GlobalSlotStokes.globalMixedMeasure_update_univ_eq omega hc hwc i₀ hva hmb
    rwa [BoundedIntegrationByParts.globalMixedMeasure_congr' rfl (Function.update_idem _ _ _)
      hva hm] at h
  have hcmp := GlobalSlotComparison.globalMixedMeasure_comparison omega w i₀ hc hy hm hmass
  rw [globalMixedMeasure_update_sub_const i₀ (-t) hx hc] at hcmp
  have hs1 : {p | c p < y p} = {p | t < (y p).toReal - (x p).toReal} := by
    ext p
    exact sub_coe_neg_lt_iff (hxb.ne_bot p) (hxb.ne_top p) (hyb.ne_bot p) (hyb.ne_top p) t
  have hs2 : {p | c p ≤ y p} = {p | t ≤ (y p).toReal - (x p).toReal} := by
    ext p
    exact sub_coe_neg_le_iff (hxb.ne_bot p) (hxb.ne_top p) (hyb.ne_bot p) (hyb.ne_top p) t
  rwa [hs1, hs2] at hcmp

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] in
/-- The lower integral of the positive part of a bounded function on a finite measure is
finite. -/
theorem lintegral_ofReal_ne_top {μ : Measure M} [IsFiniteMeasure μ] {g : M → ℝ}
    (hgb : ∃ Q : ℝ, ∀ p, |g p| ≤ Q) : ∫⁻ p, ENNReal.ofReal (g p) ∂μ ≠ ⊤ := by
  obtain ⟨Q, hQ⟩ := hgb
  refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal Q ∂μ) ?_ ?_
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ univ)
  · exact lintegral_mono fun p => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hQ p))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The layer-cake integrand of the positive part, at a positive level. -/
theorem setOf_lt_max_zero {g : M → ℝ} {t : ℝ} (ht : 0 < t) :
    {p | t < max (g p) 0} = {p | t < g p} := by
  ext p
  simp only [Set.mem_ofPred_eq, lt_max_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (not_lt.mpr ht.le)
  · exact Or.inl

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem setOf_le_max_zero {g : M → ℝ} {t : ℝ} (ht : 0 < t) :
    {p | t ≤ max (g p) 0} = {p | t ≤ g p} := by
  ext p
  simp only [Set.mem_ofPred_eq, le_max_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (not_le.mpr ht)
  · exact Or.inl

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] in
theorem lintegral_ofReal_eq_max_zero (μ : Measure M) (g : M → ℝ) :
    ∫⁻ p, ENNReal.ofReal (g p) ∂μ = ∫⁻ p, ENNReal.ofReal (max (g p) 0) ∂μ := by
  refine lintegral_congr fun p => ?_
  rcases le_total (g p) 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos h, max_eq_right h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

/-- **Negativity in one slot**: `∫ (u - v) d(μ[u] - μ[v]) ≤ 0`, i.e.
`∫ (u - v) dμ[u] ≤ ∫ (u - v) dμ[v]`, for bounded `u`, `v` in slot `i₀` of a bounded tuple on a
compact Kähler manifold. -/
theorem integral_sub_le_of_update (omega : KahlerBackground n M)
    {η : Fin n → ClosedRealOneOneForm n M} {w : Fin n → M → EReal}
    (hwb : ∀ i, IsBoundedPotential (w i)) (i₀ : Fin n) {u v : M → EReal}
    (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v)
    (hu : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ u i))
    (hv : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ v i)) :
    ∫ p, ((u p).toReal - (v p).toReal) ∂(globalMixedMeasure η (Function.update w i₀ u) hu) ≤
      ∫ p, ((u p).toReal - (v p).toReal) ∂(globalMixedMeasure η (Function.update w i₀ v) hv) := by
  classical
  have hwu : ∀ i, IsBoundedPotential (Function.update w i₀ u i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa using hub
    · simpa [Function.update_of_ne h] using hwb i
  have hwv : ∀ i, IsBoundedPotential (Function.update w i₀ v i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa using hvb
    · simpa [Function.update_of_ne h] using hwb i
  have hfu := globalMixedMeasure_isFiniteMeasure_of_bounded hu hwu
  have hfv := globalMixedMeasure_isFiniteMeasure_of_bounded hv hwv
  set μu := globalMixedMeasure η (Function.update w i₀ u) hu with hμu
  set μv := globalMixedMeasure η (Function.update w i₀ v) hv with hμv
  set f : M → ℝ := fun p => (u p).toReal - (v p).toReal with hf
  have hui : ThetaPlurisubharmonic (η i₀).val u := by simpa using hu i₀
  have hvi : ThetaPlurisubharmonic (η i₀).val v := by simpa using hv i₀
  have hfm : Measurable f := (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hui).sub
    (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hvi)
  obtain ⟨Qu, hQu⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hub
  obtain ⟨Qv, hQv⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hvb
  have hfb : ∃ Q : ℝ, ∀ p, |f p| ≤ Q :=
    ⟨Qu + Qv, fun p => (abs_sub _ _).trans (add_le_add (hQu p) (hQv p))⟩
  have hfb' : ∃ Q : ℝ, ∀ p, |-f p| ≤ Q := by
    obtain ⟨Q, hQ⟩ := hfb
    exact ⟨Q, fun p => by rw [abs_neg]; exact hQ p⟩
  have hint : ∀ (μ : Measure M) [IsFiniteMeasure μ], Integrable f μ := fun μ _ => by
    obtain ⟨Q, hQ⟩ := hfb
    exact GlobalSlotStokes.integrable_of_measurable_bounded hfm hQ μ
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint μu),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint μv)]
  have hpos : ∫⁻ p, ENNReal.ofReal (f p) ∂μu ≤ ∫⁻ p, ENNReal.ofReal (f p) ∂μv := by
    rw [lintegral_ofReal_eq_max_zero μu f, lintegral_ofReal_eq_max_zero μv f,
      lintegral_eq_lintegral_meas_lt (f := fun p => max (f p) 0) μu
        (ae_of_all _ fun p => le_max_right _ _) (hfm.max measurable_const).aemeasurable,
      lintegral_eq_lintegral_meas_le (f := fun p => max (f p) 0) μv
        (ae_of_all _ fun p => le_max_right _ _) (hfm.max measurable_const).aemeasurable]
    refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [setOf_lt_max_zero ht, setOf_le_max_zero ht]
    exact measure_lt_le_measure_le omega hwb i₀ hvb hub hv hu t
  have hneg : ∫⁻ p, ENNReal.ofReal (-f p) ∂μv ≤ ∫⁻ p, ENNReal.ofReal (-f p) ∂μu := by
    have hfm' : Measurable fun p => -f p := hfm.neg
    rw [lintegral_ofReal_eq_max_zero μv (fun p => -f p), lintegral_ofReal_eq_max_zero μu (fun p => -f p),
      lintegral_eq_lintegral_meas_lt (f := fun p => max (-f p) 0) μv
        (ae_of_all _ fun p => le_max_right _ _) (hfm'.max measurable_const).aemeasurable,
      lintegral_eq_lintegral_meas_le (f := fun p => max (-f p) 0) μu
        (ae_of_all _ fun p => le_max_right _ _) (hfm'.max measurable_const).aemeasurable]
    refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    rw [setOf_lt_max_zero ht, setOf_le_max_zero ht]
    have e : ∀ p, -f p = (v p).toReal - (u p).toReal := fun p => by simp only [hf]; ring
    simp only [e]
    exact measure_lt_le_measure_le omega hwb i₀ hub hvb hu hv t
  have h1 := ENNReal.toReal_mono (lintegral_ofReal_ne_top hfb) hpos
  have h2 := ENNReal.toReal_mono (lintegral_ofReal_ne_top hfb') hneg
  linarith

end Negativity

/-! ### Comparison, monotonicity, concavity, translation -/

section Consequences

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- In `lay k j`, the slot `j < k` carries `y`; replacing it by `x` gives `lay k (j + 1)`. -/
theorem update_lay_at {k j : ℕ} (hj : j < n) (hjk : j < k) (x y : M → EReal)
    (S : Fin n → M → EReal) :
    Function.update (lay k j x y S) ⟨j, hj⟩ x = lay k (j + 1) x y S ∧
      Function.update (lay k j x y S) ⟨j, hj⟩ y = lay k j x y S := by
  constructor
  · funext i
    by_cases hi : i = ⟨j, hj⟩
    · subst hi; simp [lay]
    · rw [Function.update_of_ne hi]
      have : i.val ≠ j := fun h => hi (Fin.ext h)
      unfold lay
      by_cases a1 : i.val < j
      · have : i.val < j + 1 := by omega
        simp [a1, this]
      · have : ¬ i.val < j + 1 := by omega
        simp [a1, this]
  · funext i
    by_cases hi : i = ⟨j, hj⟩
    · subst hi; simp [lay, hjk]
    · rw [Function.update_of_ne hi]

/-- **The comparison inequalities** (Xia, SGPT (3.33)): for bounded `θ`-PSH `φ`, `u`, `v`,
`∫ (u - v) θ_u^n ≤ E^φ(u) - E^φ(v) ≤ ∫ (u - v) θ_v^n`. -/
theorem integral_le_relativeEnergyOfMinimalType_sub_le (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v) :
    ∫ x, ((u x).toReal - (v x).toReal) ∂(globalMixedMeasure (fun _ => θ) (fun _ => u)
        (fun _ => hu.1)) ≤
      relativeEnergyOfMinimalType θ φ u hφ hu - relativeEnergyOfMinimalType θ φ v hφ hv ∧
    relativeEnergyOfMinimalType θ φ u hφ hu - relativeEnergyOfMinimalType θ φ v hφ hv ≤
      ∫ x, ((u x).toReal - (v x).toReal) ∂(globalMixedMeasure (fun _ => θ) (fun _ => v)
        (fun _ => hv.1)) := by
  classical
  set S : Fin n → M → EReal := fun _ => v with hS
  set g : ℕ → ℝ := fun j => ∫ x, ((u x).toReal - (v x).toReal) ∂(layMeasure θ n j u v S hu.1 hv.1
    (fun _ => hv.1)) with hg
  -- one step: `g (j + 1) ≤ g j`
  have hstep : ∀ j, j < n → g (j + 1) ≤ g j := by
    intro j hj
    have hwb : ∀ i, IsBoundedPotential (lay n j u v S i) := lay_bounded hub hvb fun _ => hvb
    obtain ⟨e1, e2⟩ := update_lay_at hj hj u v S
    have hu' : ∀ i, ThetaPlurisubharmonic ((fun _ : Fin n => θ) i).val
        (Function.update (lay n j u v S) ⟨j, hj⟩ u i) := by
      rw [e1]; exact lay_psh hu.1 hv.1 fun _ => hv.1
    have hv' : ∀ i, ThetaPlurisubharmonic ((fun _ : Fin n => θ) i).val
        (Function.update (lay n j u v S) ⟨j, hj⟩ v i) := by
      rw [e2]; exact lay_psh hu.1 hv.1 fun _ => hv.1
    have h := integral_sub_le_of_update omega hwb ⟨j, hj⟩ hub hvb hu' hv'
    rwa [BoundedIntegrationByParts.globalMixedMeasure_congr' rfl e1 hu'
        (lay_psh hu.1 hv.1 fun _ => hv.1),
      BoundedIntegrationByParts.globalMixedMeasure_congr' rfl e2 hv'
        (lay_psh hu.1 hv.1 fun _ => hv.1)] at h
  have hup : ∀ j, j ≤ n → g j ≤ g 0 := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih => intro hj; exact (hstep j (by omega)).trans (ih (by omega))
  have hdown : ∀ m j, j + m = n → g n ≤ g j := by
    intro m
    induction m with
    | zero => intro j hj; simp only [add_zero] at hj; rw [hj]
    | succ m ih => intro j hj; exact (ih (j + 1) (by omega)).trans (hstep j (by omega))
  -- the energy difference is the average of the `g j`
  have hcoc := relativeEnergyOfMinimalType_sub omega θ hφ hu hv hφb hub hvb
  have hmul := relativeEnergyOfMinimalType_mul θ hv hu hvb hub
  have e : ∀ j, layMeasure θ n j u v (fun _ => v) hu.1 hv.1 (fun _ => hv.1) =
      layMeasure θ n j u v S hu.1 hv.1 (fun _ => hv.1) := fun _ => rfl
  simp only [e] at hmul
  have hsum : ((n : ℝ) + 1) * relativeEnergyOfMinimalType θ v u hv hu =
      ∑ j ∈ Finset.range (n + 1), g j := hmul
  have hlo : ((n : ℝ) + 1) * g n ≤ ∑ j ∈ Finset.range (n + 1), g j := by
    have := Finset.card_nsmul_le_sum (Finset.range (n + 1)) g (g n)
      fun j hj => hdown (n - j) j (by have := Finset.mem_range.mp hj; omega)
    simpa [nsmul_eq_mul] using this
  have hhi : ∑ j ∈ Finset.range (n + 1), g j ≤ ((n : ℝ) + 1) * g 0 := by
    have := Finset.sum_le_card_nsmul (Finset.range (n + 1)) g (g 0)
      fun j hj => hup j (by have := Finset.mem_range.mp hj; omega)
    simpa [nsmul_eq_mul] using this
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hgn : g n = ∫ x, ((u x).toReal - (v x).toReal) ∂(globalMixedMeasure (fun _ => θ)
      (fun _ => u) (fun _ => hu.1)) := by
    simp only [hg]
    congr 1
    exact BoundedIntegrationByParts.globalMixedMeasure_congr' rfl
      (by funext i; simp [lay, i.isLt]) _ _
  have hg0 : g 0 = ∫ x, ((u x).toReal - (v x).toReal) ∂(globalMixedMeasure (fun _ => θ)
      (fun _ => v) (fun _ => hv.1)) := by
    simp only [hg]
    congr 1
    exact BoundedIntegrationByParts.globalMixedMeasure_congr' rfl
      (by funext i; simp [lay, i.isLt]) _ _
  rw [← hgn, ← hg0, hcoc]
  constructor
  · nlinarith
  · nlinarith

/-- **Monotonicity of the energy** (Xia, SGPT Lemma 3.1.3) for bounded potentials: `u ≤ v`
implies `E^φ(u) ≤ E^φ(v)`. -/
theorem relativeEnergyOfMinimalType_mono (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v)
    (huv : u ≤ v) :
    relativeEnergyOfMinimalType θ φ u hφ hu ≤ relativeEnergyOfMinimalType θ φ v hφ hv := by
  have h := (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hv hu hφb hvb hub).1
  have hnn : 0 ≤ ∫ x, ((v x).toReal - (u x).toReal) ∂(globalMixedMeasure (fun _ => θ)
      (fun _ => v) (fun _ => hv.1)) :=
    integral_nonneg fun x => sub_nonneg.mpr
      (EReal.toReal_le_toReal (huv x) (hub.ne_bot x) (hvb.ne_top x))
  linarith

/-- **Concavity of the energy** (Xia, SGPT Lemma 3.1.5) for bounded potentials: for
`0 < t < 1`, `E^φ(t u + (1 - t) v) ≥ t E^φ(u) + (1 - t) E^φ(v)`. (The endpoints are trivial.) -/
theorem relativeEnergyOfMinimalType_concave (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) (hvb : IsBoundedPotential v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hw : IsThetaPshPotential θ.val fun x => (t : EReal) * u x + ((1 - t : ℝ) : EReal) * v x) :
    t * relativeEnergyOfMinimalType θ φ u hφ hu + (1 - t) * relativeEnergyOfMinimalType θ φ v hφ hv ≤
      relativeEnergyOfMinimalType θ φ _ hφ hw := by
  set w : M → EReal := fun x => (t : EReal) * u x + ((1 - t : ℝ) : EReal) * v x with hw_def
  have hwr : ∀ x, w x = ((t * (u x).toReal + (1 - t) * (v x).toReal : ℝ) : EReal) := by
    intro x
    rw [hw_def]
    simp only
    rw [← EReal.coe_toReal (hub.ne_top x) (hub.ne_bot x),
      ← EReal.coe_toReal (hvb.ne_top x) (hvb.ne_bot x), EReal.toReal_coe, EReal.toReal_coe,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  have hwb : IsBoundedPotential w := by
    obtain ⟨a, b, hab⟩ := id hub
    obtain ⟨a', b', hab'⟩ := id hvb
    refine ⟨t * a + (1 - t) * a', t * b + (1 - t) * b', fun x => ?_⟩
    rw [hwr x]
    have h1 := (hab x).1; have h2 := (hab x).2; have h3 := (hab' x).1; have h4 := (hab' x).2
    rw [← EReal.coe_toReal (hub.ne_top x) (hub.ne_bot x), EReal.coe_le_coe_iff] at h1 h2
    rw [← EReal.coe_toReal (hvb.ne_top x) (hvb.ne_bot x), EReal.coe_le_coe_iff] at h3 h4
    constructor <;> rw [EReal.coe_le_coe_iff] <;> nlinarith
  have hU := (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hu hw hφb hub hwb).2
  have hV := (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ hv hw hφb hvb hwb).2
  set μw := globalMixedMeasure (fun _ => θ) (fun _ => w) (fun _ => hw.1) with hμw
  have hfin : IsFiniteMeasure μw :=
    globalMixedMeasure_isFiniteMeasure_of_bounded _ fun _ => hwb
  have hmeas : ∀ {x : M → EReal}, IsThetaPshPotential θ.val x →
      Measurable fun p => (x p).toReal := fun h =>
    GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal h.1
  rw [integral_toReal_sub (hmeas hu) (hmeas hw) hub hwb] at hU
  rw [integral_toReal_sub (hmeas hv) (hmeas hw) hvb hwb] at hV
  have hwint : ∫ x, (w x).toReal ∂μw =
      t * ∫ x, (u x).toReal ∂μw + (1 - t) * ∫ x, (v x).toReal ∂μw := by
    obtain ⟨Qu, hQu⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hub
    obtain ⟨Qv, hQv⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hvb
    have iu := GlobalSlotStokes.integrable_of_measurable_bounded (hmeas hu) hQu μw
    have iv := GlobalSlotStokes.integrable_of_measurable_bounded (hmeas hv) hQv μw
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iu.const_mul t)
      (iv.const_mul (1 - t))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hwr x, EReal.toReal_coe]
  nlinarith

/-- **The translation formula** (Xia, SGPT (3.31)) for bounded potentials:
`E^φ(u - s) = E^φ(u) - s ∫ θ_φ^n`. -/
theorem relativeEnergyOfMinimalType_sub_const (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (hφb : IsBoundedPotential φ)
    (hub : IsBoundedPotential u) (s : ℝ)
    (hus : IsThetaPshPotential θ.val fun x => u x - (s : EReal)) :
    relativeEnergyOfMinimalType θ φ _ hφ hus =
      relativeEnergyOfMinimalType θ φ u hφ hu -
        s * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := by
  set us : M → EReal := fun x => u x - (s : EReal) with hus_def
  have husr : ∀ x, us x = (((u x).toReal - s : ℝ) : EReal) := fun x => by
    rw [hus_def]
    simp only
    rw [← EReal.coe_toReal (hub.ne_top x) (hub.ne_bot x), EReal.toReal_coe, ← EReal.coe_sub]
  have husb : IsBoundedPotential us := by
    obtain ⟨a, b, hab⟩ := id hub
    refine ⟨a - s, b - s, fun x => ?_⟩
    rw [husr x]
    have h1 := (hab x).1; have h2 := (hab x).2
    rw [← EReal.coe_toReal (hub.ne_top x) (hub.ne_bot x), EReal.coe_le_coe_iff] at h1 h2
    constructor <;> rw [EReal.coe_le_coe_iff] <;> linarith
  have hcoc := relativeEnergyOfMinimalType_sub omega θ hφ hus hu hφb husb hub
  have hmul := relativeEnergyOfMinimalType_mul θ hu hus hub husb
  -- every layout measure has the mass of `θ_φ^n`
  have hmass : ∀ j, (layMeasure θ n j us u (fun _ => u) hus.1 hu.1 (fun _ => hu.1)).real univ =
      (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := by
    intro j
    have h := UniformBoundedGlobalMass.globalMixedMeasure_univ_eq_of_bounded
      (GlobalNonPluripolar.oneSlotMassInvariance omega (fun _ => θ))
      (v := lay n j us u (fun _ => u)) (v' := fun _ => φ)
      (lay_psh (k := n) (j := j) hus.1 hu.1 fun _ => hu.1) (fun _ => hφ.1)
      (lay_bounded (k := n) (j := j) husb hub fun _ => hub) (fun _ => hφb)
    simp only [Measure.real, layMeasure, h]
  have hterm : ∀ j, ∫ x, ((us x).toReal - (u x).toReal) ∂(layMeasure θ n j us u (fun _ => u)
      hus.1 hu.1 (fun _ => hu.1)) =
      -s * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := by
    intro j
    have hconst : (fun x => (us x).toReal - (u x).toReal) = fun _ => -s := by
      funext x; rw [husr x, EReal.toReal_coe]; ring
    rw [hconst, integral_const, smul_eq_mul, hmass j]
    ring
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hmul
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hE : relativeEnergyOfMinimalType θ u us hu hus =
      -s * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := by
    have h' : ((n : ℝ) + 1) * relativeEnergyOfMinimalType θ u us hu hus =
        ((n : ℝ) + 1) * (-s * (globalMixedMeasure (fun _ => θ) (fun _ => φ)
          (fun _ => hφ.1)).real univ) := by
      rw [hmul]; push_cast; ring
    exact mul_left_cancel₀ hpos.ne' h'
  linarith

end Consequences

/-! ### The extended energy -/

section Extended

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- **The extended energy is increasing** (Xia, SGPT Lemma 3.1.3, last clause), for any model
potential: a larger relative potential has fewer relatively minimal majorants. -/
theorem relativeMongeAmpereEnergy_mono (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : RelativePSH θ φ u) (hv : RelativePSH θ φ v) (huv : u ≤ v) :
    relativeMongeAmpereEnergy θ φ u hφ hu ≤ relativeMongeAmpereEnergy θ φ v hφ hv := by
  refine sInf_le_sInf ?_
  rintro e ⟨w, hw, hvw, rfl⟩
  exact ⟨w, hw, huv.trans hvw, rfl⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A potential of the same singularity type as a bounded one is bounded. -/
theorem isBoundedPotential_of_sameSingularityType {φ v : M → EReal} (hφb : IsBoundedPotential φ)
    (h : SameSingularityTypeOn v φ univ) : IsBoundedPotential v := by
  obtain ⟨a, b, hab⟩ := hφb
  obtain ⟨⟨C, hC⟩, ⟨D, hD⟩⟩ := h
  refine ⟨a - D, b + C, fun x => ?_⟩
  have hup : v x ≤ ((b + C : ℝ) : EReal) := by
    calc v x ≤ φ x + (C : EReal) := hC x (mem_univ x)
      _ ≤ (b : EReal) + (C : EReal) := add_le_add (hab x).2 le_rfl
      _ = ((b + C : ℝ) : EReal) := (EReal.coe_add b C).symm
  have hlow : (a : EReal) ≤ v x + (D : EReal) := (hab x).1.trans (hD x (mem_univ x))
  have hbot : v x ≠ ⊥ := by
    intro h
    rw [h, EReal.bot_add] at hlow
    exact EReal.coe_ne_bot a (le_bot_iff.mp hlow)
  have htop : v x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  obtain ⟨r, hr⟩ : ∃ r : ℝ, v x = r := ⟨(v x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [hr] at hup hlow ⊢
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hlow
  exact ⟨EReal.coe_le_coe_iff.mpr (by linarith), hup⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Two bounded potentials have the same singularity type. -/
theorem sameSingularityType_of_bounded {u φ : M → EReal} (hub : IsBoundedPotential u)
    (hφb : IsBoundedPotential φ) : SameSingularityTypeOn u φ univ := by
  obtain ⟨a, b, hab⟩ := hub
  obtain ⟨a', b', hab'⟩ := hφb
  refine ⟨⟨b - a', fun x _ => ?_⟩, ⟨b' - a, fun x _ => ?_⟩⟩
  · calc u x ≤ (b : EReal) := (hab x).2
      _ = (a' : EReal) + ((b - a' : ℝ) : EReal) := by rw [← EReal.coe_add]; ring_nf
      _ ≤ φ x + ((b - a' : ℝ) : EReal) := add_le_add (hab' x).1 le_rfl
  · calc φ x ≤ (b' : EReal) := (hab' x).2
      _ = (a : EReal) + ((b' - a : ℝ) : EReal) := by rw [← EReal.coe_add]; ring_nf
      _ ≤ u x + ((b' - a : ℝ) : EReal) := add_le_add (hab x).1 le_rfl

/-- **The extended energy agrees with the energy formula** (Xia, SGPT Lemma 3.1.3) when the
model potential is bounded: for a bounded relative potential `u`, the infimum (3.30) over
relatively minimal majorants is the value (3.29). -/
theorem relativeMongeAmpereEnergy_eq_of_bounded (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal} (hφ : IsModelPotential θ φ)
    (hu : RelativePSH θ φ u) (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) :
    relativeMongeAmpereEnergy θ φ u hφ hu =
      (relativeEnergyOfMinimalType θ φ u hφ.plurisubharmonic hu.plurisubharmonic : EReal) := by
  refine le_antisymm (sInf_le ⟨u, ⟨hu.plurisubharmonic, sameSingularityType_of_bounded hub hφb⟩,
    le_rfl, rfl⟩) (le_sInf ?_)
  rintro e ⟨v, hv, huv, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (relativeEnergyOfMinimalType_mono omega θ _ _ _ hφb hub
    (isBoundedPotential_of_sameSingularityType hφb hv.2) huv)

end Extended

end

end SGPT.Foundations.Analysis.Pending.BoundedMongeAmpereEnergy

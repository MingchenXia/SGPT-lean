import SGPT.TestCurve.TCLinPoints

/-!
# Laurent expansions of sections of a test configuration

Let `(𝓧, 𝓛)` be a test configuration of `(X, L)`. A sum `σ = Σ σ_i` of weight
vectors (`σ_i` extending `t^{-λ_i} q^* s_i`) restricts on `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` to the Laurent
polynomial `Σ_i t^{-λ_i} s_i ∈ R(X, L)[t, t⁻¹]`. We record this correspondence as the span
`graph T m` of the pairs `(σ, t^{-λ} s)` and prove:

* `graph_unique`: **the Laurent expansion is unique** — if `(σ, z)` and `(σ, z')` lie in the
  graph, then `z = z'`. This is the independence of weight vectors of distinct weights
  (`TCLin.eq_zero_of_sum_tpow_mul`, evaluation at the points of `𝔾_m`).
* `graph_mul`: the correspondence is multiplicative.

Consequences for a `𝔾_m`-linearization (`SectionLinearization`):

* `SectionLinearization.exists_graph`: every section has a Laurent expansion;
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCLin

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TestConfig.LaurentSecRing SGPT.TestCurve.TCEnc
open SGPT.TestCurve.FGRel

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

/-- The chart coefficient `σ ↦ σ_c` as an additive map. -/
def coeffHom {Y : Scheme.{0}} {M : Y.Modules} (b : LineBundleAtlas M) (n : ℕ) (c : b.I) :
    bundlePowerGlobalSections M n →+ Γ(Y, b.opens c) :=
  AddMonoidHom.mk' (atlasPowerGlobalCoefficients b n c) (atlasPowerGlobalCoefficients_add b n c)

theorem eq_zero_of_sum_tpow_neg_mul (j : a.I) (S : Finset ℤ) (b : ℤ → Γ(X, a.opens j))
    (h : ∑ lam ∈ S, (T.tUnit j ^ (-lam)).val * pullFun T.coord (a.opens j) (b lam) = 0) :
    ∀ lam ∈ S, b lam = 0 := by
  have h' : ∑ p ∈ S.map (Equiv.neg ℤ).toEmbedding,
      (T.tUnit j ^ p).val * pullFun T.coord (a.opens j) (b (-p)) = 0 := by
    rw [Finset.sum_map]
    simpa using h
  intro lam hlam
  have := eq_zero_of_sum_tpow_mul T j _ (fun p => b (-p)) h' (-lam)
    (Finset.mem_map_of_mem _ hlam)
  simpa using this

/-! ### Sums of weight vectors -/

theorem extends_sum {ι : Type*} (s : Finset ι) (lam : ℤ) (m : ℕ) (u : ι → SectionSpace f L m)
    (σ : ι → SectionSpace T.structureMap T.line m) (h : ∀ i ∈ s, T.Extends lam m (u i) (σ i)) :
    T.Extends lam m (∑ i ∈ s, u i) (∑ i ∈ s, σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TestConfiguration'.extends_zero T lam m
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact TestConfiguration'.extends_add T (h i (Finset.mem_insert_self i s))
      (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))

/-- **Independence of weight vectors**: if weight vectors `σ_i` (extending `t^{-λ_i} q^* u_i`)
sum to zero, then so do the Laurent polynomials `Σ_i t^{-λ_i} u_i`. -/
theorem sum_mono_eq_zero [IsIntegral X] {ι : Type*} (s : Finset ι) (lam : ι → ℤ) (m : ℕ)
    (u : ι → SectionSpace f L m) (σ : ι → SectionSpace T.structureMap T.line m)
    (h : ∀ i ∈ s, T.Extends (lam i) m (u i) (σ i)) (hσ : ∑ i ∈ s, σ i = 0) :
    ∑ i ∈ s, (mono (-lam i) m (u i) : LaurentSecRing f a) = 0 := by
  classical
  let S := s.image lam
  let U : ℤ → SectionSpace f L m := fun l => ∑ i ∈ s with lam i = l, u i
  let Sg : ℤ → SectionSpace T.structureMap T.line m := fun l => ∑ i ∈ s with lam i = l, σ i
  have hU : ∀ l, T.Extends l m (U l) (Sg l) := fun l =>
    extends_sum T _ l m u σ fun i hi => by
      obtain ⟨hi', rfl⟩ := Finset.mem_filter.mp hi
      exact h i hi'
  have hsumSg : ∑ l ∈ S, Sg l = 0 := by
    rw [Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem lam hi)]
    exact hσ
  have hU0 : ∀ l ∈ S, U l = 0 := by
    have hc : ∀ j : a.I, ∀ l ∈ S, atlasPowerGlobalCoefficients a m j (U l) = 0 := by
      intro j
      apply eq_zero_of_sum_tpow_neg_mul T j S
      have h1 := congrArg (coeffHom T.extAtlas m (Sum.inr j)) hsumSg
      rw [map_sum, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun l _ => ?_
      exact (hU l j).symm
    intro l hl
    exact atlasPowerGlobalCoefficients_ext a m _ _ fun j => by
      rw [hc j l hl, atlasPowerGlobalCoefficients_zero]
  have hmono : ∑ i ∈ s, (mono (-lam i) m (u i) : LaurentSecRing f a) =
      ∑ l ∈ S, (mono (-l) m (U l) : LaurentSecRing f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem lam hi)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : ∀ (t : Finset ι), ∑ i ∈ t with lam i = l, (mono (-lam i) m (u i) : LaurentSecRing f a) =
        mono (-l) m (∑ i ∈ t with lam i = l, u i) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp [mono_zero]
      | insert i t hi ih =>
        rw [Finset.filter_insert]
        split_ifs with hil
        · rw [Finset.sum_insert (by simp [hi]), Finset.sum_insert (by simp [hi]), ih, hil,
            mono_add]
        · exact ih
    exact this s
  rw [hmono]
  exact Finset.sum_eq_zero fun l hl => by rw [hU0 l hl, mono_zero]

/-! ### The graph of the Laurent expansion -/

/-- The pairs `(σ, t^{-λ} s)` with `σ` extending `t^{-λ} q^* s`. -/
def graphGens (m : ℕ) : Set (SectionSpace T.structureMap T.line m × LaurentSecRing f a) :=
  {p | ∃ (lam : ℤ) (s : SectionSpace f L m), T.Extends lam m s p.1 ∧ p.2 = mono (-lam) m s}

/-- **Laurent expansions**: `(σ, z) ∈ graph T m` iff `σ = Σ σ_i` with `σ_i` extending
`t^{-λ_i} q^* s_i` and `z = Σ t^{-λ_i} s_i`. -/
def graph (m : ℕ) : Submodule ℂ (SectionSpace T.structureMap T.line m × LaurentSecRing f a) :=
  Submodule.span ℂ (graphGens T m)

variable {T}

theorem mem_graph_of_extends {lam : ℤ} {m : ℕ} {s : SectionSpace f L m}
    {σ : SectionSpace T.structureMap T.line m} (h : T.Extends lam m s σ) :
    (σ, mono (-lam) m s) ∈ graph T m :=
  Submodule.subset_span ⟨lam, s, h, rfl⟩

/-- **Uniqueness of the Laurent expansion.** -/
theorem graph_unique [IsIntegral X] {m : ℕ} {σ : SectionSpace T.structureMap T.line m}
    {z z' : LaurentSecRing f a} (h : (σ, z) ∈ graph T m) (h' : (σ, z') ∈ graph T m) : z = z' := by
  classical
  have h0 : ((0 : SectionSpace T.structureMap T.line m), z - z') ∈ graph T m := by
    have := Submodule.sub_mem _ h h'
    simpa using this
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp h0
  have hgen : ∀ i, ∃ (lam : ℤ) (s : SectionSpace f L m),
      T.Extends lam m s (g i : SectionSpace T.structureMap T.line m × LaurentSecRing f a).1 ∧
        (g i : SectionSpace T.structureMap T.line m × LaurentSecRing f a).2 = mono (-lam) m s :=
    fun i => (g i).2
  choose lam s hs hz using hgen
  have h1 := congrArg Prod.fst hg
  have h2 := congrArg Prod.snd hg
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd] at h1 h2
  have key := sum_mono_eq_zero T Finset.univ lam m (fun i => c i • s i)
    (fun i => c i • (g i : SectionSpace T.structureMap T.line m × LaurentSecRing f a).1)
    (fun i _ => TestConfiguration'.extends_smul T (hs i) (c i)) h1
  rw [← sub_eq_zero, ← h2]
  rw [← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hz i, mono_smul]

theorem graph_mul {m m' : ℕ} {σ : SectionSpace T.structureMap T.line m}
    {σ' : SectionSpace T.structureMap T.line m'} {z z' : LaurentSecRing f a}
    (h : (σ, z) ∈ graph T m) (h' : (σ', z') ∈ graph T m') :
    (SectionSpace.mul T.structureMap T.extAtlas m m' σ σ', z * z') ∈ graph T (m + m') := by
  let B : (SectionSpace T.structureMap T.line m × LaurentSecRing f a) →
      (SectionSpace T.structureMap T.line m' × LaurentSecRing f a) →
        (SectionSpace T.structureMap T.line (m + m') × LaurentSecRing f a) :=
    fun p p' => (SectionSpace.mul T.structureMap T.extAtlas m m' p.1 p'.1, p.2 * p'.2)
  have hB0r : ∀ p, B p 0 = 0 := fun p => by
    change (SectionSpace.mul T.structureMap T.extAtlas m m' p.1 0, p.2 * 0) = 0
    rw [map_zero, mul_zero]
    rfl
  have hB0l : ∀ p', B 0 p' = 0 := fun p' => by
    change (SectionSpace.mul T.structureMap T.extAtlas m m' 0 p'.1, 0 * p'.2) = 0
    rw [map_zero, LinearMap.zero_apply, zero_mul]
    rfl
  have hBaddr : ∀ p x y, B p (x + y) = B p x + B p y := fun p x y => by
    change (SectionSpace.mul T.structureMap T.extAtlas m m' p.1 (x.1 + y.1), p.2 * (x.2 + y.2)) =
      (SectionSpace.mul T.structureMap T.extAtlas m m' p.1 x.1 +
        SectionSpace.mul T.structureMap T.extAtlas m m' p.1 y.1, p.2 * x.2 + p.2 * y.2)
    rw [map_add, mul_add]
  have hBaddl : ∀ p' x y, B (x + y) p' = B x p' + B y p' := fun p' x y => by
    change (SectionSpace.mul T.structureMap T.extAtlas m m' (x.1 + y.1) p'.1, (x.2 + y.2) * p'.2) =
      (SectionSpace.mul T.structureMap T.extAtlas m m' x.1 p'.1 +
        SectionSpace.mul T.structureMap T.extAtlas m m' y.1 p'.1, x.2 * p'.2 + y.2 * p'.2)
    rw [map_add, LinearMap.add_apply, add_mul]
  have hBsmulr : ∀ p (c : ℂ) x, B p (c • x) = c • B p x := fun p c x => by
    change (SectionSpace.mul T.structureMap T.extAtlas m m' p.1 (c • x.1), p.2 * (c • x.2)) =
      (c • SectionSpace.mul T.structureMap T.extAtlas m m' p.1 x.1, c • (p.2 * x.2))
    rw [map_smul, mul_smul_comm]
  have hBsmull : ∀ p' (c : ℂ) x, B (c • x) p' = c • B x p' := fun p' c x => by
    change (SectionSpace.mul T.structureMap T.extAtlas m m' (c • x.1) p'.1, (c • x.2) * p'.2) =
      (c • SectionSpace.mul T.structureMap T.extAtlas m m' x.1 p'.1, c • (x.2 * p'.2))
    rw [map_smul, LinearMap.smul_apply, smul_mul_assoc]
  have hgen : ∀ p ∈ graphGens T m, ∀ p' ∈ graph T m', B p p' ∈ graph T (m + m') := by
    rintro p ⟨lam, s, hs, hp⟩ p' hp'
    refine Submodule.span_induction (p := fun p' _ => B p p' ∈ graph T (m + m'))
      ?_ ?_ ?_ ?_ hp'
    · rintro q ⟨lam', s', hs', hq⟩
      change (SectionSpace.mul T.structureMap T.extAtlas m m' p.1 q.1, p.2 * q.2) ∈ _
      rw [hp, hq, mono_mul_mono]
      have := mem_graph_of_extends (TestConfiguration'.extends_mul T hs hs')
      rwa [neg_add] at this
    · rw [hB0r]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [hBaddr]
      exact add_mem hx hy
    · intro c x _ hx
      rw [hBsmulr]
      exact Submodule.smul_mem _ c hx
  change B (σ, z) (σ', z') ∈ graph T (m + m')
  refine Submodule.span_induction (p := fun p _ => B p (σ', z') ∈ graph T (m + m'))
    ?_ ?_ ?_ ?_ h
  · intro p hp
    exact hgen p hp (σ', z') h'
  · rw [hB0l]
    exact zero_mem _
  · intro x y _ _ hx hy
    rw [hBaddl]
    exact add_mem hx hy
  · intro c x _ hx
    rw [hBsmull]
    exact Submodule.smul_mem _ c hx

/-! ### Consequences for a linearization -/

namespace SectionLinearization

variable (P : SectionLinearization T)
include P

/-- **Every section has a Laurent expansion** (for a linearized test configuration). -/
theorem exists_graph (m : ℕ) (σ : SectionSpace T.structureMap T.line m) :
    ∃ z : LaurentSecRing f a, (σ, z) ∈ graph T m := by
  classical
  obtain ⟨S, ξ, y, hy, rfl⟩ := P.exists_weight_decomposition m σ
  refine ⟨∑ lam ∈ S, mono (-lam) m (y lam), ?_⟩
  have : (∑ lam ∈ S, ξ lam, ∑ lam ∈ S, (mono (-lam) m (y lam) : LaurentSecRing f a)) =
      ∑ lam ∈ S, (ξ lam, (mono (-lam) m (y lam) : LaurentSecRing f a)) :=
    Prod.ext (by rw [Prod.fst_sum]) (by rw [Prod.snd_sum])
  rw [this]
  exact Submodule.sum_mem _ fun lam _ => mem_graph_of_extends (hy lam)

end SectionLinearization

end SGPT.TestCurve.TCLin

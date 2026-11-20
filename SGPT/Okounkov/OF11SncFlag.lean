import SGPT.Okounkov.OF11MonomialCone
import SGPT.Okounkov.OF6AdmissibleRecognition

/-!
# Admissible flags of a normal crossings chart and [CFKLRS17, Thm 2.9]

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `rmk:Abhyankar`:
*if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`, then
[CFKLRS17, Theorem 2.9] shows that it is equivalent to, but not necessarily equal to, a valuation
induced by an admissible flag on a modification of `X`.*

Let `X` be an integral scheme, smooth of relative dimension `n` over `ℂ`, and `x ∈ X` a point. We
say that `z₁, …, zₙ ∈ 𝒪_{X,x}` are **strict normal crossings coordinates** at `x`
(`IsSNCCoordinates`) if they generate the maximal ideal and, for every set `s` of indices, the
partial intersection `D_s = ⋂_{j ∈ s} V(zⱼ)` of the prime divisors `Dⱼ = V(zⱼ)` is, near `x`,
irreducible of codimension `|s|` and smooth at `x` (`(z_s)` is a prime of height `|s|` with
`𝒪_{X,x}/(z_s)` formally smooth over `ℂ`). For every ordering `σ` of the coordinates the
**coordinate flag** `Y_i = D_{σ(1)} ∩ ⋯ ∩ D_{σ(i)}` (the closure of the point of the prime
`(z_{σ(1)}, …, z_{σ(i)})`) is then an admissible flag (`def:admfl`) with point `x`
(`exists_admissibleFlag_of_primeChain`).

**Main theorem** (`exists_admissibleFlag_lexEquivalent_of_monomial`): let `ν` be a valuation of
`ℂ(X)` with values in `ℤⁿ_lex`, centred at `x`, and suppose that there are `u₁, …, uₙ ∈ 𝒪_{X,x}`
with `ν(u_k) = e_k` which are monomials in strict normal crossings coordinates at `x`, up to units:
`u_k = ε_k ∏ⱼ zⱼ^{a_{kj}}`. Then **`ν` is equivalent to the valuation of an admissible flag** on
`X` with point `x`: namely of the coordinate flag for the ordering `σ` given by the leading indices
of the values `ν(zⱼ)` (the cone lemma), with matrix `G = (ν(z_{σ(i)}))ᵢ = I + N`.

Consequently (`exists_admissibleFlag_lexEquivalent_of_model`), [CFKLRS17, Thm 2.9] holds on every
smooth model `X'` of `ℂ(X)` (in particular on every modification `X' → X`) on which `u₁, …, uₙ`
become, at the centre of `ν`, monomials in strict normal crossings coordinates — that is, on every
log resolution of `u₁, …, uₙ` (Hironaka's principalization of the ideals of their numerators,
denominators and indeterminacy); no further local uniformization or toric modification is needed.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF11

open AlgebraicGeometry CategoryTheory Topology IsLocalRing
open SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr

/-! ### Points of `X` attached to primes of a local ring -/

section Points

variable {X : Scheme.{0}}

/-- The point of `Spec 𝒪_{X,x}` of a prime `𝔭`. -/
def stalkSpecPoint (x : X) (p : Ideal (X.presheaf.stalk x)) (hp : p.IsPrime) :
    Spec (X.presheaf.stalk x) :=
  ⟨p, hp⟩

/-- The point of `X` of a prime `𝔭` of `𝒪_{X,x}` (the generic point of the subvariety through `x`
cut out by `𝔭`). -/
def stalkPrimePoint (x : X) (p : Ideal (X.presheaf.stalk x)) (hp : p.IsPrime) : X :=
  X.fromSpecStalk x (stalkSpecPoint x p hp)

theorem stalkPrimePoint_specializes (x : X) (p : Ideal (X.presheaf.stalk x)) (hp : p.IsPrime) :
    stalkPrimePoint x p hp ⤳ x := by
  have h : stalkPrimePoint x p hp ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact h

/-- The prime of `𝒪_{X,x}` cut out by the point of `𝔭` is `𝔭`. -/
theorem generizationIdeal_stalkPrimePoint (x : X) (p : Ideal (X.presheaf.stalk x)) (hp : p.IsPrime)
    (h : stalkPrimePoint x p hp ⤳ x) : generizationIdeal h = p := by
  let z : Spec (X.presheaf.stalk x) :=
    Spec.map (X.presheaf.stalkSpecializes h) (IsLocalRing.closedPoint _)
  have hz : z.asIdeal = generizationIdeal h := rfl
  have himage : X.fromSpecStalk x z = stalkPrimePoint x p hp := by
    change (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk x)
      (IsLocalRing.closedPoint _) = _
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.fromSpecStalk_closedPoint]
  have hzp : z = stalkSpecPoint x p hp := (X.fromSpecStalk x).isEmbedding.injective himage
  rw [← hz, hzp]
  rfl

/-- The codimension of the point of `𝔭` is the height of `𝔭`. -/
theorem coheight_stalkPrimePoint (x : X) (p : Ideal (X.presheaf.stalk x)) (hp : p.IsPrime) :
    Order.coheight (stalkPrimePoint x p hp) = p.height := by
  rw [stalkPrimePoint, fromSpecStalk_coheight, ← idealHeight_eq_coheight]
  rfl

/-- Inclusions of primes give specializations of their points. -/
theorem stalkPrimePoint_specializes_of_le (x : X) {p q : Ideal (X.presheaf.stalk x)}
    (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p ≤ q) :
    stalkPrimePoint x p hp ⤳ stalkPrimePoint x q hq := by
  have h : stalkSpecPoint x p hp ⤳ stalkSpecPoint x q hq :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hpq
  exact h.map (X.fromSpecStalk x).continuous

/-- The point of the maximal ideal is `x`. -/
theorem stalkPrimePoint_maximalIdeal (x : X) :
    stalkPrimePoint x (maximalIdeal (X.presheaf.stalk x)) inferInstance = x :=
  Scheme.fromSpecStalk_closedPoint

/-- The generic point of the closure of a point is the point. -/
theorem genericPoint_closure_singleton (η : X) (h : IsIrreducible (closure {η})) :
    h.genericPoint = η :=
  (h.isGenericPoint_genericPoint isClosed_closure).eq isGenericPoint_closure

/-- Generization ideals only depend on the points. -/
theorem generizationIdeal_congr {η η' x : X} (h : η ⤳ x) (h' : η' ⤳ x) (e : η = η') :
    generizationIdeal h = generizationIdeal h' := by
  subst e
  rfl

end Points

/-! ### The flag of a chain of primes -/

section Flag

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {n : ℕ}

omit [IsIntegral X] in
/-- Transport of smoothness at a point along an equality of points. -/
theorem isSubvarietySmoothAt_of_eq {Z : Set X} (hZ : IsIrreducible Z) (hZc : IsClosed Z)
    {x pt : X} (hpt : pt ∈ Z) (e : pt = x) (p : Ideal (X.presheaf.stalk x))
    (hgen : ∀ h : hZ.genericPoint ⤳ x, generizationIdeal h = p)
    (hsm : letI := stalkComplexAlgebra f x
      Algebra.FormallySmooth ℂ (X.presheaf.stalk x ⧸ p)) :
    IsSubvarietySmoothAt f hZ hZc hpt := by
  subst e
  unfold IsSubvarietySmoothAt
  rw [hgen]
  exact hsm

/-- **The admissible flag of a chain of primes.** Let `𝔭₀ = 0 ⊆ 𝔭₁ ⊆ ⋯ ⊆ 𝔭ₙ = 𝔪` be primes of
`𝒪_{X,x}` with `ht 𝔭ᵢ = i` and `𝒪_{X,x}/𝔭ᵢ` formally smooth over `ℂ`. Then the closures
`Yᵢ` of the points of the `𝔭ᵢ` form an admissible flag with point `x`, and `Yᵢ` cuts out `𝔭ᵢ`
in `𝒪_{X,x}`. -/
theorem exists_admissibleFlag_of_primeChain (x : X) (p : Fin (n + 1) → Ideal (X.presheaf.stalk x))
    (hprime : ∀ i, (p i).IsPrime) (hmono : Monotone p) (hheight : ∀ i, (p i).height = (i : ℕ))
    (hzero : p 0 = ⊥) (hlast : p (Fin.last n) = maximalIdeal (X.presheaf.stalk x))
    (hsmooth : ∀ i, letI := stalkComplexAlgebra f x
      Algebra.FormallySmooth ℂ (X.presheaf.stalk x ⧸ p i)) :
    ∃ (Y : Fin (n + 1) → Set X) (hY : IsAdmissibleFlag f n Y), hY.point = x ∧
      ∀ (i : Fin (n + 1)) (h : (hY.isIrreducible i).genericPoint ⤳ x),
        generizationIdeal h = p i := by
  classical
  let η : Fin (n + 1) → X := fun i => stalkPrimePoint x (p i) (hprime i)
  let Y : Fin (n + 1) → Set X := fun i => closure {η i}
  have hirr : ∀ i, IsIrreducible (Y i) := fun i => isIrreducible_singleton.closure
  have hcl : ∀ i, IsClosed (Y i) := fun i => isClosed_closure
  have hgp : ∀ i, (hirr i).genericPoint = η i := fun i => genericPoint_closure_singleton _ _
  have hanti : Antitone Y := by
    intro i j hij
    exact specializes_iff_closure_subset.mp
      (stalkPrimePoint_specializes_of_le x (hprime i) (hprime j) (hmono hij))
  have hηlast : η (Fin.last n) = x := by
    change stalkPrimePoint x (p (Fin.last n)) (hprime _) = x
    have : stalkSpecPoint x (p (Fin.last n)) (hprime _) =
        stalkSpecPoint x (maximalIdeal _) inferInstance := by
      exact PrimeSpectrum.ext hlast
    rw [stalkPrimePoint, this]
    exact stalkPrimePoint_maximalIdeal x
  have hgen : ∀ (i : Fin (n + 1)) (h : (hirr i).genericPoint ⤳ x), generizationIdeal h = p i := by
    intro i h
    rw [generizationIdeal_congr h (stalkPrimePoint_specializes x (p i) (hprime i)) (hgp i)]
    exact generizationIdeal_stalkPrimePoint x (p i) (hprime i) _
  have hpt : (hirr (Fin.last n)).genericPoint = x := (hgp _).trans hηlast
  -- `Y₀ = X`
  have hY0 : Y 0 = Set.univ := by
    have hgx : genericPoint X ⤳ x := _root_.genericPoint_specializes x
    have hr : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hgx
    obtain ⟨w, hw⟩ := hr
    have hle : stalkSpecPoint x (p 0) (hprime 0) ⤳ w := by
      refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
      change p 0 ≤ w.asIdeal
      rw [hzero]
      exact bot_le
    have hsp : η 0 ⤳ genericPoint X := by
      have := hle.map (X.fromSpecStalk x).continuous
      rw [hw] at this
      exact this
    have hsub := specializes_iff_closure_subset.mp hsp
    have htop : closure {genericPoint X} = (⊤ : Set X) := genericPoint_spec X
    rw [htop] at hsub
    exact Set.eq_univ_of_univ_subset hsub
  refine ⟨Y, ⟨hcl, hirr, hY0, hanti, fun i => ?_, fun i => ?_⟩, hpt, hgen⟩
  · rw [hgp i, coheight_stalkPrimePoint, hheight i]
  · exact isSubvarietySmoothAt_of_eq (hirr i) (hcl i) _ hpt (p i) (hgen i) (hsmooth i)

end Flag

/-! ### Strict normal crossings coordinates and their coordinate flags -/

section SNC

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {n : ℕ}

variable (f) in
/-- **Strict normal crossings coordinates** at `x`: `z₁, …, zₙ ∈ 𝒪_{X,x}` generate the maximal
ideal, and for every set `s` of indices the partial intersection `⋂_{j ∈ s} V(zⱼ)` of the prime
divisors `V(zⱼ)` is, near `x`, irreducible of codimension `|s|` and smooth at `x`: the ideal
`(zⱼ : j ∈ s)` is prime of height `|s|` and `𝒪_{X,x}/(zⱼ : j ∈ s)` is formally smooth over `ℂ`.
(These are local equations at `x` of `n` prime divisors meeting with simple normal crossings.) -/
def IsSNCCoordinates (x : X) (z : Fin n → X.presheaf.stalk x) : Prop :=
  Ideal.span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
    ∀ s : Finset (Fin n), (Ideal.span (z '' ↑s)).IsPrime ∧
      (Ideal.span (z '' ↑s)).height = s.card ∧
      (letI := stalkComplexAlgebra f x;
        Algebra.FormallySmooth ℂ (X.presheaf.stalk x ⧸ Ideal.span (z '' ↑s)))

/-- The first `i` indices in the ordering `σ`: `{σ(0), …, σ(i-1)}`. -/
def prefixSet (σ : Equiv.Perm (Fin n)) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => ((σ.symm j : Fin n) : ℕ) < i

theorem mem_prefixSet (σ : Equiv.Perm (Fin n)) (i : ℕ) (j : Fin n) :
    j ∈ prefixSet σ i ↔ ((σ.symm j : Fin n) : ℕ) < i := by
  simp [prefixSet]

theorem card_prefixSet (σ : Equiv.Perm (Fin n)) (i : ℕ) : (prefixSet σ i).card = min n i := by
  have h : prefixSet σ i = (Finset.univ.filter fun l : Fin n => (l : ℕ) < i).map σ.toEmbedding := by
    ext j
    simp only [mem_prefixSet, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    constructor
    · intro hj
      exact ⟨σ.symm j, hj, σ.apply_symm_apply j⟩
    · rintro ⟨l, hl, rfl⟩
      rwa [σ.symm_apply_apply]
  rw [h, Finset.card_map]
  exact Fin.card_filter_val_lt

theorem prefixSet_mono (σ : Equiv.Perm (Fin n)) {i j : ℕ} (hij : i ≤ j) :
    prefixSet σ i ⊆ prefixSet σ j := by
  intro l hl
  rw [mem_prefixSet] at hl ⊢
  omega

theorem prefixSet_zero (σ : Equiv.Perm (Fin n)) : prefixSet σ 0 = ∅ := by
  ext j
  simp [mem_prefixSet]

theorem prefixSet_of_le (σ : Equiv.Perm (Fin n)) {i : ℕ} (hi : n ≤ i) :
    prefixSet σ i = Finset.univ := by
  ext j
  simp only [mem_prefixSet, Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (σ.symm j).2 hi

theorem prefixSet_succ (σ : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) :
    prefixSet σ (i + 1) = insert (σ ⟨i, hi⟩) (prefixSet σ i) := by
  ext j
  simp only [mem_prefixSet, Finset.mem_insert]
  constructor
  · intro hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact Or.inr h
    · left
      rw [← σ.apply_symm_apply j]
      congr 1
      exact Fin.ext h
  · rintro (rfl | h)
    · simp
    · omega

/-- The ideal of the coordinate subvariety `V(z_{σ(0)}, …, z_{σ(i-1)})`. -/
def coordIdeal {x : X} (z : Fin n → X.presheaf.stalk x) (σ : Equiv.Perm (Fin n)) (i : ℕ) :
    Ideal (X.presheaf.stalk x) :=
  Ideal.span (z '' ↑(prefixSet σ i))

omit [IsIntegral X] in
theorem coordIdeal_succ {x : X} (z : Fin n → X.presheaf.stalk x) (σ : Equiv.Perm (Fin n)) {i : ℕ}
    (hi : i < n) : coordIdeal z σ (i + 1) = coordIdeal z σ i ⊔ Ideal.span {z (σ ⟨i, hi⟩)} := by
  rw [coordIdeal, coordIdeal, prefixSet_succ σ hi, Finset.coe_insert, Set.image_insert_eq,
    Ideal.span_insert, sup_comm]

/-- **The coordinate flags of strict normal crossings coordinates are admissible**: for every
ordering `σ`, the flag `Yᵢ = V(z_{σ(0)}, …, z_{σ(i-1)})` is an admissible flag with point `x`,
and `Yᵢ` cuts out the ideal `(z_{σ(0)}, …, z_{σ(i-1)})` in `𝒪_{X,x}`. -/
theorem exists_admissibleFlag_of_isSNCCoordinates {x : X} {z : Fin n → X.presheaf.stalk x}
    (hz : IsSNCCoordinates f x z) (σ : Equiv.Perm (Fin n)) :
    ∃ (Y : Fin (n + 1) → Set X) (hY : IsAdmissibleFlag f n Y), hY.point = x ∧
      ∀ (i : Fin (n + 1)) (h : (hY.isIrreducible i).genericPoint ⤳ x),
        generizationIdeal h = coordIdeal z σ i := by
  refine exists_admissibleFlag_of_primeChain x (fun i => coordIdeal z σ i)
    (fun i => (hz.2 _).1) (fun i j hij => Ideal.span_mono (Set.image_mono
      (Finset.coe_subset.mpr (prefixSet_mono σ hij)))) (fun i => ?_) ?_ ?_ (fun i => (hz.2 _).2.2)
  · change (Ideal.span (z '' ↑(prefixSet σ i))).height = _
    rw [(hz.2 _).2.1, card_prefixSet]
    congr 1
    exact_mod_cast min_eq_right (Nat.lt_succ_iff.mp i.2)
  · change Ideal.span (z '' ↑(prefixSet σ 0)) = ⊥
    rw [prefixSet_zero, Finset.coe_empty, Set.image_empty, Ideal.span_empty]
  · change Ideal.span (z '' ↑(prefixSet σ n)) = _
    rw [prefixSet_of_le σ le_rfl, Finset.coe_univ, Set.image_univ]
    exact hz.1

end SNC

/-! ### Recognition on a coordinate flag and the main theorem -/

section Main

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {n : ℕ}
  [SmoothOfRelativeDimension n f]

/-- **Recognition on a coordinate flag**: if the members of an admissible flag `Y•` with point `x`
cut out the coordinate ideals `(z_{σ(0)}, …, z_{σ(i-1)})` and `ν` is centred at `x` with
`(ν(z_{σ(i)}))ᵢ` unit upper triangular, then `ν ∼ ν_{Y•}`. -/
theorem lexEquivalent_of_coordFlag {Y : Fin (n + 1) → Set X} (hY : IsAdmissibleFlag f n Y)
    {x : X} (hpt : hY.point = x) (z : Fin n → X.presheaf.stalk x) (σ : Equiv.Perm (Fin n))
    (hgen : ∀ (i : Fin (n + 1)) (h : (hY.isIrreducible i).genericPoint ⤳ x),
      generizationIdeal h = coordIdeal z σ i)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hcent : AlgebraicValuation.IsValuationCenter ν x)
    (hG : IsUnitUpperTriangular
      (fun i => ofLex ((ν (algebraMap _ X.functionField (z (σ i)))).untopD 0))) :
    ValuationsLexEquivalent (admissibleFlagValuation hY) ν := by
  subst hpt
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hP : ∀ i : ℕ, admissibleIdeal hY i = coordIdeal z σ (min i n) := fun i =>
    hgen (memberIndex n i) (memberPoint_specializes hY i)
  have hPi : ∀ i : ℕ, i ≤ n → admissibleIdeal hY i = coordIdeal z σ i := by
    intro i hi
    rw [hP i, min_eq_left hi]
  let C : OF5.LocalEquationChain (X.presheaf.stalk hY.point) n :=
    { P := admissibleIdeal hY
      T := fun i => if h : i < n then z (σ ⟨i, h⟩) else 0
      isPrime := fun i => inferInstance
      succ_eq := fun i hi => by
        simp only [dif_pos hi]
        rw [hPi (i + 1) hi, hPi i hi.le, coordIdeal_succ z σ hi]
      T_notMem := fun i hi => by
        simp only [dif_pos hi]
        intro hmem
        apply (admissibleIdeal_lt hY hi).ne
        rw [hPi (i + 1) hi, hPi i hi.le, coordIdeal_succ z σ hi]
        rw [hPi i hi.le] at hmem
        exact (sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm }
  refine (lexEquivalent_admissibleFlagValuation_iff hY C rfl ν).mpr ⟨hcent.1, ?_⟩
  have hM : LocalEquationChain.valueMatrix C X.functionField ν =
      fun i => ofLex ((ν (algebraMap _ X.functionField (z (σ i)))).untopD 0) := by
    funext i
    change ofLex ((ν (algebraMap _ X.functionField (C.T i))).untopD 0) = _
    simp only [C, dif_pos i.2, Fin.eta]
  rw [hM]
  exact hG

/-- **[CFKLRS17, Thm 2.9] on a normal crossings chart.** Let `X` be an integral scheme, smooth of
relative dimension `n` over `ℂ`, and `ν` a valuation of `ℂ(X)` with values in `ℤⁿ_lex`, centred
at `x ∈ X`. Suppose that there are strict normal crossings coordinates `z₁, …, zₙ` at `x` and
`u₁, …, uₙ ∈ 𝒪_{X,x}` with `ν(u_k) = e_k` which are monomials in the `zⱼ` up to units,
`u_k = ε_k ∏ⱼ zⱼ^{a_{kj}}`. Then `ν` is equivalent to the valuation of an admissible flag on `X`
with point `x` (a coordinate flag `V(z_{σ(1)}) ⊇ V(z_{σ(1)}, z_{σ(2)}) ⊇ ⋯`). -/
theorem exists_admissibleFlag_lexEquivalent_of_monomial
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {x : X}
    (hcent : AlgebraicValuation.IsValuationCenter ν x)
    {z : Fin n → X.presheaf.stalk x} (hz : IsSNCCoordinates f x z)
    (u : Fin n → X.presheaf.stalk x) (ε : Fin n → (X.presheaf.stalk x)ˣ) (a : Fin n → Fin n → ℕ)
    (hu : ∀ k, u k = ε k * ∏ j, z j ^ a k j)
    (hνu : ∀ k, ν (algebraMap _ X.functionField (u k)) = basisValue k) :
    ∃ (Y : Fin (n + 1) → Set X) (hY : IsAdmissibleFlag f n Y), hY.point = x ∧
      ValuationsLexEquivalent (admissibleFlagValuation hY) ν := by
  classical
  let c : Fin n → Fin n → ℤ := fun j => ofLex ((ν (algebraMap _ X.functionField (z j))).untopD 0)
  have hz0 : ∀ j, z j ≠ 0 := by
    intro j hj
    have h1 := (hz.2 {j}).2.1
    rw [Finset.coe_singleton, Set.image_singleton, hj, Finset.card_singleton,
      Ideal.span_singleton_eq_bot.mpr rfl, Ideal.height_bot] at h1
    exact absurd h1 (by norm_num)
  have hzval : ∀ j, ν (algebraMap _ X.functionField (z j)) =
      ((toLex (c j) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
    intro j
    have hne : ν (algebraMap _ X.functionField (z j)) ≠ ⊤ := by
      rw [ne_eq, AddValuation.top_iff]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 j)
    obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hne
    change _ = ((toLex (ofLex ((ν (algebraMap _ X.functionField (z j))).untopD 0)) :
      Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))
    rw [← hw, WithTop.untopD_coe, toLex_ofLex]
  have hzmem : ∀ j, z j ∈ maximalIdeal (X.presheaf.stalk x) := by
    intro j
    rw [← hz.1]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hzpos : ∀ j, (0 : Lex (Fin n → ℤ)) < toLex (c j) := by
    intro j
    have h := hcent.2 (z j) (hzmem j)
    rw [hzval j] at h
    exact WithTop.coe_lt_coe.mp h
  have hε : ∀ k, ν (algebraMap _ X.functionField ((ε k : X.presheaf.stalk x))) = 0 :=
    fun k => val_eq_zero_of_isUnit ν hcent.1 (ε k).isUnit
  obtain ⟨σ, hσ⟩ := exists_perm_isUnitUpperTriangular_of_monomial ν z u
    (fun k => (ε k : X.presheaf.stalk x)) c hzval hzpos hε a hu hνu
  obtain ⟨Y, hY, hpt, hgen⟩ := exists_admissibleFlag_of_isSNCCoordinates hz σ
  exact ⟨Y, hY, hpt, lexEquivalent_of_coordFlag hY hpt z σ hgen ν hcent hσ⟩

end Main

/-! ### Laurent monomials: the shape produced by a log resolution -/

section Laurent

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {n : ℕ}
  [SmoothOfRelativeDimension n f]

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
/-- Strict normal crossings coordinates are prime elements. -/
theorem prime_of_isSNCCoordinates {x : X} {z : Fin n → X.presheaf.stalk x}
    (hz : IsSNCCoordinates f x z) (j : Fin n) : Prime (z j) := by
  have h := hz.2 {j}
  rw [Finset.coe_singleton, Set.image_singleton, Finset.card_singleton] at h
  have hne : z j ≠ 0 := by
    intro hj
    have h1 := h.2.1
    rw [hj, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.height_bot] at h1
    exact absurd h1 (by norm_num)
  exact (Ideal.span_singleton_prime hne).mp h.1

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
/-- Distinct strict normal crossings coordinates do not divide each other. -/
theorem not_dvd_of_isSNCCoordinates {x : X} {z : Fin n → X.presheaf.stalk x}
    (hz : IsSNCCoordinates f x z) {j l : Fin n} (hjl : j ≠ l) : ¬ z j ∣ z l := by
  intro hdvd
  have h2 := (hz.2 {j, l}).2.1
  have h1 := (hz.2 {j}).2.1
  rw [Finset.coe_singleton, Set.image_singleton, Finset.card_singleton] at h1
  have hspan : Ideal.span (z '' ↑({j, l} : Finset (Fin n))) = Ideal.span {z j} := by
    rw [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton,
      Ideal.span_insert]
    exact sup_eq_left.mpr ((Ideal.span_singleton_le_span_singleton).mpr hdvd)
  rw [hspan, h1, Finset.card_pair hjl] at h2
  exact absurd h2 (by norm_num)

omit [SmoothOfRelativeDimension n f] in
/-- **Exponents of a regular Laurent monomial are nonnegative**: if `r ∈ 𝒪_{X,x}` equals
`ε ∏ⱼ zⱼ^{aⱼ}` in `ℂ(X)` with `aⱼ ∈ ℤ` and strict normal crossings coordinates `zⱼ`, then all
`aⱼ ≥ 0` and `r = ε ∏ⱼ zⱼ^{aⱼ}` in `𝒪_{X,x}`. -/
theorem exists_nat_exponents_of_laurent {x : X} {z : Fin n → X.presheaf.stalk x}
    (hz : IsSNCCoordinates f x z) (r : X.presheaf.stalk x) (ε : (X.presheaf.stalk x)ˣ)
    (a : Fin n → ℤ)
    (h : algebraMap _ X.functionField r =
      algebraMap _ X.functionField (ε : X.presheaf.stalk x) *
        ∏ j, (algebraMap _ X.functionField (z j)) ^ (a j)) :
    ∃ b : Fin n → ℕ, r = ε * ∏ j, z j ^ b j := by
  classical
  set alg := algebraMap (X.presheaf.stalk x) X.functionField with halg
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have hz0 : ∀ j, alg (z j) ≠ 0 := fun j =>
    (map_ne_zero_iff _ hinj).mpr (prime_of_isSNCCoordinates hz j).ne_zero
  let b : Fin n → ℕ := fun j => (a j).toNat
  let d : Fin n → ℕ := fun j => (-a j).toNat
  have hab : ∀ j, (alg (z j)) ^ (a j) = (alg (z j)) ^ (b j) * ((alg (z j)) ^ (d j))⁻¹ := by
    intro j
    have : a j = (b j : ℤ) - (d j : ℤ) := by simp only [b, d]; omega
    rw [this, zpow_sub₀ (hz0 j), zpow_natCast, zpow_natCast, div_eq_mul_inv]
  -- clear denominators: `r ∏ zⱼ^{dⱼ} = ε ∏ zⱼ^{bⱼ}` in `𝒪_{X,x}`
  have hR : r * ∏ j, z j ^ d j = ε * ∏ j, z j ^ b j := by
    apply hinj
    have hd0 : ∏ j, alg (z j) ^ d j ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hz0 j)
    rw [map_mul, map_mul, map_prod, map_prod, h]
    simp only [map_pow, hab, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    field_simp
  -- no negative exponent: a coordinate dividing `ε ∏ zₗ^{bₗ}` would divide some `zₗ`, `l ≠ j`
  have hd : ∀ j, d j = 0 := by
    intro j
    by_contra hdj
    have hp := prime_of_isSNCCoordinates hz j
    have hdvd : z j ∣ ε * ∏ l, z l ^ b l := by
      rw [← hR]
      refine Dvd.dvd.mul_left ?_ _
      exact (dvd_pow_self (z j) hdj).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
    rcases hp.dvd_or_dvd hdvd with hε | hprod
    · exact hp.not_isUnit (isUnit_of_dvd_unit hε ε.isUnit)
    · obtain ⟨l, -, hl⟩ := (hp.dvd_finsetProd_iff _).mp hprod
      have hbl : b l ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hl
        exact hp.not_isUnit (isUnit_of_dvd_one hl)
      have hjl : j ≠ l := by
        rintro rfl
        simp only [b, d] at hdj hbl
        omega
      exact not_dvd_of_isSNCCoordinates hz hjl (hp.dvd_of_dvd_pow hl)
  refine ⟨b, ?_⟩
  have : ∏ j, z j ^ d j = 1 := Finset.prod_eq_one fun j _ => by rw [hd j, pow_zero]
  rw [this, mul_one] at hR
  exact hR

/-- **[CFKLRS17, Thm 2.9] on a log resolution chart.** As
`exists_admissibleFlag_lexEquivalent_of_monomial`, with the hypotheses in the form produced by a
log resolution (principalization) of `u₁, …, uₙ ∈ ℂ(X)`: at the centre `x` of `ν`, each `u_k` is
a Laurent monomial `ε_k ∏ⱼ zⱼ^{a_{kj}}` (`a_{kj} ∈ ℤ`) in strict normal crossings coordinates, and
`u_k` or `u_k⁻¹` is regular at `x` (`u_k` is a morphism to `ℙ¹` near `x`). -/
theorem exists_admissibleFlag_lexEquivalent_of_laurent
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {x : X}
    (hcent : AlgebraicValuation.IsValuationCenter ν x)
    {z : Fin n → X.presheaf.stalk x} (hz : IsSNCCoordinates f x z)
    (u : Fin n → X.functionField) (ε : Fin n → (X.presheaf.stalk x)ˣ) (a : Fin n → Fin n → ℤ)
    (hu : ∀ k, u k = algebraMap _ X.functionField (ε k : X.presheaf.stalk x) *
      ∏ j, (algebraMap _ X.functionField (z j)) ^ (a k j))
    (hreg : ∀ k, (∃ r : X.presheaf.stalk x, algebraMap _ X.functionField r = u k) ∨
      ∃ r : X.presheaf.stalk x, algebraMap _ X.functionField r = (u k)⁻¹)
    (hνu : ∀ k, ν (u k) = basisValue k) :
    ∃ (Y : Fin (n + 1) → Set X) (hY : IsAdmissibleFlag f n Y), hY.point = x ∧
      ValuationsLexEquivalent (admissibleFlagValuation hY) ν := by
  classical
  -- `u_k` is regular at `x`: `u_k⁻¹` regular would give `ν(u_k⁻¹) = -e_k ≥ 0`
  have hreg' : ∀ k, ∃ r : X.presheaf.stalk x, algebraMap _ X.functionField r = u k := by
    intro k
    rcases hreg k with h | ⟨r, hr⟩
    · exact h
    · exfalso
      have h0 := hcent.1 r
      rw [hr] at h0
      have hu0 : u k ≠ 0 := by
        intro h0'
        have := hνu k
        rw [h0', AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      have hsum : ν (u k) + ν (u k)⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hu0, AddValuation.map_one]
      rw [hνu k] at hsum
      obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp (show ν (u k)⁻¹ ≠ ⊤ from by
        intro ht
        rw [ht, WithTop.add_top] at hsum
        exact WithTop.top_ne_coe hsum)
      rw [← hw] at hsum h0
      have h1 : (toLex (Pi.single k (1 : ℤ)) : Lex (Fin n → ℤ)) + w = 0 :=
        WithTop.coe_injective hsum
      have h2 : (0 : Lex (Fin n → ℤ)) ≤ w := WithTop.coe_le_coe.mp h0
      have h3 : (0 : Lex (Fin n → ℤ)) < toLex (Pi.single k (1 : ℤ)) := by
        refine (lex_pos_iff _).mpr ⟨k, fun j hj => ?_, by simp⟩
        simp [hj.ne]
      have := add_pos_of_pos_of_nonneg h3 h2
      rw [h1] at this
      exact lt_irrefl _ this
  choose r hr using hreg'
  have hb : ∀ k, ∃ b : Fin n → ℕ, r k = ε k * ∏ j, z j ^ b j := fun k =>
    exists_nat_exponents_of_laurent hz (r k) (ε k) (a k) ((hr k).trans (hu k))
  choose b hb using hb
  exact exists_admissibleFlag_lexEquivalent_of_monomial ν hcent hz r ε b hb
    (fun k => by rw [hr k]; exact hνu k)

end Laurent

/-! ### On a model of `ℂ(X)` -/

section Model

variable {n : ℕ}

/-- **[CFKLRS17, Thm 2.9] on a model.** Let `X` be integral, `ν : ℂ(X)^× → ℤⁿ_lex` a valuation,
and `X'` an integral scheme, smooth of relative dimension `n` over `ℂ`, with an identification
`e : ℂ(X) ≃ ℂ(X')` (a model of `ℂ(X)`; for a modification `X' → X` the pull-back of rational
functions). Suppose that, at the centre `x` of `ν` on `X'`, the functions `u₁, …, uₙ ∈ ℂ(X)` with
`ν(u_k) = e_k` become Laurent monomials in strict normal crossings coordinates, `u_k` or `u_k⁻¹`
regular at `x` (as after a log resolution of `u₁, …, uₙ`). Then `ν` is equivalent to the
valuation `ν_{Y•} ∘ e` of `ℂ(X)` induced by an admissible flag `Y•` on `X'` with point `x`. -/
theorem exists_admissibleFlag_lexEquivalent_of_model {X X' : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] {f' : X' ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension n f']
    (e : X.functionField ≃+* X'.functionField)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {x : X'}
    (hcent : AlgebraicValuation.IsValuationCenter (ν.comap e.symm.toRingHom) x)
    {z : Fin n → X'.presheaf.stalk x} (hz : IsSNCCoordinates f' x z)
    (u : Fin n → X.functionField) (ε : Fin n → (X'.presheaf.stalk x)ˣ) (a : Fin n → Fin n → ℤ)
    (hu : ∀ k, e (u k) = algebraMap _ X'.functionField (ε k : X'.presheaf.stalk x) *
      ∏ j, (algebraMap _ X'.functionField (z j)) ^ (a k j))
    (hreg : ∀ k, (∃ r : X'.presheaf.stalk x, algebraMap _ X'.functionField r = e (u k)) ∨
      ∃ r : X'.presheaf.stalk x, algebraMap _ X'.functionField r = (e (u k))⁻¹)
    (hνu : ∀ k, ν (u k) = basisValue k) :
    ∃ (Y : Fin (n + 1) → Set X') (hY : IsAdmissibleFlag f' n Y), hY.point = x ∧
      ValuationsLexEquivalent ((admissibleFlagValuation hY).comap e.toRingHom) ν := by
  obtain ⟨Y, hY, hpt, G, hG, hν⟩ := exists_admissibleFlag_lexEquivalent_of_laurent
    (ν.comap e.symm.toRingHom) hcent hz (fun k => e (u k)) ε a hu hreg (fun k => by
      change ν (e.symm (e (u k))) = _
      rw [e.symm_apply_apply]
      exact hνu k)
  refine ⟨Y, hY, hpt, G, hG, ?_⟩
  ext g
  have h := congrArg
    (fun w : AddValuation X'.functionField (WithTop (Lex (Fin n → ℤ))) => w (e g)) hν
  change ν (e.symm (e g)) = lexWithTopHom G hG (admissibleFlagValuation hY (e g)) at h
  rw [e.symm_apply_apply] at h
  rw [lexMapValuation_apply]
  exact h

/-- **[CFKLRS17, Thm 2.9] on a proper model**: as `exists_admissibleFlag_lexEquivalent_of_model`
for `X'` proper over `ℂ` (e.g. a projective modification of `X`), where the centre `x` of `ν` on
`X'` exists and is unique (valuative criterion); only the log resolution data of
`u₁, …, uₙ` at the centre are assumed. -/
theorem exists_admissibleFlag_lexEquivalent_of_properModel {X X' : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] {f' : X' ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension n f'] [IsProper f']
    (e : X.functionField ≃+* X'.functionField)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    {z : Fin n → X'.presheaf.stalk
      (AlgebraicValuation.valuationCenter f' (ν.comap e.symm.toRingHom))}
    (hz : IsSNCCoordinates f' _ z)
    (u : Fin n → X.functionField)
    (ε : Fin n → (X'.presheaf.stalk
      (AlgebraicValuation.valuationCenter f' (ν.comap e.symm.toRingHom)))ˣ)
    (a : Fin n → Fin n → ℤ)
    (hu : ∀ k, e (u k) = algebraMap _ X'.functionField ((ε k).1) *
      ∏ j, (algebraMap _ X'.functionField (z j)) ^ (a k j))
    (hreg : ∀ k, (∃ r : X'.presheaf.stalk
        (AlgebraicValuation.valuationCenter f' (ν.comap e.symm.toRingHom)),
        algebraMap _ X'.functionField r = e (u k)) ∨
      ∃ r : X'.presheaf.stalk (AlgebraicValuation.valuationCenter f' (ν.comap e.symm.toRingHom)),
        algebraMap _ X'.functionField r = (e (u k))⁻¹)
    (hνu : ∀ k, ν (u k) = basisValue k) :
    ∃ (Y : Fin (n + 1) → Set X') (hY : IsAdmissibleFlag f' n Y),
      hY.point = AlgebraicValuation.valuationCenter f' (ν.comap e.symm.toRingHom) ∧
      ValuationsLexEquivalent ((admissibleFlagValuation hY).comap e.toRingHom) ν :=
  exists_admissibleFlag_lexEquivalent_of_model e ν
    (AlgebraicValuation.isValuationCenter_valuationCenter f' _) hz u ε a hu hreg hνu

end Model

end SGPT.Okounkov.OF11

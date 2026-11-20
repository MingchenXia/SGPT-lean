import SGPT.TestCurve.TestConfigFiltration

/-!
# Monomial generators of a finitely generated `ℤ`-filtration

Input of `SkodaInclusionIdeal` (the Skoda-division part of [RWN14, Theorem 7.10], used for
`rmk:PhongSturm`, chapter *Test curves*). A finitely generated `ℤ`-filtration `𝓕` of the section
ring `R(X, L)` (the encoding of an ample test configuration, [BHJ17, Prop. 2.15]) has a finite
family of bihomogeneous generators `t^{-μᵢ} gᵢ`, `gᵢ ∈ 𝓕^{μᵢ}_{mᵢ}`, of its Rees algebra. Hence
every element of `𝓕^λ_k` is a linear combination of the *monomials*
`g^e = ∏ᵢ gᵢ^{eᵢ}` of degree `∑ eᵢ mᵢ = k` and weight `∑ eᵢ μᵢ = λ`.

## Main definitions

* `ReesGenerators 𝓕`: a finite family of bihomogeneous generators of the Rees algebra.
* `ReesGenerators.secMonomial e = ∏ᵢ gᵢ^{eᵢ}` (in the section ring), with its degree
  `ReesGenerators.degree e = ∑ eᵢ mᵢ` and weight `ReesGenerators.weight e = ∑ eᵢ μᵢ`.

## Main results

* `SectionZFiltration.exists_reesGenerators`: a finitely generated `ℤ`-filtration has a finite
  family of bihomogeneous generators.
* `ReesGenerators.exists_secMonomial_eq`: `g^e` is homogeneous of degree `∑ eᵢ mᵢ`, lies in
  `𝓕^{∑ eᵢ μᵢ}`, and every multiplicative function of sections takes the value
  `∏ᵢ ν(gᵢ)^{eᵢ}` on it.
* **`ReesGenerators.mem_span_secMonomial`**: `𝓕^λ_k` is spanned by the monomials of degree `k`
  and weight `λ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.SkodaInc

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TestConfig.LaurentSecRing

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}

/-- A finite family of bihomogeneous generators `t^{-μᵢ} gᵢ` (`gᵢ ∈ 𝓕^{μᵢ}_{mᵢ}`) of the Rees
algebra of a `ℤ`-filtration `𝓕` of `R(X, L)`. -/
structure ReesGenerators (G : SectionZFiltration f a) where
  /-- The number of generators. -/
  card : ℕ
  /-- The weights `μᵢ`. -/
  wt : Fin card → ℤ
  /-- The degrees `mᵢ`. -/
  deg : Fin card → ℕ
  /-- The sections `gᵢ ∈ H⁰(X, L^{mᵢ})`. -/
  gen : (i : Fin card) → SectionSpace f L (deg i)
  gen_mem : ∀ i, gen i ∈ G.piece (wt i) (deg i)
  adjoin_eq : Algebra.adjoin ℂ
    (Set.range fun i => (mono (-wt i) (deg i) (gen i) : LaurentSecRing f a)) = G.rees

namespace SectionZFiltration

variable (G : SectionZFiltration f a)

/-- **A finitely generated `ℤ`-filtration has finitely many bihomogeneous generators.** -/
theorem exists_reesGenerators (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤) :
    Nonempty (ReesGenerators G) := by
  classical
  obtain ⟨T, hT⟩ := hG
  have hmem : ∀ x : T, ∃ U : Finset (LaurentSecRing f a),
      (↑U : Set (LaurentSecRing f a)) ⊆ G.reesGen ∪ {1} ∧ x.1 ∈ Submodule.span ℂ (↑U : Set _) :=
    fun x => G.exists_finset_of_mem_rees (hT ▸ Algebra.subset_adjoin x.2)
  choose U hUgen hUspan using hmem
  set V : Finset (LaurentSecRing f a) := T.attach.biUnion U with hV
  have hVgen : ∀ v ∈ V, ∃ (μ : ℤ) (m : ℕ) (s : SectionSpace f L m),
      s ∈ G.piece μ m ∧ v = mono (-μ) m s := by
    intro v hv
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hv
    rcases hUgen x hx with ⟨μ, m, s, hs, rfl⟩ | h1
    · exact ⟨μ, m, s, hs, rfl⟩
    · refine ⟨0, 0, secOne f L, by rw [h0]; exact Submodule.mem_top, ?_⟩
      rw [Set.mem_singleton_iff.mp h1, neg_zero]
      rfl
  have hadj : Algebra.adjoin ℂ (↑V : Set (LaurentSecRing f a)) = G.rees := by
    apply le_antisymm
    · refine Algebra.adjoin_le fun v hv => ?_
      obtain ⟨μ, m, s, hs, rfl⟩ := hVgen v hv
      exact G.mono_mem_rees hs
    · rw [← hT]
      refine Algebra.adjoin_le fun x hx => ?_
      have hx' := hUspan ⟨x, hx⟩
      have hle : Submodule.span ℂ (↑(U ⟨x, hx⟩) : Set (LaurentSecRing f a)) ≤
          Subalgebra.toSubmodule (Algebra.adjoin ℂ (↑V : Set (LaurentSecRing f a))) := by
        refine Submodule.span_le.mpr fun y hy => Algebra.subset_adjoin ?_
        exact Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩
      exact hle hx'
  let e := V.equivFin.symm
  have hgen : ∀ i : Fin V.card, ∃ (μ : ℤ) (m : ℕ) (s : SectionSpace f L m),
      s ∈ G.piece μ m ∧ (e i).1 = mono (-μ) m s := fun i => hVgen (e i).1 (e i).2
  choose μ m s hs hes using hgen
  refine ⟨⟨V.card, μ, m, s, hs, ?_⟩⟩
  have hrange : (Set.range fun i => (mono (-μ i) (m i) (s i) : LaurentSecRing f a)) = ↑V := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      change (mono (-μ i) (m i) (s i) : LaurentSecRing f a) ∈ (↑V : Set (LaurentSecRing f a))
      rw [← hes i]
      exact (e i).2
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, ?_⟩
      simp only [← hes, Equiv.apply_symm_apply]
  rw [hrange, hadj]

end SectionZFiltration

namespace ReesGenerators

variable {G : SectionZFiltration f a} (R : ReesGenerators G)

/-- The monomial `g^e = ∏ᵢ gᵢ^{eᵢ}` in the section ring. -/
def secMonomial (e : Fin R.card → ℕ) : SecRing f a :=
  ∏ i, (SecRing.of (R.deg i) (R.gen i) : SecRing f a) ^ e i

/-- The degree `∑ eᵢ mᵢ` of the monomial `g^e`. -/
def degree (e : Fin R.card → ℕ) : ℕ := ∑ i, e i * R.deg i

/-- The weight `∑ eᵢ μᵢ` of the monomial `g^e`. -/
def weight (e : Fin R.card → ℕ) : ℤ := ∑ i, (e i : ℤ) * R.wt i

/-- The homogeneous elements of the section ring, of degree `D` and in `𝓕^Λ`, with the value
`g` of a function `ν` of sections. -/
private def IsHomog {Y : Type*} (ν : ∀ D : ℕ, SectionSpace f L D → Y → ℝ) (x : SecRing f a)
    (D : ℕ) (Λ : ℤ) (g : Y → ℝ) : Prop :=
  ∃ s : SectionSpace f L D, x = SecRing.of D s ∧ s ∈ G.piece Λ D ∧ ν D s = g

private theorem IsHomog.congr {Y : Type*} {ν : ∀ D : ℕ, SectionSpace f L D → Y → ℝ}
    {x : SecRing f a} {D D' : ℕ} {Λ Λ' : ℤ} {g : Y → ℝ} (h : IsHomog (G := G) ν x D Λ g)
    (hD : D = D') (hΛ : Λ = Λ') : IsHomog (G := G) ν x D' Λ' g := by
  subst hD hΛ
  exact h

private theorem IsHomog.one {Y : Type*} {ν : ∀ D : ℕ, SectionSpace f L D → Y → ℝ}
    (hν1 : ν 0 (secOne f L) = 1) (h0 : G.piece 0 0 = ⊤) :
    IsHomog (G := G) ν 1 0 0 1 :=
  ⟨secOne f L, rfl, by rw [h0]; exact Submodule.mem_top, hν1⟩

private theorem IsHomog.mul {Y : Type*} {ν : ∀ D : ℕ, SectionSpace f L D → Y → ℝ}
    (hνmul : ∀ (D D' : ℕ) (s : SectionSpace f L D) (t : SectionSpace f L D'),
      ν (D + D') (SectionSpace.mul f a D D' s t) = ν D s * ν D' t)
    {x y : SecRing f a} {D D' : ℕ} {Λ Λ' : ℤ} {g g' : Y → ℝ}
    (hx : IsHomog (G := G) ν x D Λ g) (hy : IsHomog (G := G) ν y D' Λ' g') :
    IsHomog (G := G) ν (x * y) (D + D') (Λ + Λ') (g * g') := by
  obtain ⟨s, rfl, hs, rfl⟩ := hx
  obtain ⟨t, rfl, ht, rfl⟩ := hy
  exact ⟨SectionSpace.mul f a D D' s t, SecRing.of_mul_of D D' s t,
    G.mul_mem Λ Λ' D D' s t hs ht, hνmul D D' s t⟩

private theorem IsHomog.pow {Y : Type*} {ν : ∀ D : ℕ, SectionSpace f L D → Y → ℝ}
    (hν1 : ν 0 (secOne f L) = 1) (h0 : G.piece 0 0 = ⊤)
    (hνmul : ∀ (D D' : ℕ) (s : SectionSpace f L D) (t : SectionSpace f L D'),
      ν (D + D') (SectionSpace.mul f a D D' s t) = ν D s * ν D' t)
    {x : SecRing f a} {D : ℕ} {Λ : ℤ} {g : Y → ℝ} (hx : IsHomog (G := G) ν x D Λ g) (k : ℕ) :
    IsHomog (G := G) ν (x ^ k) (k * D) ((k : ℤ) * Λ) (g ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact (IsHomog.one hν1 h0).congr (by ring) (by ring)
  | succ k ih =>
    rw [pow_succ, pow_succ]
    refine (IsHomog.mul hνmul ih hx).congr ?_ ?_
    · ring
    · push_cast; ring

/-- **The monomials are homogeneous.** `g^e` is the image of a section `s ∈ 𝓕^{∑ eᵢ μᵢ}` of
degree `∑ eᵢ mᵢ`, and every multiplicative function `ν` of sections (normalized by `ν(1) = 1`)
satisfies `ν(s) = ∏ᵢ ν(gᵢ)^{eᵢ}`. -/
theorem exists_secMonomial_eq {Y : Type*} (ν : ∀ D : ℕ, SectionSpace f L D → Y → ℝ)
    (hν1 : ν 0 (secOne f L) = 1)
    (hνmul : ∀ (D D' : ℕ) (s : SectionSpace f L D) (t : SectionSpace f L D'),
      ν (D + D') (SectionSpace.mul f a D D' s t) = ν D s * ν D' t)
    (h0 : G.piece 0 0 = ⊤) (e : Fin R.card → ℕ) :
    ∃ s : SectionSpace f L (R.degree e), R.secMonomial e = SecRing.of (R.degree e) s ∧
      s ∈ G.piece (R.weight e) (R.degree e) ∧ ν (R.degree e) s = ∏ i, ν (R.deg i) (R.gen i) ^ e i := by
  classical
  have key : ∀ T : Finset (Fin R.card),
      IsHomog (G := G) ν (∏ i ∈ T, (SecRing.of (R.deg i) (R.gen i) : SecRing f a) ^ e i)
        (∑ i ∈ T, e i * R.deg i) (∑ i ∈ T, (e i : ℤ) * R.wt i)
        (∏ i ∈ T, ν (R.deg i) (R.gen i) ^ e i) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact (IsHomog.one hν1 h0).congr (by simp) (by simp)
    | insert j T hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, Finset.prod_insert hj]
      exact IsHomog.mul hνmul
        (IsHomog.pow hν1 h0 hνmul ⟨R.gen j, rfl, R.gen_mem j, rfl⟩ (e j)) ih
  obtain ⟨s, hs, hmem, hν⟩ := key Finset.univ
  exact ⟨s, hs, hmem, hν⟩

/-- The product of the powers of the generators `t^{-μᵢ} gᵢ` of the Rees algebra. -/
theorem prod_mono_pow (e : Fin R.card → ℕ) :
    (∏ i, (mono (-R.wt i) (R.deg i) (R.gen i) : LaurentSecRing f a) ^ e i) =
      AddMonoidAlgebra.single (-R.weight e) (R.secMonomial e) := by
  simp only [mono, AddMonoidAlgebra.single_pow]
  rw [AddMonoidAlgebra.prod_single]
  congr 1
  simp only [weight, nsmul_eq_mul, mul_neg, Finset.sum_neg_distrib]

/-- **The monomials span the filtration**: every `s ∈ 𝓕^λ_k` is a linear combination of the
monomials `g^e` of degree `k` and weight `λ`. -/
theorem mem_span_secMonomial (h0 : G.piece 0 0 = ⊤) {lam : ℤ} {k : ℕ} {s : SectionSpace f L k}
    (hs : s ∈ G.piece lam k) :
    s ∈ Submodule.span ℂ {t : SectionSpace f L k | ∃ e : Fin R.card → ℕ,
      R.weight e = lam ∧ R.degree e = k ∧ t = SecRing.comp k (R.secMonomial e)} := by
  classical
  have h1 : (mono (-lam) k s : LaurentSecRing f a) ∈ Subalgebra.toSubmodule G.rees :=
    G.mono_mem_rees hs
  rw [← R.adjoin_eq, Algebra.adjoin_eq_span] at h1
  have h2 := Submodule.mem_map_of_mem (f := coeffAt (a := a) (-lam) k) h1
  rw [coeffAt_mono_same, Submodule.map_span] at h2
  refine (Submodule.span_le.mpr ?_) h2
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨c, rfl⟩ := Submonoid.mem_closure_range_iff.mp hy
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), R.prod_mono_pow]
  change SecRing.comp k ((AddMonoidAlgebra.single (-R.weight c) (R.secMonomial c) :
    LaurentSecRing f a).coeff (-lam)) ∈ _
  rw [AddMonoidAlgebra.coeff_single]
  by_cases hw : -R.weight c = -lam
  · rw [hw, Finsupp.single_eq_same]
    have hw' : R.weight c = lam := neg_injective hw
    by_cases hd : R.degree c = k
    · exact Submodule.subset_span ⟨c, hw', hd, rfl⟩
    · obtain ⟨t, ht, -, -⟩ := R.exists_secMonomial_eq (Y := Unit) (fun _ _ _ => 1) rfl
        (fun _ _ _ _ => (mul_one 1).symm) h0 c
      rw [ht, SecRing.comp_of_ne (Ne.symm hd)]
      exact zero_mem _
  · rw [Finsupp.single_eq_of_ne (Ne.symm hw)]
    exact zero_mem _

end ReesGenerators

end SGPT.TestCurve.SkodaInc
